import docker
from docker.errors import APIError, NotFound
import os
import socket
import requests
import sqlite3
import datetime
import subprocess
import psutil
import logging
import time
# from rich.logging import RichHandler
from globalSettings import DBPath
from docker_cli_helper import run_container_with_sdk

# Initialize logger
# logging.basicConfig(level="INFO", format="%(message)s", datefmt="[%X]", handlers=[RichHandler()])
logging.basicConfig(level="INFO", format="%(message)s", datefmt="[%X]")
logger = logging.getLogger("docker-sdk-functions")


def get_host_available_resources(container_name=None):
    client = docker.from_env()
    
    # CPU: Total logical cores
    total_cpus = int(subprocess.getoutput('nproc --all'))
    
    # Memory: Total in GB
    mem_output = subprocess.getoutput("free -g | awk '/Mem:/ {print $2}'")
    total_memory_gb = float(mem_output) if mem_output.isdigit() else 0.0
    
    used_cpus = 0
    used_memory_gb = 0
    if container_name:
        try:
            container = client.containers.get(container_name)
            stats = container.stats(stream=False)
            
            # Safe memory access
            used_memory_gb = round(stats.get('memory_stats', {}).get('usage', 0) / (1024 ** 3), 2)
            
            # Safe CPU access with nested gets
            cpu_stats = stats.get('cpu_stats', {})
            precpu_stats = stats.get('precpu_stats', {})
            cpu_usage = cpu_stats.get('cpu_usage', {})
            precpu_usage = precpu_stats.get('cpu_usage', {})
            
            cpu_delta = cpu_usage.get('total_usage', 0) - precpu_usage.get('total_usage', 0)
            system_delta = cpu_stats.get('system_cpu_usage', 0) - precpu_stats.get('system_cpu_usage', 0)
            
            percpu = cpu_usage.get('percpu_usage', [])  # Fallback to empty list if missing
            num_cpus = len(percpu) if percpu else total_cpus  # Use host CPUs if per-CPU data missing
            
            cpu_percent = (cpu_delta / system_delta) * num_cpus * 100 if system_delta > 0 and cpu_delta > 0 else 0
            used_cpus = round(cpu_percent / 100, 1)
        except Exception as e:
            print(f"[WARN] Could not get stats for '{container_name}': {e}. Defaulting usage to 0.")
    
    # Storage: From DB and df (assumes partition mount)
    conn = sqlite3.connect(DBPath)
    c = conn.cursor()
    c.execute("""
        SELECT sp.location, v.vm_disk_size 
        FROM virtualmachine v 
        JOIN vm_storage vs ON vs.vm_id = v.id 
        JOIN storagepath sp ON sp.id = vs.volume_id 
        WHERE v.name = ?
    """, (container_name,))
    row = c.fetchone()
    partition_path = row[0] if row else None
    current_disk_gb = row[1] if row else 0
    used_disk_gb = free_disk_gb = total_disk_gb = 0
    if partition_path:
        df_output = subprocess.getoutput(f"df -BG {partition_path} | tail -1")
        parts = df_output.split()
        if len(parts) >= 4:
            total_disk_gb = float(parts[1].rstrip('G'))
            used_disk_gb = float(parts[2].rstrip('G'))
            free_disk_gb = float(parts[3].rstrip('G'))
    conn.close()
    
    return {
        "cpus": {"total": total_cpus, "used": used_cpus, "free": total_cpus - used_cpus},
        "memory_gb": {"total": total_memory_gb, "used": used_memory_gb, "free": total_memory_gb - used_memory_gb},
        "storage_gb": {"total": total_disk_gb, "used": used_disk_gb, "free": free_disk_gb, "current": current_disk_gb}
    }

def list_available_partitions():
    conn = sqlite3.connect(DBPath)
    c = conn.cursor()
    c.execute("SELECT id, location FROM storagepath WHERE state=1")
    rows = c.fetchall()
    if not rows:
        print("No available partitions found.")
    else:
        print("Available Partitions:")
        for row in rows:
            print(f"ID: {row[0]} - Path: {row[1]}")
    c.close()
    conn.close()

def create_container_with_partition_attached(args):
    partition_id = int(args.partition_id)
    conn = sqlite3.connect(DBPath)
    c = conn.cursor()
    c.execute("SELECT location FROM storagepath WHERE id=? AND state=1", (partition_id,))
    row = c.fetchone()
    if not row:
        print(f"❌ Partition ID {partition_id} is not available.")
        return

    mount_path = row[0]
    print(f"🧩 Using mount path: {mount_path}")

    # Mark it as in-use
    c.execute("UPDATE storagepath SET state=0 WHERE id=?", (partition_id,))
    # Save to vm_storage
    c.execute("SELECT id FROM virtualmachine WHERE name=?", (args.name,))
    vm_row = c.fetchone()
    if vm_row:
        vm_id = vm_row[0]
        c.execute("INSERT INTO vm_storage (name, state, vm_id, cr_date) VALUES (?, ?, ?, datetime())", (f"partition_{partition_id}", 1, vm_id))
    conn.commit()
    c.close()
    conn.close()

    # Now create the container
    print("🚀 Launching container...")
    result = create_container(
        image=args.image,
        name=args.name,
        exec_cmd=args.exec,
        memory=args.memory,
        cpus=args.cpus,
        port=args.port,
        volume_host_path=mount_path,
        volume_container_path="/data",
        network=args.network,
        runtime=args.runtime,
    )
    print("✅ Container created:")
    print(result)


def register_vm_and_networks_in_db(
    name, vcpu, memory, disk_size, image_id, vm_type, portNo, ssh_port, network_names: list, state=6, saved_path=None
):
    date = datetime.date.today().strftime("%Y-%m-%d")
    conn = sqlite3.connect(DBPath)
    conn.text_factory = str
    c = conn.cursor()
    try:
        # --- Check if VM exists ---
        c.execute("SELECT id FROM virtualmachine WHERE name = ?", (name,))
        row = c.fetchone()
        if row:
            vm_id = row[0]
            # Update the existing VM's config and state!
            c.execute("""
                UPDATE virtualmachine SET num_cores=?, memory_GB=?, vm_disk_size=?, vm_image_id=?, 
                    edit_date=?, saved_path=?, state=?, type=?, port=?, ssh_port=?
                WHERE id=?
            """, (vcpu, memory, disk_size, image_id, date, saved_path or f"/vm/{name}", state, vm_type, portNo, ssh_port, vm_id))

            # First, clean up old veth/links for this VM
            # c.execute("SELECT veth_id FROM vm_network WHERE vm_id = ?", (vm_id,))
            # veth_ids = [row[0] for row in c.fetchall()]
            # if veth_ids:
            #     # Delete old vm_network mappings
            #     c.execute("DELETE FROM vm_network WHERE vm_id = ?", (vm_id,))
            #     # Delete those veth_ports
            #     c.executemany("DELETE FROM veth_port WHERE id = ?", [(veth_id,) for veth_id in veth_ids])
        else:
            # Insert new VM
            c.execute("""
                INSERT INTO virtualmachine
                (name,num_cores,memory_GB,vm_disk_size,vm_image_id,cr_date,edit_date,saved_path,state,type,port,ssh_port)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                name, vcpu, memory, disk_size, image_id, date, date, saved_path or f"/vm/{name}", state, vm_type, portNo, ssh_port
            ))
            vm_id = c.lastrowid

        # --- Insert fresh mappings for this VM ---
        veth_id_list = []
        for net_name in network_names:
            c.execute("SELECT id FROM network WHERE name=?", (net_name,))
            netrow = c.fetchone()
            if netrow:
                network_id = netrow[0]
                c.execute("""
                    INSERT INTO veth_port (name,state,cr_date,edit_date,ip,netmask,network_id)
                    VALUES (?, 0, ?, ?, '0.0.0.0', '255.255.255.0', ?)
                """, (net_name, date, date, network_id))
                veth_id = c.lastrowid
                veth_id_list.append(veth_id)
        # Map veth_ports to VM in vm_network
        for veth_id in veth_id_list:
            c.execute("INSERT INTO vm_network (vm_id,veth_id) VALUES (?, ?)", (vm_id, veth_id))

        conn.commit()
        return vm_id
    finally:
        c.close()
        conn.close()
def ensure_image_and_group(image_name, group_name="SanuyiRepo"):
    conn = sqlite3.connect(DBPath)
    c = conn.cursor()
    # Find the group, create if needed
    c.execute("SELECT id FROM vm_group WHERE group_name=?", (group_name,))
    group_row = c.fetchone()
    if group_row:
        group_id = group_row[0]
    else:
        # create group with default icon if missing
        c.execute("INSERT INTO vm_group (group_name, path_group_icon) VALUES (?, ?)", (group_name, "/images/sanuyi.svg"))
        group_id = c.lastrowid

    # Now ensure image exists and is linked to the group!
    c.execute("SELECT id FROM vm_image WHERE image_name=?", (image_name,))
    img_row = c.fetchone()
    if img_row:
        image_id = img_row[0]
        # always force the group assignment!
        c.execute("UPDATE vm_image SET vm_group_id=? WHERE id=?", (group_id, image_id))
    else:
        date = datetime.date.today().strftime("%Y-%m-%d")
        c.execute(
            "INSERT INTO vm_image (image_name, state, cr_date, edit_date, vm_group_id) VALUES (?, ?, ?, ?, ?)",
            (image_name, 1, date, date, group_id)
        )
        image_id = c.lastrowid

    conn.commit()
    c.close()
    conn.close()
    return image_id
def assign_group_to_image(c, image_id, group_name):
    c.execute("SELECT id FROM vm_group WHERE group_name=?", (group_name,))
    g_row = c.fetchone()
    if g_row:
        group_id = g_row[0]
        c.execute("UPDATE vm_image SET vm_group_id=? WHERE id=?", (group_id, image_id))
        return group_id
    return None

# Now, when you create a container, call ensure_image_and_group instead of ensure_image_exists
def ensure_image_exists(image_name, group_id=None, group_name=None):
    conn = sqlite3.connect(DBPath)
    c = conn.cursor()
    # Try to find exact match first
    c.execute("SELECT id FROM vm_image WHERE image_name=?", (image_name,))
    row = c.fetchone()
    if row:
        image_id = row[0]
        # Optionally update group_id if provided and not already set
        if group_id and group_id != 0:
            c.execute("UPDATE vm_image SET vm_group_id=? WHERE id=?", (group_id, image_id))
        elif group_name:
            c.execute("SELECT id FROM vm_group WHERE group_name=?", (group_name,))
            g_row = c.fetchone()
            if g_row:
                c.execute("UPDATE vm_image SET vm_group_id=? WHERE id=?", (g_row[0], image_id))
        conn.commit()
    else:
        date = datetime.date.today().strftime("%Y-%m-%d")
        gid = None
        if group_id and group_id != 0:
            gid = group_id
        elif group_name:
            c.execute("SELECT id FROM vm_group WHERE name=?", (group_name,))
            g_row = c.fetchone()
            gid = g_row[0] if g_row else None
        c.execute(
            "INSERT INTO vm_image (image_name, state, cr_date, edit_date, vm_group_id) VALUES (?, ?, ?, ?, ?)",
            (image_name, 1, date, date, gid)
        )
        image_id = c.lastrowid
        conn.commit()
    c.close()
    conn.close()
    return image_id
#def parse_memory(mem_str):
 #   if not mem_str:
  #      return 0
   # mem_str = str(mem_str).lower().strip()
   # if mem_str.endswith("g"):
    #    return float(mem_str[:-1])
    #elif mem_str.endswith("m"):
    #    return round(float(mem_str[:-1]) / 1024, 3)
    #else:
     #   return float(mem_str)


def docker_login(registry, username, password):
    """
    Perform 'docker login' via the Docker SDK to authenticate with a private registry.
    """
    client = docker.from_env()
    try:
        client.login(username=username, password=password, registry=registry)
        print(f"[DEBUG] Docker login succeeded for {registry}")
        return True
    except Exception as e:
        print(f"[DEBUG] Docker login failed for {registry}: {e}")
        return False

def import_docker_image_from_tar(tar_path, image_name=None):
    """
    Load a Docker image tarball (as from `docker save`) into Docker.
    Optionally retag as image_name.
    """
    client = docker.from_env()
    if not os.path.exists(tar_path):
        return f"Image tar {tar_path} does not exist"
    try:
        with open(tar_path, "rb") as f:
            result = client.images.load(f.read())
        if image_name:
            loaded_image = result[0]
            loaded_image.tag(image_name)
        return "success"
    except Exception as e:
        return f"Error loading docker image: {e}"

def find_free_port():
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.bind(('', 0))
        return s.getsockname()[1]

def get_public_ip():
    try:
        return requests.get("https://api.ipify.org").text
    except Exception:
        return "localhost"

def create_container(
    image,
    name,
    exec_cmd=None,
    auto_remove=False,
    cap_add=None,
    volume_host_path=None,
    volume_container_path=None,
    network=None,
    memory=None,
    cpus=None,
    port=None,
    storage=None,
    runtime=None
):
    PRIVATE_REGISTRY = "3.7.194.44:443"
    REGISTRY_USER = "admin"
    REGISTRY_PASS = "S3curePassw0rd"
    if image.startswith(PRIVATE_REGISTRY):
        docker_login(PRIVATE_REGISTRY, REGISTRY_USER, REGISTRY_PASS)

    client = docker.from_env()
    cmd_list = exec_cmd.split() if exec_cmd else None
    volumes = {}
    
    # Device mapping setup
    devices = []
    device_cgroup_rules = []
    if volume_host_path and volume_container_path:
        if os.path.exists(volume_host_path):
            volumes[volume_host_path] = {'bind': volume_container_path, 'mode': 'rw'}
            # Find the device associated with volume_host_path
            try:
                # Use `findmnt` or `lsblk` to get the device for the mount point
                import subprocess
                result = subprocess.run(
                    ['findmnt', '-n', '-o', 'SOURCE', volume_host_path],
                    capture_output=True, text=True, check=True
                )
                device_path = result.stdout.strip()  # e.g., /dev/sdb1
                if device_path and os.path.exists(device_path):
                    devices.append(f"{device_path}:{device_path}:rwm")
                    # Get major:minor number for the device
                    stat = os.stat(device_path)
                    major = os.major(stat.st_rdev)
                    minor = os.minor(stat.st_rdev)
                    device_cgroup_rules.append(f"b {major}:{minor} rwm")
                else:
                    pass
                    # print(f"[WARNING] Could not determine device for {volume_host_path}")
            except subprocess.CalledProcessError as e:
                pass
                # print(f"[WARNING] Failed to find device for {volume_host_path}: {e}")
    elif storage:
        volumes[storage] = {'bind': '/data', 'mode': 'rw'}

    host_config_kwargs = {
        "auto_remove": auto_remove,
        "cap_add": cap_add or [],
        "binds": [f"{k}:{v['bind']}:rw" for k, v in volumes.items()] if volumes else [],
        "devices": devices,  # Map specific device
        "device_cgroup_rules": device_cgroup_rules,  # Restrict to specific device
        # "cpuset_cpus": args.cpuset_cpus if args.cpuset_cpus else None,
    }
    if memory:
        host_config_kwargs["mem_limit"] = str(memory)
    if cpus:
        host_config_kwargs["nano_cpus"] = int(float(cpus) * 1e9)
        # print(f"DEBUG: Setting nano_cpus to {int(float(cpus) * 1e9)} for {name}")
    port_to_bind = int(port) if port else find_free_port()
    # host_config_kwargs["port_bindings"] = {8080: ('0.0.0.0', port_to_bind)}
    host_config_kwargs["port_bindings"] = {8000: ('0.0.0.0', port_to_bind)}
    # print(f"DEBUG: cpuset_cpus value before host_config: {args.cpuset_cpus}")
    host_config = client.api.create_host_config(**host_config_kwargs)

    networking_config = None
    if network:
        networking_config = client.api.create_networking_config({
            network: client.api.create_endpoint_config()
        })

    # --- BUILD container_kwargs for dynamic runtime injection ---
    container_kwargs = dict(
        image=image,
        name=name,
        command=cmd_list,
        tty=True,
        stdin_open=True,
        volumes=volumes,
        detach=True,
        host_config=host_config,
        networking_config=networking_config,
        # cpuset=args.cpuset_cpus if args.cpuset_cpus else None
    )
    if runtime:
        container_kwargs['runtime'] = runtime
    # print("DEBUG: container_kwargs =", container_kwargs)
    if "runtime" in container_kwargs:
        del container_kwargs["runtime"]
    if runtime:
        # print(f"Creating container with runtime={runtime} and container_kwargs={container_kwargs}")
        container = client.api.create_container(runtime=runtime, **container_kwargs)
    else:
        container = client.api.create_container(**container_kwargs)
    client.api.start(container=container.get("Id"))
    details = client.containers.get(container.get("Id"))
    port_info = details.attrs['NetworkSettings']['Ports'].get('8080/tcp')
    host_port = port_info[0]['HostPort'] if port_info and isinstance(port_info, list) else "N/A"

    return {
        "id": details.short_id,
        "name": details.name,
        "status": details.status,
        "host_port": host_port,
        "url": f"http://{get_public_ip()}:{host_port}/"
    }
def pull_image(image):
    PRIVATE_REGISTRY = "3.7.194.44:443"
    REGISTRY_USER = "admin"
    REGISTRY_PASS = "S3curePassw0rd"
    if image.startswith(PRIVATE_REGISTRY):
        docker_login(PRIVATE_REGISTRY, REGISTRY_USER, REGISTRY_PASS)
    client = docker.from_env()
    client.images.pull(image)
    return f"Pulled {image}"

def push_image(image, repository):
    client = docker.from_env()
    client.images.push(repository)
    return f"Pushed {image} to {repository}"

def get_container_stats(name):
    client = docker.from_env()
    container = client.containers.get(name)
    stats = container.stats(stream=False)
    memory = stats['memory_stats']['usage']
    memory_limit = stats['memory_stats']['limit']
    cpu_total = stats['cpu_stats']['cpu_usage']['total_usage']
    cpu_total_prev = stats['precpu_stats']['cpu_usage']['total_usage']
    system_cpu = stats['cpu_stats']['system_cpu_usage']
    system_cpu_prev = stats['precpu_stats']['system_cpu_usage']
    cpu_delta = cpu_total - cpu_total_prev
    system_delta = system_cpu - system_cpu_prev
    num_cpus = len(stats['cpu_stats']['cpu_usage'].get('percpu_usage', []))
    cpu_percent = (cpu_delta / system_delta) * num_cpus * 100.0 if system_delta > 0 and cpu_delta > 0 else 0.0
    return {
        "memory_usage": memory,
        "memory_limit": memory_limit,
        "cpu_percent": cpu_percent
    }

def list_containers():
    client = docker.from_env()
    containers = client.containers.list(all=True)
    public_ip = get_public_ip()
    result = []
    for container in containers:
        container.reload()
        ports_info = container.attrs['NetworkSettings'].get('Ports', {})
        mappings = []
        for container_port, binding in ports_info.items():
            if binding:
                for entry in binding:
                    host_ip = entry.get("HostIp", "0.0.0.0")
                    host_port = entry.get("HostPort", "")
                    ip_to_display = public_ip if host_ip in ["0.0.0.0", "127.0.0.1"] else host_ip
                    mappings.append(f"{ip_to_display}:{host_port}")
            else:
                mappings.append("N/A")
        mapped_ports = ", ".join(mappings) if mappings else "None"
        result.append({
            "name": container.name,
            "id": container.short_id,
            "status": container.status,
            "public_ports": mapped_ports
        })
    return result

def remove_container(name):
    client = docker.from_env()
    try:
        container = client.containers.get(name)
        container.remove(force=True)
    except docker.errors.NotFound:
        pass
        # print(f"[WARN] Container '{name}' not found—skipping removal.")

    # Fetch associated vm_id
    conn = sqlite3.connect(DBPath)
    c = conn.cursor()
    c.execute("SELECT id FROM virtualmachine WHERE name=?", (name,))
    row = c.fetchone()
    if row:
        vm_id = row[0]
        # Look up and release all partitions linked to this VM
        c.execute("SELECT volume_id FROM vm_storage WHERE vm_id=?", (vm_id,))
        rows = c.fetchall()
        for row in rows:
            volume_id = row[0]
            c.execute("UPDATE storagepath SET state=1 WHERE id=?", (volume_id,))
            c.execute("DELETE FROM vm_storage WHERE volume_id=? AND vm_id=?", (volume_id, vm_id))
            print(f"🧹 Partition {volume_id} released.")
        # Optional: Delete the VM entry if needed
        c.execute("DELETE FROM virtualmachine WHERE id=?", (vm_id,))
    conn.commit()
    c.close()
    conn.close()
    return f"Removed {name}"

def pause_container(name):
    try:
        client = docker.from_env()
        container = client.containers.get(name)
        if container.status == "running":
            container.pause()
            # Update DB state to paused (e.g., 7 as per your script)
            conn = sqlite3.connect(DBPath)
            c = conn.cursor()
            c.execute("UPDATE virtualmachine SET state=7 WHERE name=?", (name,))
            conn.commit()
            c.close()
            conn.close()
            return f"Paused {name}"
        else:
            return f"Cannot pause {name}: Container is not running (status: {container.status})"
    except NotFound:
        return f"Container {name} not found"
    except APIError as e:
        return f"API Error pausing {name}: {str(e)}"

def unpause_container(name):
    try:
        client = docker.from_env()
        container = client.containers.get(name)
        if container.status == "paused":
            container.unpause()
            # Update DB state to running (e.g., 6)
            conn = sqlite3.connect(DBPath)
            c = conn.cursor()
            c.execute("UPDATE virtualmachine SET state=6 WHERE name=?", (name,))
            conn.commit()
            c.close()
            conn.close()
            return f"Unpaused {name}"
        else:
            return f"Cannot unpause {name}: Container is not paused (status: {container.status})"
    except NotFound:
        return f"Container {name} not found"
    except APIError as e:
        return f"API Error unpausing {name}: {str(e)}"

def get_logs(name):
    client = docker.from_env()
    container = client.containers.get(name)
    output = container.logs().decode("utf-8")
    return output

def start_container(name):
    client = docker.from_env()
    container = client.containers.get(name)
    container.start()
    return f"Started {name}"

def stop_container(name):
    client = docker.from_env()
    container = client.containers.get(name)
    container.stop()
    return f"Stopped {name}"

def create_network(name, driver="bridge", internal=False):
    client = docker.from_env()
    client.networks.create(
        name=name,
        driver=driver,
        internal=internal
    )
    return f"Created network {name} with driver {driver}"

def connect_network(container_name, network_name):
    client = docker.from_env()
    network = client.networks.get(network_name)
    network.connect(container_name)
    return f"Connected {container_name} to {network_name}"

def disconnect_network(container_name, network_name):
    client = docker.from_env()
    network = client.networks.get(network_name)
    network.disconnect(container_name)
    return f"Disconnected {container_name} from {network_name}"

def list_networks():
    client = docker.from_env()
    networks = client.networks.list()
    return [{"name": net.name, "id": net.id[:12]} for net in networks]

def create_vlan_network(name, vlan, subnet, gateway, bridge):
    import docker.types
    client = docker.from_env()
    ipam_pool = docker.types.IPAMPool(
        subnet=subnet,
        gateway=gateway
    )
    ipam_config = docker.types.IPAMConfig(pool_configs=[ipam_pool])
    client.networks.create(
        name=name,
        driver="bridge",
        options={
            "com.docker.network.bridge.name": bridge
        },
        ipam=ipam_config
    )
    return f"Created VLAN network {name} on bridge {bridge} with subnet {subnet}"

def remove_network(name):
    client = docker.from_env()
    client.networks.get(name).remove()
    return f"Removed network {name}"

def update_vm_state(name, new_state):
    conn = sqlite3.connect(DBPath)
    c = conn.cursor()
    c.execute("UPDATE virtualmachine SET state=?, edit_date=CURRENT_TIMESTAMP WHERE name=?", (new_state, name))
    conn.commit()
    c.close()
    conn.close()

def get_image_id_from_name(image_name):
    # Looks up vm_image.id for a given docker image name (e.g., 'ubuntu:latest')
    import sqlite3
    conn = sqlite3.connect(DBPath)
    c = conn.cursor()
    try:
        # Match either full repo/tag or just the tag
        c.execute("SELECT id FROM vm_image WHERE image_name=? OR image_name LIKE ?", (image_name, f"%{image_name}%"))
        row = c.fetchone()
        return row[0] if row else None
    finally:
        c.close()
        conn.close()
def get_image_id(image_name):
    import sqlite3
    DBPath = "/mnt/data/quantumDB.db"
    conn = sqlite3.connect(DBPath)
    c = conn.cursor()
    c.execute("SELECT id FROM vm_image WHERE image_name = ?", (image_name,))
    row = c.fetchone()
    c.close()
    conn.close()
    return row[0] if row else None

def parse_memory(mem_str):
    if not mem_str:
        return 0
    mem_str = str(mem_str).lower().strip()
    if mem_str.endswith("g"):
        return float(mem_str[:-1])
    elif mem_str.endswith("m"):
        return round(float(mem_str[:-1]) / 1024, 3)
    else:
        return float(mem_str)  # Assume already GB

def clean_stale_vm_entries(dry_run=False):
    docker_client = docker.from_env()
    running_containers = [c.name for c in docker_client.containers.list(all=True)]

    conn = sqlite3.connect(DBPath)
    cursor = conn.cursor()
    cursor.execute("SELECT id, name FROM virtualmachine")
    all_vms = cursor.fetchall()

    for vm_id, vm_name in all_vms:
        if vm_name not in running_containers:
            print(f"🗑️ Stale VM: {vm_name} (ID {vm_id})")
            if dry_run:
                print("👉 Dry-run mode: Not deleting.")
            else:
                cursor.execute("DELETE FROM vm_storage WHERE vm_id = ?", (vm_id,))
                cursor.execute("DELETE FROM virtualmachine WHERE id = ?", (vm_id,))

    if not dry_run:
        conn.commit()
    conn.close()

def recreate_container_from_db(vm_name):
    import sqlite3
    import traceback
    from docker_cli_helper import run_container_with_sdk
    from docker_cli_helper import get_public_ip

    try:
        conn = sqlite3.connect("/mnt/data/quantumDB.db")
        c = conn.cursor()

        # Fetch original container config from DB
        c.execute("""
            SELECT v.num_cores, v.memory_GB, v.vm_disk_size, v.port, 
                   v.saved_path, v.vm_image_id, vi.image_name, v.exec_command, 
                   v.runtime, v.network_name
            FROM virtualmachine v
            JOIN vm_image vi ON v.vm_image_id = vi.id
            WHERE v.name = ?
        """, (vm_name,))
        row = c.fetchone()

        if not row:
            return {"status": "error", "message": f"No VM named '{vm_name}' found."}

        (
            num_cores, memory_gb, disk_size, port, saved_path,
            image_id, image_name, exec_command, runtime, network
        ) = row

        # Get the mounted partition path if applicable
        c.execute("""
            SELECT s.location 
            FROM vm_storage vs
            JOIN storagepath s ON vs.volume_id = s.id
            WHERE vs.vm_id = (SELECT id FROM virtualmachine WHERE name = ?)
        """, (vm_name,))
        vol_row = c.fetchone()
        volume_host_path = vol_row[0] if vol_row else None

        # Call SDK-based container launcher
        result = run_container_with_sdk(
            image=image_name,
            name=vm_name,
            exec_cmd=exec_command,
            auto_remove=False,
            cap_add=None,
            volume_host_path=volume_host_path,
            volume_container_path="/mnt/data",
            network=network,
            memory=f"{memory_gb}g",
            cpus=num_cores,
            port=port,
            storage=disk_size,
            runtime=runtime,
            dns=True,  # only if you mounted /etc/resolv.conf originally
            cpuset_cpus=args.cpuset_cpus
        )

        if result.get("status") != "success":
            return {"status": "error", "message": result.get("stderr", "Unknown error")}

        return {
            "status": "success",
            "id": result["id"],
            "name": result["name"],
            "host_port": result["host_port"],
            "url": f"http://{get_public_ip()}:{result['host_port']}/",
        }

    except Exception as e:
        print("[DEBUG] Exception during recreate_container_from_db:\n", traceback.format_exc())
        return {"status": "error", "message": str(e)}

    finally:
        try:
            c.close()
            conn.close()
        except:
            pass


def update_docker_vm_resources(container_name, cpus, memory_gb):
    client = docker.from_env()

    try:
        # If container exists, stop and update
        container = client.containers.get(container_name)
        container.stop()
        memory_bytes = int(float(memory_gb) * 1024 * 1024 * 1024)
        container.update(cpu_period=100000, cpu_quota=int(float(cpus)*100000), mem_limit=memory_bytes)
        return {"status": "success", "message": f"Updated container {container_name}"}

    except docker.errors.NotFound:
        # Container does not exist, recreate it
        try:
            conn = sqlite3.connect(DBPath)
            c = conn.cursor()
            c.execute("""
                SELECT v.name, v.num_cores, v.memory_GB, v.vm_disk_size, v.port,
                       vm.image_name, vg.group_name, sp.location, v.runtime,
                       v.internet_access
                FROM virtualmachine v
                LEFT JOIN vm_image vm ON v.vm_image_id = vm.id
                LEFT JOIN vm_group vg ON vm.vm_group_id = vg.id
                LEFT JOIN vm_storage vs ON vs.vm_id = v.id
                LEFT JOIN storagepath sp ON sp.id = vs.volume_id
                WHERE v.name=?
            """, (container_name,))
            row = c.fetchone()
            if not row:
                return {"status": "fail", "message": f"No VM DB entry for {container_name}"}

            (name, cpu, mem, disk, port, image, group, mount_path,
             runtime, internet) = row

            cmd = [
                "python3", "main.py", "create",
                "--image", image,
                "--name", name,
                "--exec", "gotty --permit-write bash",
                "--memory", f"{int(float(mem)*1024)}m",
                "--cpus", str(cpu),
                "--port", str(port),
                "--network", f"vlan{group}-net"
            ]
            if mount_path:
                cmd += ["--volume-host-path", mount_path, "--volume-container-path", "/data"]
            if runtime:
                cmd += ["--runtime", runtime]
            if internet:
                cmd += ["--allow-internet"]
            cmd += ["--image-id", "84"]  # optional or read from DB

            result = subprocess.run(cmd, capture_output=True, text=True)
            return {
                "status": "recreated",
                "message": f"Container {container_name} recreated after resize",
                "output": result.stdout + result.stderr
            }

        except Exception as e:
            return {"status": "fail", "message": str(e)}
    except Exception as e:
        return {"status": "fail", "message": str(e)}

def parse_memory(memory_str):
    if not memory_str:
        return None
    multiplier = {'g': 1024**3, 'm': 1024**2, 'k': 1024, 'b': 1}
    num = float(memory_str.rstrip('bkmg'))
    unit = memory_str[-1].lower() if memory_str[-1].lower() in 'bkmg' else 'b'
    return int(num * multiplier[unit])

def attach_storage_to_container(container_name, partition_id, container_path="/data_new"):
    import traceback
    logger.debug(f"Attaching partition {partition_id} to {container_name} at {container_path}")

    conn = sqlite3.connect(DBPath)
    c = conn.cursor()
    temp_name = f"{container_name}-temp-{int(time.time())}"  # Unique temp name
    try:
        # Get partition path and validate
        c.execute("SELECT location, state FROM storagepath WHERE id=?", (partition_id,))
        row = c.fetchone()
        if not row:
            c.execute("SELECT id, location FROM storagepath WHERE state=1")
            available = c.fetchall()
            logger.info(f"Available partitions: {[(pid, loc) for pid, loc in available]}")
            return {"status": "error", "message": f"Partition ID {partition_id} does not exist. Available partitions: {[(pid, loc) for pid, loc in available]}"}
        mount_path, state = row
        if state != 1:
            # Find where the partition is mounted
            c.execute("SELECT v.name FROM vm_storage vs JOIN virtualmachine v ON vs.vm_id=v.id WHERE vs.volume_id=?", (partition_id,))
            mounted = c.fetchone()
            mount_info = f" in container {mounted[0]}" if mounted else ""
            c.execute("SELECT id, location FROM storagepath WHERE state=1")
            available = c.fetchall()
            logger.info(f"Available partitions: {[(pid, loc) for pid, loc in available]}")
            return {"status": "error", "message": f"Partition ID {partition_id} ({mount_path}) is already in use (state={state}){mount_info}. Available partitions: {[(pid, loc) for pid, loc in available]}"}

        # Check for duplicate paths in storagepath
        c.execute("SELECT id, location FROM storagepath WHERE location=? AND id!=?", (mount_path, partition_id))
        duplicates = c.fetchall()
        if duplicates:
            logger.warning(f"Duplicate partition paths found for {mount_path}: {duplicates}")
            return {"status": "error", "message": f"Partition path {mount_path} is duplicated in storagepath with IDs {', '.join(str(d[0]) for d in duplicates)}"}

        # Connect Docker and get existing container config
        client = docker.from_env()
        container = client.containers.get(container_name)
        attrs = container.attrs

        # Preserve configuration
        image_name = attrs['Config']['Image']
        exec_cmd = ' '.join(attrs['Config']['Cmd']) if attrs['Config']['Cmd'] else None
        environment = {}
        for env_str in attrs['Config']['Env']:
            if '=' in env_str:
                key, value = env_str.split('=', 1)
                environment[key] = value
        volume_mounts = []
        for m in attrs['Mounts']:
            mode = 'rw' if m['RW'] else 'ro'
            volume_mounts.append(f"{m['Source']}:{m['Destination']}:{mode}")
        new_mount = f"{mount_path}:{container_path}:rw"
        if any(vm == new_mount for vm in volume_mounts):
            return {"status": "error", "message": f"Partition already mounted as {new_mount}."}
        volume_mounts.append(new_mount)
        network_mode = attrs['HostConfig']['NetworkMode']
        port_bindings = attrs['HostConfig']['PortBindings']
        port = None
        if port_bindings:
            first_port = list(port_bindings.keys())[0]  # e.g., '8000/tcp'
            port = int(port_bindings[first_port][0]['HostPort'])
        cpus = attrs['HostConfig']['NanoCpus'] / 1_000_000_000
        memory_bytes = attrs['HostConfig']['Memory']
        memory = f"{memory_bytes // (1024 ** 3)}g" if memory_bytes > 0 else None
        runtime = attrs['HostConfig']['Runtime']
        cpuset_cpus = attrs['HostConfig']['CpusetCpus']
        cap_add = attrs['HostConfig']['CapAdd']
        auto_remove = attrs['HostConfig']['AutoRemove']

        # DNS override
        dns = False
        if 'allow-internet' in environment or network_mode == 'none':
            dns_file = "/opt/dns_override/resolv.conf"
            if os.path.exists(dns_file):
                volume_mounts.append(f"{dns_file}:/etc/resolv.conf:ro")
                dns = True

        logger.debug(f"[DEBUG] Memory limit: {memory}, Binds: {volume_mounts}, Network mode: {network_mode}")
        logger.debug(f"[DEBUG] Memory limit in bytes: {memory_bytes}")

        # Ensure mount_path permissions
        try:
            subprocess.run(["sudo", "mkdir", "-p", mount_path], check=True)
            subprocess.run(["sudo", "chown", f"{os.getuid()}:{os.getgid()}", mount_path], check=True)
            subprocess.run(["sudo", "chmod", "755", mount_path], check=True)
            logger.debug(f"[DEBUG] Set up permissions for {mount_path}")
        except subprocess.CalledProcessError as e:
            return {"status": "error", "message": f"Failed to set up {mount_path}: {e}"}

        # Stop and rename to temp (preserve original)
        was_running = container.status == "running"
        if was_running:
            container.stop()
        container.rename(temp_name)
        logger.debug(f"Renamed original container to {temp_name}")

        # Attempt to recreate with original name
        result = run_container_with_sdk(
            image=image_name,
            name=container_name,
            exec_cmd=exec_cmd,
            auto_remove=auto_remove,
            cap_add=cap_add,
            volume_mounts=volume_mounts,
            network=network_mode,
            memory=memory,
            cpus=cpus,
            port=port,
            storage=None,
            runtime=runtime,
            dns=dns,
            cpuset_cpus=cpuset_cpus,
            environment=environment
        )

        if result.get("status") != "success":
            raise Exception(result.get("message", "Recreation failed"))

        # Mark as in-use and update DB on success
        c.execute("UPDATE storagepath SET state=2, edit_date=CURRENT_TIMESTAMP WHERE id=?", (partition_id,))
        c.execute("SELECT id, COALESCE(saved_path, '') AS saved_path FROM virtualmachine WHERE name=?", (container_name,))
        vm_row = c.fetchone()
        if vm_row:
            vm_id, current_saved_path = vm_row
            # Clean up all stale vm_storage entries
            c.execute("DELETE FROM vm_storage WHERE vm_id=? OR vm_id=0", (vm_id,))
            # Update vm_storage for all mounts
            for mount in volume_mounts:
                source_path = mount.split(':')[0]
                c.execute("SELECT id FROM storagepath WHERE location=?", (source_path,))
                row = c.fetchone()
                if row:
                    volume_id = row[0]
                    c.execute("INSERT INTO vm_storage (volume_id, vm_id, state, cr_date) VALUES (?, ?, 1, CURRENT_TIMESTAMP)", (volume_id, vm_id))
            # Update saved_path
            new_saved_path = current_saved_path
            if mount_path not in new_saved_path.split(","):
                new_saved_path = f"{new_saved_path},{mount_path}" if new_saved_path else mount_path
            c.execute("UPDATE virtualmachine SET saved_path=?, state=6 WHERE id=?", (new_saved_path, vm_id))
        conn.commit()

        # Remove the temp container only on success
        temp_container = client.containers.get(temp_name)
        temp_container.remove(force=True)
        logger.debug(f"Removed temp container {temp_name}")

        return {
            "status": "success",
            "message": f"Attached partition {partition_id} ({mount_path}) to {container_name} at {container_path}",
            "id": result["id"],
            "name": result["name"],
            "host_port": result["host_port"],
            "url": f"http://{get_public_ip()}:{result['host_port']}/",
        }

    except Exception as e:
        logger.error(f"DEBUG: Exception during attach: {traceback.format_exc()}")
        try:
            logger.error(f"Failed config: image={image_name}, mounts={volume_mounts}, network={network_mode}, memory={memory}, cpus={cpus}")
        except UnboundLocalError:
            logger.error("Failed config: variables not defined due to early exception")
        # Rollback: Remove any partial new container, then rename temp back
        try:
            partial_container = client.containers.get(container_name)
            partial_container.remove(force=True)
            logger.debug(f"Removed partial container {container_name}")
        except docker.errors.NotFound:
            pass  # No partial container
        # Rename temp back
        try:
            temp_container = client.containers.get(temp_name)
            temp_container.rename(container_name)
            if was_running:
                temp_container.start()
            logger.debug(f"Restored original container from {temp_name}")
        except Exception as restore_e:
            logger.error(f"Failed to restore container: {restore_e}")
        # DB rollback
        c.execute("UPDATE storagepath SET state=1 WHERE id=?", (partition_id,))
        conn.commit()
        return {"status": "error", "message": str(e)}
    finally:
        c.close()
        conn.close()

def resize_container(name, cpus=None, memory=None, storage=None):
    client = docker.from_env()
    conn = sqlite3.connect(DBPath)
    c = conn.cursor()
    try:
        # Get existing container
        container = client.containers.get(name)
        current_state = container.status

        # Fetch DB config (7 columns, no network_name)
        c.execute("""
            SELECT v.num_cores, v.memory_GB, v.vm_disk_size, v.port, 
                   v.saved_path, v.vm_image_id, vi.image_name
            FROM virtualmachine v
            JOIN vm_image vi ON v.vm_image_id = vi.id
            WHERE v.name = ?
        """, (name,))
        row = c.fetchone()
        if not row:
            return {"status": "error", "message": f"No VM named '{name}' found in DB."}
        (num_cores, memory_gb, disk_size, port, saved_path, image_id, image_name) = row
        exec_command = "gotty --permit-write bash"

        # Update new values or use existing if not provided
        new_cpus = cpus if cpus is not None else num_cores
        new_memory = memory if memory else f"{memory_gb}g"
        new_memory_bytes = parse_memory(new_memory)
        new_memory_gb = new_memory_bytes / (1024 ** 3) if new_memory_bytes else memory_gb

        # Stop and remove the container
        if current_state == "running":
            stop_container(name)
        remove_container(name)

        # Recreate with new settings
        binds = []
        if saved_path:
            binds.append(f"{saved_path}:/data:rw")
        dns = False
        if "allow-internet" in container.attrs.get('Config', {}).get('Env', []):
            dns_file = "/opt/dns_override/resolv.conf"
            if os.path.exists(dns_file):
                binds.append(f"{dns_file}:/etc/resolv.conf:ro")
                dns = True

        result = run_container_with_sdk(
            image=image_name,
            name=name,
            exec_cmd=exec_command,
            auto_remove=False,
            volume_host_path=saved_path,
            volume_container_path="/data",
            network=container.attrs['HostConfig']['NetworkMode'],
            memory=new_memory,
            cpus=new_cpus,
            port=port,
            storage=None,
            runtime="runsc",
            dns=dns,
            binds=binds
        )

        if result.get("status") != "success":
            print(f"DEBUG: Recreation result: {result}")
            return {"status": "error", "message": result.get("message", "Unknown error")}

        # Update DB with new values and log
        with conn:
            c.execute("""
                UPDATE virtualmachine SET num_cores = ?, memory_GB = ?, vm_disk_size = ?
                WHERE name = ?
            """, (new_cpus, new_memory_gb, disk_size, name))
            print(f"[DEBUG] Updated DB: num_cores={new_cpus}, memory_GB={new_memory_gb}, vm_disk_size={disk_size} for {name}")
            # Re-link storage if exists
            if saved_path:
                c.execute("SELECT id FROM storagepath WHERE location = ?", (saved_path,))
                volume_id = c.fetchone()[0]
                c.execute("INSERT INTO vm_storage (volume_id, vm_id, state, cr_date) VALUES (?, ?, 1, CURRENT_TIMESTAMP)",
                          (volume_id, c.lastrowid))

        conn.commit()
        return {"status": "success", "message": f"Resized {name}: CPU={new_cpus}, Memory={new_memory_gb} GB"}

    except NotFound:
        return {"status": "error", "message": f"Container {name} not found."}
    except APIError as e:
        return {"status": "error", "message": f"API Error: {str(e)}"}
    except Exception as e:
        return {"status": "error", "message": str(e)}
    finally:
        c.close()
        conn.close()
