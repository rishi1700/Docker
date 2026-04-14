import docker
import docker
import os
import requests
import subprocess

def get_public_ip():
    try:
        return requests.get("https://api.ipify.org").text
    except Exception:
        return "localhost"

def convert_to_bytes(mem_str):
    units = {"g": 1024 ** 3, "m": 1024 ** 2}
    if isinstance(mem_str, str) and mem_str[-1].lower() in units:
        return int(float(mem_str[:-1]) * units[mem_str[-1].lower()])
    return int(mem_str)

def run_container_with_sdk(
    image, name, memory, exec_cmd=None, auto_remove=True, cap_add=None,
    volume_mounts=None, network=None, cpus=None, port=None, storage=None,
    runtime=None, dns=False, no_internet=False, cpuset_cpus=None, environment=None
):
    try:
        client = docker.from_env()

        if cpuset_cpus is None and cpus is not None:
            cpuset_cpus = f"0-{int(cpus)-1}" if int(cpus) > 1 else "0"
        print(f"[DEBUG] Using cpuset_cpus: {cpuset_cpus}")

        # Convert memory string to bytes
        mem_limit_bytes = convert_to_bytes(memory)

        binds_list = volume_mounts[:] if volume_mounts else []

        if storage and os.path.exists(storage):
            binds_list.append(f"{storage}:/data:rw")

        if dns:
            dns_file = "/opt/dns_override/resolv.conf"
            if os.path.exists(dns_file):
                binds_list.append(f"{dns_file}:/etc/resolv.conf:ro")

        if no_internet and not network:
            network = "none"

        # Dynamically determine container port to bind
        image_info = client.api.inspect_image(image)
        exposed_ports = image_info.get('Config', {}).get('ExposedPorts', {}) or {}
        exposed_port_nums = [p.split('/')[0] for p in exposed_ports.keys()]

        container_port = "80"  # default fallback
        if port and str(port) in exposed_port_nums:
            container_port = str(port)
        elif exposed_port_nums:
            container_port = exposed_port_nums[0]

        print(f"[DEBUG] Detected exposed container ports: {exposed_port_nums}")
        print(f"[DEBUG] Mapping host:{port} -> container:{container_port}")

        port_bindings = {f"{container_port}/tcp": port} if port else {}

        host_config = client.api.create_host_config(
            auto_remove=auto_remove,
            cap_add=cap_add or [],
            binds=binds_list,
            mem_limit=mem_limit_bytes,
            nano_cpus=int(float(cpus) * 1e9) if cpus else None,
            port_bindings=port_bindings,
            dns=None if no_internet else (["8.8.8.8"] if dns else None),
            runtime=runtime if runtime else None,
            network_mode=network,
            cpuset_cpus=cpuset_cpus
        )

        networking_config = None
        if network not in [None, "", "none", "host"]:
            networking_config = client.api.create_networking_config({
                network: client.api.create_endpoint_config()
            })

        print(f"[DEBUG] Final bind mounts: {binds_list}")
        container = client.api.create_container(
            image=image,
            name=name,
            command=exec_cmd,
            host_config=host_config,
            ports=[f"{container_port}/tcp"],
            detach=True,
            networking_config=networking_config,
            environment=environment or {}
        )

        client.api.start(container=container.get("Id"))

        container_obj = client.containers.get(container.get("Id"))
        port_info = container_obj.attrs['NetworkSettings']['Ports'].get(f"{container_port}/tcp")
        host_port = port_info[0]['HostPort'] if port_info else "N/A"
   
        return {
            "status": "success",
            "id": container_obj.short_id,
            "name": container_obj.name,
            "container_status": container_obj.status,
            "host_port": host_port,
            "url": f"http://{get_public_ip()}:{host_port}/",
        }

    except Exception as e:
        return {
            "status": "error",
            "message": str(e)
        }
