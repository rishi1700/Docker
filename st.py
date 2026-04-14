import sys
import socket
import os
import signal
import time
from array import *
import re
import ast
import json
import datetime
import sqlite3
import pexpect
import ast
import ipaddress
import traceback
from rq import Queue, Connection,  Worker
from redis import Redis
import psutil
from ipmi_thread import pbtAck  #,wd
import builtins

#from ris_Docker import *
from Docker import (
    DockerCreate, DockerStart, DockerStop, DockerDelete,
    DockerResize, DockerPause, DockerUnPause, DockerList, DockerAttachStorage, DockerNetworkCreate,
    DockerSnapshotCreate, DockerSnapshotList, DockerSnapshotDelete, DockerBackupStart, DockerBackupStatus,
    DockerBackupLocal, DockerBackupFull, DockerBackupCustom, DockerBackupDelete, DockerAttachVolume,
    DockerDetachVolume, _db_delete_backups_for_vm, _db_delete_snapshots_for_vm, _db_clear_vm_storage_for_vm,
    has_retained_backups_or_snapshots, _pick_gateway_for_cidr, EnsureDockerNetworkFromDB
)
from ccm_mod import *
from schedule_thread import init_job_queue, get_jobList, dwnld_myApp, set_gRun_ftp, run_ftp
from tot_resources import *
from globalSettings import *
from dbQueries import *
from logRoutine import loggerArgs, init_logger, init_CONlogger
from multiprocessing import Process
import unpackage
import license_unpack
from job import CheckBackUpOnInsert
import base64
import binascii
import threading
from ZFSpoolSM import get_zpool_status,get_drive_by_id_dict
#sudo apt-get install zfsutils-linux
#https://www.digitalocean.com/community/tutorials/how-to-set-filesystem-quotas-on-ubuntu-18-04
#bus 81:00.0:  physical PCIe slot 1 --> canister 3 --> storcli /c0 bus 
#c1:00.0:  physical PCIe slot 3 --> canister 2 --> storcli /c1 bus 
#c2:00.0:  physical PCIe slot 5 --> canister 1 --> storcli /c2
#https://forum.proxmox.com/threads/restore-overflown-lvm-just-one-small-step-im-sure.99405/ LVM/VG repair
#sudo /opt/MegaRAID/storcli/storcli64 /c0/e252/sall show all J > disk.txt
#sudo /opt/MegaRAID/storcli/storcli64 /c1 set jbod=off
#sudo /opt/MegaRAID/storcli/storcli64 /c0/vall show
#https://medium.com/@kcoupal/unlocking-high-throughput-the-power-of-combining-openstack-and-nvme-of-f36ef3b19eae -- primer of NVME0F technology
#https://spdk.io/doc/intro.html for NVMEoF
#https://www.mankier.com/8/nvmetcli like targetcli for NVMEoF
#https://www.starwindsoftware.com/blog/hyper-v/nvme-part-1-linux-nvme-initiator-linux-spdk-nvmf-target/
#sudo mount -t cifs -o username=sanuyi //192.168.30.16/cifs1 /mnt/cifs1/
#sudo mount -t nfs 192.168.30.16:/mnt/vmware1 /mnt/test
#sudo iscsiadm -m discovery -t st -p 192.168.32.15 
#sudo iscsiadm -m node --targetname iqn.2018-04.com.quantum:vdisk1lv0 -p 192.168.32.15 -l
#
#import sys
#sudo /opt/MegaRAID/storcli/storcli64 /c0/v239 del force J
#sudo /opt/MegaRAID/storcli/storcli64 /c0/vall show J
#sys.path.append('/var/www/sanuyi/cgi') #to allow global include path
#https://www.ixsystems.com/documentation/freenas/9.10/storage.html
#https://news.ycombinator.com/item?id=11768886 (managing consistent snapshots)
#sudo zfs send  p3/disk_test@disk_test-ss1  | sudo ssh will@192.168.30.13  sudo zfs recv p2/v9
#https://www.polyomica.com/improving-transfer-speeds-for-zfs-sendreceive-in-a-local-network/
# replicating a snapshot.
#https://www.thegeekdiary.com/solaris-zfs-command-line-reference-cheat-sheet/
#https://github.com/presslabs/z3
#https://serverfault.com/questions/241588/how-to-automate-ssh-login-with-password
# zfs send -Rvn -i pool@migration_base pool@migration_base_20160706 what will be sent!
#https://www.socallinuxexpo.org/sites/default/files/presentations/zfs-send-and-receive.pdf (restart ZFS after network failure)
#https://blog.yucas.mx/2017/01/04/fast-zfs-send-with-netcat/
#https://www.tutorialspoint.com/How-to-perform-different-commands-over-ssh-with-Python
#https://forums.freebsd.org/threads/how-to-zfs-send-and-receive-between-two-servers-on-the-same-lan-without-ssh.67418/
#https://serverfault.com/questions/241588/how-to-automate-ssh-login-with-password
#https://www.freebsd.org/cgi/man.cgi?query=zfs&sektion=8 Good for options used in ZFS commands
#sudo -i to get to root
#sudo  echo 1 > /sys/block/sde/device/delete
#http://fibrevillage.com/storage/279-hot-add-remove-rescan-of-scsi-devices-on-linux   
#https://www.hiroom2.com/2018/05/05/ubuntu-1804-tgt-en/ #tgt usage
#https://virtualizationreview.com/articles/2019/08/08/how-to-use-linux-for-an-esxi-iscsi-server.aspx
#https://www.server-world.info/en/note?os=Ubuntu_18.04&p=iscsi&f=1
#https://community.mellanox.com/s/article/howto-setup-rdma-connection-using-inbox-driver--rhel--ubuntu-x
#https://advantech-ncg.zendesk.com/hc/en-us/articles/360028285872-How-to-use-ipmitool-command-to-set-BMC-watchdog-timer
#https://openzfs.github.io/openzfs-docs/Basic%20Concepts/dRAID%20Howto.html
#journalctl -p 2
#############Added by Rishi#####
# -----------------------------
# Helpers & logging
# -----------------------------
# --- TEMP DEBUG ---
def _dbg_dump_tokens(prefix, msg_list):
    try:
        from pprint import pformat
    except Exception:
        pformat = lambda x: str(x)
    try:
        sprint(f"{prefix} RAW message_list:", 0)
        sprint(pformat(msg_list), 0)
    except Exception:
        print(prefix, "RAW message_list:", msg_list)

def _dbg_log_token(name, value):
    try:
        sprint(f"[TOK] {name} = {repr(value)}", 0)
    except Exception:
        print(f"[TOK] {name} = {repr(value)}")
# --- END TEMP DEBUG ---

def _system_caps_db():
    """
    Read totals/used from `system` and return free capacities.
    Returns: {"free_vcpu": float, "free_mem": float, "free_store": float}
    """
    try:
        import sqlite3
        from globalSettings import DBPath
        conn = sqlite3.connect(DBPath); cur = conn.cursor()
        row = cur.execute("""
            SELECT
                COALESCE(total_vcpu,0),
                COALESCE(total_memoryGB,0.0),
                COALESCE(total_storageGB,0.0),
                COALESCE(used_vcpu,0),
                COALESCE(used_memoryGB,0.0),
                COALESCE(used_storageGB,0.0)
            FROM system LIMIT 1
        """).fetchone() or (0, 0.0, 0.0, 0, 0.0, 0.0)
        cur.close(); conn.close()
        tv, tm, ts, uv, um, us = row
        return {
            "free_vcpu":  max(0.0, float(tv) - float(uv)),
            "free_mem":   max(0.0, float(tm) - float(um)),
            "free_store": max(0.0, float(ts) - float(us)),
        }
    except Exception:
        return {"free_vcpu": 0.0, "free_mem": 0.0, "free_store": 0.0}

def _current_vm_limits_db(name: str):
    """
    Current per-VM targets from DB (state doesn't matter here).
    Returns tuple: (cur_cpu: float, cur_mem: float, cur_disk: float)
    """
    try:
        import sqlite3
        from globalSettings import DBPath
        conn = sqlite3.connect(DBPath); cur = conn.cursor()
        row = cur.execute("""
            SELECT
                COALESCE(num_cores,0.0),
                COALESCE(memory_GB,0.0),
                COALESCE(vm_disk_size,0.0)
            FROM virtualmachine
            WHERE TRIM(name)=?
        """, (str(name).strip(),)).fetchone() or (0.0, 0.0, 0.0)
        cur.close(); conn.close()
        return float(row[0]), float(row[1]), float(row[2])
    except Exception:
        return 0.0, 0.0, 0.0

def _replace_vm_network_links(vm_name: str, network_names) -> bool:
    """
    Replace the VM's network links with exactly 'network_names' (ordered, deduped).
    Removes prior vm_network links and their veth_port rows for this VM,
    then recreates links for the requested networks that exist in 'network' table.
    """
    try:
        conn = sqlite3.connect(DBPath); c = conn.cursor()  # NOTE: DBPath from st.py

        # vm id
        row = c.execute("SELECT id FROM virtualmachine WHERE TRIM(name)=?",
                        (vm_name.strip(),)).fetchone()
        if not row:
            print(f"[DB] WARN: VM '{vm_name}' not found")
            c.close(); conn.close(); return False
        vm_id = row[0]

        # wipe old links for this VM
        c.execute("DELETE FROM vm_network WHERE vm_id=?", (vm_id,))
        # remove prior veth_port rows we created (pattern vm-ethN)
        c.execute("DELETE FROM veth_port WHERE name LIKE ?", (f"{vm_name}-eth%",))

        # normalize: strip + dedupe while preserving order
        seen = builtins.set()
        nets = []
        for n in (network_names or []):
            nn = str(n).strip()
            if nn and nn not in seen:
                seen.add(nn)
                nets.append(nn)

        # map names -> ids actually present in network table
        name_to_id = {}
        if nets:
            placeholders = ",".join("?" for _ in nets)
            rows = c.execute(f"SELECT id,name FROM network WHERE name IN ({placeholders})",
                             tuple(nets)).fetchall()
            name_to_id = {name: nid for (nid, name) in rows}

        # create new veth + vm_network rows in requested order
        for idx, n in enumerate(nets):
            net_id = name_to_id.get(n)
            if not net_id:
                print(f"[DB] WARN: network '{n}' not present; skip link")
                continue

            veth_name = f"{vm_name}-eth{idx}"
            c.execute("""
                INSERT INTO veth_port(name,state,cr_date,edit_date,ip,netmask,network_id)
                VALUES(?, 1, datetime('now'), datetime('now'), NULL, NULL, ?)
            """, (veth_name, net_id))
            veth_id = c.lastrowid
            c.execute("INSERT INTO vm_network(vm_id, veth_id) VALUES(?,?)", (vm_id, veth_id))

        conn.commit()
        c.close(); conn.close()
        return True

    except Exception as e:
        print(f"[DB] _replace_vm_network_links error: {e}")
        try:
            c.close(); conn.close()
        except Exception:
            pass
        return False

def _normalize_network_names(val):
    """
    Accepts: list/tuple, "netA", "['netA','netB']"
    Returns: de-duplicated list of clean names in order.
    """
    raw = []
    if isinstance(val, builtins.list) or isinstance(val, tuple):
        raw = [n for n in val if n]
    elif isinstance(val, str) and val.strip():
        s = val.strip()
        if s.startswith("[") and s.endswith("]"):
            try:
                parsed = json.loads(s.replace("'", '"'))
                raw = parsed if isinstance(parsed, builtins.list) else [s]
            except Exception:
                raw = [s]
        else:
            # allow single name or comma-separated "netA,netB"
            raw = [p.strip() for p in s.split(",") if p.strip()]
    else:
        raw = []

    seen = builtins.set()
    nets = []
    for n in raw:
        nn = str(n).strip()
        if nn and nn not in seen:
            seen.add(nn)
            nets.append(nn)
    return nets

def _parse_network_arg(val):
    """Normalize network arg into a list of plain strings"""
    if not val:
        return []
    # Already a list of strings?
    if isinstance(val, list):
        if len(val) == 1 and isinstance(val[0], str) and val[0].startswith("["):
            try:
                parsed = ast.literal_eval(val[0])
                if isinstance(parsed, list):
                    return [str(x).strip() for x in parsed if x]
            except Exception:
                return [val[0].strip()]
        return [str(x).strip() for x in val if str(x).strip()]
    # Single string
    if isinstance(val, str):
        try:
            parsed = ast.literal_eval(val)
            if isinstance(parsed, list):
                return [str(x).strip() for x in parsed if x]
        except Exception:
            pass
        return [val.strip()]
    return []

def _fix_gateway_for_cidr(cidr_str: str, gw_str: str) -> str:
    """
    If gw_str is empty/invalid or not inside cidr_str, return the first usable IP in cidr.
    Otherwise return gw_str as-is (normalized).
    """
    try:
        net = ipaddress.ip_network(str(cidr_str).strip(), strict=False)
    except Exception:
        return gw_str  # CIDR itself is bad; let DockerNetworkCreate validate

    try:
        gw_ip = ipaddress.ip_address((gw_str or "").strip())
    except Exception:
        gw_ip = None

    if (
        gw_ip is None
        or gw_ip not in net
        or gw_ip == net.network_address
        or gw_ip == net.broadcast_address
    ):
        # pick first usable host: network+1
        return str(ipaddress.ip_address(int(net.network_address) + 1))
    return str(gw_ip)

def _dbg_var(label, val):
    try:
        s = repr(val)
    except Exception:
        s = f"<unreprable:{type(val).__name__}>"
    try:
        ln = len(str(val)) if val is not None else "NA"
    except Exception:
        ln = "NA"
    sprint(f"[DBG] {label}={s} (type={type(val).__name__}, len={ln})", 0)

from typing import Optional
def _docker_container_state(name: str) -> Optional[str]:
    """Return 'running', 'exited', 'created', etc., or None if not found."""
    if not name:
        return None
    try:
        # prints the container status (e.g., "running", "exited") for the exact name
        cmd = ["bash", "-lc", f"docker ps -a --filter name=^/{name}$ --format '{{{{.Status}}}}' | awk '{{print tolower($1)}}'"]
        p = subprocess.run(cmd, capture_output=True, text=True, check=False)
        status = (p.stdout or "").strip()
        return status if status else None
    except Exception as e:
        sprint(f"[WARN] _docker_container_state({name!r}) errored: {repr(e)}", 0)
        return None

def _docker_container_exists(name: str) -> bool:
    """True if a container with this exact name exists locally."""
    try:
        cmd = ["bash", "-lc", f"docker ps -a --filter name=^/{name}$ --format '{{{{.ID}}}}'"]
        p = subprocess.run(cmd, capture_output=True, text=True, check=False)
        return bool((p.stdout or "").strip())
    except Exception:
        return False
def _docker_image_exists_locally(ref: str) -> bool:
    """Check if a Docker image exists locally (safe wrapper)."""
    if not ref:
        return False
    try:
        out = subprocess.run(
            ["docker", "image", "inspect", ref],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False
        )
        return out.returncode == 0
    except Exception as e:
        sprint(f"[WARN] _docker_image_exists_locally({ref!r}) errored: {repr(e)}", 0)
        return False
def _normalize_image(ref):
    if ref is None:
        return ref
    r = str(ref).strip().strip('"').strip("'")
    if ' ' in r:
        sprint("[WARN] Image ref contains spaces (invalid for Docker): " + repr(r), 0)
    return r

def _parse_network_arg(val):
    if val is None:
        return []
    if isinstance(val, list):
        return val
    s = str(val).strip()
    if s.startswith('[') and s.endswith(']'):
        try:
            parsed = ast.literal_eval(s)
            if isinstance(parsed, list):
                return [str(x) for x in parsed]
        except Exception:
            pass
    parts = [p.strip() for p in s.split(',') if p.strip()]
    return parts

def _to_int_or_none(v):
    try:
        if v is None or str(v).strip() == "":
            return None
        return int(float(str(v).strip()))
    except Exception:
        return None

def _to_str_or_none(v):
    if v is None:
        return None
    s = str(v).strip()
    return s if s != "" else None

def _cidr_overlaps_host(cidr_str: str) -> bool:
    """Return True if cidr overlaps any host IPv4 interface."""
    try:
        import ipaddress, subprocess, json as _json
        net = ipaddress.ip_network(str(cidr_str).strip(), strict=False)
        r = subprocess.run(["ip", "-j", "-4", "addr"], capture_output=True, text=True, check=True)
        data = _json.loads(r.stdout)
        for link in data:
            for ai in link.get("addr_info", []):
                if ai.get("family") == "inet":
                    hostnet = ipaddress.ip_network(f"{ai['local']}/{ai['prefixlen']}", strict=False)
                    if net.overlaps(hostnet):
                        return True
    except Exception:
        pass
    return False

def _fetch_network_rows_from_db():
    """Returns list of (name, cidr, gateway) from the `network` table."""
    rows = []
    try:
        conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
        cur.execute("""
            SELECT name, cidr, gateway
            FROM network
            WHERE TRIM(name) <> ''
              AND cidr IS NOT NULL  AND TRIM(cidr) <> ''
              AND gateway IS NOT NULL AND TRIM(gateway) <> ''
        """)
        rows = cur.fetchall() or []
        cur.close(); conn.close()
    except Exception as e:
        sprint(f"[WARN] startup network fetch failed: {e}", 0)
    return rows

def _reconcile_docker_networks_on_startup():
    """Ensure all DB-defined networks exist in Docker as bridge networks."""
    try:
        from Docker import DockerNetworkCreate   # reuse your existing function
    except Exception as e:
        sprint(f"[ERR] cannot import DockerNetworkCreate: {e}", 0)
        return

    nets = _fetch_network_rows_from_db()
    if not nets:
        sprint("[INFO] No DB networks to reconcile on startup", 0)
        return

    sprint(f"[INFO] Reconciling {len(nets)} network(s) from DB into Docker...", 0)
    for (n_name, n_cidr, n_gw) in nets:
        name = (n_name or "").strip()
        cidr = (n_cidr or "").strip()
        gw   = (n_gw or "").strip()
        if not name or not cidr or not gw:
            continue

        if _cidr_overlaps_host(cidr):
            sprint(f"[WARN] Skip ensuring Docker network '{name}': subnet {cidr} overlaps host interfaces", 0)
            continue

        rc = DockerNetworkCreate(cidr, gw, name, cmd_id="BOOT")
        if rc == 0:
            sprint(f"[INFO] Ensured Docker network '{name}' ({cidr} gw {gw})", 0)
        elif rc in (-14, -15):
            sprint(f"[ERR] Invalid DB network '{name}': cidr={cidr} gw={gw} (rc={rc})", 0)
        else:
            sprint(f"[ERR] Failed to ensure Docker network '{name}': rc={rc}", 0)


def _bootstrap_docker_networks_from_db():
    """
    On st.py restart, reconcile network rows from DB into Docker.
    Idempotent: if a network with the same name exists in Docker, DockerNetworkCreate returns 0.
    """
    import sqlite3
    from Docker import DockerNetworkCreate
    try:
        conn = sqlite3.connect(DB_PATH)
        cur  = conn.cursor()
        # adjust columns/names to your schema if different
        cur.execute("""
            SELECT name, cidr, gateway
            FROM network
            WHERE TRIM(COALESCE(name,'')) <> ''
              AND TRIM(COALESCE(cidr,'')) <> ''
              AND TRIM(COALESCE(gateway,'')) <> ''
        """)
        rows = cur.fetchall() or []
        sprint(f"[BOOT] Found {len(rows)} network rows in DB", 0)
        for (n_name, n_cidr, n_gw) in rows:
            sprint(f"[BOOT] Ensuring Docker network: name={n_name} cidr={n_cidr} gw={n_gw}", 0)
            rc = DockerNetworkCreate(n_cidr, n_gw, n_name, cmd_id="BOOT")
            if rc == 0:
                sprint(f"[BOOT] OK (created or exists) → {n_name} {n_cidr} gw={n_gw}", 0)
            elif rc == -14:
                sprint(f"[BOOT][WARN] Invalid CIDR in DB row → {n_name} {n_cidr} gw={n_gw}", 0)
            elif rc == -15:
                sprint(f"[BOOT][WARN] Invalid gateway in DB row → {n_name} {n_cidr} gw={n_gw}", 0)
            else:
                sprint(f"[BOOT][ERR] Failed to ensure network → {n_name} {n_cidr} gw={n_gw} rc={rc}", 0)
        cur.close(); conn.close()
    except Exception as e:
        import traceback
        sprint(f"[BOOT][EXC] network bootstrap failed: {e}", 0)
        sprint(traceback.format_exc(), 0)

def _first_host_gateway(cidr: str) -> str:
    """
    Return first usable host (x.x.x.1) for a given CIDR string.
    Accepts either network CIDR (192.168.40.0/24) or host-style (192.168.40.20/24).
    """
    net = ipaddress.ip_interface(cidr.strip()).network  # strict=False behavior via ip_interface
    gw = net.network_address + 1
    return str(gw)


# -----------------------------
# DB connectivity (existing)
# -----------------------------
def db_connect():
    CheckFile=DBPath
    try:
        if os.path.isfile(CheckFile):
            conn=sqlite3.connect(DBPath,check_same_thread=False)
            return conn
    except Exception as err:
        return(-1)

def _safe_conn():
    conn = db_connect()
    return None if conn == -1 else conn

def _vm_exists(name):
    conn = _safe_conn()
    if not conn: return False
    try:
        c = conn.cursor()
        c.execute("SELECT 1 FROM virtualmachine WHERE name=?", (name,))
        row = c.fetchone()
        c.close(); conn.close()
        return bool(row)
    except Exception:
        try: c.close(); conn.close()
        except Exception: pass
        return False

def _parse_mem_gb(mem_str):
    if mem_str is None: return None
    s = str(mem_str).strip().lower()
    try:
        if s.endswith('g'):  return float(s[:-1])
        if s.endswith('m'):  return float(s[:-1]) / 1024.0
        if s.endswith('k'):  return float(s[:-1]) / (1024.0*1024.0)
        if s == '':          return None
        return float(s)      # treat bare number as GB
    except Exception:
        return None

def _lookup_vm_image_id_and_type(image_name):
    """Resolve vm_image.id and vm_type from image_name. Defaults to docker if unknown."""
    if not image_name:
        return (None, 'docker')
    conn = _safe_conn()
    if not conn: return (None, 'docker')
    try:
        c = conn.cursor()
        c.execute("SELECT id, image_type FROM vm_image WHERE lower(image_name) = lower(?) LIMIT 1", (image_name,))
        row = c.fetchone()
        c.close(); conn.close()
        if not row:
            return (None, 'docker')
        vm_image_id, image_type = row
        vm_type = 'docker' if str(image_type).lower() in ('docker','zip','tar.gz','tgz') else 'native'
        return (vm_image_id, vm_type)
    except Exception:
        try: c.close(); conn.close()
        except Exception: pass
        return (None, 'docker')

def _file_name_for_image(image_name):
    """Return vm_image.file_name for a given image_name (case-insensitive), or None."""
    conn = _safe_conn()
    if not conn: return None
    try:
        c = conn.cursor()
        c.execute("SELECT file_name FROM vm_image WHERE lower(image_name) = lower(?) LIMIT 1", (image_name,))
        row = c.fetchone()
        c.close(); conn.close()
        return row[0] if row else None
    except Exception:
        try: c.close(); conn.close()
        except Exception: pass
        return None

# --- Resolve the host saved_path for a VM's primary storage (loopback mount) ---
def _resolve_primary_saved_path(vm_name: str) -> str:
    import os
    base = None
    try:
        # Prefer the live/mounted base used by Docker.py
        from Docker import _active_storage_base
        try:
            base = _active_storage_base()
        except Exception:
            base = None
    except Exception:
        base = None

    if not base:
        try:
            # Fallback: base chosen via DB volume selection logic
            from Docker import _db_get_docker_storage_base_from_volume
            try:
                base = _db_get_docker_storage_base_from_volume()
            except Exception:
                base = None
        except Exception:
            base = None

    # Final fallback (keeps legacy behavior working if nothing is mounted/resolved)
    if not base or not os.path.isdir(base):
        base = "/mnt/dockervol1"

    return f"{base.rstrip('/')}/{vm_name}/mnt"

def _insert_vm_row(name, vcpu, memory_str, disk, image_name, port, ssh_port=None):
    conn = _safe_conn()
    if not conn: return -1
    try:
        if _vm_exists(name):
            conn.close()
            return 1

        vm_image_id, vm_type = _lookup_vm_image_id_and_type(image_name)
        mem_gb = _parse_mem_gb(memory_str)
        if mem_gb is None: mem_gb = 0.5
        vcpu_int = int(float(vcpu)) if vcpu not in (None, "") else 1
        disk_int = int(float(disk)) if disk not in (None, "") else 10
        port_int = int(str(port)) if port not in (None, "") else None
        ssh_port_int = int(str(ssh_port)) if ssh_port not in (None, "") else None
        now = datetime.date.today().strftime("%Y-%m-%d")

        # DYNAMIC: path reflects the actual host mount used by Docker.py allocator
        saved_path = _resolve_primary_saved_path(name)

        c = conn.cursor()
        c.execute(
            "INSERT INTO virtualmachine "
            "(name,num_cores,memory_GB,vm_disk_size,vm_image_id,cr_date,edit_date,saved_path,state,type,port,ssh_port) "
            "VALUES(?,?,?,?,?,?,?,?,4,?,?,?)",
            [name, vcpu_int, mem_gb, disk_int, vm_image_id, now, now, saved_path, vm_type, port_int, ssh_port_int]
        )
        conn.commit()
        c.close(); conn.close()
        return 0
    except Exception:
        try: c.close(); conn.close()
        except Exception: pass
        return -1

def _update_vm_state(name, new_state, set_started_date=False):
    conn = _safe_conn()
    if not conn: return -1
    try:
        c = conn.cursor()
        if set_started_date and new_state == 6:
            c.execute("UPDATE virtualmachine SET state=?, started_date=date('now') WHERE name=?", (new_state, name))
        else:
            c.execute("UPDATE virtualmachine SET state=? WHERE name=?", (new_state, name))
        conn.commit()
        c.close(); conn.close()
        return 0
    except Exception:
        try: c.close(); conn.close()
        except Exception: pass
        return -1

def _delete_vm_row(name):
    conn = _safe_conn()
    if not conn: return -1
    try:
        c = conn.cursor()
        c.execute("DELETE FROM virtualmachine WHERE name=?", (name,))
        conn.commit()
        c.close(); conn.close()
        return 0
    except Exception:
        try: c.close(); conn.close()
        except Exception: pass
        return -1

# -----------------------------
# Image name → Docker ref resolver
# -----------------------------
def _heuristic_ref_from_friendly(img: str) -> str:
    """
    Convert friendly UI names to a plausible Docker ref.
    Examples:
      'archiware 1.0.3'      -> 'archiware:1.0.3'
      'mysql 8.0'            -> 'mysql:8.0'
      'nginx stable'         -> 'nginx:stable'
      'sanuyi ubuntu-ssh 1.1'-> 'sanuyi-ubuntu-ssh:1.1'
    """
    s = (img or "").strip()
    if not s:
        return s
    parts = s.split()
    if len(parts) >= 2:
        tag = parts[-1]
        repo = "-".join(parts[:-1])
        return f"{repo}:{tag}"
    # single token: leave as-is
    return s

def _ref_from_file_name(file_name: str) -> str:
    """
    Build a docker-ish ref from vm_image.file_name (stored WITHOUT suffix).
    e.g., 'sanuyi_archiver_1.0.3' -> 'sanuyi-archiver:1.0.3'
    """
    if not file_name:
        return None
    stem = file_name.strip()
    # split by underscores; last token as tag if looks like version
    toks = stem.split("_")
    if len(toks) >= 2:
        tag = toks[-1]
        repo = "-".join(toks[:-1])
        return f"{repo}:{tag}"
    return stem

def _resolve_docker_ref(image_name: str) -> str:
    """
    Try DB-assisted mapping first; fall back to heuristic.
    """
    friendly = _to_str_or_none(image_name)
    if not friendly:
        return friendly

    # 1) If already valid-ish (contains ':' and no spaces), accept as-is
    if " " not in friendly and ":" in friendly and not friendly.endswith(":"):
        return friendly

    # 2) DB lookup by image_name -> file_name, derive ref from file_name
    fname = _file_name_for_image(friendly)
    if fname:
        ref = _ref_from_file_name(fname)
        if ref and " " not in ref:
            sprint(f"[DBG] Resolved via DB file_name: image_name={friendly!r} -> ref={ref!r}", 0)
            return ref

    # 3) Heuristic split of friendly name
    ref = _heuristic_ref_from_friendly(friendly)
    sprint(f"[DBG] Resolved via heuristic: image_name={friendly!r} -> ref={ref!r}", 0)
    return ref

 

def sprint (a,b):
    x=True
    if x==True:
        if b!=0:
            print(a,b)
            loggerName="STCON_logger"
            logger=STCON_logger
            logger[0].info(loggerName+":"+str(a)+","+str(b))
        else:
            print(a)
            loggerName="STCON_logger"
            logger=STCON_logger
            logger[0].info(loggerName+":"+str(a))
            
def getNetworkCIDR(name):
    cidr='0.0.0.0/24'
    DBopen=False    
    try:
        conn=sqlite3.connect(DBPath)
        conn.text_factory=str
        c=conn.cursor()
        DBopen=True
        query = c.execute("select  cidr from network where name=?",[name])
        resp=c.fetchone()
        if resp!=None:
            cidr=resp[0] 
        sprint ("network cidr",cidr)

    except Exception as err:
        sprint("getNetwork except",err)
    if DBopen==True:
        c.close()
        conn.close()
    return cidr

def wd(action,time,WDen):
# init, reset, stop, get

    #ipmitool raw 0x06 0x24 0xWW 0xXX 0x00 0x00 0xYY 0xZZ
    #sudo ipmitool raw 0x06 0x24 0x04 0x01 0x00 0x00 0x00 0x02 this is 50 secs
    #ipmitool mc watchdog get (get status)
    #ipmitool mc watchdog reset (start the WD timer)
    #ipmitool mc watchdog off (stop the wd timer)
    #0xXX = 0x01 (Hard Reset)
    #0xWW = 0x03
    #0xYY = 
    #0xZZ = 
    #WDen=True
    try:
        
        WDen=False
        print(("Watchdog",action))
        if WDen==False:
            return
            
        if action == "init":
            #ipmitool raw 0x06 0x24 0x04 0x01 0x00 0x00 0x00 0x02
            arg1='0x06'
            arg2='0x24'
            arg3='0x04'
            arg4='0x01' 
            arg5='0x00' 
            arg6='0x00'
            arg7='0x00'
            arg8='0x04'
            process1= subprocess.check_output(['ipmitool','raw',arg1,arg2,arg3,arg4,arg5,arg6,arg7,arg8])   
            print(process1)
            
        if action == "reset":
            #ipmitool mc watchdog reset 
            arg1="mc"
            arg2="watchdog"
            arg3="reset"
            process1= subprocess.check_output(['ipmitool',arg1,arg2,arg3])
            print(process1)
            
        if action == "stop":
            #sudo ipmitool mc watchdog off 
            arg1="mc"
            arg2="watchdog"
            arg3="off"
            process1= subprocess.check_output(['ipmitool',arg1,arg2,arg3]) 
            print(process1)
            
        if action == "get":
            #sudo ipmitool mc watchdog get 
            arg1="mc"
            arg2="watchdog"
            arg3="get"
            process1= subprocess.check_output(['ipmitool',arg1,arg2,arg3]) 
            print(process1)
    except Exception as e:
        sprint ("wd except ",e)
        
def InitSTlogger():
    global ST_logger
    global STCON_logger
    ST_logger=init_logger("ST")
    STCON_logger=init_CONlogger("STCON")
    
def rm_logs():
    return 0
    #choice=raw_input("<c> to continue init_logger <x> exit")
    try:
        f="/mnt/xdata/ccmloggerFile.log"
        process1= subprocess.check_output(['chmod','666',f])
        sprint (process1,0)
        f="/mnt/xdata/alerts.log"
        process1= subprocess.check_output(['chmod','666',f])
        sprint (process1,0)
    except Exception as e:
        sprint ("chmod except ccmloggerfiles",e)

#choice=raw_input("<c> to continue chmod <x> exit")

def ccmLogger(level_num,data,arguments):
    my_logger=ST_logger
    ccmLogger1(my_logger,level_num,data,arguments)

def ccmLogger1(logger,level_num,data,arguments):
    gll = 90
    # print "in ccmLogger1", "handlers : ", logger[0].handlers[0].baseFilename, " , ", logger[1].handlers[0].baseFilename
    if int(arguments['LogLevel']) <= gll:
        if level_num ==ccmINFO:
            logger[0].info(data,extra=arguments)
        elif level_num == ccmWARNING:
            logger[0].warning(data,extra=arguments)
        elif level_num == ccmERROR:
            logger[0].error(data,extra=arguments)
            logger[1].error(data, extra=arguments)
        elif level_num == ccmCRITICAL:
            logger[0].critical(data,extra=arguments)
            logger[1].critical(data, extra=arguments)
        elif level_num == ccmDEBUG:
            logger[0].debug(data,extra=arguments)
        #else:
        #   logger.notset(data,extra=arguments)
    else:
        pass
        
def updateLinuxPwd(username,newPwd):
    try:
        process1= subprocess.check_output(['sudo','./chpw.sh',username,newPwd])
        return 0
    except subprocess.CalledProcessError as e:
        print(("update password except ",str(e)))
        return -1

def getCIFS_UserPassword(share):
    user="null"
    pw="null"
    try:
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        query=c.execute("select user_name,pw from host where name ='"+str(share)+"'")
        for val in c:
            user = val[0]
            pw = val[1]
        c.close()
        conn.close()
        return 0,user,pw
    except Exception as err:
        sprint("getCIFS_UserPassword except ",err)
        return -1,"NA","NA"

def updateCBA_SSH(enCBA, enSSH,cbaUpload,cbaUpdate,cbaUploadType,cbaUpdateType):
    conn = db_connect()
    conn.text_factory = str
    c = conn.cursor()
    retval=0
    try:
        query_lan = c.execute("delete from cbaServer")
        conn.commit()
        query_lan = c.execute("insert into cbaServer (enableCBA, enableSSH,cbaUpload,cbaUpdate,cbaUploadType,cbaUpdateType) values(?,?,?,?,?,?)",[enCBA, enSSH,cbaUpload,cbaUpdate,cbaUploadType,cbaUpdateType])
        conn.commit()

        if enSSH=="yes":
            sprint ("enable SSH",0)
            #systemctl start ssh
            arg1="start"
            arg2="ssh"
            process = subprocess.check_output(["systemctl",arg1,arg2])
            sprint (process,0)
        elif enSSH=="no":
            sprint ("disable SSH",0)
            #systemctl stop ssh
            arg1="stop"
            arg2="ssh"
            process = subprocess.check_output(["systemctl",arg1,arg2])
            sprint (process,0)

    except Exception as e:
        sprint ("updateCBA_SSH except",e)
        retval=-1

    c.close()
    conn.close()
    return retval

def updateCBA(enCBA,cbaUpload,cbaUpdate,cbaUploadType,cbaUpdateType):
    conn = db_connect()
    conn.text_factory = str
    c = conn.cursor()
    retval=0
    try:
        query_lan = c.execute("select * from cbaServer")
        db_lan = c.fetchone()
        if db_lan:
            query_lan = c.execute("update cbaServer set enableCBA=?,cbaUpload=?,cbaUpdate=?,cbaUploadType=?,cbaUpdateType=? where id=?",
                [enCBA,cbaUpload,cbaUpdate,cbaUploadType,cbaUpdateType,db_lan[0]])
            conn.commit()
        else:
            query_lan = c.execute("insert into cbaServer (enableCBA,cbaUpload,cbaUpdate,cbaUploadType,cbaUpdateType) values(?,?,?,?,?)",[enCBA,cbaUpload,cbaUpdate,cbaUploadType,cbaUpdateType])
            conn.commit()

    except Exception as e:
        sprint ("updateCBA except",e)
        retval=-1

    c.close()
    conn.close()
    return retval
    
def updateReverse_SSH(enSSH,reverseSSH):
    conn = db_connect()
    conn.text_factory = str
    c = conn.cursor()
    retval=0
    sprint ("updateReverse_SSH called",0)
    try:
        query_lan = c.execute("select * from cbaServer")
        db_lan = c.fetchone()
        if db_lan:
            query_lan = c.execute("update cbaServer set enableSSH=?,reverseSSH=? where id=?",
                [enSSH,reverseSSH,db_lan[0]])
            conn.commit()
        else:
            query_lan = c.execute("insert into cbaServer (enableSSH,reverseSSH) values(?,?)",[enSSH,reverseSSH])
            conn.commit()

        if enSSH=="yes":
            sprint ("enable SSH",0)
            #systemctl start ssh
            arg1="start"
            arg2="ssh"
            process = subprocess.check_output(["systemctl",arg1,arg2])
            sprint (process,0)
        elif enSSH=="no":
            sprint ("disable SSH",0)
            #systemctl stop ssh
            arg1="stop"
            arg2="ssh"
            process = subprocess.check_output(["systemctl",arg1,arg2])
            sprint (process,0)

    except Exception as e:
        sprint ("updateReverse_SSH except",e)
        retval=-1

    c.close()
    conn.close()
    return retval
    
def DB_UpdateCPU(cpuName,cpuSys_name,cpuState,cpuAction,cpuTemp):
    tempLow="10"
    tempHigh="65"
    conn=db_connect()
    conn.text_factory = str
    c=conn.cursor()
    query=c.execute("select count(*) from cpu where system_name='"+cpuSys_name+"'")
    count = c.fetchone()[0]
    if count==0:
        queryInsert  =c.execute("insert into cpu(name,system_name,temperature,state,cr_date,edit_date,controller_id,low_threshold,hi_threshold) values(?,?,?,?,datetime(),datetime(),1,?,?)",
                                [cpuName,cpuSys_name,cpuTemp,cpuState,tempLow,tempHigh])
        conn.commit()
    else:
        queryUpdate = c.execute("update cpu set temperature=? where system_name=?",[cpuTemp,cpuSys_name])
        conn.commit()
    c.close()
    conn.close()


def is_EncodedString_base64(s):
    try:
        sprint("is_EncodedString_base64",s)
        base64.b64decode(s).decode()
		#decodeStr = base64.decodestring(s)
        pwdDecode = pwd_decoding(s)
        if s==pwdDecode:
            return False
        else:
            return True
    except Exception as e:
        sprint ("is_EncodedString_base64 except", e)
        return False

def pwd_encoding(sample_string):
    try:
        sample_string_bytes = sample_string.encode("ascii")
        base64_bytes = base64.b64encode(sample_string_bytes)
        base64_string = base64_bytes.decode("ascii")
        return base64_string
    except Exception as e:
        sprint ("pwd_encoding except", e)
        return False

def pwd_decoding(base64_string):
    
    #print "base64_string",base64_string
    sample_string=" "
    try:
        base64_bytes = base64_string.encode("ascii")
        sample_string_bytes = base64.b64decode(base64_bytes)
        sample_string = sample_string_bytes.decode("ascii")
    except Exception as e:
        sprint ("pwd_decoding except", e)
		#sample_string=(base64_string)
        return sample_string
        
    return sample_string


def testEncryption():
    encPwd = str(input("Enter Encrypted password to decode:"))
    check = is_EncodedString_base64(encPwd)
    if check:
        decodePwd=pwd_decoding(encPwd)
        print(decodePwd)
    else:
        print("Password is not an encrypted one")
    


def CreateSystemVolume(vgName,VolName):

    VolType="F"
    dev="/dev/"+vgName+"/"+VolName
    try:
        LVM_arg1="-n"
        LVM_arg2=VolName
        LVM_arg3="-L"
        LVM_arg4='1G'
        LVM_arg5=vgName
        LVM_arg6="-y"
        try:
            #lvcreate -n system -L 1G mrp1 -y
            process1 = subprocess.check_output(["sudo","lvcreate",LVM_arg1,LVM_arg2,LVM_arg3,LVM_arg4,LVM_arg5,LVM_arg6])
            sprint(process1,0)
        except Exception as err:
            sprint("lvcreat except ",err)

        if (VolType=="F"):
            dev="/dev/"+vgName+"/"+VolName
            sprint("device=",dev)
            LVM_arg1="-t"
            LVM_arg2="ext4"
            #mkfs.ext4 -O uninit_bg=1 -E lazy_itable_init=1
            try:
                process1 = subprocess.check_output(["sudo","mkfs",LVM_arg1,LVM_arg2,dev])
                sprint(process1,0)
            except Exception as err:
                sprint("mkfs except ",err)
                return(wErrCommandFailed)
        return(0)

    except Exception as err:
        sprint("CreateSystemVolume ",err)
        return(wErrCommandFailed)
        
def BackUpDB2SystemVolume():
    try:
        ForeignDbFileName="/mnt/system/quantumDB.db"
        #Check if Canister is Foreign
        isfile=os.path.isfile(ForeignDbFileName)
        if isfile==True:
            msg1= "ForeignDbFile is present1="+ForeignDbFileName
            LogLevel=20
            ccmINFO=0
            CCM_Alert(ccmINFO,LogLevel,msg1)
            sprint (msg1,0)
            f_size=os.path.getsize(ForeignDbFileName)
            if f_size==0:
                #delete the file
                arg1='-rf'
                sprint ("Remove zero length ForeignDbFile file",0)
                try:
                    process = subprocess.check_output(["rm",ForeignDbFileName])
                except:
                    sprint ("Remove zero length ForeignDbFile file except",0)
            else: #Non Zero file
                res=CheckSerial(ForeignDbFileName)
                if res!=0:
                    sprint ("Canister is foreign =",res)
                    return (0)
    except Exception as err:
        sprint("BackUpDB2SystemVolume Foreign except ",err)
        return (0)
        
    err="None"
    try:
        vgName="null"
        error=False
        filename=DBPath
        conn = sqlite3.connect(filename)
        conn.text_factory = str    
        c=conn.cursor()
        dbquery=c.execute("select system_name from multi_device where name='MegaRAID POOL'")
        resp=c.fetchone()
        sprint ("resp",resp)
        if str(resp) != str("None"):
            vgName=resp[0]
        c.close()
        conn.close()
    except Exception as err:
        sprint("BackUpDB2SystemVolume 1 except ",err)
        error=True

    sprint ("vgName",vgName)
    VolName='system'
    mount='/mnt/system'
    try:
        isdir = os.path.isdir(mount)
        sprint("isdir",(isdir))
        if isdir==False:
            mount="/mnt/"+VolName
            try:
                arg1="-p"
                flag1='-R'
                flag2='777'
                process1 = subprocess.check_output(["sudo","mkdir",arg1,mount])
                process1 = subprocess.check_output(["chown","www-data:www-data",mount])
                process1 = subprocess.check_output(["chmod",flag1,flag2,mount])
            except Exception as err:
                sprint("mkdir-2 except ",err)
                error=True   
        else:
            try:
                arg1="-p"
                flag1='-R'
                flag2='777'
                process1 = subprocess.check_output(["chown","www-data:www-data",mount])
                process1 = subprocess.check_output(["chmod",flag1,flag2,mount])
            except Exception as err:
                sprint("mkdir-3 except ",err)
                error=True
                
    except Exception as err:
        sprint("mkdir-1 except ",err)
        error=True
    try:
        sprint("step",2)
        dev="/dev/"+vgName+"/"+VolName
        isfile = os.path.isfile(dev)
        sprint(dev,isfile)

        if isfile!=True:
            sprint("Calling CreateSystemVolume",0)
            CreateSystemVolume(vgName,VolName)
        sprint("step",3)
        ismount = os.path.ismount(mount)
        if ismount==False:
            sprint("step",4)
            try:
                sprint("step","4a")
                process1 = subprocess.check_output(["sudo","mount",dev,mount])
                sprint("mount",str(dev+" "+mount))
            except Exception as err:
                sprint("mount except ",0)
                error=True
            try:
                arg2=mount
                process1 = subprocess.check_output(["sudo","mountpoint",arg2]) #Check if mountpoint exists
                sprint("step","4b")
                sprint (process1,0)
            except Exception as err:
                sprint("mountpoint except ",0)
                error=True
        
        sprint("step",5)
        try:
            db=DBPath
            dst=mount+'/'+"quantumDB.db"
            process = subprocess.check_output(["sudo","cp",db,dst])
        except Exception as err:
            sprint("step","5a")
            sprint("cp DB except ",err)
            error=True

        if error==True:
            sprint("step","5b")
            sprint ("Error copying ",dst)

    except Exception as err:
        sprint("step","5c")
        sprint("BackUpDB2SystemVolume ",err)
        return(wErrCommandFailed)

def CCM_Alert(LogType,LogLevel,err):
        sprint ("CCM_Alert ",err)
        log_elt="SERVER Manager"
        log_eltName="CCM"
        args=loggerArgs(log_elt,log_eltName,LogLevel,str(err))
        ccmLogger(LogType,"CCM_Alert ",args)
        return 1
        
def InitGlobals ():

    global ccmINFO
    ccmINFO=0
    global ccmWARNING
    ccmWARNING=1
    global ccmERROR
    ccmERROR=2
    global ccmCRITICAL
    ccmCRITICAL=3
    global ccmDEBUG
    ccmDEBUG=4
    
    global ccmVolumeCreate
    ccmVolumeCreate="VolCreate"
    global ccmVolumeDelete
    ccmVolumeDelete="VolDelete"
    global ccmVolumeUpdate
    ccmVolumeUpdate="VolUpdate"
    global ccmVdiskCreate
    ccmVdiskCreate="vDiskCreate"
    global ccmVdiskDelete
    ccmVdiskDelete="vDiskDelete"
    global ccmVdiskUpdate
    ccmVdiskUpdate="vDiskUpdate"
    global ccmPoolCreate
    ccmPoolCreate="PoolCreate"
    global cmPoolUpdate
    cmPoolUpdate="PoolUpdate"
    global cmPoolDelete
    cmPoolDelete="PoolDelete"

    global wErrUpdateFailed
    wErrUpdateFailed=100
    global wErrDuplicateName
    wErrDuplicateName=101
    global wErrNameNotFound
    wErrNameNotFound=102
    global wErrDependents
    wErrDependents=103
    global wErrVolumeInUse
    wErrVolumeInUse=104
    global wErrDeviceNotFound
    wErrDeviceNotFound=105
    global wErriSCSI_SesionInUse
    wErriSCSI_SesionInUse=106
    global wErrBootDiskforeign
    
    wErrBootDisk=107
    global wErrUnknownCmd
    wErrUnknownCmd=108
    global wErrCommandFailed
    wErrCommandFailed=109
    global wErrPoolInUse
    wErrPoolInUse=110

    global StorageBackend
    StorageBackend="LVM"
    StorageBackend="zfs"
    
    global gVolOff
    gVolOff=4
    global gVolOn
    gVolOn=6
    global gVolStarting
    gVolStarting=5
    global gVolSuspended
    gVolSuspended=7
    global cifs
    cifs=1
    global nfs
    nfs=2
    global iSCSI_Chap
    iSCSI_Chap=3
    global iSCSI_NoChap
    iSCSI_NoChap=4
    global ftp
    ftp=5    
    global iSER_Chap
    iSER_Chap=8
    global iSER_NoChap
    iSER_NoChap=9
    global cifs_RDMA
    cifs_RDMA=10
    global nfs_RDMA
    nfs_RDMA=11
    global S3
    S3=12    
    
    global machine
    machine=1
    #machine=2
    global OEM
    OEM = "Quantum"

    global log_elt
    log_elt = "SERVER Manager"
    global MegaRAID
    MegaRAID = "MegaRAID POOL"
    
    global gTarget
    gTarget="tgt"
    
    global LicenceState
    LicenceState=-1

    global gTID
    gTID=1
    print("gTID",gTID)

    global tidStack
    tidStack = []
    
    global stackCnt
    stackCnt = 0
    i=0
    while i<128:
        tidStack.append(128-i)
        i=i+1

    #Storman globals
    global gInvalidLocalDirectory
    gInvalidLocalDirectory=-3
    global gMountError
    gMountError=-4
    global guMountError
    guMountError=-5
    global grmdirError
    grmdirError=-6
    global gLinkError
    gLinkError=-7
    global gExportError
    gExportError=-8

    #Alert Log globals
    global INFO
    INFO=0
    global WARNING
    WARNING=1
    global ERROR
    ERROR=2
    global CRITICAL
    CRITICAL=3
    global DEBUG
    DEBUG=4
    global CodeDebug
    CodeDebug=20

    global PowerOff
    PowerOff=False
    
    global ST_logger
    ST_logger=None
    global STCON_logger
    STCON_logger=None
    
    global G15
    G15=None
    
    global DelOnExtraction
    DelOnExtraction=True
    global raptor
    raptor =False
       
def DeleteSystemVol(vgName):
#/dev/mapper/p1-system
# sudo rm -rf /dev/disk/by-id/dm-name-p1-system
#sudo rm /dev/disk/by-uuid/c879ca2c-4142-4b75-9186-626d47e8f024
# sudo rm /dev/dm-0

    sysVol=True
    volName='system'    
    sprint ("removing system mount",0)
    try:
        arg1='-la'
        arg2='/dev/'+vgName+'/'+volName
        process1 = subprocess.check_output(["ls",arg1,arg2]) #Check if mountpoint exists
    except Exception as err:
        sysVol=False
        sprint ("system Vol except 1 ",err)
        
    if sysVol==False:
        return (0)
    try:
        mount="/mnt/"+volName
        arg2=mount
        isdir = os.path.isdir(mount)
        sprint ("isdir",isdir)
        if isdir==True:
            sprint ("removing system mount",0)
            try:
                process1 = subprocess.check_output(["mountpoint",arg2]) #Check if mountpoint exists
                sprint (process1,0)
            except Exception as err:
                sprint ("mountpoint except ",err)
            try:
                process1 = subprocess.check_output(["umount",arg2])
                sprint (process1,0)
                time.sleep(2)
                #needs to poll here until mountpoint is gone
            except Exception as err:
                sprint ("umount except ",err)

            try:
                #sudo rmdir -p /mnt/nfs_backup
                arg1="-p"
                arg2=mount
                sprint ("rmdir",arg2)
                process1 = subprocess.check_output(["rmdir",arg1,arg2])
            except Exception as err:
                sprint ("rmdir except ",err)
            
        dev="/dev/"+vgName+"/"+volName
        LVM_arg1="-y"
        try:
            process1 = subprocess.check_output(["lvremove",LVM_arg1,dev])
            sprint(process1,0)
        except Exception as err:
            sprint("lvremove except ",err)
            
    except Exception as err:
        sprint ("system Vol except 2 ",err)
        return (0)
def GetPools(location):
    pool=[]
    try:
        filename=DBPath
        conn = sqlite3.connect(filename)
        conn.text_factory = str
        c = conn.cursor()
        query=c.execute("select system_name from multi_device where location='"+ str(location)+"'")
        resp = c.fetchall()
        sprint ("Multi Device values",resp)
        if resp !="None":
            for col in resp:
                pool.append(str(col[0]))
        c.close()
        conn.close()
        return 0,pool
        
    except Exception as err:
        sprint("GetPools except ",err)
        c.close()
        conn.close()
        return -1,pool

def getVolFSTYPE (vol):
    try:
        sprint("getVolFSTYPE Vol=",vol)
        arg1= "-f"
        arg2= "-J"
        i=0
        retVal=-1
        fstype=""
        #lsblk -f -J
        process = subprocess.check_output(["lsblk",arg1,arg2])
        y = json.loads(process)
        NbDisk= len(y['blockdevices'])
        sprint ("NB disks ",NbDisk)
        while (i < NbDisk):
            if (y['blockdevices'][i]['fstype']=="LVM2_member"):
                NbParts=len(y['blockdevices'][i]['children'])
                sprint ("getVolFSTYPE NbParts",NbParts)
                j=0
                while (j<NbParts):
                    VolName=str(y['blockdevices'][i]['children'][j]["name"])
                    fstype= str(y['blockdevices'][i]['children'][j]["fstype"])
                    sprint (VolName,fstype)
                    if vol==VolName:
                        sprint ("Found Vol==", vol)
                        retVal=0
                        break
                    j=j+1
            i=i+1
            
        return (retVal,fstype)

    except Exception as err:
        sprint("GetVolFSTYPE except ",err)
        return (retVal,fstype)
        
def GetVolDefaultValues(protocol):
    sprint('GetVolDefaultValues',protocol)
    try:
        filename=DBPath
        conn = sqlite3.connect(filename)
        conn.text_factory = str
        c = conn.cursor()
        res=-1
        port_id=0
        host_id=0
        lun= getFreeVolumeLun()
        query=c.execute("select id from volume where size=?",[0])
        resp=c.fetchone()
        conn.commit()
        sprint ("default vol id resp=",resp)
        vol_id=9999
        #if str(resp) !=None or str(resp)!='None':
        if str(resp)!='None':
            vol_id=resp[0]    
        if vol_id!=9999:
            query=c.execute("select port_id,host_id,lun from  export where vol_id=?",[vol_id])
            resp=c.fetchone()
            conn.commit()
            sprint ("vol id resp=",resp)
            if str(resp) != str("None"):
                port_id=resp[0]
                host_id=resp[1]
                lun=resp[2]
                res=0
            msg='port_id='+str(port_id)+' host_id='+str(host_id)+' lun='+str(lun)
            sprint(msg,0)
        c.close()
        conn.close()
        return res,port_id,host_id,lun
    
    except Exception as err:
        sprint("GetVolDefaultValues except ",err)
        return -1,0,0,0




def OrphanZFSVolumeCreate(PoolName,location,VolList):
    vm='zfs'
    print ("OrphanZFSVolumeCreate step1")
    try:
        if vm=='zfs':
            print ("ZFS")
        lun=getFreeVolumeLun()
        print ("OrphanZFSVolumeCreate step2")
        portId=1
        V_type="Native"
        zfsCompression="false"
        zfsDedup="false"
        backup="false"
        thin="false"
        res=DB_UpdateHost("localvolume","","127.0.0.1","",nfs,"Single Host")
        if res[0]==0:
            LocalVol_Host=res[1]
            
        res=DB_UpdateHost("localnfs","","127.0.0.1","",nfs,"Single Host")
        if res[0]==0:
            LocalNFS_Host=res[1]
            
        res=DB_UpdateHost("localcifs","sanuyi","127.0.0.1","hello123",cifs,"Single Host")
        if res[0]==0:
            LocalCIFS_Host=res[1]
            
        res=DB_UpdateHost("localiscsi","","127.0.0.1","",iSCSI_NoChap,"Single Host")
        if res[0]==0:
            LocaliSCSI_Host=res[1]
        host=LocalVol_Host
        fstype="ext4"
        print ("OrphanZFSVolumeCreate step3")
        for item in VolList:
            print ("OrphanZFSVolumeCreate step4")
            #sprint ("item",item)
            element="volume"
            VolName=str(item[1])
            lvsize=str(item[0])
            print ("OrphanZFSVolumeCreate step5")
            PoolVolName=PoolName+"-"+VolName
            result=DB_CheckElement(element,VolName)
            #result=0 #Andrew
            print ("OrphanZFSVolumeCreate step6")            
            if (result==0 and VolName!="system"):
                sprint (("DB Volume does not exist, Orphan Volume "),str(VolName))
                sprint (("Create Orphan Volume "),str(VolName))
                result=DB_CreateVolumeBis(PoolName,VolName,lvsize,zfsCompression, zfsDedup,V_type,backup,thin,location,lun)
                if result==0:
                    sprint (("DB_CreateVolumeBis success"),VolName)
                else:
                    sprint (("DB_CreateVolumeBis failure"),VolName)
                bs=" "
                try:
                    
                    ret=getVolFSTYPE(PoolVolName)
                    msg=str(ret[0]) +'/'+ str(ret[1])
                    sprint("FSTYPE=",msg)
                    if ret[0]==0:
                        fstype=ret[1]
                    if fstype=="None":
                        host=LocaliSCSI_Host
                    elif fstype=="ext4":
                        host=LocalVol_Host
                    elif fstype=="xfs":
                        host=LocalNFS_Host
                    elif fstype=="vfat":
                        host=LocalNFS_Host
                    elif fstype=="iso9660":
                        host=LocalNFS_Host
                except Exception as err:
                    sprint("getVolFSTYPE except2 ",err)
    
                res=GetVolDefaultValues('nfs')
                portId=0
                host=0
                protocol=0
                sprint('protocol=',fstype)
                if res[0]==0:
                    portId=res[1]
                    host=res[2]
                    lun=res[3]
                    protocol=[4]
                    msg=str(PoolName)+bs+str(portId)+bs+str(VolName)+bs+str(host)+bs+str(lun)
                    sprint ("Update Export",msg)
                    DB_UpdateExport(PoolName,portId,VolName,host,lun)
                    lun=lun+1
                else:
                    sprint ("GetVolDefaultValues error=",res[0])
            else:
                msg=VolName+':'+str(lv_size)
                sprint ("DB Volume exists, update size ",msg)
                DB_UpdateVolumeSize(VolName,lvsize)

            #input('OrphanZFS VolumeCreate ==>')
        
        return 0,VolList
    except Exception as err:
        sprint("UpdateZFSOrphanVolumes except ",err)
        return -1,VolList
        


def OrphanVolumeCreate(PoolName,location):
    VolList=[]
    try:
        device="null"
        LVM_arg1="-C"
        LVM_arg2="--noheadings"
        LVM_arg3="--reportformat"
        LVM_arg4="json"
        process1 = subprocess.check_output(["lvdisplay",LVM_arg1,LVM_arg2,LVM_arg3,LVM_arg4])
        #sudo lvdisplay -C --noheadings --reportformat json
        y = json.loads(process1)
        NbLv= len(y['report'][0]['lv'])
        i=0
        j=0
        sprint ("NbLv",NbLv)
        while (i < NbLv):
            lvname=(y['report'][0]['lv'][i]['lv_name'])
            vg=(y['report'][0]['lv'][i]["vg_name"])
            VolSize=(y['report'][0]['lv'][i]["lv_size"])
            str_len=len(VolSize)
            sprint ("lvdisplay VolSize",str(VolSize))
            if VolSize.find(str('<'),0,str_len) !=-1:
                sectors=VolSize.replace(str('<'), '')
                VolSize=sectors
                str_len=str_len-1
            if VolSize.find("g",0,str_len) !=-1:
                sectors=VolSize.replace('g', '')
                sectors=float(sectors)
            elif VolSize.find("t",0,str_len) !=-1:
                sectors=VolSize.replace('t', '')
                sectors=float(sectors)*1024
            lv_size=int(sectors)
            if vg==PoolName:
                device="/dev/"+vg+"/"+lvname
                sprint ("Device Found",device)
                VolList.insert(j,[lv_size,lvname])
                j=j+1
            i=i+1
        sprint ("Volumes found",VolList)
        lun=getFreeVolumeLun()
        portId=1
        V_type="Native"
        zfsCompression="false"
        zfsDedup="false"
        backup="false"
        thin="false"
        res=DB_UpdateHost("localvolume","","127.0.0.1","",nfs,"Single Host")
        if res[0]==0:
            LocalVol_Host=res[1]
            
        res=DB_UpdateHost("localnfs","","127.0.0.1","",nfs,"Single Host")
        if res[0]==0:
            LocalNFS_Host=res[1]
            
        res=DB_UpdateHost("localcifs","sanuyi","127.0.0.1","hello123",cifs,"Single Host")
        if res[0]==0:
            LocalCIFS_Host=res[1]
            
        res=DB_UpdateHost("localiscsi","","127.0.0.1","",iSCSI_NoChap,"Single Host")
        if res[0]==0:
            LocaliSCSI_Host=res[1]
        host=LocalVol_Host
        fstype="ext4"
        for item in VolList:
            sprint ("item",item)
            element="volume"
            VolName=str(item[1])
            lvsize=str(item[0])
            PoolVolName=PoolName+"-"+VolName
            result=DB_CheckElement(element,VolName)
            result=0                        #Andrew
            if (result==0 and VolName!="system"):
                sprint (("DB Volume does not exist, Orphan Volume "),str(VolName))
                sprint (("Create Orphan Volume "),str(VolName))
                result=DB_CreateVolumeBis(PoolName,VolName,lvsize,zfsCompression, zfsDedup,V_type,backup,thin,location,lun)
                if result==0:
                    sprint (("DB_CreateVolumeBis success"),VolName)
                else:
                    sprint (("DB_CreateVolumeBis failure"),VolName)
                bs=" "
                try:
                    
                    ret=getVolFSTYPE(PoolVolName)
                    msg=str(ret[0]) +'/'+ str(ret[1])
                    sprint("FSTYPE=",msg)
                    if ret[0]==0:
                        fstype=ret[1]
                    if fstype=="None":
                        host=LocaliSCSI_Host
                    elif fstype=="ext4":
                        host=LocalVol_Host
                    elif fstype=="xfs":
                        host=LocalNFS_Host
                    elif fstype=="vfat":
                        host=LocalNFS_Host
                    elif fstype=="iso9660":
                        host=LocalNFS_Host
                except Exception as err:
                    sprint("getVolFSTYPE except2 ",err)
    
                res=GetVolDefaultValues('nfs')
                portId=0
                host=0
                lun=0
                protocol=0
                sprint('protocol=',fstype)
                if res[0]==0:
                    portId=res[1]
                    host=res[2]
                    lun=res[3]
                    protocol=[4]
                    msg=str(PoolName)+bs+str(portId)+bs+str(VolName)+bs+str(host)+bs+str(lun)
                    sprint ("Update Export",msg)
                    DB_UpdateExport(PoolName,portId,VolName,host,lun)
                    lun=lun+1
                else:
                    sprint ("GetVolDefaultValues error=",res[0])
            else:
                msg=VolName+':'+str(lv_size)
                sprint ("DB Volume exists, update size ",msg)
                DB_UpdateVolumeSize(VolName,lvsize)

        #input('OrphanVolumeCreate ==>')
        
        return 0,VolList
    except Exception as err:
        sprint("UpdateOrphanVolumes except ",err)
        return -1,VolList
        


def QuiescePools(flag):
#   BUG, we need to use  sudo vgchange --refresh after a Canister is inserted
    try:
        #filename="/var/www/quantumDB.db"
        #drop caches

        vgErr=False
        filename=DBPath
        conn = sqlite3.connect(filename)
        conn.text_factory = str
        c = conn.cursor()
        query = c.execute("select system_name from multi_device")
        resp = c.fetchall()
        arg1="-v"
        arg2="-a"
        #The vgchange command activates or deactivates one or more volume groups
        if flag==True:
            arg3="n"    #deactivate the pools
            os.system("echo 1 > /proc/sys/vm/drop_caches")
            os.system("echo 2 > /proc/sys/vm/drop_caches")
            os.system("echo 3 > /proc/sys/vm/drop_caches")
        else:
            arg3="y"    #activate the pools

        sprint ("Multi Device values",resp)
        if resp !="None":
            for col in resp:
                arg4=col[0]
                sprint ("Quiesce Pool ",arg4)
                #sudo vgchange -v -a y mrp1 mrp1
                #sudo vgchange -v -a n mrp1
                #for pool in list TBD
                if arg4 !="system":
                    try:
                        msg=arg1+" "+arg2+" "+arg3+" "+str(arg4)
                        sprint ("vgchange", msg)
                        process1 = subprocess.check_output(["vgchange", arg1,arg2,arg3,arg4])
                        sprint (process1,0)
                        vgErr=False
                    except Exception as err:
                        sprint("vgchange-1 except ",err)
                        vgErr=True
                        vgErr=False  #BUG?
        c.close()
        conn.close()
        if vgErr==True:
            return -1
        else:
            return 0
    except Exception as err:
        sprint("vgchange-2 except ",err)
        c.close()
        conn.close()        
        return (-1)


def GetBaseBoard():
    #sudo dmidecode -s baseboard-product-name
    process1 = subprocess.check_output(["sudo",'dmidecode','-s','baseboard-product-name'])
    bbName = process1.strip()
    bbN=bbName.decode("utf-8")
    print(("baseboard name=",bbN))
    if len(bbN)==0:
        return (-1,"NA")
    else:
        return 0,bbN
 
def SetStorageBackend():

    global StorageBackend
    
    res=GetBaseBoard()
    if res[0]==0:
        bb=res[1]
        print("baseboard=",bb)
        if res[1]=="X13SAV-LVDS":
            StorageBackend="LVM"
        elif res[1]=="X570D4I-2T":
            StorageBackend="LVM"
        elif res[1]=="H12SSL-I":
            StorageBackend="LVM"
        elif res[1]=="015C68":
            StorageBackend="zfs"
        elif res[1]=="440BX Desktop Reference Platform":
            StorageBackend="zfs"
        elif res[1]=="015C68":
            StorageBackend="zfs"
        elif res[1]=="Inagua CRB":
            StorageBackend="zfs"
        elif res[1]=='E3C224D4I-14S':
            StorageBackend="zfs"
        else:
            StorageBackend="zfs"
    
    sprint ("storage backend step1 =",StorageBackend)
    StorageBackend='zfs'    
    sprint ("storage backend step2 =",StorageBackend)
    
def CheckBaseBoard(bb):
    #sudo dmidecode -s baseboard-product-name
    process1 = subprocess.check_output(["sudo",'dmidecode','-s','baseboard-product-name'])
    bbName = process1.strip()
    bbN=bbName.decode("utf-8")
    print ("bbName",bbN,bb)
    if len(bbN)==0:
        return (-1)
    if bbN==bb:
        return 0
    else:
        return (-1)      

def CheckSerial(filename):

    isfile=os.path.isfile(filename)
    if isfile==True:
        sprint ("CheckSerial file ",filename)
        try:
            Fconn = sqlite3.connect(filename)
            Fconn.text_factory = str
            Fconn.execute('pragma foreign_keys=ON')
            Fc = Fconn.cursor()

            #sudo dmidecode -s baseboard-serial-number
            process1 = subprocess.check_output(["sudo",'dmidecode','-s','baseboard-serial-number'])
            dmiS =  process1.strip()
            dmiSerial=dmiS.decode("utf-8")
            sprint ("Serial found",dmiSerial)
            sprint ("len dmiSerial",len(dmiSerial))
            if (len(dmiSerial)!=0 and dmiSerial!="None"):
                sprint ("dmidecode serial(uuid)=",dmiSerial)
            else:

                #sudo dmidecode -s system-uuid
                process1 = subprocess.check_output(["sudo",'dmidecode','-s','system-uuid'])
                ID = process1.strip()
                UUID=ID.decode("utf-8")
                sprint ("UUID=",UUID)
                dmiSerial=UUID.replace("-","")
                sprint ("dmidecode serial (baseboard)=",dmiSerial)

            query = Fc.execute("select serial_number from system")
            dbSerial = Fc.fetchone()[0]
            sprint ("DB serial=",dbSerial)
            Fc.close()
            Fconn.close()
            if dbSerial==dmiSerial:
                sprint ("Canister serial is local",dbSerial)
                return 0
            else:
                sprint ("Canister serial is Foreign ",dbSerial)
                return -1
        except Exception as err:
            sprint ("except CheckSerial",err)
            Fc.close()
            Fconn.close()
            return(wErrCommandFailed)
    else:
        sprint ("no Foreign DB",filename)
        return 0

def ImportMegaRAID(cx):

    MR=False
    WDen=False
    res=CheckBaseBoard("X570D4I-2T")            #R6000 standard baseboard
    if res==0:
        MR=True
        WDen=True
        sprint ("X570D4I-2T detected",0)

    res=CheckBaseBoard("H12SSL-I")            #Raptor standard baseboard
    if res==0:
        MR=True
        WDen=True
        sprint ("H12SSL-I detected",0)
        
    res=CheckBaseBoard("X13SAV-LVDS")       #Prowler standard baseboard
    if res==0:
        sprint ("X13SAV-LVDS detected",0)
        MR=True
        WDen=False

        
    if MR==False:
        sprint ("MR is False",0)
        #choice=raw_input("Step 0a: ImportMegaRAID  MR is False <cr> ")
        return 0
        

    
    #add in logs
    storcli="/opt/MegaRAID/storcli/storcli64"
    # 1 vgchange
    # 2 hide vd from os
    # 3 pull canister
    # 4 restart controller
    # 5 set drives good
    # 6 import foreign config
    
    # sudo /opt/MegaRAID/storcli/storcli64 /c0/e252/sall set offline
    #storcli /c0/v0 set hidden=on hide a raid set
    #/c0/e25/s4 set offline
    wd("reset",0,WDen)
    logMsg="Import MegaRAID"
    sprint (logMsg,0)
    LogLevel=20
    ccmINFO=0
    CCM_Alert(ccmINFO,LogLevel,logMsg)
    
    try:
        powerCtrl="./set-power"
        arg1="all"
        arg2="on"
        msg=arg1+" "+arg2
        sprint ("powerCtrl ON ", msg)
        process1 = subprocess.check_output([powerCtrl, arg1,arg2])
        logMsg= "Power to the drives"
        sprint (logMsg,arg2)
        CCM_Alert(ccmINFO,LogLevel,logMsg)
        
    except Exception as err:
        sprint("powerCtrl ON except ","err")

    try:
        waitCR=False
        try:
            #sudo /opt/MegaRAID/storcli/storcli64 /c0/vall set hidden=on
            arg1=cx+"/vall"
            arg2="set"
            arg3="hidden="
            arg4="on"
            msg=arg1+" "+arg2+" "+arg3+" "+arg4
            sprint ("storcli", msg)
            process1 = subprocess.check_output([storcli, arg1,arg2,arg3,arg4])
            #sprint (process1,0)
            time.sleep(2)
            logMsg= "MegaRAID set hidden=on"
            #sprint (logMsg,0)
            CCM_Alert(ccmINFO,LogLevel,logMsg)
        except Exception as err:
            sprint("storcli hidden except ",err)
            #return (-2)

        arg1="/c0"
        arg1=cx
        wd("reset",0,WDen)
        MegaRaidRestart=True
        if MegaRaidRestart==True:
            arg2="restart"
        else:
            arg2="NOrestart"
        msg=arg1+" "+arg2
        sprint ("storcli", msg)
        if arg2=="restart":
            try:
                process1 = subprocess.check_output([storcli, arg1,arg2])
                #sprint (process1,0)
                logMsg= "MegaRAID restart"
                sprint (logMsg,0)
                CCM_Alert(ccmINFO,LogLevel,logMsg)
                if waitCR==True:
                    zero=input("(c)ontinue to restart controller =>")
            except Exception as err:
                sprint("storcli Restart except ",err)
                #return (-3)

        arg1=cx
        arg2="show"
        arg3="all"
        msg=arg1+" "+arg2+" "+arg3
        sprint ("storcli", msg)        
            #sudo ./set-power all on
        try:
            process1 = subprocess.check_output([storcli, arg1,arg2,arg3])
            #sprint (process1,0)
        except Exception as err:
            sprint("storcli show all except ",err)
            #return (-4)
            
        wd("reset",0,WDen)
        #Poll for drives to come online
        logMsg= "MegaRAID Poll for drives to come online"
        sprint (logMsg,0)
        CCM_Alert(ccmINFO,LogLevel,logMsg)
        CheckLoop=0
        NbDisks=0

        if MR==True:
            NbDisksNeeded=4
        else:
            res=CheckBaseBoard("440BX Desktop Reference Platform") #VMWARE standard baseboard
            if res==0:
                NbDisksNeeded=0
            else:
                NbDisksNeeded=2
        WaitLoop=0
        WaitLoopMaX=3
        while ((NbDisks !=NbDisksNeeded) and (WaitLoop!=WaitLoopMaX)):
            list=CheckMegaRAIDDrives(cx)
            if list[0]==0:
                NbDisks=len(list[1])
            else:
                NbDisks=0
            sprint ("NbDisks", NbDisks)
            time.sleep(2)
            WaitLoop=WaitLoop+1
            msg1= "Minimum number of disks not available, loop= "
            sprint (msg1,WaitLoop)
            if WaitLoop==WaitLoopMaX:
                sprint ("Max loops exceeded",str(WaitLoop))
                ccmINFO=0
                LogLevel=20
                CCM_Alert(ccmINFO,LogLevel,msg1)
                
        sprint ("Number of disks found=",NbDisks)
        if NbDisksNeeded==NbDisks:
            sprint ("Disks found, importing RAID",0)
            try:
                #sudo /opt/MegaRAID/storcli/storcli64 /c0/e252/sall set good force
                arg1=cx+"/e252/sall"
                arg2="set"
                arg3="good"
                arg4="force"
                msg= arg1+" "+arg2+" "+arg3+" "+arg4                
                sprint ("storcli",msg)
                process1 = subprocess.check_output([storcli, arg1,arg2,arg3,arg4])
                #sprint (process1,0)
                logMsg= "MegaRAID set drives to ugood"
                sprint (logMsg,0)
                CCM_Alert(ccmINFO,LogLevel,logMsg)
            except Exception as err:
                sprint("storcli set Good except ",err)
                #return (-6)
            try:
                wd("reset",0,WDen)
                #sudo /opt/MegaRAID/storcli/storcli64 /c0/fall import
                arg1=cx+"/fall"
                arg2="import"
                process1 = subprocess.check_output([storcli, arg1,arg2])        
                #sprint (process1,0)
                logMsg= "MegaRAID config import"
                sprint (logMsg,0)
                CCM_Alert(ccmINFO,LogLevel,logMsg)
            except Exception as err:
                sprint("storcli set fall import  except ",err)
                #return (-1)
                
            #sudo /opt/MegaRAID/storcli/storcli64 /c0/vall set hidden=off
            try:
                arg1=cx+"/vall"
                arg2="set"
                arg3="hidden="
                arg4="off"
                logMsg= "MegaRAID set hidden=off step 1"
                sprint (logMsg,0)
                process1 = subprocess.check_output([storcli, arg1,arg2,arg3,arg4])
                #sprint (process1,0)
                logMsg= "MegaRAID set hidden=off"
                sprint (logMsg,0)
                CCM_Alert(ccmINFO,LogLevel,logMsg)
                time.sleep(2)
                #choice=raw_input("Step 0b: ImportMegaRAID <cr> ")
                return (0)

            except Exception as err:
                sprint("storcli set hidden off except ",0)
                #choice=raw_input("Step 0c: ImportMegaRAID <cr> ")
                return (0)
        else:
            sprint ("NO Disks found, Not Importing RAID",0)
            #choice=raw_input("Step 0c: ImportMegaRAID <cr> ")
            return (-5)
        
    except Exception as err:
        sprint("ImportMegaRAID except ",err)
        #choice=raw_input("Step 0e: ImportMegaRAID <cr> ")
        return (-6)
        
def RestartServices():
    sprint ("RestartServices",0)
    try:
        process1 = subprocess.check_output(["systemctl","restart","nfs-kernel-server"])
        sprint (process1,0)   
        process1 = subprocess.check_output(["service","smbd","restart"])
        sprint (process1,0)
        process1 = subprocess.check_output(["service","nmbd","restart"])
        sprint (process1,0)
        process1 = subprocess.check_output(["systemctl", "restart","tgt"])
        sprint (process1,0)
        #systemctl restart lvm2-lvmetad.service
        #process1 = subprocess.check_output(["systemctl", "restart","lvm2-lvmetad.service"])
        #sprint (process1,0)
        return 0
    except Exception as err:
        sprint("RestartServices except ",err) 
        return -1
       
def getForeignDevice(VolumeName):
    try:
        device="null"
        LVM_arg1="-C"
        LVM_arg2="--noheadings"
        LVM_arg3="--reportformat"
        LVM_arg4="json"
        process1 = subprocess.check_output(["lvdisplay",LVM_arg1,LVM_arg2,LVM_arg3,LVM_arg4])
        #sudo lvdisplay -C --noheadings --reportformat json
        y = json.loads(process1)
        NbLv= len(y['report'][0]['lv'])
        i=0
        sprint ("NbLv",NbLv)
        while (i < NbLv):
            lvname=(y['report'][0]['lv'][i]['lv_name'])
            vg=(y['report'][0]['lv'][i]["vg_name"])
            if lvname==VolumeName:
                device="/dev/"+vg+"/"+lvname
                sprint ("Device Found",device)
                return (0,device)
            i=i+1
        sprint ("Device NOT Found",device)
        return -1,"null"
    except Exception as err:
        sprint("getForeignDevice except ",err)

def CheckForeignDB():
    try:
        sprint ("CheckForeignDB",0)
        ConfigPath="/mnt/system/"
        ForeignDB="quantumDB.db"
        isdir = os.path.isdir(ConfigPath)
        if isdir:
            sprint ("directory exists ",ConfigPath)
        else:
            sprint ("create the directory to mount",0)
            process = subprocess.check_output(["mkdir",ConfigPath])
            sprint (process,0)

        ismount = os.path.ismount(ConfigPath)
        if ismount:
            sprint ("path is  mounted ",ConfigPath)
        else:
            sprint ("mount Foreign DB DATA device",0)
            Fvol="system"
            res=getForeignDevice(Fvol)
            if res[0]==0:
                ForeignDevice=res[1]
                sprint ("Mounting Device",ForeignDevice)
                process = subprocess.check_output(["mount",ForeignDevice,ConfigPath])

            else:
                sprint ("Foreign volume not found ",Fvol)
                return -1
        flag1='+x'
        flag2='666'
        arg1="www-data:www-data"
        sprint ("Change permissions ",ConfigPath+ForeignDB)
        #sudo chmod -R 777 /mnt/data/
        try:
            process = subprocess.check_output(["chmod",flag1,ConfigPath+ForeignDB])
            sprint("Chmod +x ForeignDB = ",ConfigPath+ForeignDB)
        except Exception as err:
            sprint("CheckForeignDB chmod except ",err)
            return -1
        try:
            sprint ("Chown ForeignDB =",ConfigPath+ForeignDB)
            process = subprocess.check_output(["chown",arg1,ConfigPath+ForeignDB])
        except Exception as err:
            sprint("CheckForeignDB chown except ",err)
            return -1

        return 0
    
    except Exception as err:
        sprint("CheckForeignDB except ",err)
        return -1
        
def CheckMegaRAID_Pools(cx):
#8|MegaRAID POOL|1|No|0|No|Yes|2021-08-12 20:53:11|2021-08-12 20:53:11||||mrp1|0|14300|||||0||14300
    location=getPoolLocation(cx)
    FakePoolUpdate("critical",location)
    storcli="/opt/MegaRAID/storcli/storcli64"
    keepVD="xxxx"
    kilobytes=1000
    try:
        #argLog="logfile="+storCLIlog
        arg1=cx+"/vall"
        cmd="show"
        argLast='J'
        #sudo /opt/MegaRAID/storcli/storcli64 /c0/vall show J logfile=/mnt/data/storcli.log
        process1 = subprocess.check_output([storcli,arg1,cmd,argLast])
        y = json.loads(process1)
        sprint ("# controllers",len (y['Controllers']))
        x=y['Controllers'][0]['Command Status']
        #print x["CLI Version"]
        #print x["Operating system"]
        #print x["Status"]
        #print x["Description"]
        if x["Description"] != "No VD's have been configured.":
            sprint ("MegaRAID Pools are configured",str(x["Description"]))
            NbVD= len(y['Controllers'][0]['Response Data']["Virtual Drives"])
            i=0
            sprint ("NbVD=",NbVD)
            x=y['Controllers'][0]['Response Data']["Virtual Drives"]
            sprint (x,0)
            while (i< NbVD):
                PoolName=x[i]["Name"]
                sizeStr=x[i]["Size"]
                sprint ("MegaRAID Pool name",PoolName)
                sprint ("MegaRAID Pool size",str(sizeStr))
                
                if sizeStr.find("MB") !=-1:
                    size=float(sizeStr.replace(" MB", ""))
                    size=1
                elif sizeStr.find("GB") !=-1:
                    size=float(sizeStr.replace(" GB", ""))
                elif sizeStr.find("TB") !=-1:
                    size=float(sizeStr.replace(" TB", ""))
                    size=size*kilobytes
                PoolSize=int(size)
                sprint ("MegaRAID Pool size",str(PoolSize))
                Pool="MegaRAID POOL"
                level=x[i]["TYPE"]
                if level=="RAID0":
                    PoolLevel=0
                elif level=="RAID5":
                    PoolLevel=1
                elif level=="RAID1":
                    PoolLevel=1
                else: 
                    PoolLevel=0
                    
                location=getPoolLocation(cx)
                #sprint "#######################START####################################"
                msg=str(PoolName)+" "+str(PoolSize)+" "+str(PoolLevel)+" "+str(location)
                sprint ("FakePoolCreate",msg)
                #sprint "#######################END####################################"
                FakePoolCreate(Pool,PoolName,PoolSize,PoolLevel,location)
                i=i+1
                
        else:
            sprint ("No VD's have been configured.",0)
        return 0
    except Exception as err:
        sprint("CheckMegaRAID_Pools except ",err) 

def CheckLVM_Pools(location):
    try:
        LVM_arg1="-C"
        LVM_arg2="--noheadings"
        LVM_arg3="--reportformat"
        LVM_arg4="json"
        #sudo vgdisplay -C --noheadings --reportformat json
        process1 = subprocess.check_output(["vgdisplay",LVM_arg1,LVM_arg2,LVM_arg3,LVM_arg4])
        sprint(process1,0)
        y = json.loads(process1)
        NbVg= len(y['report'][0]['vg'])
        i=0
        sprint ("NbVg",NbVg)
        #print (y['report'])
        Pool="HDD POOL"
        PoolLevel=0
        while (i < NbVg):
            #print (y['report'][0]['vg'])
            PoolName=y['report'][0]['vg'][i]['vg_name']
            PoolSize=y['report'][0]['vg'][i]['vg_size']
            str_len=len(PoolSize)
            sprint ("vgdisplay PoolSize",str(PoolSize))
            if PoolSize.find(str('<'),0,str_len) !=-1:
                sectors=PoolSize.replace(str('<'), '')
                PoolSize=sectors
                str_len=str_len-1
            if PoolSize.find("g",0,str_len) !=-1:
                sectors=PoolSize.replace('g', '')
                sectors=float(sectors)
            elif PoolSize.find("t",0,str_len) !=-1:
                sectors=PoolSize.replace('t', '')
                sectors=float(sectors)*1024
            p_size=int(sectors)
            #sprint "#######################START####################################"
            msg=str(PoolName)+" "+str(p_size)+" "+str(PoolLevel)+" "+str(location)
            sprint ("FakePoolCreate",msg)
            #sprint "#######################END####################################"
            FakePoolCreate(Pool,PoolName,p_size,PoolLevel,location)
            i=i+1

    except Exception as err:
        sprint("CheckLVM_Pools except ",err)


def CheckMounts():
    try:
        #findmnt /mnt/remote/mnt/nfs16 -o SOURCE,TARGET,SIZE,AVAIL,USED,USE% -J
        arg1="-o"
        arg2="SOURCE,TARGET,SIZE,AVAIL,USED,USE%"
        arg3="-J"
        process1 = subprocess.check_output(["findmnt","-J"])
        y = json.loads(process1)
        x=y['filesystems'][0]["children"]
        NbFS=len(x)
        i=0
        sprint ("NbFS=",NbFS)
        while (i< NbFS):
            MyMnt=x[i]["target"]
            if MyMnt.find("mnt")!=-1:
                sprint ("MyMnt",MyMnt)
                if (MyMnt != "/mnt/data"):
                    if (MyMnt != "/mnt/xdata"):
                        if (MyMnt != "/mnt/system"):
                            sprint ("umount ",MyMnt)
                            process1 = subprocess.check_output(["umount",'-l',MyMnt])
                            try:
                                process1 = subprocess.check_output(["rm",'-rf',MyMnt])
                            except Exception as err:
                                sprint("CheckMounts delete except ",MyMnt)
            i=i+1
    except Exception as err:
        sprint("CheckMounts except ",err)
        return -1


def setAllOnOff(arg):
    try:
        ccmINFO=0
        LogLevel=20
        msg1= "SetAllOnOff="+arg
        SetDevicesOnOff(arg)               #BUG, should be per controller, if I insert a canister it will clobber everything
        msg=msg1+' Devices'
        CCM_Alert(ccmINFO,LogLevel,msg)
        SetVolumesOnOff(arg,'c0')               #BUG, should be per controller, if I insert a canister it will clobber everything
        SetVolumesOnOff(arg,'c1')               #BUG, should be per controller, if I insert a canister it will clobber everything
        SetVolumesOnOff(arg,'c2')               #BUG, should be per controller, if I insert a canister it will clobber everything
        msg=msg1+' Volumes'
        CCM_Alert(ccmINFO,LogLevel,msg1)
    except Exception as err:
        sprint("setAllOnOff except ",err)
        return (-1)

def RefreshPools(flag):
#   BUG, we need to use  sudo vgchange --refresh after a Canister is inserted
    try:
        vgErr=0
        arg1="--refresh"
        #sudo vgchange --refresh
        try:
            sprint ("vgchange", arg1)
            process1 = subprocess.check_output(["vgchange", arg1])
            sprint (process1,0)
        except Exception as err:
            sprint("vgchange-1 except ",err)
            vgErr=-1
        return vgErr

    except Exception as err:
        sprint("vgchange-2 except ",err)
        return (-1)
     
def RestartMegaRAID(cx,arg,q):

    #res=QuiescePools(True)
    ccmINFO=0
    LogLevel=20
    msg1= "Restart MegaRAID called=" + cx
    CCM_Alert(ccmINFO,LogLevel,msg1)
    #choice=raw_input("Step 0a: Restart MegaRAID called <cr> ")
    if cx=='/c0':
        location='c0'
    elif cx=='/c1':
        location='c1'  
    elif cx=='/c2':
        location='c2'     
    sprint('Location=',location)
    res=GetBaseBoard()
    if res[0]==0:
        if res[1]=="X570D4I-2T":
            MID="R6000"
            WDen=True
        elif res[1]=="H12SSL-I":
            MID="R6000"
            WDen=True
        else:
            if res[1]=="X13SAV-LVDS" :
                MID="R6000"
                WDen=False
            else: 
                MID="NA"
                WDen=False

    if MID=="R6000":
        wd("reset",0,WDen)
        
    #choice=raw_input("Step 0b: Restart MegaRAID <cr> ")
    
    try:
        if MID=="R6000":
            res=ImportMegaRAID(cx)
            sprint ("res ImportMegaRAID ",str(res))
            #choice=raw_input("Step 0c: Restart MegaRAID <cr> ")
        else:
            res=0

        if res!=0:
            return res

        if res==0:
            if MID=="R6000":
                msg1= "Check MegaRAID_Pools"
                CCM_Alert(ccmINFO,LogLevel,msg1)
                CheckMegaRAID_Pools(cx)       #Check if pools exist and create the DB if they are not
            else:
                msg1= "Check LVM_Pools"
                CCM_Alert(ccmINFO,LogLevel,msg1)
                CheckLVM_Pools(location)                #Check if pools exist and create the DB if they are not
                
            if arg=="verbose":
                choice=input("Step 2: DB is updated with the Pools found on Canister <cr> ")
            #FakeVolDeleteAll("Remote")       #Remove all the remote Volumes where a multi_device ID does not exist.
            #FakeVolDeleteAll("Foreign")      #Remove all the remote Volumes where a multi_device ID does not exist.
            #FakeDeviceDeleteAll()
            #res=CheckForeignDB()             #Check does /pool/system/quantumDB.db exist 
            res=-1
            if arg=="verbose":
                choice=input("<f> Foreign or <l> Local DB")     ###################WOTEST##############
                if choice!='f':
                    res=-1
            if res ==0: #/mnt/system/quantumDB.db exists
                msg1= "Create Foreign Volumes"
                sprint (msg1,str(0))
                CCM_Alert(ccmINFO,LogLevel,msg1)
                res=ForeignVolumeCreate()                   #if Foreign then Create Foreign Volumes in the Local /mnt/data/DB              
                if res!=0:
                    msg="ForeignVolume import Failure"
                    ccmCRITICAL=3
                    CCM_Alert(ccmCRITICAL,LogLevel,msg)
                else:
                    msg="ForeignVolume import success"
                    CCM_Alert(ccmINFO,LogLevel,msg)
            else:
                msg="Canister is Native"
                
            sprint (msg,str(res))
            if arg=="verbose":
                choice=input("Step 3: Canister DB has been checked <cr> ")
            res=GetPools(location)                          #Read the pools configured in the DB
            if res[0]==0:
                pools=res[1]
                sprint("Pools detected",pools)
                if len(pools)!=0:
                    for pool in pools:
                        vols=OrphanVolumeCreate(pool,location)  #Create Volumes on the LVM pool not in the DB & Create default NFS export 
                        sprint ("Updated OrphanVolumes()",vols)
                else:
                    sprint ("No Pools Detected",0)
            else:
                sprint ("Error reading Pools Detected",0)
            if arg=="verbose":
                choice=input("Step 4: DB is updated with the Orphan Volumes found on Canister <cr> ")
            msg1= "Restart Services"
            CCM_Alert(ccmINFO,LogLevel,msg1)
            if q==False:
                sprint ("Setting All Volumes ON",0)
                RestartServices()               #Restart the protocole services NFS, CIFS, iSCSI
                time.sleep(3)
                CheckMounts()
            AtInsertTest=False
            if AtInsertTest==True:
                sprint ("DB_UpdateAtInsertSchedule",)
                DB_UpdateAtInsertSchedule()
                if arg=="verbose":
                    choice=input("Step 5: At Insert checked <cr> ")
            return (0)
        else:
            msg1= "Restart MegaRAID failed"
            CCM_Alert(ccmINFO,LogLevel,msg1)  
            return (-1)
            DeleteDisk('mrx',cx)   

    except Exception as err:
        sprint("ReStartMegaRAID except ",err)
        return (-1)

def CheckMegaRAID(controller):
    #/c0, /c1 etc
    storcli="/opt/MegaRAID/storcli/storcli64"
    try:
        cmd="show"
        argLast='J'
        #sudo /opt/MegaRAID/storcli/storcli64 /c0 show J
        process1 = subprocess.check_output([storcli, controller,cmd, argLast])
        y = json.loads(process1)
        x=y['Controllers'][0]['Command Status']
        sprint (x['Status'],0)
        if str(x['Status'])=="Success":
            return (0,y)
        else:
            return (-1,"controller not found")
    except Exception as err:
        sprint("CheckMegaRAID except ",err)
        return (-1,"controller not found")
      
def CheckMegaRAIDDrives(cx):
    storcli="/opt/MegaRAID/storcli/storcli64"
    slotList=[]
    try:
        cmd="show"
        arg1=cx+'/e252/sall'
        argLast='J'
        #sudo /opt/MegaRAID/storcli/storcli64 /c0/e252/sall show J
        #print storcli,cmd,cx,arg1,argLast
        process1 = subprocess.check_output([storcli, arg1,cmd, argLast])
        y = json.loads(process1)
        x=y['Controllers'][0]['Command Status']
        sprint (x['Status'],0)
        if str(x['Status'])=="Success":
            i=0
            j=0
            x=y['Controllers'][0]['Response Data']['Drive Information']
            NbSlots=len(x)
            while (i<NbSlots):
                state=str(x[i]['State'])
                #print ("state",state,i)
                if ((state=='Onln') or (state=="UGood") or (state=="UBad")):
                    slotList.append(str(x[j]['EID:Slt']))
                    j=j+1
                i=i+1
    except Exception as err:
        sprint("CheckMegaRAIDDrives except ",err)
        return -1,slotList  
        
    return 0,slotList

def SetLicenceState(state):
    global LicenceState
    LicenceState=state

def GetLicenceState():
    global LicenceState
    val=LicenceState
    return (val)


def CheckLicence():
       
    CL=False
    res=GetBaseBoard()
    print ("BaseBoard=",res[1])
    if res[0]==0:
        if res[1]=="X570D4I-2T":
            CL=True
        elif res[1]=="X13SAV-LVDS":
            CL=True
        elif res[1]=="H12SSL-I":
            CL=False                    #BUG change this please
        else:
            CL=False
    CL=False
    if CL==False:
        SetLicenceState(0)
        return (0)
        
    LicenceFileName="/mnt/data/licence/License.cert"
    if os.path.isfile(LicenceFileName):
        sprint ("LicenceFileName",LicenceFileName)
        stat, mssg = license_unpack.unpack(LicenceFileName)
        if stat=="success":
            sprint (LicenceFileName,' is OK')
            SetLicenceState(0)
        else:
            sprint (LicenceFileName,' is NOT OK')
            SetLicenceState(-1)
    else:
        SetLicenceState(-1)

    if (GetLicenceState()==-1):
        LicenceFileName="/var/www/uploaded/License.cert"
        if os.path.isfile(LicenceFileName):
            sprint ("LicenceFileName",LicenceFileName)
            stat, mssg = license_unpack.unpack(LicenceFileName)
            if stat=="success":
                sprint (LicenceFileName," is OK")
                SetLicenceState(0)
                arg1="-p"
                dir="/mnt/data/licence"
                process = subprocess.check_output(["mkdir",arg1,dir])
                src=LicenceFileName
                dst="/mnt/data/licence/License.cert"
                process = subprocess.check_output(["cp",src,dst])
            else:
                sprint (LicenceFileName, " is NOT OK")
                SetLicenceState(-1)
    else:
        SetLicenceState(0)
        return (0)
        
        
def EpochToTime(epoch):
    mytime=time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(epoch))
    print(mytime)


def CreateGroup(Group):
    process1 = subprocess.check_output(["groupadd", Group])

def CheckGroup(Group):
    try:
        process1 = subprocess.check_output(["getent", "group",Group]).decode("UTF-8")
        my_index= process1.find(Group,0,len(process1))
        if (my_index ==-1):
            return -1
        else:
            return 0
    except subprocess.CalledProcessError as e:
        sprint ("CheckGroup error= ", str(e.returncode))
        CCM_Alert(DEBUG,CodeDebug,e)
        return -1
            
def AddUserToGroup(Group,UserList): 
    sprint ("AddUserToGroup -IN",Group)
    for user in UserList:
        try:  
            processx = subprocess.check_output(["id",user[0]])
            sprint (processx,0)
        except subprocess.CalledProcessError as e:
            sprint ("error= ", str(e.returncode))
            #my_index= e.find("no",0,len(e))
            #print "step2 " + str(my_index)
        #if (my_index!=-1):
            #Create user,
            #useradd -M 
            msg= "Creating User = "+user[0] + " with password =" +user[1]
            sprint(msg,0)
            process1 = subprocess.check_output(["useradd" ,"-M" ,"-N", user[0], "-g", Group, "-p", user[1]])
            sprint (process1,0)
            CCM_Alert(DEBUG,CodeDebug,e)
    sprint("AddUserToGroup -OUT",Group)        

def AddSambaPW(UserList):
    try:
        for user in UserList:
            username=user[0]
            passwd=user[1]
            check = is_EncodedString_base64(passwd)
            if check:
                decodePwd=pwd_decoding(passwd)
            else:
                decodePwd=passwd
                
            sprint (username,decodePwd)
            child = pexpect.spawn('/usr/bin/smbpasswd -a '+ username)
            child.expect('New SMB password:')
            child.sendline (decodePwd)
            child.expect ('Retype new SMB password:')
            child.sendline (decodePwd)
            time.sleep(.5)
        return 0
    except subprocess.CalledProcessError as e:
        sprint ("AddSambaPW except =",UserList)
        return -1

def VolInfo(VolName,ProtocolID):

    return 0

def getCanisterByPool(Pool):
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    location='cx'
    try:
        query=c.execute("select location from multi_device where system_name='"+str(Pool)+"'")
        if str(query)!='None':
            location = c.fetchone()[0]
            sprint ("getCanisterByPool location=" ,str(location))
        #location='c0'
        conn.commit()
        c.close()
        conn.close()
        return location

    except Exception as err:
        sprint("getCanisterByPool",err)
        conn.commit()
        c.close()
        conn.close()
        return location
        
def VolumeStartCIFS(zfsPool, VolName, ProtID,VolSnap):
    sprint ("Starting CIFS volume",0)
    pool=zfsPool
    protocol=ProtID
    #VolList=DB_GetVolList(pool,protocol)
    #print VolList
    Group="t1"      ###################WOTEST##############
    sprint (Group,VolName)
    if VolSnap=="null":
        ShareName=VolName
        if StorageBackend=="zfs":
            SharePath="/mnt/"+VolName
            device="/"+pool+"/"+VolName
            
        if StorageBackend=="LVM":
            SharePath=CIFSmnt+VolName
            device="/dev/"+pool+"/"+VolName
    else:
        if StorageBackend=="zfs":
            ShareName=VolSnap
            SharePath="/mnt/"+VolName+"/.zfs/snapshot/"+VolSnap
        if StorageBackend=="LVM":
            ShareName=VolName
            SharePath=LVMmnt+VolName

    sprint ("ShareName=",ShareName)
    sprint ("SharePath=",SharePath)
    if (CheckGroup(Group)!=0):
        CreateGroup(Group)
    UserList=DB_GetUsersByVol(VolName)
    if UserList==-1:
        return -1
    sprint ("VolumeStartCIFS UserList",UserList)
    AddUserToGroup(Group,UserList)
    sprint ("VolumeStartCIFS step 1",0)
    AddSambaPW(UserList)
    sprint ("VolumeStartCIFS step 2",0)
    ShareOwner="nobody:"+Group
    sprint (ShareOwner,0)

    try:
            process1 = subprocess.check_output(["mountpoint",SharePath]) #Check if mountpoint exists
            #/mnt/lv0 is a mountpoint
            mp=True
            sprint (process1,0)
    except Exception as err:
            sprint("mountpoint except ",err)
            mp=False
            #need to create mountpoint
    try:
        if mp==False:
            arg1="-p"
            process1= subprocess.check_output(["mkdir",arg1,SharePath])
            process1= subprocess.check_output(["mount",device,SharePath])
            mp=True
    except Exception as err:
            sprint("mount except 1",err)
    try:
        #chown nobody:t1 /mnt/lv2           
        process1 = subprocess.check_output(["chown",ShareOwner,SharePath])
        sprint (process1,0)
        chmodPermissions="777"
        chmodFlag1="-f"
        #sudo chmod -f 770 /mnt/lv2
        process1 = subprocess.check_output(["chmod",chmodFlag1,chmodPermissions,SharePath])
        sprint (process1,0)
        #http://manpages.ubuntu.com/manpages/xenial/man8/net.8.html
        #sudo net usershare add cifs1 /mnt/myminio/cifs1 "Samba Test" Everyone:F guest_ok=y
        #sudo net usershare add cifs1 /mnt/cifs1 "Samba Test" Everyone:F guest_ok=y
        process1 = subprocess.check_output(["net", "usershare", "add", ShareName, SharePath, "Samba Test", "Everyone:F" ,"guest_ok=y"])
        sprint (process1,0)
    except Exception as err:
        sprint("usershare except 1",err)
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    if VolSnap=="null":
        query=c.execute("select id from Volume where name='"+str(VolName)+"'")
        volumeId = c.fetchone()[0]
        sprint ("Volume ID=",str(volumeId))
        #Need to get the Volume ID
        volumeState=gVolOn
        query=c.execute("update Volume set state=?,edit_date=datetime() where id=?",[volumeState,volumeId])
    else:
        query=c.execute("select id from volume_snapshot where name='"+str(VolSnap)+"'")
        volumeId = c.fetchone()[0]
        sprint ("Volume ID=" , str(volumeId))
        #Need to get the Volume ID
        volumeState=gVolOn
        query=c.execute("update volume_snapshot set state=?,edit_date=datetime() where id=?",[volumeState,volumeId])
    conn.commit()
    c.close()
    conn.close()
    return 0
    
def VolumeStartNFS (zfsPool, VolName, ProtID,VolSnap):
    msg =VolName+":"+StorageBackend
    sprint ("Starting NFS volume",msg)
    pool=zfsPool
    protocol=ProtID
    can='canx/'
    #VolList=DB_GetVolList(pool,protocol)
    #print VolList
    location=getCanisterByPool(zfsPool)
    if location=='c0':
        can='can0/'
    elif location=='c1':
        can='can1/'
    elif location=='c2':
        can='can2/'
    Group="nobody"
    sprint (Group,VolName+'@'+can)
    if VolSnap=="null":
        ShareName=VolName
        if StorageBackend=="zfs":
            SharePath="/mnt/"+VolName
            device="/"+pool+"/"+VolName
        if StorageBackend=="LVM":
            SharePath=LVMmnt+can+VolName
    else:
        if StorageBackend=="zfs":
            ShareName=VolSnap
            SharePath="/mnt/"+VolName+"/.zfs/snapshot/"+VolSnap
        elif StorageBackend=="LVM":
            ShareName=VolName
            SharePath=LVMmnt+can+VolName
    try:
            process1 = subprocess.check_output(["mountpoint",SharePath]) #Check if mountpoint exists
            #/mnt/lv0 is a mountpoint
            sprint("path mounted",SharePath)
            mp=True
            sprint (process1,0)
    except Exception as err:
            sprint("mountpoint StartNFS except ",err)
            mp=False
            #need to create mountpoint
    try:
        if mp==False:
            arg1="-p"
            if VolSnap=="null":     #make dir for volumes not snapshots
                process1= subprocess.check_output(["mkdir",arg1,SharePath])
            if StorageBackend=="zfs":
                device=pool+'/'+VolName
                process1= subprocess.check_output(["zfs","mount",device])
            else:
                device="/dev/"+pool+"/"+VolName
                process1= subprocess.check_output(["mount",device,SharePath])
            msg=device+" "+SharePath
            mp=True
            sprint("mount NFS device ",msg)
    except Exception as err:
            if VolSnap!="null":
                mp=True
            sprint("mount except 1",err)

    if mp==True:
        try:
            host=GetHostbyVolume(VolName)
            arg1="nobody:nogroup"
            if VolSnap=="null":
                process1 = subprocess.check_output(["chown",arg1,SharePath]) #Change ownership to nobody:nogroup so everyone can write
                sprint (process1,0)
                #sudo chmod 777 /mnt/lv0
                arg1="777"
                process1 = subprocess.check_output(["chmod",arg1,SharePath]) #change permissions
                sprint (process1,0)
                #exportfs -o insecure_locks 192.168.31.15:/mnt/lv0
                #/mnt/lv1 192.168.32.11(rw,sync,no_subtree_check)
                #sudo mount -t nfs 192.168.31.6:/mnt/myminio/nfs /mnt/backup
                #cat /var/lib/nfs/etab
                #https://support.microfocus.com/kb/doc.php?id=7021756
                
            arg1="-o"
            if VolSnap == 'null':
                arg2= "rw,async,no_subtree_check"
            else:
                arg2= "ro,async,no_subtree_check"
                
            if StorageBackend=="zfs":
                arg3=host+':'+SharePath
            else:
                arg3=host+':'+NFSmnt+can+VolName
            sprint ("exportfs",arg3)
            #sudo exportfs -o rw,async,no_subtree_check 192.168.32.15:/mnt/nfs2
            process1 = subprocess.check_output(["exportfs",arg1,arg2,arg3]) #change permissions
            sprint (process1,0)
            sprint ("Volume, mounted and exported",VolName)
        except Exception as err:
            sprint("mount except 2 ",err)
    else:
            sprint ("Volume not Mounted",VolName)
            return -1
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    try:
        query=c.execute("select id from multi_device where system_name ='"+str(pool)+"'")
        resp=c.fetchone()
        sprint ("VolumeStartNFS step 1 Resp",resp)
        if str(resp) != str("None"): 
            multi_device_id = resp[0]
            sprint ("VolumeStartNFS Pool ID",multi_device_id)
        else:
            sprint ("VolumeStartNFS NO Pool ID",0)
            conn.commit()
            c.close()
            conn.close()
            return -1
    except Exception as err:
            sprint("VolumeStartNFS except step1 ",err)
            conn.commit()
            c.close()
            conn.close()
            return -1
            
    try:
        if VolSnap=="null":
            query=c.execute("select id from Volume  where name='"+str(VolName)+"' and multi_device_id="+str( multi_device_id))  #qualify with Pool
            volumeId = c.fetchone()[0]
            sprint ("Volume ID=" ,str(volumeId))
            volumeState=gVolOn
            query=c.execute("update Volume set state=?,edit_date=datetime() where id=?",[volumeState,volumeId])
        else:
            query=c.execute("select id from volume_snapshot where name='"+str(VolSnap)+"'")
            volumeId = c.fetchone()[0]
            sprint ("Volume ID=",str(volumeId))
            #Need to get the Volume ID
            volumeState=gVolOn
            query=c.execute("update volume_snapshot set state=?,edit_date=datetime() where id=?",[volumeState,volumeId])
    except Exception as err:
            sprint("VolumeStartNFS except step2 ",err)
            conn.commit()
            c.close()
            conn.close()
            return -1
    conn.commit()
    c.close()
    conn.close()
    return 0

def VolumeStartS3 (zfsPool, VolName, ProtID, VolSnap):
    msg =VolName+":"+StorageBackend
    sprint ("Starting S3 volume",msg)
    pool=zfsPool
    protocol=ProtID
    can='canx/'
    location=getCanisterByPool(zfsPool)
    if location=='c0':
        can='can0/'
    elif location=='c1':
        can='can1/'
    elif location=='c2':
        can='can2/'
        
    Group="minio"
    sprint (Group,VolName+'@'+can)
    if VolSnap=="null":
        ShareName=VolName
        if StorageBackend=="zfs":
            SharePath="/mnt/"+VolName
            device="/"+pool+"/"+VolName
        if StorageBackend=="LVM":
            SharePath=LVMmnt+can+VolName
    else:
        if StorageBackend=="zfs":
            ShareName=VolSnap
            SharePath="/mnt/"+VolName+"/.zfs/snapshot/"+VolSnap
        elif StorageBackend=="LVM":
            ShareName=VolName
            SharePath=LVMmnt+can+VolName
    try:
            process1 = subprocess.check_output(["mountpoint",SharePath]) #Check if mountpoint exists
            #/mnt/lv0 is a mountpoint
            sprint("path mounted",SharePath)
            mp=True
            sprint (process1,0)
    except Exception as err:
            sprint("mountpoint StartS3 except ",err)
            mp=False
            #need to create mountpoint
    try:
        if mp==False:
            arg1="-p"
            if VolSnap=="null":     #make dir for volumes not snapshots
                process1= subprocess.check_output(["mkdir",arg1,SharePath])
            if StorageBackend=="zfs":
                device=pool+'/'+VolName
                process1= subprocess.check_output(["zfs","mount",device])
            else:
                device="/dev/"+pool+"/"+VolName
                process1= subprocess.check_output(["mount",device,SharePath])
            msg=device+" "+SharePath
            mp=True
            sprint("mount S3 device ",msg)
    except Exception as err:
            if VolSnap!="null":
                mp=True
            sprint("mount except 1",err)

    if mp==True:
        try:
            arg1="nobody:nogroup"
            if VolSnap=="null":
                sprint('SharePath',SharePath)
                sprint('VolName',VolName)
                process1 = subprocess.check_output(["chown",arg1,SharePath]) #Change ownership to nobody:nogroup so everyone can write
                sprint (process1,0)
                #sudo chmod 777 /mnt/lv0
                arg1="777"
                process1 = subprocess.check_output(["chmod",arg1,SharePath]) #change permissions
                sprint (process1,0)
                #restart Minio
                process1 = subprocess.check_output(["systemctl",'restart', 'minio.service'])
                sprint ("S3 Volume, mounted and exported",VolName)
        except Exception as err:
            sprint("mount except 2 ",err)
    else:
            sprint ("S3 Volume not Mounted",VolName)
            return -1
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    try:
        query=c.execute("select id from multi_device where system_name ='"+str(pool)+"'")
        resp=c.fetchone()
        sprint ("VolumeStartNFS step 1 Resp",resp)
        if str(resp) != str("None"): 
            multi_device_id = resp[0]
            sprint ("S3 VolumeStart Pool ID",multi_device_id)
        else:
            sprint ("S3 VolumeStart NO Pool ID",0)
            conn.commit()
            c.close()
            conn.close()
            return -1
    except Exception as err:
            sprint("S3 VolumeStart except step1 ",err)
            conn.commit()
            c.close()
            conn.close()
            return -1
            
    try:
        if VolSnap=="null":
            query=c.execute("select id from Volume  where name='"+str(VolName)+"' and multi_device_id="+str( multi_device_id))  #qualify with Pool
            volumeId = c.fetchone()[0]
            sprint ("Volume ID=" ,str(volumeId))
            volumeState=gVolOn
            query=c.execute("update Volume set state=?,edit_date=datetime() where id=?",[volumeState,volumeId])
        else:
            query=c.execute("select id from volume_snapshot where name='"+str(VolSnap)+"'")
            volumeId = c.fetchone()[0]
            sprint ("Volume ID=",str(volumeId))
            #Need to get the Volume ID
            volumeState=gVolOn
            query=c.execute("update volume_snapshot set state=?,edit_date=datetime() where id=?",[volumeState,volumeId])
    except Exception as err:
            sprint("S3 VolumeStart except step2 ",err)
            sprint("S3 VolumeStart except step2 ",err)
            conn.commit()
            c.close()
            conn.close()
            return -1
    conn.commit()
    c.close()
    conn.close()
    return 0


def VolumeStartFTP(zfsPool, VolName, ProtID):
#https://pyftpdlib.readthedocs.io/en/latest/tutorial.html#a-base-ftp-server
#sudo useradd -m -d /p2/ftp/user14 -s /bin/false -c "FTP" -U user14 for ProFTPd
# and set the PW
#user14:x:1018:1018:FTP:/p2/ftp/user14:/bin/false
#make sure the ,profile etc are R only
#https://www.tecmint.com/add-users-in-linux/
#https://www.tecmint.com/install-proftpd-in-ubuntu-and-debian/
    sprint ("Starting FTP volume",0)
    pool=zfsPool
    protocol=ProtID
    #VolList=DB_GetVolList(pool,protocol)
    #print VolList
    Group="ftp"
    sprint (Group,VolName)
    if StorageBackend=="zfs":
        SharePath="/"+pool+"/"+VolName
    if StorageBackend=="LVM":
        SharePath=LVMmnt+VolName
        sprint ("ShareName",ShareName)
        sprint ("SharePath",SharePath)
        try:
                process1 = subprocess.check_output(["mountpoint",SharePath]) #Check if mountpoint exists
                #/mnt/lv0 is a mountpoint
                mp=True
                sprint (process1,0)
        except Exception as err:
                sprint("mountpoint except ",err)
                mp=False
                #need to create mountpoint
        try:
            if mp==False:
                arg1="-p"
                process1= subprocess.check_output(["mkdir",arg1,SharePath])
                device="/dev/"+pool+"/"+VolName
                process1= subprocess.check_output(["mount",device,SharePath])
                mp=True
        except Exception as err:
                sprint("mount except 1",err)

    if (CheckGroup(Group)!=0):
        CreateGroup(Group)
    UserList=DB_GetUsersByVol(VolName)
    sprint (UserList,0)
    AddUserToGroup(Group,UserList)
    AddFtpPW(UserList)
    ShareOwner="nobody:"+Group
    sprint (ShareOwner,0)
    process1 = subprocess.check_output(["chown",ShareOwner,SharePath])
    sprint (process1,0)
    chmodPermissions="770"
    chmodFlag1="-f"
    process1 = subprocess.check_output(["chmod",chmodFlag1,chmodPermissions,SharePath])
    sprint (process1,0)
    #http://manpages.ubuntu.com/manpages/xenial/man8/net.8.html
    process1 = subprocess.check_output(["net", "usershare", "add", ShareName, SharePath, "Samba Test", "Everyone:F" ,"guest_ok=y"])
    sprint (process1,0)
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    query=c.execute("select id from Volume where name='"+str(VolName)+"'")
    volumeId = c.fetchone()[0]
    sprint ("Volume ID=",str(volumeId))
    #Need to get the Volume ID
    volumeState=6
    query=c.execute("update Volume set state=?,edit_date=datetime() where id=?",[volumeState,volumeId])
    conn.commit()
    c.close()
    conn.close()
    return 0   


def GetHostbyVolume(volName):
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    
    iqn="null"
    query=c.execute("select id from volume where name='"+ str(volName)+"'")
    resp=c.fetchone()
    if resp !="None":
        VolId = resp[0]
        query=c.execute("select host_id from export where vol_id='"+ str(VolId)+"'")
        resp=c.fetchone()
        if resp !="None":
            HostId = resp[0]
            query=c.execute("select iqn from host where id='"+ str(HostId)+"'")
            if resp !="None":
                resp=c.fetchone()
                iqn = resp[0]
    sprint ("GetHostbyVolume",volName+iqn)
    conn.commit()
    c.close()
    conn.close()
    return iqn
    
def VolumeStopS3 (zfsPool, VolName, ProtID,VolSnap):
    if StorageBackend=='zfs':
        can=''
    
    else:
        can='canx'
        location=getCanisterByPool(zfsPool)
        if location=='c0':
            can='can0/'
        elif location=='c1':
            can='can1/'
        elif location=='c2':
            can='can2/'
            

    msg=str(str(zfsPool)+ str(VolName)+ str(ProtID)) #+str(VolSnap)+str(can))
    sprint ("Stop S3",msg)
    arg1="-u"
    try:
        process1 = subprocess.check_output(["systemctl",'stop','minio.service'])
    except Exception as err:
        sprint ("S3 STOP except err",err)

    try:
        if StorageBackend=='zfs':
            arg1=zfsPool+'/'+VolName
            if VolSnap=='null':
                process1 = subprocess.check_output(["zfs","umount",arg1])
        else:
            arg1=NFSmnt+can+VolName
            process1 = subprocess.check_output(["umount",'-f','-l',arg1])
        sprint (process1,0)
        
        process1 = subprocess.check_output(["systemctl",'stop','minio.service'])
        sprint (process1,0)

        
    except Exception as err:
        #ccm_logging(log_elt,40,err)
        sprint ("Exception Message in VolumeStopS3 ",str(err))

    try:
        if VolSnap=='null':    
            ret= DB_UpdateVolumeState(VolName,gVolOff)
        else:
            ret=DB_UpdateVolumeSnapState(VolSnap,gVolOff)
        return ret
        
    except Exception as err:
        sprint ("Exception Message in VolumeStopS3 ",str(err))
        return  wErrCommandFailed
        
def VolumeStopNFS (zfsPool, VolName, ProtID,VolSnap):
    if StorageBackend=='zfs':
        can=''
    
    else:
        can='canx'
        location=getCanisterByPool(zfsPool)
        if location=='c0':
            can='can0/'
        elif location=='c1':
            can='can1/'
        elif location=='c2':
            can='can2/'
            

    msg=str(str(zfsPool)+ str(VolName)+ str(ProtID)+str(VolSnap)+str(can))
    sprint ("Stop NFS",msg)
    arg1="-u"
    host=GetHostbyVolume(VolName)
    if VolSnap=='null':
        arg3=host+':'+NFSmnt+can+VolName
    else:
        #192.168.30.55:/mnt/wo1/.zfs/snapshot/wo1-ss2 
        arg3=host+':'+NFSmnt+can+VolName+'/.zfs/snapshot/'+VolSnap
    sprint ("VolumStopNFS Host:",arg3)
    try:
        process1 = subprocess.check_output(["exportfs",arg1,arg3])
    except Exception as err:
        sprint ("exportfs STOP except err",err)

    try:
        if StorageBackend=='zfs':
            arg1=zfsPool+'/'+VolName
            if VolSnap=='null':
                process1 = subprocess.check_output(["zfs","umount",arg1])
        else:
            arg1=NFSmnt+can+VolName
            process1 = subprocess.check_output(["umount",'-f','-l',arg1])
        sprint (process1,0)

    except Exception as err:
        #ccm_logging(log_elt,40,err)
        sprint ("Exception Message in VolumeStopNFS ",str(err))

    try:
        if VolSnap=='null':    
            ret= DB_UpdateVolumeState(VolName,gVolOff)
        else:
            ret=DB_UpdateVolumeSnapState(VolSnap,gVolOff)
        return ret
        
    except Exception as err:
        sprint ("Exception Message in VolumeStopNFS ",str(err))
        return  wErrCommandFailed
        
def VolumeStopCIFS(zfsPool, VolName, ProtID,VolSnap):
    sprint ("Stopping CIFS volume",zfsPool)
    pool=zfsPool
    protocol=ProtID
    if VolSnap=="null":
        sprint (VolName,zfsPool)
        ShareName=VolName
        #SharePath="/"+pool+"/"+VolName+"/"
    else:
        ShareName=VolSnap
        #SharePath="/"+pool+"/"+VolName+"/"

    process1 = subprocess.check_output(["smbstatus"]).decode("UTF-8")
    my_len=int(len(process1))
    sprint ("my_len=" +str(my_len),0)
    my_cmd="Locked files:"
    sprint ("Checking" +(my_cmd),0)
    my_index=process1.find(my_cmd,0,my_len)
    sprint (process1,0)
    sprint (my_index,0)
    if (my_index !=-1):
        sprint ("SMB Status - check1",0)
        #return wErrVolumeInUse
    my_cmd=ShareName
    sprint ("Checking" ,(my_cmd))
    my_index=process1.find(my_cmd,my_index,my_len)
    my_index =-1    #Hack
    if (my_index !=-1):
        sprint ("Volume in use - check2",0)
        return wErrVolumeInUse
   
    #step 2 delete the share ex.  sudo net usershare delete sharename
    try:
        sprint ("deleting share",0)
        #sudo net usershare delete wo1
        process1 = subprocess.check_output(["net", "usershare", "delete", ShareName])
        sprint (process1,0)

    except Exception as err:

        #ccm_logging(log_elt,40,err)
        sprint ("Exception Message in VolumeStopCIFS ",str(err))
        dargs=loggerArgs("volume"," ",10,"VolumeStopCIFS")
        ccmLogger(3,str(err),dargs)
        #return wErrVolumeInUse

    process1 = subprocess.check_output(["service", "smbd", "restart"])
    #sudo service smbd restart
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    if VolSnap=="null":
        query=c.execute("select id from Volume where name='"+str(VolName)+"'")
        volumeId = c.fetchone()[0]
        sprint ("Volume ID=", str(volumeId))
        #Need to get the Volume ID
        volumeState=gVolOff
        query=c.execute("update Volume set state=?,edit_date=datetime() where id=?",[volumeState,volumeId])
    else:
        query=c.execute("select id from volume_snapshot where name='"+str(VolSnap)+"'")
        volumeId = c.fetchone()[0]
        sprint ("Volume ID=" , str(volumeId))
        #Need to get the Volume ID
        volumeState=gVolOff
        query=c.execute("update volume_snapshot set state=?,edit_date=datetime() where id=?",[volumeState,volumeId])
    conn.commit()
    c.close()
    conn.close()
    if StorageBackend=="zfs":
        try:
            zfsShare=zfsPool+'/'+VolName
            sprint ("unmount zfs share",zfsShare)
            process1 = subprocess.check_output(["zfs", "unmount", zfsShare])
            sprint (process1,0)
        except Exception as err:
            sprint ("unmount zfs share except",zfsShare)
    return 0
        
def zvol_GetDevice(pool,zvol):
# ls -l /dev/zvol/tank/disk1
#lrwxrwxrwx 1 root root 11 Dec 20 22:10 /dev/zvol/tank/disk1 -> ../../zd144

    try:
        ls_arg1="-l"
        ls_arg2="/dev/zvol/"+pool+"/"+zvol
        process1 = subprocess.check_output(["ls", ls_arg1, ls_arg2]).decode('utf-8')
        my_len= len(process1)
        my_index= process1.find("zd",0,my_len)
        device=str(process1[my_index : (my_len-1)])
        sprint ("Zvol Device",device)
        return 0,device
    except Exception as err:
        sprint ("Zvol GetDevice except",err)
        return -1,0
        

def vol_DeleteLun(pool,VolName,prot):

    if gTarget=="iet":
        ietZvol_DeleteLun(pool,VolName,prot)
    elif gTarget=="tgt":
        tgtVol_DeleteLun(pool,VolName,prot)
    
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    query=c.execute("select id from Volume where name='"+str(VolName)+"'")
    volumeId = c.fetchone()[0]
    sprint ("Volume ID=" , str(volumeId))
    #Need to get the Volume ID
    volumeState=gVolOff
    query=c.execute("update Volume set state=?,edit_date=datetime() where id=?",[volumeState,volumeId])
    conn.commit()
    c.close()
    conn.close()
    return 0

#iscsiadm -m discovery -o new -o old -t st -I iser -p <ip:port> -l
def iSCSIadm_Discover(host,iface):
    null="null"
    try:
        iSCSI_arg1="-m"
        iSCSI_arg2="discovery"
        iSCSI_arg3="-t"
        iSCSI_arg4="st"
        iSCSI_arg5="-I"
        iSCSI_arg6=iface 
        iSCSI_arg7="-p"
        iSCSI_arg8=host
        if iface!="null":
            process1 = subprocess.check_output(["iscsiadm",iSCSI_arg1,iSCSI_arg2,iSCSI_arg3,iSCSI_arg4,iSCSI_arg5,iSCSI_arg6,iSCSI_arg7,iSCSI_arg8 ])
        else:
            process1 = subprocess.check_output(["iscsiadm",iSCSI_arg1,iSCSI_arg2,iSCSI_arg3,iSCSI_arg4,iSCSI_arg7,iSCSI_arg8 ])
        sprint (process1,0)
        return process1
    except Exception as err:
        sprint ("iSCSIadm_Discover except ",err)
        return null


#sudo iscsiadm -m discovery -t st -p 192.168.32.15 
def iSCSIadm_Login(host,iDisk):
#sudo iscsiadm -m node --targetname iqn.2018-04.com.quantum:vdisk1lv0 -p 192.168.32.15 -l
    null="null"
    try:
        iSCSI_arg1="-m"
        iSCSI_arg2="node"
        iSCSI_arg3="--targetname"
        iSCSI_arg4=iDisk
        iSCSI_arg5="-p"
        iSCSI_arg6=host   
        iSCSI_arg7="-l"
        process1 = subprocess.check_output(["iscsiadm",iSCSI_arg1,iSCSI_arg2,iSCSI_arg3,iSCSI_arg4,iSCSI_arg5,iSCSI_arg6,iSCSI_arg7])
        sprint (process1,0)
        return process1
    except Exception as err:
        sprint ("iSCSIadm_Login except ",err)
        return null       


def iSCSIadm_Logout(host,iDisk):
#sudo iscsiadm -m node --targetname iqn.2018-05.com.hiroom2:disk -p localhost -u
    null="null"
    try:
        iSCSI_arg1="-m"
        iSCSI_arg2="node"
        iSCSI_arg3="--targetname"
        iSCSI_arg4=iDisk
        iSCSI_arg5="-p"
        iSCSI_arg6=host   
        iSCSI_arg7="-u"
        process1 = subprocess.check_output(["iscsiadm",iSCSI_arg1,iSCSI_arg2,iSCSI_arg3,iSCSI_arg4,iSCSI_arg5,iSCSI_arg6,iSCSI_arg7])
        sprint (process1,0)
        return process1
    except Exception as err:
        sprint ("iSCSIadm_Logout except ",err )
        return null 

    



def DB_updateStorManDevice(StorManID,iDisk,size,state):

    #name TEXT,sys_name TEXT,state INT,cr_date DATETIME,edit_date DATETIME,del_date DATETIME,stor_man_id INT,size INT,
    sprint ("DB_updateStorManDevice",0)
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    system_name="iDisk"
    sprint ("query=",iDisk)
    query=c.execute("select id from device where name='{}".format(iDisk)+"'")
    sprint ("execute query",query)
    resp=c.fetchone()
    e_date=datetime.datetime.now()    
    if str(resp) != str("None"):
        DeviceId=resp[0]
        sprint ("Device=",DeviceId)
        sprint ("Update Device=" , str(iDisk))
        sprint ("Update Device Size=",int(size))
        if int(size)!=0:
            query=c.execute("update device set size=?,state=? where id=?",[int(size),state,DeviceId])
        conn.commit()
    else:
        sprint ("Create Device=",str(iDisk))
        name=iDisk
        query=c.execute("insert into device(sys_name,name,state,size,stor_man_id,cr_date) values(?,?,?,?,?,datetime())",\
        [system_name,name,state,size,StorManID])
        DeviceId=c.lastrowid
        conn.commit()
    c.close()
    conn.close()
    return 0,DeviceId

def GetPoolID(PoolSystemName):
    sprint ("GetPoolID ",PoolSystemName)
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    try:
        query_lan=c.execute("select id from multi_device where system_name='"+ str(PoolSystemName)+"'")
        PoolID = c.fetchone()[0]
        conn.commit()
        c.close()
        conn.close()
        return PoolID
    except Exception as err:
        sprint ("GetPoolID except ",err)
        c.close() 
        conn.close()        
        return -1

def DB_PoolStateUpdate(pool,PoolState):
    if PoolState=="critical":
        p_state=2
    elif PoolState=="OK":
        p_state=0
    else:
        p_state=1
    msg=str(pool)+':'+str(PoolState)
    sprint ("PoolUpdate",msg)
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    try:
        query=c.execute("update multi_device set state=? where system_name=?",[p_state,pool])
        conn.commit()
        c.close()
        conn.close()
        return

    except Exception as err:
        c.close()
        conn.close()
        sprint ("PoolUpdate except ",err)


def FakePoolUpdate(PoolState,location):
    sprint ("FakePoolUpdate",location)
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    try:
        query_lan=c.execute("select id,name,system_name,state from multi_device where location=?",[location])
        resp=c.fetchall()
        sprint ("resp=",resp)
        if resp!=None:
            for col in resp:
                PoolID=col[0]
                name=col[1]
                system_name=col[2]
                state=col[3]
                if name=="MegaRAID POOL":
                    if PoolState=="critical":
                        p_state=2
                    elif PoolState=="OK":
                        p_state=0
                    else:
                        p_state=1
                    msg=str(system_name)+" to "+str(p_state)
                    sprint ("FakePoolUpdate set ", msg)
                    query=c.execute("update multi_device set state=? where id=?",[p_state,PoolID])
                    conn.commit()
        c.close()
        conn.close()
        return
    except Exception as err:
        c.close()
        conn.close()
        sprint ("FakePoolUpdate except ",err)
        
def getPoolLocation(arg1):

    location='cx'

    if 'c0' in arg1:
        location='c0'
    elif 'c1' in arg1:
        location='c1'
    elif 'c2' in arg1:
        location='c2'
    msg=arg1 +'='+location
    sprint ("getPoolLocation ", msg)
    return location


def FakePoolCreate(PoolName,PoolSystemName,PoolSize,PoolLevel,location):
    msg=str(str(PoolName) + str(PoolSystemName) + str(PoolSize) +str(PoolLevel)+str(location))
    sprint ("FakePoolCreate args=",msg)
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    try:
        query_lan=c.execute("select count(*) from multi_device where system_name='"+ str(PoolSystemName)+"'")
        nameCount = c.fetchone()[0]
        conn.commit()
        if nameCount == 0:
            sprint ("FakePoolCreate Insert DB ",PoolName)
            zfsCompression="false"
            zfsAcceleration=0
            zfsDedup="false"
            PoolAccelerationStorage=0
            query_SP = c.execute(
            "insert into multi_device(name,pool_storage,level,state,cr_date,edit_date,compression,acceleration,deduplication,acceleration_storage,system_name,calculatedraw,location) \
            values(?,?,?,0,datetime(),datetime(),?,?,?,?,?,?,?)",[PoolName, PoolSize, PoolLevel, zfsCompression, zfsAcceleration, zfsDedup,PoolAccelerationStorage,PoolSystemName,PoolSize,location])
            conn.commit()
        else:
            sprint ("FakePoolCreate Update DB PoolSystemName ",PoolSystemName)
            query=c.execute("update multi_device set state=0 where system_name=?",[PoolSystemName])

            conn.commit()
        c.close()
        conn.close()
        return
    except Exception as err:
        c.close()
        conn.close()
        sprint ("FakePoolCreate except ",err)

def fake_volume_create(volumeName,size,hostId,multi_device_id,deviceID,protocol):
    try:
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        dedup="false"
        compression="false"
        backup_device="true"
        
        if (int(protocol)==nfs):
            state=8
        elif (int(protocol)==cifs):
            state=10
        else:
            state=12
        query_lan=c.execute("select count(*) from Volume where name='"+ str(volumeName)+"'")
        nameCount = c.fetchone()[0]
        conn.commit()
        volumeId=-1
        type="Remote"
        if nameCount == 0:
            sprint ("insert into volume",volumeName)
            query=c.execute("insert into  volume(name,state,size,multi_device_id,compression,deduplication,cr_date,backup_device,type) values(?,?,?,?,?,?,datetime(),?,?)",\
            [volumeName,state,size,multi_device_id,compression, dedup,backup_device,type]) 
            conn.commit() 
            volumeId = c.lastrowid
        else:
            sprint ("update volume",volumeName)
            query=c.execute("update volume set state=?, size=? where name=?",[state,size,volumeName]) 
            conn.commit() 
            volumeId = c.lastrowid

        if (volumeId !=-1):
            portId=1
            lun=1
            state=1
            msg=str(portId)+" "+str(volumeId)+" "+str(hostId)+" "+str(lun)
            sprint ("insert into export",msg)            
            query_SP=c.execute("insert into export(port_id,vol_id,host_id,lun) values(?,?,?,?)",[portId,volumeId,hostId,lun])
            conn.commit()
            msg=str(state)+" "+str(volumeId)+" "+str(size)+" "+str(deviceID)
            sprint ("update device ID=",msg)            
            query=c.execute("update device set state=?, vol_id=?, size=? where id =?",[state,volumeId,size,deviceID])
            conn.commit()
        c.close()
        conn.close()
        return volumeId
    except Exception as err:
        sprint ("fake_volume_create except ",err)
        state=0
        query=c.execute("update device set state=?, vol_id=?, size=? where id =?",[state,volumeId,size,deviceID])
        conn.commit()
        c.close()
        conn.close()
        return -1
        
def fake_volume_delete(name,hostId,multi_device_id):
    msg=str(str(name)+str(hostId)+str(multi_device_id))
    sprint ("fake_volume_delete",msg)
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    try:
        query=c.execute("select id from volume where name='"+ str(name)+"'")
        resp=c.fetchone()
        if str(resp) != str("None"):
            volId = resp[0]
            #print "vol_id = "+str(volId)
            query=c.execute("delete from export where vol_id=?",[volId])
            conn.commit()
            query=c.execute("delete from  volume where name=?",[name])
            conn.commit()
        c.close()
        conn.close()
    except Exception as err:
        c.close()
        conn.close()
        sprint ("fake_volume_delete except ",err)
        return -1

def FakeDeviceDeleteAll():
    sprint ("FakeDeviceDeleteAll",0)
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    try:
        query=c.execute("delete from  device")
        conn.commit()
        c.close()
        conn.close()
    except Exception as err:
        c.close()
        conn.close()
        sprint ("FakeDeviceDeleteAll except ",err)
        return -1
     
def FakeVolDeleteAll(VolType):
    sprint ("FakeVolDeleteAll",VolType) 
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    try:
        query=c.execute("delete from  volume where type=?",[VolType])
        conn.commit()
        c.close()
        conn.close()
    except Exception as err:
        c.close()
        conn.close()
        sprint ("FakeVolDeleteAll except ",err)
        return -1
        
def CheckSanMounts(mnt,param):
    val='null'
    sprint ("mnt,param",str(mnt)+str(param))
    try:
        process1 = subprocess.check_output(["mountpoint",mnt])
        sprint (process1,0)
    except Exception as err:
        sprint ("CheckSanMounts except 1",err)
        return val
        
    try:
        if (param=='source' or param=='target' or param=="size" or param =="avail" or param=="used" or param =="use%"): 
        #findmnt /mnt/remote/mnt/cifs1 -o SOURCE,TARGET,SIZE,AVAIL,USED,USE% -J
            arg1="-o"
            arg2="SOURCE,TARGET,SIZE,AVAIL,USED,USE%"
            arg2=param
            arg3="-J"
            process1 = subprocess.check_output(["findmnt",mnt,arg1, arg2,arg3])
            y = json.loads(process1)
            sprint ("findmnt",y)
            val=y['filesystems'][0][param]
            sprint (val,0)
            mySize=0
            if val.find('T') != -1:
                size= val.replace('T','')
                mySize=float(size)            
            elif val.find('G') != -1:
                size= val.replace('G','')
                mySize=float(size)
            elif val.find('M') != -1:
                size=val.replace('M','')
                mySize=float(size)
        sprint ("mnt size",int(mySize))
        return int(mySize)
    except Exception as err:
        sprint ("CheckSanMounts except 2",err)
        return val

def DeleteDisk(disk,location):
    try:
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        if disk=='all':
            query=c.execute("delete from disks")
            conn.commit()
        elif disk=="mrx":
            dbquery=c.execute("delete from disks where (name='mra' or name='mrb' or name='mrc' or name='mrd') and controller_id=location")
            conn.commit()
        c.close()
        conn.close()
        sprint ("Deleted Disks ",disk)
        return 0
    except Exception as err:
        sprint ("DeleteDisk except",err)
        c.close()
        conn.close()
        return -1

def SetVolumesOnOff(action,location):
    msg= action+' '+location
    sprint("SetVolumesOnOff ", msg)
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    multi_device_id_list='('

    try:
        if location!='cx':
            query_lan=c.execute("select id from multi_device where location=?",[location])
            resp=c.fetchall()
            sprint ("multi_device resp=",resp)
            if str(resp) != str("None"):
                for col in resp:
                    sprint ("MultiDevice ID=", col[0])
                    multi_device_id_list=multi_device_id_list+"'"+str(col[0])+"'"+','
                multi_device_id_list=multi_device_id_list +"'1000'"+')'
                sprint ("multi_device_id_list",multi_device_id_list)
                
        if location=='cx':
            sprint ("location is =",location)            
            query=c.execute("select id,name,multi_device_id,state from volume")
        else:
            #query=c.execute("select id,name,multi_device_id,state from volume where multi_device_id=?",[multi_device_id])
            q="select id,name,multi_device_id,state from volume where multi_device_id IN" + multi_device_id_list
            sprint ("Query=",q)
            query=c.execute(q)
            #select id,name,multi_device_id,state from volume where multi_device_id IN ('4','5');
        resp= c.fetchall()
        sprint ("Vols to start/stop",resp)
        if resp !="None":
            for col in resp:
                VolID=col[0]
                VolName=col[1]
                PoolID=col[2]
                state=col[3]
                if (state==gVolOn or state==gVolOff):
                    try:
                        sprint ("step 1",VolID)
                        query=c.execute("select host_id from export where vol_id='"+ str(VolID)+"'")
                        hostId= c.fetchone()[0]
                        conn.commit()
                    except Exception as err:
                        sprint ("SetVolumesOnOff step 1 except ",err)
                    try:  
                        sprint ("step 2",0)                    
                        query=c.execute("select protocol from host where id='"+ str(hostId)+"'")
                        protocolId = c.fetchone()[0]
                        conn.commit()
                    except Exception as err:
                        sprint ("SetVolumesOnOff step 2 except ",err)
                    try:  
                        sprint ("step 3",0)                    
                        query=c.execute("select system_name from multi_device where id='"+ str(PoolID)+"'")
                        PoolName = c.fetchone()[0]
                        conn.commit()
                    except Exception as err:
                        sprint ("SetVolumesOnOff step 2 except ",err)
                    try:
                        sprint ("step 4",0)
                        conn.commit()
                        if action=="on":
                            msg=str(str(PoolName)+ str(VolName)+ str(protocolId))
                            sprint ("VolumeStart",msg)
                            res=VolumeStart(PoolName, VolName, protocolId,'null')
                            sprint ("VolumeStart Result",str(res))
                        elif action=="off":
                            msg=str(str(PoolName)+ str(VolName)+ str(protocolId))
                            sprint ("VolumeStop",msg)
                            res=VolumeStop(PoolName, VolName, protocolId,'null')
                            sprint ("VolumeStop Result",str(res))
                    except Exception as err:
                        sprint ("SetVolumesOnOff step 2 except ",err)
                        
        c.close()
        conn.close()
        return 0
    except Exception as err:
        c.close()
        conn.close()
        sprint ("SetVolumesOnOff except ",err)
        return -1
        
def SetDevicesOnOff(on_off):
    if on_off=='on':
        action='C'
        OnOffStr="SetDevicesON"
        sprint(OnOffStr,action)
    elif on_off=='off':
        action='D'
        OnOffStr="SetDevicesOFF"
        sprint(OnOffStr,action)
    else:
        return -1

    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    try:
        query=c.execute("select id from stor_man")
        resp= c.fetchall()
        sprint ("StorMan to start",resp)
        if resp !="None":
            for col in resp:
                StorManID=col[0]
                dbquery="SELECT sm.state,sm.name,h.name,h.iqn,sm.remote_share,sm.protocol,h.id from stor_man sm join host h on h.id=sm.host_id where sm.id="+str(StorManID)
                query = c.execute(dbquery)
                dbdata = []
                conn.commit()
                for col in c:
                    state = col[0]
                    StorName=[1]
                    host_name = col[2]
                    HostIQN = col[3]
                    share = col[4]
                    StorProt = col[5]
                    HostID = col[6]
                    sprint ("step1",0)
                msg= "STEP 1","state:",state,"StormanID",StorManID,"host:",host_name,"IQN",HostIQN,"Share:",share,"Prot",StorProt,"HostID",HostID
                sprint(msg,0)
                res=StorManConnect(StorName,StorManID,HostID,HostIQN,StorProt,action,share)
                if res!=0:
                    query=c.execute("update stor_man set state = 0 where id=?",[StorManID])
                    conn.commit()
        query=c.execute("select id from device")
        resp= c.fetchall()
        sprint("select id from device",0)
        sprint("select id from device",str(resp))
        sprint (str(OnOffStr),str(resp))
        if resp !="None":
            for col in resp:
                deviceId=col[0]
                action='C'
                DeviceConnect(deviceId, action)
        c.close()
        conn.close()
        return 0
    except Exception as err:
        c.close()
        conn.close()
        sprint ("SetDevicesOn except ",err)
        return -1

def ShowMount (remote,mnt):

    arg1='-e'
    #sudo showmount -e 192.168.32.15
    sprint ("showmount remote",remote)
    sprint ("showmount mount",mnt)
    try:
        process1 = subprocess.check_output(["showmount",arg1,remote])
        sprint (process1,0)
        res=process1.decode('utf-8')
        msg=str(remote) + str(mnt)
        if res.find(mnt)!=-1:
            sprint ("mnt exported",msg)
            status=0
        else:
            status=-1
            sprint ("mnt NOT exported",msg)
    except Exception as err:
        sprint ("ShowMount except",err)
        sprint ("ShowMount except",msg)
        return -1
        
    return status
    
def PingRemote(remote,interface):

    arg1='-c'
    arg2='1'
    arg3='-W'
    arg4='2'
    arg5='-I'
    #ping -c 1 -W 2 -I enp46s0f0 192.168.32.15
    try:
        if interface=='all':
            process1 = subprocess.check_output(["ping",remote,arg1,arg2,arg3,arg4])
        else:
            process1 = subprocess.check_output(["ping",remote,arg1,arg2,arg3,arg4,arg5,interface])

        sprint (process1,0)
        res=process1.decode('utf-8')
        if res.find("0% packet loss")!=-1:
            sprint("PingRemote OK",remote)
            sprint("PingRemote OK",interface)
            status=0
        else:
            status=-1
            sprint("PingRemote Not OK",interface)
    except Exception as err:
        sprint("PingRemote except",err)
        return -1
        
    return status

def StorManGetHost(HostID):
    sprint ("StorManGetHost",HostID)
    state=1
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    sprint ("query=","select iqn from host ")
    query=c.execute("select iqn from host where id='{}".format(HostID)+"'")
    resp=c.fetchone()
    if str(resp) != str("None"):
        host=str (resp[0])
        host = host.strip()
        sprint ("Host",host)
        conn.commit()
        c.close()
        conn.close()
    return host

def StorManCreate(StorName,StorManID,HostID,StorProt):
    try:

        host=StorManGetHost(HostID)
        iSCSIdiskList=[]
        if ((StorProt==iSER_Chap) or (StorProt==iSER_NoChap)):
            iface="iser"
        else:
            iface="null"
        result=iSCSIadm_Discover(host,iface)
        if result!="null":
            iDisks=result.splitlines()
            for iDisk in iDisks:
                disk = iDisk.split("iqn")
                iSCSIdisk= "iqn"+disk[1]
                iSCSIdiskList.append(iSCSIdisk)
                #print iSCSIdisk
                #result=iSCSIadm_Login(host,iSCSIdisk)
                sprint (result,0)
            for iDisk in iSCSIdiskList:
                state=0
                result=DB_updateStorManDevice(StorManID,iDisk,10,state)
                sprint (result,0)    

    except Exception as err:
        sprint ("StorManCreate",err)
        
    return (0)
    
def StorManDiscover(StorName,storManId,HostID,HostIQN,StorProt,action,share):

    if ((int(StorProt)==int(iSCSI_Chap)) or (int(StorProt) ==int(iSCSI_NoChap)) or (int(StorProt)==int(iSER_Chap)) or (int(StorProt) ==int(iSER_NoChap))):
        if action=='st':    #SendTargets
            sprint ("StorMan iSCSI/iSER discover",StorProt)
            try:
                if ((int(StorProt)==int(iSER_Chap)) or (int(StorProt) ==int(iSER_NoChap))):
                    iface="iser"
                else:
                    iface="null"
                iSCSIdiskList=[]
                sprint("iqn",HostIQN)
                sprint("iface",iface)
                result=iSCSIadm_Discover(HostIQN,iface)
                sprint ("iSCSIadm_Discover",0)
                if result!="null":
                    iDisks=result.splitlines()
                    for iDisk in iDisks:
                        sprint ("iSCSI Disks",iDisks)
                        disk = iDisk.split("iqn")
                        iSCSIdisk= "iqn"+disk[1]
                        iSCSIdiskList.append(iSCSIdisk)
                        sprint(iSCSIdisk,0)
                    for iDisk in iSCSIdiskList:
                        sprint ("step 3 iSCSI",iDisk)
                        size=0
                        state=0
                        result=DB_updateStorManDevice(storManId,iDisk,size,state)
                        sprint(result,iDisk)
                        sprint ("result",iDisk)
                    sprint ((json.JSONEncoder().encode({'status':'success','description':'Updated Successfully'})),0)
                    return 0
                else:
                    return -1
            except Exception as err:
                sprint("Err",err)
                print(((json.JSONEncoder())))
                
    c=conn.cursor()
    sprint ("query=","select name,stor_man_id from device where id=")
    query=c.execute("select name,stor_man_id from device where id='{}".format(DeviceID)+"'")
    resp=c.fetchone()
    if str(resp) != str("None"):
        iSCSIdisk=resp[0]
        sprint ("iSCSIdisk",iSCSIdisk)
        StorManID=resp[1]
        sprint ("StorManID",StorManID)
        query=c.execute("select host_id from stor_man where id='{}".format(StorManID)+"'")
        resp=c.fetchone()
        HostID="localhost"
        if str(resp) != str("None"):
            HostID=resp[0]
        host=StorManGetHost(HostID)
        result=iSCSIadm_Login(host,iSCSIdisk)
        sprint (result,0)
        query=c.execute("update device set state=? where id=?",[state,DeviceID])
        conn.commit()
        c.close()
        conn.close()
    return (0)


def StorManStop(DeviceID,StorProt):
    sprint ("StorManStop DeviceID",DeviceID)
    state=0
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    sprint ("query=","select name,stor_man_id from device where id=")
    query=c.execute("select name,stor_man_id from device where id='{}".format(DeviceID)+"'")
    resp=c.fetchone()
    if str(resp) != str("None"):
        iSCSIdisk=resp[0]
        sprint ("iSCSIdisk",iSCSIdisk)
        StorManID=resp[1]
        sprint ("StorManID",StorManID)
        query=c.execute("select host_id from stor_man where id='{}".format(StorManID)+"'")
        resp=c.fetchone()
        HostID="localhost"
        if str(resp) != str("None"):
            HostID=resp[0]
        host=StorManGetHost(HostID)
        result=iSCSIadm_Logout(host,iSCSIdisk)
        sprint (result,0)
        query=c.execute("update device set state=? where id=?",[state,DeviceID])
        conn.commit()
        c.close()
        conn.close()
    return (0)

def StorManDelete(StorName,StorManID,HostID,StorProt):
    return (0)


def StorManConnect(StorName,storManId,HostID,HostIQN,StorProt,action,share):

    try:
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        
        if ((int(StorProt)==int(iSCSI_Chap)) or (int(StorProt) ==int(iSCSI_NoChap)) or (int(StorProt)==int(iSER_Chap)) or (int(StorProt) ==int(iSER_NoChap))):
            if action=='C':
                sprint ("StorMan iSCSI/iSER connect",str(StorProt))
                try:
                    if ((int(StorProt)==int(iSER_Chap)) or (int(StorProt) ==int(iSER_NoChap))):
                        iface="iser"
                    else:
                        iface="null"
                    iSCSIdiskList=[]
                    sprint("iqn",HostIQN)
                    sprint("iface",iface)
                    result=iSCSIadm_Discover(HostIQN,iface)
                    sprint ("iSCSIadm_Discover",0)
                    if result!="null":
                        iDisks=result.splitlines()
                        for iDisk in iDisks:
                            sprint ("iSCSI Disks",iDisks)
                            disk = iDisk.split("iqn")
                            iSCSIdisk= "iqn"+disk[1]
                            iSCSIdiskList.append(iSCSIdisk)
                            sprint(iSCSIdisk,0)
                        for iDisk in iSCSIdiskList:
                            sprint ("step 3 iSCSI",iDisk)
                            size=1
                            state=0
                            result=DB_updateStorManDevice(storManId,iDisk,size,state)
                            sprint(result,iDisk)
                            #logout devices
                            result=iSCSIadm_Logout(HostIQN,iDisk)
                            sprint ("result",iDisk)
                        query=c.execute("update stor_man set state = 1 where id=?",[storManId])
                        conn.commit()
                        sprint ((json.JSONEncoder().encode({'status':'success','description':'Updated Successfully'})),0)
                        c.close()
                        conn.close()
                        return 0
                    else:
                        return -1
                except Exception as err:
                    sprint("Err",err)
                    sprint ((json.JSONEncoder().encode({'status':'fail','description':'Remote Discovery'})),0)
                    return -1
            # sudo echo 1 > /sys/block/sdc/device/delete for a broken sd device
            elif action=="D":   #dis-connection
                sprint ("StorMan iSCSI disconnect",0)
                sprint("protocol",StorProt)
                dbquery="SELECT name from device where stor_man_id="+str(storManId)
                query = c.execute(dbquery)
                resp= c.fetchall()
                if resp !="None":
                    for col in resp:
                        deviceName=col[0]
                        sprint("deviceName",deviceName)
                        result=iSCSIadm_Logout(HostIQN,deviceName)
                        if result == "null":
                            sprint ((json.JSONEncoder().encode({'status':'fail','description':'failed to un-mount device'})),0)
                query=c.execute("update stor_man set state = 0 where id=?",[storManId])
                conn.commit()
                c.close()
                conn.close()
                sprint ((json.JSONEncoder().encode({'status':'success','description':'Updated Successfully'})),0)
                return 0

        elif ((int(StorProt)==int(nfs))):
            remote_share=share
            if action=='C':
                interface='all'
                host_iqn=HostIQN

                linkState=PingRemote(host_iqn,interface)
                if linkState==-1:
                    return -10
                else:
                    sprint ("Remote Link OK",host_iqn)
                MntState=ShowMount(host_iqn,remote_share)
                if MntState==-1:
                    return -11
                else:
                    sprint ("Remote Mnt OK",remote_share)

                sprint ("STEP 2",0)
                local_path="/mnt/remote/"+remote_share
                arg1="-p"
                arg2=local_path
                isdir = os.path.isdir(local_path)
                sprint ("isdir",isdir)
                if isdir==False: 
                    #ex. sudo mkdir -p /mnt/remote/mnt/lv1
                    try:
                        sprint ("STEP 2a mkdir",local_path)
                        process1 = subprocess.check_output(["sudo","mkdir",arg1,local_path])
                    except Exception as err:
                        sprint ((json.JSONEncoder().encode({'status':'fail','description':'invalid local directory'})),0)
                        return -1
                ismount = os.path.ismount(local_path)
                sprint ("ismount",ismount)
                if ismount ==False:
                    #print(process1)
                    #sudo mount -t nfs 192.168.32.16:/mnt/lv1 /mnt/lolv1
                    #sudo mount 192.168.30.7:/mnt/nfs_backup  /mnt/nfs_backup
                    #sudo mount 192.168.30.14:/mnt/nfstest  /mnt/nfstest
                    arg1="-t"
                    arg2="nfs"
                    NFSshare= str(host_iqn)+":"+"/"+remote_share
                    arg4=local_path
                    try:
                        process1 = subprocess.check_output(["sudo","mount",arg1,arg2,NFSshare,arg4])
                        #print process1
                    except Exception as err:
                        sprint ((json.JSONEncoder().encode({'status':'fail','description':'invalid remote directory'})),0)
                        process1 = subprocess.check_output(["rmdir",arg4])
                        return -1
                else:
                    NFSshare= str(host_iqn)+":"+"/"+remote_share
                    sprint ("Is already Mounted",NFSshare)
                    process1 = subprocess.check_output(["sudo","findmnt",local_path,"-J"])
                    y = json.loads(process1)
                    source=y['filesystems'][0]["source"]
                    sprint (source,0)
                    if str(source)!=str(NFSshare):
                        sprint ((json.JSONEncoder().encode({'status':'fail','description':'directory already in use'})),0)
                        return -1
                    else:
                        sprint ((json.JSONEncoder().encode({'status':'success','description':'directory already mounted'})),0)
                        query=c.execute("update stor_man set state = 1 where id=?",[storManId])
                        conn.commit() 
                sprint ("step 4",0)
                DeviceName=local_path
                sys_name=NFSshare
                protocolId=nfs
                val="null"
                try:
                    val = CheckSanMounts(local_path,"size")
                except Exception as err:
                    sprint("StorManConnect CheckSanMounts except",err)
                size=0
                sprint ("val=",val)
                if (str(val) !="null"):
                    size=int (val)
                if size !=0:
                    state=1
                    res= DB_updateStorManDevice(storManId,DeviceName,size,state)
                    deviceID=res[1]
                    multi_device_id=GetPoolID("system")
                    query=c.execute("update stor_man set state = 1 where id=?",[storManId])
                    conn.commit()
                    volName=share+'@'+HostIQN
                    fake_volume_create(volName,size,HostID,multi_device_id,deviceID,int(StorProt))
                    sprint ((json.JSONEncoder().encode({'status':'success','description':'Updated Successfully'})),0)
                    conn.commit()
                    c.close()
                    conn.close()
                    return 0
                else:
                    return gMountError

            elif action=="D":   #dis-connection
                #print "disconnect"
                #print "D"
                local_path="/mnt/remote/"+remote_share
                isdir = os.path.isdir(local_path)
                ismount = os.path.ismount(local_path)
                umountError=False
                rmdirError=False
                sprint ("step 5",0)
                if ((int(StorProt)==int(nfs))):
                    if isdir==True:
                        if ismount==True:
                            try:
                                process1 = subprocess.check_output(["sudo","umount",'-l',local_path])
                                #print process1
                                #needs to poll here until mountpoint is gone
                            except Exception as err:
                                sprint ("umount except ",err)
                                sprint ((json.JSONEncoder().encode({'status':'fail','description':'umount error'})),0)
                                umountError=True

                        if isdir==True:
                            try:
                                #sudo rmdir -p /mnt/nfs_backup
                                arg1="-p"
                                arg2=local_path
                                process1 = subprocess.check_output(["sudo","rmdir",arg2])
                            except Exception as err:
                                sprint ("rmdir except ",err)
                                rmdirError=True
                                if umountError==False:
                                    sprint ((json.JSONEncoder().encode({'status':'fail','description':'rmdir error'})),0)

                            #print "deleting device"
                    #print "step 6",isdir,ismount
                    try:
                        query=c.execute("delete from  device where name=?",[local_path])
                        conn.commit()
                        sprint ("step 7",0)
                    except Exception as err:
                        sprint ("delete from  device except",local_path)
                    volName=share+'@'+HostIQN
                    multi_device_id=1
                    query=c.execute("update stor_man set state = 0 where id=?",[storManId])
                    conn.commit()
                    c.close()
                    conn.close()
                    sprint("fake_volume_delete",0)
                    fake_volume_delete(volName,HostID,multi_device_id)
                    if (umountError==False and rmdirError==False):
                        sprint ((json.JSONEncoder().encode({'status':'success','description':'Updated Successfully'})),0)
                        return 0
                    else:
                        sprint ((json.JSONEncoder().encode({'status':'fail','description':'failed to delete share'})),0)
                        return -1

        elif ((int(StorProt)==int(cifs))):
            #Step 1: Install the CIFS Utils pkg. sudo apt-get install cifs-utils.
            #Step 2: Create a mount point. sudo mkdir /mnt/local_share.
            #Step 3: Mount the volume. sudo mount -t cifs //<vpsa_ip_address>/<export_share> /mnt/<local_share> You can get the vpsa_ip_address/export_share from your VPSA GUI.
            remote_share=share
            if action=='C':
                res=getCIFS_UserPassword(share)
                if res[0]==0:
                    user=res[1]
                    pw=res[2]
                else:
                    user="null"
                    pw="null"
                check = is_EncodedString_base64(pw)
                if check:
                    password=pwd_decoding(pw)
                else:
                    password=pw
                sprint ("CIFS User/Password",str(user)+"/"+str(password))
                
                interface='all'
                host_iqn=HostIQN

                linkState=PingRemote(host_iqn,interface)
                if linkState==-1:
                    return -10
                else:
                    sprint ("Remote Link OK",host_iqn)
                
                user="sanuyi"       #this is to access the service ! not the share user/pw
                password="hello123" #this is to access the service ! not the share user/pw
                MntState=ShowCifsMount(host_iqn,remote_share,user,password)
                if MntState==-1:
                    return -11
                else:
                    sprint ("Remote Mnt OK",remote_share)
                sprint ("STEP 2",0)
                local_path="/mnt/remote/mnt/"+remote_share
                arg1="-p"
                arg2=local_path
                isdir = os.path.isdir(local_path)
                sprint ("isdir",isdir)
                if isdir==False: 
                    #ex. sudo mkdir -p /mnt/remote/mnt/lv1
                    try:
                        sprint ("STEP 2a mkdir",local_path)
                        process1 = subprocess.check_output(["sudo","mkdir",arg1,local_path])
                    except Exception as err:
                        sprint ((json.JSONEncoder().encode({'status':'fail','description':'invalid local directory'})),0)
                        return -1
                ismount = os.path.ismount(local_path)
                sprint ("ismount",ismount)
                if ismount ==False:
                    try:
                        arg0=" -t cifs -o username=guest -o password=hello123 //192.168.30.6/cifs1 /mnt/remote/mnt/cifs1"
                        arg1='-t cifs '
                        arg4=' -o username='
                        arg5=' -o password='
                        #share='cifs15'
                        remote=' //'+host_iqn+'/'+remote_share
                        local_path=' /mnt/remote/mnt/'+remote_share
                        user='wo'
                        password='hello123hello123'
                        arg0=str(arg1)+" "+str(arg4)+str(user)+" "+str(arg5)+str(password)+" "+str(remote)+" "+str(local_path)
                        command='mount '+arg0
                        sprint (command,0)
                        #sprint ("deliberate crash",0)
                        #msg=crash           #########################WOTEST####################
                        p = subprocess.Popen([command],shell=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
                        sprint (p.stdout.read(),0)
                    except Exception as err:
                        #https://linux.die.net/man/8/mount.cifs
                        sprint ("DeviceConnectCIFS except",err)
                        sprint ((json.JSONEncoder().encode({'status':'fail','description':'invalid remote directory'})),0)
                        process1 = subprocess.check_output(["rmdir",arg4])
                        return -1
                else:
                    CIFSshare= '//'+str(host_iqn)+"/"+remote_share
                    #sudo findmnt /mnt/remote/mnt/cifs1 -J
                    sprint ("Is already Mounted",CIFSshare)
                    process1 = subprocess.check_output(["sudo","findmnt",'/mnt/remote/mnt/'+remote_share,"-J"])
                    y = json.loads(process1)
                    source=y['filesystems'][0]["source"]
                    sprint ("source",str("s="+source))
                    if str(source)!=str(CIFSshare):
                        sprint ((json.JSONEncoder().encode({'status':'fail','description':'directory already in use'})),0)
                        return -1
                    else:
                        sprint ((json.JSONEncoder().encode({'status':'success','description':'directory already mounted'})),0)
                        query=c.execute("update stor_man set state = 1 where id=?",[storManId])
                        conn.commit() 
                CIFSshare= '//'+str(host_iqn)+"/"+remote_share
                sprint ("step 4",0)
                DeviceName=local_path
                sys_name=CIFSshare
                val="null"
                try:
                    val = CheckSanMounts('/mnt/remote/mnt/'+remote_share,"size")
                except Exception as err:
                    sprint("StorManConnect CheckSanMounts except",err)
                size=0
                sprint ("val=",val)
                if (str(val) !="null"):
                    size=int (val)
                if size !=0:
                    state=1
                    res= DB_updateStorManDevice(storManId,DeviceName,size,state)
                    deviceID=res[1]
                    multi_device_id=GetPoolID("system")   #some valid pool ID
                    query=c.execute("update stor_man set state = 1 where id=?",[storManId])
                    conn.commit()
                    volName=share+'@'+HostIQN
                    fake_volume_create(volName,size,HostID,multi_device_id,deviceID,int(StorProt))
                    sprint ((json.JSONEncoder().encode({'status':'success','description':'Updated Successfully'})),0)
                    conn.commit()
                    c.close()
                    conn.close()
                    return 0
                else:
                    return gMountError

            elif action=="D":   #dis-connection
                #print "disconnect"
                #print "D"
                local_path="/mnt/remote/"+remote_share
                isdir = os.path.isdir(local_path)
                ismount = os.path.ismount(local_path)
                umountError=False
                rmdirError=False
                sprint ("step 5",0)
                if ((int(StorProt)==int(cifs))):
                    if isdir==True:
                        if ismount==True:
                            try:
                                process1 = subprocess.check_output(["sudo","umount",'-l',local_path])
                                #print process1
                                #needs to poll here until mountpoint is gone
                            except Exception as err:
                                sprint ("umount except ",err)
                                sprint ((json.JSONEncoder().encode({'status':'fail','description':'umount error'})),0)
                                umountError=True

                        if isdir==True:
                            try:
                                #sudo rmdir -p /mnt/nfs_backup
                                arg1="-p"
                                arg2=local_path
                                process1 = subprocess.check_output(["sudo","rmdir",arg2])
                            except Exception as err:
                                sprint ("rmdir except ",err)
                                rmdirError=True
                                if umountError==False:
                                    sprint ((json.JSONEncoder().encode({'status':'fail','description':'rmdir error'})),0)

                            #print "deleting device"
                    #print "step 6",isdir,ismount
                    try:
                        query=c.execute("delete from  device where name=?",[local_path])
                        conn.commit()
                        sprint ("step 7",0)
                    except Exception as err:
                        sprint ("delete from  device except",local_path)
                    volName=share+'@'+HostIQN
                    multi_device_id=1
                    query=c.execute("update stor_man set state = 0 where id=?",[storManId])
                    conn.commit()
                    c.close()
                    conn.close()
                    fake_volume_delete(volName,HostID,multi_device_id)
                    if (umountError==False and rmdirError==False):
                        sprint ((json.JSONEncoder().encode({'status':'success','description':'Updated Successfully'})),0)
                        return 0
                    else:
                        sprint ((json.JSONEncoder().encode({'status':'fail','description':'failed to delete share'})),)
                        return -1
    except Exception as err:
        sprint ("StorManConnect except ",err)
        return -1
        
def DeviceConnect(deviceId, action):
    try:
        invalidDeviceID=-1
        invalidProtocol=-2
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        
        sprint ("DeviceConnect",deviceId)
        query=c.execute("select stor_man_id,name from device where id='"+ str(deviceId)+"'")
        resp=c.fetchone()
        if str(resp) != str("None"):
                storManId = resp[0]        
                DeviceName = resp[1]
                sprint ("StorManId",storManId)
                sprint ("DeviceName",DeviceName)
        else:
                sprint ((json.JSONEncoder().encode({'status':'fail','description':'invalid Device ID'})),0)
                conn.commit()
                c.close()
                conn.close()
                return invalidDeviceID

        dbquery="SELECT sm.state,h.name,h.iqn,h.pw,h.user_name,sm.remote_share,sm.protocol,h.id from stor_man sm join host h on h.id=sm.host_id where sm.id="+str(storManId)
        query = c.execute(dbquery)
        dbdata = []
        conn.commit()
        for col in c:
            if col[0] != None:
                state = col[0]
            else:
                state="None"
            if col[1] != None:
                host_name = col[1]
            else:
                host_name="None"
                
            if col[2] != None:
                host_iqn = col[2]
            else:
                host_iqn="None"
                
            if col[3] != None:
                pw = col[3]
            else:
                pw="None"
                
            if col[4] != None:
                user= col[4]
            else:
                user="None"
  
            if col[5] != None:
                remote_share = col[5]
            else:
                remote_share="None"
            if col[6] != None:
                protocol = col[6]
            else:
                protocol="None"
            if col[7] != None:
                hostId = col[7]
            else:
                hostId="None"

        c.close()
        conn.close()
        sprint ("DeviceConnect step1",str(0))
        msg= "STEP 1 "+"state:"+str(state)+" host:"+host_name+" IQN:"+host_iqn+" Share:"+remote_share+" Prot:"+str(protocol)+" HostID:"+str(hostId)+" Action:"+str(action)
        sprint(msg,str(0))
        if protocol==nfs:
            retVal=DeviceConnectNFS(deviceId,action,host_name,host_iqn,hostId,remote_share,protocol)
        elif ((int(protocol)==int(iSCSI_Chap)) or (int(protocol) ==int(iSCSI_NoChap)) or (int(protocol)==int(iSER_Chap)) or (int(protocol) ==int(iSER_NoChap))):
            retVal=DeviceConnectiSCSI(deviceId,action,host_name,host_iqn,hostId,remote_share,protocol,DeviceName)
        elif protocol==cifs:
            retVal=DeviceConnectCIFS(deviceId,action,host_name,host_iqn,hostId,remote_share,protocol,user,pw)
        else:
            retVal= invalidProtocol
            
        sprint ("DeviceConnect step2",str(retVal))
        return retVal
        
    except Exception as err:
        sprint ("DeviceConnect except",err)
        return -1
 
#'mount', '-t', 'cifs', '-o', 'username=', 'wo', '-o', 'password=', 'hello123hello123', '//192.168.30.15/cifs15', '/mnt/remote/mnt/cifs15')
    #sudo mount -v -t cifs  -o username=wo -o password=hello123hello123 //192.168.32.15/cifs15 /mnt/remote/mnt/cifs15
    #sudo mount -t cifs -o username=wo -o password=hello123hello123 //192.168.32.15/cifs15 /mnt/remote/mnt/cifs15
    #sudo mount -t cifs -o username=wo -o password=hello123hello123 //192.168.30.7/TMC /mnt/remote/mnt/cifs15

def ShowCifsMount(host_iqn,share,user,password):
    msg=str(host_iqn)+" "+str(share)+" "+str(user)+" "+str(password)
    sprint ("ShowCifsMount",msg)
    #smbclient --option='client min protocol=SMB2' -L 192.168.30.16 -U sanuyi%hello123 -g
    arg1="-L"
    arg2=host_iqn
    arg3="-U"
    arg4=user+"%"+password
    arg5="-g"
    try:
        process1 = subprocess.check_output(["smbclient",arg1,arg2,arg3,arg4,arg5])
        sprint (process1,0)
        if process1.find(share)!=-1:
            sprint ("CIFS mnt exported",msg)
            status=0
        else:
            status=-1
            sprint ("CIFS mnt NOT exported",msg)
    except Exception as err:
        sprint ("ShowCifsMount except",msg)
        return -1
        
    return status


def DeviceConnectCIFS(deviceId,action,host_name,host_iqn,hostId,remote_share,protocol,user,password):

    check = is_EncodedString_base64(password)
    if check:
        decodePwd=pwd_decoding(password)
    else:
        decodePwd=password

    sprint (action,deviceId)
    if action=="C":   #connection
        sprint ("connect",action)
        umountError=False
        rmdirError=False
        if protocol==cifs:
            sprint ("STEP 2",0)
            interface='all'
            linkState=PingRemote(host_iqn,interface)
            if linkState==-1:
                return gLinkError
            else:
                sprint ("Remote Link OK",host_iqn)
            sys_user="sanuyi"       #this is to access the service ! not the share user/pw
            sys_password="hello123" #this is to access the service ! not the share user/pw
            MntState=ShowCifsMount(host_iqn,remote_share,sys_user,sys_password)
            if MntState==-1:
                return gExportError
            else:
                sprint ("Remote Mnt OK",remote_share)
                
            #remote_share="nfs_backup"   #get the share name from host/share
            local_path="/mnt/remote/mnt/"+remote_share
            arg1="-p"
            arg2=local_path
            isdir = os.path.isdir(local_path)
            sprint ("isdir",isdir)
            if isdir==False: 
                #ex. sudo mkdir -p /mnt/remote/mnt/lv1
                try:
                    sprint ("STEP 2a mkdir",local_path)
                    process1 = subprocess.check_output(["sudo","mkdir",arg1,local_path])
                    i=0
                    while (i < 10):
                        time.sleep(.1)
                        isdir = os.path.isdir(local_path)
                        if (isdir==True):
                            i=10
                        else:
                            time.sleep(.1)
                            i=i+1
                            sprint("mkdir loop",i)
                except Exception as err:
                    sprint ((json.JSONEncoder().encode({'status':'fail','description':'invalid local directory'})),0)
                    return gInvalidLocalDirectory
            ismount = os.path.ismount(local_path)
            sprint ("ismount",ismount)
            if ismount ==False:
                #sudo mount -t cifs 192.168.32.16:/mnt/lv1 /mnt/lolv1
                #sudo mount -t cifs 192.168.32.15:/mnt/nfs16 /mnt/remote/mnt/nfs16
                try:
                    arg0=" -t cifs -o username=wo -o password=hello123hello123 //192.168.32.15/cifs15 /mnt/remote/mnt/cifs15"
                    arg1='-t cifs '
                    arg4=' -o username='
                    arg5=' -o password='
                    #share='cifs15'
                    remote=' //'+host_iqn+'/'+remote_share
                    local_path=' /mnt/remote/mnt/'+remote_share
                    arg0=arg1+arg4+user+arg5+decodePwd+remote+local_path
                    command='mount '+arg0
                    sprint (command,0)
                    #sprint ("Deliberate Crash",0)
                    #msg=crash
                    p = subprocess.Popen([command],shell=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
                    sprint (p.stdout.read(),0)
                except Exception as err:
                    #https://linux.die.net/man/8/mount.cifs
                    sprint ("DeviceConnectCIFS except",err)
                try:
                    sprint ("STEP 2b CIFS mount",remote)
                    time.sleep(1)
                    i=0
                    iMAX=10
                    p='/mnt/remote/mnt/'+remote_share
                    while i<iMAX:
                        ismount = os.path.ismount(p)
                        time.sleep(1)
                        i=i+1
                        if ismount==True:
                            i=iMAX
                        msg=p+" "+str(i)
                        sprint ("STEP 2b.1",msg)
                    if ismount==True:
                        sprint ("STEP 2c mounted",0)
                        multi_device_id=GetPoolID("system")
                        val = CheckSanMounts(p,"size")
                        size=0
                        sprint ("mnt val",val)
                        if (str(val) !="null"):
                            size= int(val)
                        sprint ("mnt size",val)
                        if size !=0:
                            volName=remote_share+'@'+host_iqn
                            fake_volume_create(volName,size,hostId,multi_device_id,deviceId,int(protocol))
                            return 0
                        else:
                            sprint ("gMountError",str(i))
                            return gMountError
                    else:
                        sprint ("gMountError",str(i))
                        return gMountError
                except Exception as err:
                    sprint ("DeviceConnect CIFS except",err)
                    return gMountError
            else:
                #//192.168.32.15/cifs15
                share= '//'+str(host_iqn)+"/"+remote_share
                process1 = subprocess.check_output(["sudo","findmnt",local_path,"-J"])
                y = json.loads(process1)
                source=y['filesystems'][0]["source"]
                sprint (source,0)
                if str(source)!=str(share):
                    sprint ("Is not Mounted",share)
                    return gMountError
                else:
                    sprint ("Is already Mounted",share)
                    return 0

    elif action=="D":   #dis-connection
        local_path="/mnt/remote/mnt/"+remote_share
        isdir = os.path.isdir(local_path)
        ismount = os.path.ismount(local_path)
        sprint ("step 5",0)
        if protocol==cifs:
            if isdir==True:
                sprint ("step 5a",0)
                if ismount==True:
                    sprint ("step 5b",0)
                    try:
                        process1 = subprocess.check_output(["sudo","umount","-l",local_path])
                        sprint ("step 5c",0)
                        #print process1
                        #needs to poll here until mountpoint is gone
                    except Exception as err:
                        sprint ("umount except ",err)
                        sprint ((json.JSONEncoder().encode({'status':'fail','description':'umount error'})),0)
                        return guMountError
                if isdir==True:
                    try:
                        #sudo rmdir -p /mnt/nfs_backup
                        arg1="-p"
                        arg2=local_path
                        process1 = subprocess.check_output(["sudo","rmdir",arg2])
                        multi_device_id=1
                        volName=remote_share+'@'+host_iqn
                        fake_volume_delete(volName,hostId,multi_device_id)
                        return 0
                    except Exception as err:
                        sprint ("rmdir except ",err)
                        return grmdirError
            else:
                return 0
        
def DeviceConnectNFS(deviceId,action,host_name,host_iqn,hostId,remote_share,protocol):


    sprint (action,deviceId)
    if action=="C":   #connection
        sprint ("connect",action)
        #print "N"
        umountError=False
        rmdirError=False
        if protocol==nfs:
            sprint ("STEP 2",0)
            interface='all'
            linkState=PingRemote(host_iqn,interface)
            if linkState==-1:
                return gLinkError
            else:
                sprint ("Remote Link OK",host_iqn)
            MntState=ShowMount(host_iqn,remote_share)
            if MntState==-1:
                return gExportError
            else:
                sprint ("Remote Mnt OK",remote_share)
                
            #remote_share="nfs_backup"   #get the share name from host/share
            local_path="/mnt/remote/"+remote_share
            arg1="-p"
            arg2=local_path
            isdir = os.path.isdir(local_path)
            sprint ("isdir",isdir)
            if isdir==False: 
                #ex. sudo mkdir -p /mnt/remote/mnt/lv1
                try:
                    sprint ("STEP 2a mkdir",local_path)
                    process1 = subprocess.check_output(["sudo","mkdir",arg1,local_path])
                    i=0
                    while (i < 10):
                        time.sleep(.1)
                        isdir = os.path.isdir(local_path)
                        if (isdir==True):
                            i=10
                        else:
                            time.sleep(.1)
                            i=i+1
                            sprint("mkdir loop",i)

                except Exception as err:
                    sprint ((json.JSONEncoder().encode({'status':'fail','description':'invalid local directory'})),0)
                    return gInvalidLocalDirectory
            ismount = os.path.ismount(local_path)
            sprint ("ismount",ismount)
            if ismount ==False:
                #print(process1)
                #sudo mount -t nfs 192.168.32.16:/mnt/lv1 /mnt/lolv1
                #sudo mount -t nfs 192.168.32.15:/mnt/nfs16 /mnt/remote/mnt/nfs16
                #sudo mount 192.168.30.7:/mnt/nfs_backup  /mnt/nfs_backup
                #sudo mount 192.168.30.14:/mnt/nfstest  /mnt/nfstest
                arg1a="-v"
                arg1="-t"
                arg2="nfs"
                NFSshare= str(host_iqn)+":"+"/"+remote_share
                arg4=local_path
                try:
                    process1 = subprocess.check_output(["sudo","mount",arg1a,arg1,arg2,NFSshare,arg4])
                    sprint (process1,0)
                    sprint ("STEP 2b NFS mount",NFSshare)
                    time.sleep(1)
                    i=0
                    iMAX=5
                    while i<iMAX:
                        ismount = os.path.ismount(local_path)
                        time.sleep(1)
                        i=i+1
                        if ismount ==True:
                            i=iMAX
                    if ismount ==True:
                        sprint ("STEP 2c mounted",0)
                        multi_device_id=GetPoolID("system")
                        val = CheckSanMounts(local_path,"size")
                        size=0
                        sprint ("NFS mnt val",val)
                        if (str(val) !="null"):
                            size= int(val)
                        if size!=0:
                            volName=remote_share+'@'+host_iqn
                            fake_volume_create(volName,size,hostId,multi_device_id,deviceId,int(protocol))
                            return 0
                        else:
                            return gMountError
                    else:
                        return gMountError
                except Exception as err:
                    sprint ("DeviceConnectNFS except",err)
                    return gMountError
            else:
                NFSshare= str(host_iqn)+":"+"/"+remote_share
                process1 = subprocess.check_output(["sudo","findmnt",local_path,"-J"])
                y = json.loads(process1)
                source=y['filesystems'][0]["source"]
                sprint (source,0)
                if str(source)!=str(NFSshare):
                    sprint ("Is not Mounted",NFSshare)
                    return gMountError
                else:
                    sprint ("Is already Mounted",NFSshare)
                    return 0

    elif action=="D":   #dis-connection
        local_path="/mnt/remote/"+remote_share
        isdir = os.path.isdir(local_path)
        ismount = os.path.ismount(local_path)
        sprint ("step 5",0)
        if protocol==nfs:
            if isdir==True:
                sprint ("step 5a",0)
                if ismount==True:
                    sprint ("step 5b",0)
                    try:
                        process1 = subprocess.check_output(["sudo","umount","-l",local_path])
                        sprint ("step 5c",0)
                        #print process1
                        #needs to poll here until mountpoint is gone
                    except Exception as err:
                        sprint ("umount except ",err)
                        print(((json.JSONEncoder().encode({'status':'fail','description':'umount error'})),0))
                        return guMountError
                if isdir==True:
                    try:
                        #sudo rmdir -p /mnt/nfs_backup
                        arg1="-p"
                        arg2=local_path
                        process1 = subprocess.check_output(["sudo","rmdir",arg2])
                        multi_device_id=1
                        volName=remote_share+'@'+host_iqn
                        fake_volume_delete(volName,hostId,multi_device_id)
                        return 0
                    except Exception as err:
                        sprint ("rmdir except ",err)
                        return grmdirError
            else:
                return 0
                
                
def getSDdevice(device):
    arg1="-m"
    arg2="session"
    arg3="-P"
    arg4='3'
    size=0
    sd_device='null'
    try:
        process1 = subprocess.check_output(["iscsiadm",arg1,arg2,arg3,arg4])
    except Exception as err:
        sprint("getSDdevice except ",err)
        return sd_device,size
        
    if process1.find("No active sessions")!=-1:
        return sd_device,size
        
    sprint ("getSDdevice","step2")
    line=process1.splitlines()
    i=0
    cnt =len(line)
    sd_device='null'
    sprint ("cnt=",cnt)
    while( i < cnt):
        if line[i].startswith("Target:"):
            target=line[i].split("Target:")
            sprint ("found Target:",target)
            dev=target[1].split(" ")
            sprint (dev[1],0)
            if (dev[1]==device):
                cnt2=cnt-i
                j=0
                while ( j<cnt2):
                    index=line[i+j].find("Attached scsi disk ")
                    if (index != -1):
                        len1=len("Attached scsi disk ")
                        sd_device=line[i+j][index+len1:index+len1+3]
                        sprint (sd_device,0)
                        break
                    j=j+1
                break
        i=i+1
    arg1="-o"
    arg2="NAME,SIZE"
    arg3="-J"
    #lsblk -o NAME,SIZE,HOTPLUG,TRAN -J
    process = subprocess.check_output(["lsblk",arg1,arg2,arg3])
    y = json.loads(process)
    #print ("lsblk",y)
    gbsize=0
    NbDisk= len(y['blockdevices'])
    i=0
    try:
        while (i < NbDisk):
            if y['blockdevices'][i]['name']==sd_device:
                size=str(y['blockdevices'][i]['size'])
                if size.find("G") !=-1:
                    gbsize=float(size.replace("G",""))
                if size.find("T") !=-1:
                    gbsize=1024*float(size.replace("T",""))
                sprint (sd_device,size)
                break
            i=i+1
    except Exception as err:
        sprint("lsblk except ",err)

    return sd_device,int(gbsize)
    
def DeviceConnectiSCSI(deviceId,action,host_name,host_iqn,hostId,remote_share,protocol,DeviceName):

    sprint (action,deviceId)
    if action=="C":   #connection
        sprint ("connect",action)
        #print "N"
        if ((int(protocol)==int(iSCSI_Chap)) or (int(protocol) ==int(iSCSI_NoChap)) or (int(protocol)==int(iSER_Chap)) or (int(protocol) ==int(iSER_NoChap))):
                sprint("deviceName",DeviceName)
                sprint("Protocol",protocol)
                sprint ("host_iqn",host_iqn)
                try:
                    iSCSIadm_Logout(host_iqn,DeviceName)
                except Exception as err:
                    sprint("iSCSIadm_Logout ",err)
                    time.sleep(1)

                result=iSCSIadm_Login(host_iqn,DeviceName)
                if result =="null":
                    iSCSIadm_Logout(host_iqn,DeviceName)
                    sprint ((json.JSONEncoder().encode({'status':'fail','description':'failed to connect to device'})),0)
                    return -1
                else:
                    multi_device_id=GetPoolID("system")
                    val=getSDdevice(DeviceName)
                    size =val[1]
                    fake_volume_create(DeviceName,size,hostId,multi_device_id,deviceId,int(protocol))

                    return 0

    elif action=="D":   #dis-connection
        sprint ("step 5",0)
        if ((int(protocol)==int(iSCSI_Chap)) or (int(protocol) ==int(iSCSI_NoChap)) or (int(protocol)==int(iSER_Chap)) or (int(protocol) ==int(iSER_NoChap))):
                sprint("protocol",protocol)
                sprint("deviceName",DeviceName)
                result=iSCSIadm_Logout(host_iqn,DeviceName)
                multi_device_id=1
                fake_volume_delete(DeviceName,hostId,multi_device_id)
                if result =="null":
                    sprint ((json.JSONEncoder().encode({'status':'fail','description':'failed to un-mount device'})),0)
                    return -1
                else:
                    return 0

#######################################################


    
def ietZvol_DeleteLun(pool,VolName,prot):
# ls -l /dev/zvol/tank/disk1
#lrwxrwxrwx 1 root root 11 Dec 20 22:10 /dev/zvol/tank/disk1 -> ../../zd144
    ls_arg1="-l"
    ls_arg2="/dev/zvol/"+pool+"/"+VolName
    process1 = subprocess.check_output(["ls", ls_arg1, ls_arg2])
    my_len= len(process1)
    my_index= process1.find("zd",0,my_len)
    device=str(process1[my_index : (my_len-1)])
    sprint (device,0)
    process1 = subprocess.check_output(["cat", "/proc/net/iet/volume"]).decode("utf-8")
    sprint (process1,0)
    my_len= len(process1)
    index=0
    tidString="tid:"
    pathString="path:/dev/"
    lunString="lun:"
    checking=0
    while checking==0:
        sprint ("checking ietZvol_DeleteLun","step1")
        my_indexTid= process1.find(tidString,index,my_len)
        sprint ((str(index)+ " " + str(my_len)),0)
        if my_indexTid==-1:
            checking=-1
            sprint ("debug1 ",checking)
            break
        my_indexLun= process1.find(lunString,my_indexTid,my_len-my_indexTid)
        sprint ((str(my_indexLun) + " " + str(my_len-my_indexLun)),"step2")
        if my_indexLun==-1:
            checking=-1
            sprint ("debug2 ",checking)
            break
        my_indexPath = process1.find(pathString,my_indexLun,my_len)
        sprint ((str(my_indexPath) + " " + str(my_len-my_indexPath)),"step3")
        if my_indexPath==-1:
           checking=-1
           sprint ("debug3",checking)
           break
        tid=str(process1[my_indexTid+len(tidString) : (my_indexTid+len(tidString)+1)])
        lun=str(process1[my_indexLun+len(lunString): (my_indexLun+len(lunString)+1)])
        path=str(process1[my_indexPath+len(pathString): (my_indexPath+len(pathString)+4)])
        msg= tid+" "+lun+" "+path
        sprint ("tid,lun,path=",msg)
        index=my_indexPath
        my_len=my_len-index
        if str(device) in str(path):
        #if (str(path)==str(device)):
            iSCSI_DeleteLun(tid,lun,pro)
            iSCSI_DeleteTarget(tid,prot)
            break
    if (checking==0):
        sprint ("device found",0)
    else:
        sprint ("device not found",0)
        return wErrDeviceNotFound

    process1 = subprocess.check_output(["cat", "/proc/net/iet/session"])
    sprint (process1,0)  
    return 0
    
def iSCSI_CreateTarget(tid,VolName,prot):
#*
    try:
    
        if gTarget=="iet":
            iet_arg1="--op"
            iet_arg2="new"
            iet_arg3="--tid="+str(tid)
            iet_arg4="--params"
            iet_arg5="Name=iqn.2018-04.com.sanuyi:target"+str(tid)
            process1 = subprocess.check_output(["ietadm", iet_arg1, iet_arg2,iet_arg3,iet_arg4,iet_arg5])
            sprint (process1,0)
    #sudo tgtadm --lld iscsi --op new --mode target --tid 1 -T iqn.2018-05.com.hiroom2:disk1
    #sudo tgtadm --lld iscsi --op new --mode target --tid 1 \
    #      -T iqn.2018-05.com.hiroom2:disk
        elif gTarget=="tgt":
            tgt_arg1="--lld"
            iser=True
            if (prot==iSER_Chap or prot==iSER_NoChap):
                tgt_arg2="iser"
            else:
                tgt_arg2="iscsi"
            tgt_arg3="--op"
            tgt_arg4="new"
            tgt_arg5="--mode"
            tgt_arg6="target"
            tgt_arg7="--tid"
            tgt_arg8=tid
            tgt_arg9="-T"
            tgt_arg10="iqn.2018-04.com.cheetah:vdisk"+str(tid)+VolName
            sprint ("tgt_arg10",tgt_arg10)
            process1 = subprocess.check_output(["tgtadm", tgt_arg1, tgt_arg2,tgt_arg3,tgt_arg4,tgt_arg5,tgt_arg6, tgt_arg7,tgt_arg8,tgt_arg9,tgt_arg10]).decode("utf-8")
            sprint (process1,0)
            return 0
    except Exception as err:
        sprint ("iSCSI_CreateTarget except error",err)
        return -1
        
def iSCSI_DeleteTarget(tid,prot):
#*
    try:
        if gTarget=="iet":
            iet_arg1="--op"
            iet_arg2="delete"
            iet_arg3="--tid="+str(tid)
            process1 = subprocess.check_output(["ietadm", iet_arg1, iet_arg2,iet_arg3])
            sprint (process1,0)
            return 0
        elif gTarget=="tgt":
    #       sudo tgtadm --lld iscsi --op delete --force --mode target --tid 1
            tgt_arg1="--lld"
            if (prot==iSER_Chap or prot==iSER_NoChap):
                tgt_arg2="iser"
            else:
                tgt_arg2="iscsi"
            tgt_arg3="--op"
            tgt_arg4="delete"
            tgt_arg5="--force"
            tgt_arg6="--mode"
            tgt_arg7="target"
            tgt_arg8="--tid"
            tgt_arg9=tid
            process1 = subprocess.check_output(["tgtadm", tgt_arg1, tgt_arg2,tgt_arg3,tgt_arg4,tgt_arg5,tgt_arg6, tgt_arg7,tgt_arg8,tgt_arg9]).decode("utf-8")
            sprint (process1,0)
            return 0
    except Exception as err:
        sprint ("iSCSI_DeleteTarget except error",err)
        return -1
        
def iSCSI_DeleteLun(tid,lun,prot):
#*
    try:
        if gTarget=="iet":
            iet_arg1="--op"
            iet_arg2="delete"
            iet_arg3="--tid="+str(tid)
            iet_arg4="--lun="+str(lun)
            process1 = subprocess.check_output(["ietadm", iet_arg1, iet_arg2,iet_arg3,iet_arg4])
            sprint (process1,0)
            return 0
        elif gTarget=="tgt":
    #       --lld <driver> --op delete --mode logicalunit --tid <id> --lun <lun>    
            tgt_arg1="--lld"
            if (prot==iSER_Chap or prot==iSER_NoChap):
                tgt_arg2="iser"
            else:
                tgt_arg2="iscsi"
            tgt_arg3="--op"
            tgt_arg4="delete"
            tgt_arg5="--mode"
            tgt_arg6="logicalunit"
            tgt_arg7="--tid"
            tgt_arg8=tid
            tgt_arg9="--lun"
            tgt_arg10=lun
            process1 = subprocess.check_output(["tgtadm", tgt_arg1, tgt_arg2,tgt_arg3,tgt_arg4,tgt_arg5,tgt_arg6, tgt_arg7,tgt_arg8,tgt_arg9,tgt_arg10]).decode("utf-8")
            sprint (process1,0)
            return 0
    except Exception as err:
        sprint ("iSCSI_DeleteLun except error",err)
        return -1
        
        
def iSCSI_CreateLun(tid,lun,device,serial,prot,rev):
#*
    global OEM

    try:
    
        if gTarget=="iet":
            iet_arg1="--op"
            iet_arg2="new"
            iet_arg3="--tid="+str(tid)
            iet_arg4="--lun="+str(lun)
            iet_arg5="--params"
            iet_arg6="Path=/dev/"+str(device)
            iet_arg7=",Type=fileio"
        #ietadm --op new --tid=[id] --lun=[lun] --params Path=/path/to/exported/file,Type=fileio
            process1 = subprocess.check_output(["ietadm", iet_arg1, iet_arg2,iet_arg3,iet_arg4,iet_arg5,iet_arg6])
            sprint (process1,0)
            return 0
        elif gTarget=="tgt":
    # sudo tgtadm --lld iscsi --op new --mode logicalunit --tid 1 --lun 1 \
    #     -b /var/lib/iscsi/disk
    #sanuyi@ubuntu:~$ sudo tgtadm --lld iscsi --op new --mode logicalunit --tid 1 --lun 1 -b /dev/mrp1/lv0
    #sudo tgtadm --lld iscsi --op new --mode logicalunit --tid 1 --lun 1 -b /dev/mrp1/lv1

            tgt_arg1="--lld"
            if (prot==iSER_Chap or prot==iSER_NoChap):
                tgt_arg2="iser"
            else:
                tgt_arg2="iscsi"
            tgt_arg3="--op"
            tgt_arg4="new"
            tgt_arg5="--mode"
            tgt_arg6="logicalunit"
            tgt_arg7="--tid"
            tgt_arg8=tid
            tgt_arg9="--lun"
            tgt_arg10=lun
            tgt_arg11="-b"
            tgt_arg12="/dev/"+device
            process1 = subprocess.check_output(["tgtadm", tgt_arg1, tgt_arg2,tgt_arg3,tgt_arg4,tgt_arg5,tgt_arg6, tgt_arg7,tgt_arg8,tgt_arg9,tgt_arg10,tgt_arg11,tgt_arg12]).decode("utf-8")
            sprint (process1,0)
            tgt_arg13="--params"
            vid="Cheetahraid"
            pid="prowler" #Fixup
            prev=rev
            scsi_sn=serial
            tgt_arg14='vendor_id='+vid+',product_id='+pid+',product_rev='+prev+',scsi_sn='+scsi_sn
            sprint (tgt_arg14,0)
            tgt_arg4="update"
            #tgtadm --lld iscsi --mode logicalunit --op update --tid 1 --lun 1 --params vendor_id=STGT_LV1,product_id=LV101,product_rev=0010,scsi_sn=STGTDVD01
            process1 = subprocess.check_output(["tgtadm", tgt_arg1, tgt_arg2,tgt_arg3,tgt_arg4,tgt_arg5,tgt_arg6, tgt_arg7,tgt_arg8,tgt_arg9,tgt_arg10,tgt_arg13,tgt_arg14]).decode("utf-8")
            sprint (process1,0)
            return 0
    except Exception as err:
        sprint ("iSCSI_CreateLun except error",err)
        return -1
        
        
def iSCSI_AddIP(tid,ipAdr,prot):
#*
    try:
#$ sudo tgtadm --lld iscsi --op bind --mode target --tid 1 -I ALL
        if gTarget=="iet":
            return(0)
            #sanuyi@ubuntu:~$ sudo tgtadm --lld iscsi --op bind --mode target --tid 1 -I ALL
        elif gTarget=="tgt":
            tgt_arg1="--lld"
            if (prot==iSER_Chap or prot==iSER_NoChap):
                tgt_arg2="iser"
            else:
                tgt_arg2="iscsi"
            tgt_arg3="--op"
            tgt_arg4="bind"
            tgt_arg5="--mode"
            tgt_arg6="target"
            tgt_arg7="--tid"
            tgt_arg8=tid
            tgt_arg9="-I"
            tgt_arg10=ipAdr
            process1 = subprocess.check_output(["tgtadm", tgt_arg1, tgt_arg2,tgt_arg3,tgt_arg4,tgt_arg5,tgt_arg6, tgt_arg7,tgt_arg8,tgt_arg9,tgt_arg10]).decode("utf-8")
            sprint (process1,0)
            return(0)
    except Exception as err:
        sprint ("iSCSI_AddIP except error",err)
        return -1
        
def iSCSI_DeleteIP(tid,ipAdr,prot):
#*
    try:
        if gTarget=="iet":
            return(0)
    #--lld <driver> --op unbind --mode target --tid <id> --initiator-address <address>
    #Delete the address from the access lists of the target with <id>        
        elif gTarget=="tgt":
            tgt_arg1="--lld"
            if (prot==iSER_Chap or prot==iSER_NoChap):
                tgt_arg2="iser"
            else:
                tgt_arg2="iscsi"
            tgt_arg3="--op"
            tgt_arg4="unbind"
            tgt_arg5="--mode"
            tgt_arg6="target"
            tgt_arg7="--tid"
            tgt_arg8=tid
            tgt_arg9="--initiator-address"
            tgt_arg10=ipAdr
            process1 = subprocess.check_output(["tgtadm", tgt_arg1, tgt_arg2,tgt_arg3,tgt_arg4,tgt_arg5,tgt_arg6, tgt_arg7,tgt_arg8,tgt_arg9,tgt_arg10]).decode("utf-8")
            sprint (process1,0)
            return 0
    except Exception as err:
        sprint ("iSCSI_DeleteIP except error",err)
        return -1
        
        
def iSCSI_AddChapUser(tid,name,password,prot):
#sudo ietadm --op new --tid=1 --user --params=incominguser=wo,Password=hello123hello123
#*
    try:
        if gTarget=="iet":
            iet_arg1="--op"
            iet_arg2="new"
            iet_arg3="--tid="+str(tid)
            iet_arg4="--user"
            #iet_arg5=""
            iet_arg6="--params=incominguser="+name+",password="+password
            iet_arg7=",password="+password
            process1 = subprocess.check_output(["ietadm", iet_arg1, iet_arg2,iet_arg3,iet_arg4,iet_arg6]).decode("utf-8")
            sprint (process1,0)
            return 0
    # tgtadm --lld iscsi --mode account --op new --user ''consumer'' --password ''Longsw0rd''
    # tgtadm --lld iscsi --mode account --op bind --tid 1 --user ''consumer''
        elif gTarget=="tgt":
            tgt_arg1="--lld"
            if (prot==iSER_Chap or prot==iSER_NoChap):
                tgt_arg2="iser"
            else:
                tgt_arg2="iscsi"
            tgt_arg3="--mode"
            tgt_arg4="account"
            tgt_arg5="--op"
            tgt_arg6="new"
            tgt_arg7="--user"
            tgt_arg8=name
            tgt_arg9="--password"
            tgt_arg10=password
            process1 = subprocess.check_output(["tgtadm", tgt_arg1, tgt_arg2,tgt_arg3,tgt_arg4,tgt_arg5,tgt_arg6, tgt_arg7,tgt_arg8,tgt_arg9,tgt_arg10]).decode("utf-8")
            tgt_arg6="bind"
            tgt_arg7="--tid"
            tgt_arg8=tid
            tgt_arg9="--user"
            tgt_arg10=name
            process1 = subprocess.check_output(["tgtadm", tgt_arg1, tgt_arg2,tgt_arg3,tgt_arg4,tgt_arg5,tgt_arg6, tgt_arg7,tgt_arg8,tgt_arg9,tgt_arg10]).decode("utf-8")
            sprint (process1,0)
            return 0
    except Exception as err:
        sprint ("iSCSI_AddChapUser except error",err)
        return -1

def iSCSI_DeleteChapUser(tid,name,prot):
#*
    try:
        if gTarget=="iet":
            iet_arg1="--op"
            iet_arg2="delete"
            iet_arg3="--tid="+str(tid)
            iet_arg4="--params=InComingUser="+name
            process1 = subprocess.check_output(["ietadm", iet_arg1, iet_arg2,iet_arg3,iet_arg4]).decode("utf-8")
            sprint (process1,0)
            return 0
#--lld <driver> --op unbind --mode target --tid <id> --initiator-name <name>
#Delete the initiator's name from the access lists of the target with <id>.
#--lld <driver> --op unbind --mode target --tid <id> --initiator-name <name>

        elif gTarget=="tgt":
            tgt_arg1="--lld"
            if (prot==iSER_Chap or prot==iSER_NoChap):
                tgt_arg2="iser"
            else:
                tgt_arg2="iscsi"
            tgt_arg3="--op"
            tgt_arg4="unbind"
            tgt_arg5="--mode"
            tgt_arg6="target"
            tgt_arg7="--tid"
            tgt_arg8=tid
            tgt_arg9="--initiator-name"
            #tgt_arg9="-Q"
            tgt_arg10=name
            process1 = subprocess.check_output(["tgtadm", tgt_arg1, tgt_arg2,tgt_arg3,tgt_arg4,tgt_arg5,tgt_arg6, tgt_arg7,tgt_arg8,tgt_arg9,tgt_arg10]).decode("utf-8")
            sprint (process1,0)
            return 0
    except Exception as err:
        sprint ("iSCSI_DeleteChapUser except error",err)
        return -1
        
def iSCSI_ShowChapUsers(tid):
#*
    try:
    
        iet_arg1="--op"
        iet_arg2="show"
        iet_arg3="--tid="+str(tid)
        iet_arg4="--user"
        iet_arg5="--params=InComingUser"
        #sudo ietadm --op show --tid=2 --user --params=IncomingUser=wo1
        process1 = subprocess.check_output(["ietadm", iet_arg1, iet_arg2,iet_arg3,iet_arg4,iet_arg5])
        sprint (process1,0)
        
    except Exception as err:
        sprint ("iSCSI_ShowChapUsers except error",err)
        
        
def iSCSI_ShowChapUser(tid,name):
    try:
        iet_arg1="--op"
        iet_arg2="show"
        iet_arg3="--tid="+str(tid)
        iet_arg4="--user"
        iet_arg5="--params=InComingUser="+name
        #sudo ietadm --op show --tid=2 --user --params=IncomingUser=wo1
        process1 = subprocess.check_output(["ietadm", iet_arg1, iet_arg2,iet_arg3,iet_arg4,iet_arg5])
        sprint (process1,0)
    
    except Exception as err:
        sprint ("iSCSI_ShowChapUsers except error",err)
        
#sudo tgtadm --lld iscsi --mode target --op show

def tgtVol_DeleteLun(pool,VolName,prot):
    try:
        if StorageBackend=="zfs":
            ls_arg1="-l"
            ls_arg2="/dev/zvol/"+pool+"/"+VolName
            process1 = subprocess.check_output(["ls", ls_arg1, ls_arg2]).decode("utf-8")
            my_len= len(process1)
            my_index= process1.find("zd",0,my_len)
            Zdevice=str(process1[my_index : (my_len-1)])
            my_device="/dev/"+Zdevice
        if StorageBackend=="LVM":
            my_device="/dev/"+pool+"/"+VolName
            
        sprint ("my_device",my_device)
        tgt_arg1="--lld"
        if (prot==iSER_Chap or prot==iSER_NoChap):
            tgt_arg2="iser"
        else:
            tgt_arg2="iscsi"
        tgt_arg3="--mode"
        tgt_arg4="target"
        tgt_arg5="--op"
        tgt_arg6="show"
        process1 = subprocess.check_output(["tgtadm", tgt_arg1, tgt_arg2,tgt_arg3,tgt_arg4,tgt_arg5,tgt_arg6]).decode("utf-8")
        #print process1
        process_output= process1.splitlines()
        #print process_output        
        try:
            for line in process_output:
                lineNWS=line.strip()
                #print lineNWS
                if "Target" in lineNWS:
                    target= lineNWS
                    #print target
                if "LUN" in lineNWS:
                    lun=lineNWS
                    #print lun
                if lineNWS.startswith("Backing store path:"):
                    list1=lineNWS.split(":")
                    device=list1[1].strip()
                    if device==my_device:
                        msg=target+lun+device
                        sprint ("Found tgt Device",msg)
                        list1=target.split(":")
                        tid= list1[0].replace('Target','')
                        list1=lun.split(":")
                        lun=list1[1]
                        sprint ("tid=",int(tid))
                        sprint ("lun=",int(lun))
                        iSCSI_DeleteLun(tid,lun,prot)
                        iSCSI_DeleteTarget(tid,prot)
                        stackTID=int(tid)
                        DB_FreeTid(stackTID)

        except Exception as err:
           sprint ("tgtVol_DeleteLun except1",err)
           
    except Exception as err:
        sprint ("tgtVol_DeleteLun except2 ",err)
        
def iSCSI_Show(prot):
#*
    tgt_arg1="--lld"
    if (prot==iSER_Chap or prot==iSER_NoChap):
        tgt_arg2="iser"
    else:
        tgt_arg2="iscsi"
    tgt_arg3="--mode"
    tgt_arg4="target"
    tgt_arg5="--op"
    tgt_arg6="show"
    #sudo tgtadm --lld iscsi --mode target --op show
    process1 = subprocess.check_output(["tgtadm", tgt_arg1, tgt_arg2,tgt_arg3,tgt_arg4,tgt_arg5,tgt_arg6]).decode("utf-8")
    sprint (process1,0)

def DB_updateDisk(name,location,pid,vid,prl,serial,d_id,state):
    #query=c.execute("select id from volume where name ='{}".format(VolName)+"'")
    #VolID=c.fetchone()[0]
    sprint ("DB_updateDisk",0)
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    system_name=str(d_id)
    sprint ("query=","select id from disks where serial=")
    query=c.execute("select id from disks where serial='{}".format(serial)+"'")
    DiskId=c.fetchone()[0]
    sprint ("DiskId=",DiskId)
    e_date=datetime.datetime.now()
    if DiskId!=str("None"):
        sprint ("Update Serial=" , str(serial))
        query=c.execute("update disks set system_name=?,name=?,state=?,d_id=?,location=?,vid=?,pid=?,prl=?, edit_date=? where serial=?",\
        [system_name,name,state,d_id,location,vid,pid,prl,e_date,serial])
    else:
        sprint ("Create Serial=", str(serial))
        query=c.execute("insert into disks(system_name,name,state,d_id,location,vid,pid,prl,serial,cr_date) values(?,?,?,?,?,?,?,?,?,datetime())",\
        [system_name,name,state,d_id,location,vid,pid,prl,serial]) 
    conn.commit()
    c.close()
    conn.close()
    return 0

def DB_GetVolList(pool,protocol):
   
    if (protocol==iSCSI_Chap):
        GlobalVolList=['vola', 'volb', 'volc', 'vold']
    if (protocol==CIFS):
        GlobalVolList=['cifs5']
    return GlobalVolList

def DB_GetLunByVol(VolName):
    if (VolName=="vola"):
        return 0
    if (VolName=="volb"):
        return 1
    if (VolName=="volc"):
        return 2
    if (VolName=="vold"):
        return 3        
    return 1

def DB_FreeTid(tid):
    global gTID
    global tidStack
    global stackCnt
    tidStack.append(tid)
    gTID=tid
    cnt=stackCnt
    stackCnt=cnt-1 
    sprint ("push stackCnt",stackCnt+tid)

    
def DB_GetTid():
    global gTID
    global tidStack
    global stackCnt    
    tid=tidStack.pop()
    gTID=tid
    cnt=stackCnt
    stackCnt=cnt+1
    sprint ("pop stackCnt",str(stackCnt)+str(tid))
    return tid

def DB_GetTidByVol(VolName):
    global gTID
    global tidStack
    #tid=gTID
    #tid=tid+1
    tid=tidStack.pop()
    gTID=tid
    stackCnt=stackCnt+1
    sprint("GTID",gTID)
    return tid
        
def DB_GetIQNByVol(VolName):
    try:
        null="null"
        NullRsp=-1
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        query=c.execute("select id from volume where name ='{}".format(VolName)+"'")
        resp=c.fetchone()
        if str(resp) == str("None"):
            sprint ("No VolID",0)
            return NullRsp,null
        else:
            VolID=resp[0]
            sprint ("VolID=",str(VolID))

        query=c.execute("select host_id from export where vol_id='{}".format(VolID)+"'")
        for val in c:
            HostID = val[0]
            sprint ("HostID=" , str(HostID))

        query=c.execute("select iqn from host where id='{}".format(HostID)+"'")
        resp=c.fetchone()
        if str(resp) == str("None"):
            sprint ("No Host Name",0)
            return NullRsp,null
        else:
            iqn=resp[0]
        c.close()
        conn.close()
        return 0,iqn
    except Exception as err:
        sprint("DB_GetIQNByVol except ",err)
        return NullRsp,null

def DB_GetUsersByVol(VolName):

    try:
        NullRsp=-1
        UserList=[[]]
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        query=c.execute("select id from volume where name ='{}".format(VolName)+"'")
        resp=c.fetchone()
        if str(resp) == str("None"):
            sprint ("No VolID",0)
            c.close()
            conn.close()
            return NullRsp
        else:
            VolID=resp[0]
            sprint ("VolID=" , str(VolID))
        #if query:
        #c.close()
        #c=conn.cursor()
        #Get the list of exports mapped to zvol
        #query_lan=c.execute("select count(*) from export where vol_id='{}".format(VolID)+"'")
        #nameCount = c.fetchone()[0]
        #HostName="@eng"
        query=c.execute("select host_id, port_id from export where vol_id='{}".format(VolID)+"'")
        for val in c:
            HostID = val[0]
            PortID = val[1]
            sprint ("PortID=" , str(PortID))
            sprint ("HostID=" , str(HostID))

            #else:
            #print "No HostID for vol_id=" +  str(VolID)
        query=c.execute("select name from host where id='{}".format(HostID)+"'")
        resp=c.fetchone()
        if str(resp) == str("None"):
            sprint ("No Host Name",0)
            c.close()
            conn.close()
            return NullRsp
        else:
            HostName=resp[0]
            sprint ("Host Name x",HostName)
        if HostName[0]=='@': 
            sprint ("this is a group=",HostName[1:])
            query=c.execute("select id from OrgGroup where name='{}".format(HostName[1:])+"'")
            resp=c.fetchone()
            if str(resp) == str("None"):
                sprint ("Err No GroupID",0)
                c.close()
                conn.close()
                return NullRsp
            GroupID=resp[0]
            sprint ("GroupID=", str(GroupID))
            #select person_id from UserLink where group_id=1;
            query=c.execute("select person_id from UserLink where group_id='{}".format(GroupID)+"'")
            resp=c.fetchone()
            if str(resp) == str("None"):
                sprint ("Err No person_id",0)
                c.close()
                conn.close()
                return NullRsp
            person_id=resp[0]
            query=c.execute("select userName, password from Person where id='{}".format(person_id)+"'")
            #select userName, password from user where GroupId=4;
            #select Username,password from Person where id=2;
            
            i=0;
            for val in c:
                User = val[0]
                PW = val[1]
                UserList[i].append(User)
                UserList[i].append(PW)
                i=i+1
        else:
            query=c.execute("select user_name, pw from host where id='{}".format(HostID)+"'")
            resp=c.fetchone()
            #print "User",resp[0]
            #print "PW",resp[1]
            UserList[0]=resp
            #rsp=UserList[0]
            #print "User1",rsp[0]
            #print "PW1",rsp[1]
            #serList[0].append(PW)
        sprint ("UserList=",UserList)
        c.close()
        conn.close()
        return UserList
        
    except Exception as err:
        sprint("DB_GetUsersByVol ",err)
        c.close()
        conn.close()
        return NullRsp

def PowerOnOff(action):
        try:
            #sudo ./set-power all off
            #sudo ./set-power all on
            powerCtrl="./set-power"
            arg1="all"
            arg2=action
            sprint ("powerCtrl action ", arg1+arg2)
            process1 = subprocess.check_output([powerCtrl, arg1,arg2])
            return (0)
        except Exception as err:
            sprint("powerCtrl except ",err)
            return (-3)

def PoolStop(PoolName, PoolSystemName,PowerAction):
#1) SetDevicesOnOff('off') #this stops the storage manager import
#2) SetVolumesOnOff('off') #this stops the export
#3) #sudo umount /mnt/system (this stores canister metadata)
#4) QuiescePools(True) #This quiesces all the running pools
#5) Flush controller disk and controller cache
#6) sync all RAIDS #This flushes any cached data
#7) drop_caches #Flush all OS caches
#8) set hidden=on #This sets the controller RAID attribute to hidden (i.e the device is removed from the OS)
#9) Remove Power from backplane

    storcli="/opt/MegaRAID/storcli/storcli64"
    LogLevel=20
    logMsg="Stopping Volumes and Pools"
    CCM_Alert(ccmINFO,LogLevel,logMsg)
    msg=str(str(PoolName)+str(PoolSystemName)+str(PowerAction))
    sprint ("Pool Stop",msg)
    try:
        logMsg="Stopping Volumes, set to OFF"
        CCM_Alert(ccmINFO,LogLevel,logMsg)
        SetDevicesOnOff('off')
        SetVolumesOnOff('off','c0')
        SetVolumesOnOff('off','c1')
        SetVolumesOnOff('off','c2')
        try:
            #sudo umount /mnt/system
            arg1="/mnt/system"
            logMsg="Unmounting volume="+arg1
            CCM_Alert(ccmINFO,LogLevel,logMsg)
            sprint ("umount", arg1)
            process1 = subprocess.check_output(['umount', arg1])
            sprint (process1,0)
            sprint ("rm -rf ", arg1)
            arg2='-rf'
            process1 = subprocess.check_output(['rm',arg2,arg1])
            sprint (process1,0)
            time.sleep(2)
        except Exception as err:
            logMsg="Unmounting failed, volume="+arg1
            CCM_Alert(ccmINFO,LogLevel,logMsg)
            sprint("umount except ",err)

        QuiescePools(True)
        logMsg="dropping all caches "
        CCM_Alert(ccmINFO,LogLevel,logMsg)
        logMsg="Quiesced all Pools "
        CCM_Alert(ccmINFO,LogLevel,logMsg)
        try:
            #sudo /opt/MegaRAID/storcli/storcli64 /c0 flushcache
            logMsg="Flushing controller and disk cache "
            CCM_Alert(ccmINFO,LogLevel,logMsg)
            arg1="/c0"
            arg2="flushcache"
            sprint ("storcli", arg1+arg2)
            process1 = subprocess.check_output([storcli, arg1,arg2])
            sprint (process1,0)
            time.sleep(1)
        except Exception as err:
            sprint("storcli Flush Cache except ",err)
            logMsg="Flushing controller and disk cache failed"
            CCM_Alert(ccmCRITICAL,LogLevel,logMsg)
            
        try:
            #sudo /opt/MegaRAID/storcli/storcli64 /c0/vall set hidden=on
            logMsg="Set controller volumes to hidden "
            CCM_Alert(ccmINFO,LogLevel,logMsg)
            arg1="/c0/vall"
            arg2="set"
            arg3="hidden="
            arg4="on"
            sprint ("storcli", arg1+arg2+arg3+arg4)
            process1 = subprocess.check_output([storcli, arg1,arg2,arg3,arg4])
            sprint (process1,0)
            time.sleep(1)
        except Exception as err:
            logMsg="Set controller volumes to hidden failed"
            CCM_Alert(ccmINFO,LogLevel,logMsg)
            sprint("storcli hidden except ",err)

        try:
            if PowerAction=='none':
                return (0)
            elif PowerAction=='off':
                logMsg="Removing Power to Backplane "
                CCM_Alert(ccmINFO,LogLevel,logMsg)
                sprint (logMsg,0)
                PowerOnOff('off')
            elif PowerAction=='on':
                logMsg="Turning On Power to Backplane"
                CCM_Alert(ccmINFO,LogLevel,logMsg)
                sprint (logMsg,0)
                PowerOnOff('on')
            return (0)
        except Exception as err:
            logMsg="powerCtrl OFF except "
            CCM_Alert(ccmCRITICAL,LogLevel,logMsg)
            sprint(logMsg,err)
            return (-3)
    except Exception as err:
        logMsg="Pool Stop except "
        CCM_Alert(ccmCRITICAL,LogLevel,logMsg)
        sprint(logMsg,err)
        return (-4)

    return (0)

def PoolUpdate(PoolName, zfsCompression, zfsAcceleration, zfsDedup):
    sprint ("Pool Update",0)

def CheckZFSvols(PoolSystemName):
    PoolPath="/"+PoolSystemName+"/"
    process1 = subprocess.check_output(["ls", PoolPath])
    vols=process1.split()
    NbVols=len(vols)
    sprint ("NBvols=",NbVols)
    if NbVols !=0:
        return wErrPoolInUse
    else:
        return 0


def CheckPool(PoolSystemName):
    sprint ("CheckPool=",PoolSystemName)
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    query=c.execute("select id from multi_device where system_name='{}".format(PoolSystemName)+"'")
    resp = c.fetchone()
    sprint ("resp=",resp)
    if resp!=None:
        PoolID=resp[0]
    #get the pool_id
    #check if vols using this id
    type='Native'
#    query=c.execute("select count(*) from volume where type=Native and multi_device_id='{}".format(PoolID)+"'")
    query=c.execute("select count(*) from volume where multi_device_id='{}".format(PoolID)+"'")
    count = c.fetchone()[0]
    sprint ("Vol count=",count)
    cnt=int(count)
    if cnt ==0:
        if StorageBackend=="zfs":
            cnt=CheckZFSvols(PoolSystemName)
            if cnt ==0:
                return 0
            else:
                return wErrPoolInUse
        else:
            return 0
    else:
        return wErrVolumeInUse

def getLVMbyIdDisks(pool):
        LVM_arg1="-C"
        LVM_arg2="--noheadings"
        LVM_arg3="--reportformat"
        LVM_arg4="json"
        PVlist=[]
        #mega
        #pvdisplay 
        process1 = subprocess.check_output(["pvdisplay",LVM_arg1,LVM_arg2,LVM_arg3,LVM_arg4])
        #print(process1)
        y = json.loads(process1)
        NbPv= len(y['report'][0]['pv'])
        i=0
        sprint ("NbPv",NbPv)
        while (i < NbPv):
            if str(y['report'][0]['pv'][i]['vg_name'])==pool:
                sprint ("PV found for pool=",pool)
                dev=str(y['report'][0]['pv'][i]['pv_name'])
                PVlist.append(dev)
            i=i+1
        sprint ("PVlist",PVlist)
        i=0
        return 0,PVlist

def PoolDelete(PoolName,PoolSystemName):
    sprint ("Pool Delete",PoolName)
    sprint ("Pool Delete",PoolSystemName)
    ret=CheckPool(PoolSystemName)
    if ret !=0:
        return ret

    if StorageBackend=="zfs":
        zfs_cmd='destroy'
        try:
            process1 = subprocess.check_output(["zpool", zfs_cmd, PoolSystemName])
            sprint (process1,0)
            res=DB_PoolDelete(PoolSystemName)
            return res
        except Exception as err:
            sprint ("Pool delete failed=",PoolSystemName)
            sprint ("Error=",err) 
            return wErrCommandFailed
            
    elif StorageBackend=="LVM":
        try:
            DeleteSystemVol(PoolSystemName)
            list=getLVMbyIdDisks(PoolSystemName)
            LVM_arg1="-q"
            LVM_arg2="-ff"
            sprint ("VG Remove",PoolSystemName)
            #sudo vgremove -q -ff pa
            process1 = subprocess.check_output(["vgremove",LVM_arg1,LVM_arg2,PoolSystemName])
            sprint (process1,0)
        except Exception as err:
            sprint("vgremove except ",err)
            sprint ("Pool delete failed=",PoolSystemName)
            sprint ("Error=",err)  
            #return wErrCommandFailed
        try:
            if list[0] !=0:
                sprint ("getLVMbyIdDisks Failed",0)
                return -1
            byIdList=list[1]
            for dev in byIdList:
                LVM_arg1=dev
                LVM_arg2="-v"
                LVM_arg3="-ff"
                msg=LVM_arg1+" "+LVM_arg2+" "+LVM_arg3
                #sudo pvremove /dev/sdb -v -ff
                sprint ("pvremove args=",msg)
                try:
                   process1 = subprocess.check_output(["pvremove",LVM_arg1,LVM_arg2,LVM_arg3])
                   sprint (process1,0)
                   sprint("zero RAID=",LVM_arg1)    
                   arg1="if=/dev/zero"
                   arg2="of="+LVM_arg1
                   arg3="count=100"
                   arg4="bs=1M"
                   process = subprocess.check_output(["dd",arg1,arg2,arg3,arg4])
                   #sudo wipefs -a /dev/sdc  #WO check is this required please
                except Exception as err:
                   sprint("pvremove except ",err)
        except Exception as err:
            sprint("PV remove except ",err)
            sprint ("Error=",err)   
            #return -1
        try:
            #########################HACK#####################
            PoolName="MegaRAID"
            sprint ("Check MegaRAID delete",PoolName)
            if PoolName=="MegaRAID":
                volSize='0'
                action='d'
                level='raid0'
                val=MegaRaidVol(action, PoolSystemName,volSize,level)
                if ((val[0]==0) or (val[0]==-2)):
                    sprint("MegaRaidVol Delete OK",val)
                else:
                    sprint("MegaRaidVol Delete NOT OK",val)
                    return -1
            res=DB_PoolDelete(PoolSystemName)
            try:
            #sudo umount /mnt/system
                arg1="/mnt/system"
                logMsg="Unmounting volume="+arg1
                LogLevel=20
                CCM_Alert(ccmINFO,LogLevel,logMsg)
                sprint ("umount", arg1)
                process1 = subprocess.check_output(['umount', arg1])
                sprint (process1,0)
                sprint ("rm -rf ", arg1)
                arg2='-rf'
                process1 = subprocess.check_output(['rm',arg2,arg1])
                sprint (process1,0)
                time.sleep(2)
            except Exception as err:
                logMsg="Unmounting failed, volume="+arg1
                CCM_Alert(ccmINFO,LogLevel,logMsg)
                sprint("umount except ",err)
            BackUpDB2SystemVolume()
            return res                
        except Exception as err:
            print(("MegaRaidVol Delete except ",err))
            return -1

#{
#   "blockdevices": [
#      {"name": "fd0", "wwn": null, "mountpoint": null},
#      {"name": "sda", "wwn": "0x50014ee001ff8839", "mountpoint": null,
#         "children": [
#            {"name": "sda1", "wwn": "0x50014ee001ff8839", "mountpoint": "/"}
#         ]
#      },
#      {"name": "sdb", "wwn": "0x5000c5002dbf3b9f", "mountpoint": null},
#      {"name": "sdc", "wwn": "0x5000c500200e601b", "mountpoint": null},
#      {"name": "sde", "wwn": "0x600062b2025386c0280f5f2ca7a0aa0a", "mountpoint": null}
#   ]
#}
def GetAllocatedDisks(PVlist):
    try:
        LVM_arg1="-C"
        LVM_arg2="--noheadings"
        LVM_arg3="--reportformat"
        LVM_arg4="json"
        #sudo pvdisplay -C --noheadings --reportformat json
        process1 = subprocess.check_output(["pvdisplay",LVM_arg1,LVM_arg2,LVM_arg3,LVM_arg4])
        #print(process1)
        y = json.loads(process1)
        NbPv= len(y['report'][0]['pv'])
        i=0
        sprint ("NbPv",NbPv)
        while (i < NbPv):
            pool=str(y['report'][0]['pv'][i]['vg_name'])
            sprint ("GetAllocatedDisks vg_name",pool)
            sprint ("GetAllocatedDisks vg_name len",len(pool))
            if pool !="":
                dev=str(y['report'][0]['pv'][i]['pv_name'])
                PVlist.append(dev)
            i=i+1
        sprint ("PVlist",PVlist)
        return 0
    except Exception as err:
        sprint("GetAllocatedDisks except ",err)
        return -1

def getMegaRaidDisk():
    dev="null"
    wwn="null"
    #FreeDisks=AllDisks-LVM configured Disks
    AllocatedDisks=[]
    Vendor="BROADCOM"
    GetAllocatedDisks(AllocatedDisks)
    sprint ("Allocated Disks",AllocatedDisks)
    try:
        # lsblk -o NAME,WWN,VENDOR,SIZE -J
        arg1="-o"
        arg2="NAME,WWN,VENDOR,SIZE"
        arg3="-J"
        process1 = subprocess.check_output(["lsblk",arg1,arg2,arg3])
        y = json.loads(process1)
        sprint (y,0)
        NbDisk= len(y['blockdevices'])
        sprint ("NbDisk",NbDisk)
        i=0
        while (i < NbDisk):
            dev=str(y['blockdevices'][i]['name'])
            CheckDev="/dev/"+dev
            sprint ("Check disk in allocated disks",CheckDev)
            if str("/dev/"+dev) not in AllocatedDisks:
                wwn=y['blockdevices'][i]['wwn']
                disk_size=y['blockdevices'][i]['size']
                vendor=str(y['blockdevices'][i]['vendor'])
                sprint ("Check Vendor",CheckDev)
                if vendor== "BROADCOM":
                    sprint ("getMegaRaidDisk",dev+" "+wwn+" "+vendor+" "+disk_size)
                    str_len=len(disk_size)
                    if disk_size.find("G",0,str_len) !=-1:
                        size=float(disk_size.replace('G', ''))
                    elif disk_size.find("T",0,str_len) !=-1:
                        size=disk_size.replace('T', '')
                        size=float(size)*1000
                    Isize=int(size)
                    sprint ("Disk size",int(Isize))
                    return 0,str("/dev/"+dev),"/dev/disk/by-id/wwn-"+str(wwn), int(Isize)
            i=i+1
        return -1,dev,wwn 
    except Exception as err:
        sprint("getMegaRaidDisk except ",err)
        return -1,dev,wwn,0 

def GetFreeDisks(selector,zfsDisk,rota,poolname=None):
    FreeDisks=[]
    disk_size=0
    size=0
    zfs_disk_size=0
    #try:
        #disk='/dev/disk/by-id/'+zfsDisk
        #cmd = ["sudo", "fdisk",'-s', disk]
        #sudo fdisk -s /dev/disk/by-id/wwn-0x50014ee05781587c
        #output = subprocess.check_output(cmd, text=True)
        #zfs_disk_size=int(output)
        #zfs_disk_size=zfs_disk_size+1
        #print ('zfs disk size',zfs_disk_size)
    #except Exception as err:
    #    print(("GetFreeDisks except",err))
    #    zfs_disk_size=0   
                              #BUG we need to improve this by having the max disk size needed of the pool.
    try:
        #output = subprocess.check_output(cmd, text=True)
        zfs_disk_size=0 
        ZFSdisklist=[]
        zfs_status = get_zpool_status()
        print ('zpool status',zfs_status)
        for mypool,status in zfs_status.items():
            pool = status["pool"]  
            print ('status',mypool,status)
            pool_state = status["pool_state"]
            disks = status["disks"]
            disk_type=status["disk_type"]
            #print(pool_state)
            #print('zfs disk list',disks)
            #print('zfs disk type',disk_type)
            for disk in disks:
                ZFSdisklist.append(disk['disk'])

        #selector = disk_type
        if selector=='scsi':
            choice='name'
        elif selector=='wwn':
            choice='wwn'
        elif selector=='ata':
            choice='name'               
        elif selector=='nvme':
            choice='name'
        else:
            choice='wwn'
        check=True
        if check==True:
                nb_ZFSdisks=len(ZFSdisklist)
                print ('ZFS disklist',nb_ZFSdisks,ZFSdisklist)
                print ('Getting Free disks',choice,selector)
                allDisks=get_drive_by_id_dict(mode=choice,selector=selector)
                ad=dict(allDisks)
                print ('allDisks',ad)
                free=True
                if len(ad)==0:
                    return (-1,FreeDisks,size)
                for k,v in ad.items():
                    free=True
                        #print ('disk /dev/=',k,v)
                    for zdisk in ZFSdisklist:
                        print ('zdisk / disk',zdisk,v)
                        if v  == zdisk:
                            print ('found',zdisk)
                            free=False
                            break
                    if free==True:
                        #sudo fdisk -s /dev/disk/by-id/wwn-0x50014ee05781587c
                        disk='/dev/disk/by-id/'+v
                        #lsblk -o NAME,MODEL,SERIAL,ROTA,SIZE /dev/disk/by-id/wwn-0x50014ee05781587c
                        cmd = ["sudo", "lsblk",'-o','NAME,MODEL,SERIAL,ROTA,SIZE', disk, '-J']
                        print ('cmd=',cmd)
                        output = subprocess.check_output(cmd, text=True)
                        i=0
                        y = json.loads(output)
                        print('y=',y)
                        name=str(y['blockdevices'][i]['name'])
                        D_rota=y['blockdevices'][i]['rota']
                        print ("name",name)
                        print ('rota',D_rota)
                        DiskSize=str(y['blockdevices'][i]['size'])
                        sprint ("Disk Size=",DiskSize)
                        if DiskSize.find('M') != -1:
                            s=DiskSize.replace('M', '')
                            Dsize=float(s)
                        elif DiskSize.find('G') != -1:
                            s=DiskSize.replace('G', '')
                            Dsize=float(s)
                            Dsize=Dsize*1000
                        elif DiskSize.find('T') != -1:
                            s=DiskSize.replace('T', '')
                            Dsize=float(s)
                            Dsize=Dsize*1000*1000
                        disk_size=int(Dsize)
                        try:
                            process = subprocess.check_output(["sg_turs", disk,"-n1"])
                            print ('tur ok=',disk,process)
                            tur='OK'
                        except:    
                            print ('tur not OK=',process)
                            tur='NOK'
                            
                        print ("Disk Size",disk_size,zfs_disk_size,str(rota),str(D_rota))
                        #disk_size=int(output)/(1048591)
                        if disk_size >= zfs_disk_size and str(D_rota)==str(rota) and tur=='OK':
                            print ('zfs_disk_size:disk size:rota',zfs_disk_size,disk_size,rota)
                            FreeDisks.append(disk)
                            size=size+disk_size
                            #break

        return (0,FreeDisks,int(size))     
        print('ZFS Free disks=',-1)   
        if free==True:
            return (0,FreeDisks,int(size))
        else:
            print('No ZFS Free disk',-1)        
            return (-1,FreeDisks,int(size))
    except Exception as err:
        print(("GetFreeDisks except 2",err))
        return (-1,FreeDisks,int(size)) 
   

def getPVdisksToUse():
    list=[]
    return -1,list

def getPVdisks():

    LVM_arg1="-C"
    LVM_arg2="--noheadings"
    LVM_arg3="--reportformat"
    LVM_arg4="json"
    PVlist=[]
    #sudo pvdisplay -C --noheadings --reportformat json
    try:    
        process1 = subprocess.check_output(["pvdisplay",LVM_arg1,LVM_arg2,LVM_arg3,LVM_arg4])
        #print(process1)
        y = json.loads(process1)
        NbPv= len(y['report'][0]['pv'])
        i=0
        sprint ("NbPv",NbPv)
        while (i < NbPv):
            dev=str(y['report'][0]['pv'][i]['pv_name'])
            vg=str(y['report'][0]['pv'][i]['vg_name'])
            if vg != None:
                PVlist.append(dev)
            i=i+1
        sprint ("PVlist",PVlist)
        return 0,PVlist
    except Exception as err:
        sprint("pvdisplay except 2 ",err)
        return -1,PVlist

def getlvList():
    lvList=[]
    try:
        LVM_arg1="-C"
        LVM_arg2="--noheadings"
        LVM_arg3="--reportformat"
        LVM_arg4="json"
        process1 = subprocess.check_output(["lvdisplay",LVM_arg1,LVM_arg2,LVM_arg3,LVM_arg4])
        #sudo lvdisplay -C --noheadings --reportformat json
        sprint(process1,0)
        y = json.loads(process1)
        NbLv= len(y['report'][0]['lv'])
        i=0
        sprint ("NbLv",NbLv)
        while (i < NbLv):
            lvname=(y['report'][0]['lv'][i]['lv_name'])
            vgname=(y['report'][0]['lv'][i]['vg_name'])
            sprint ("lv name",lvname)
            sprint ("vg name",vgname)
            report=False
            if report==True:
                sprint(y['report'][0]['lv'][i]["lv_attr"],0)
                sprint(y['report'][0]['lv'][i]["lv_size"],0)
                sprint(y['report'][0]['lv'][i]["pool_lv"],0)
                sprint(y['report'][0]['lv'][i]["origin"],0)
                sprint(y['report'][0]['lv'][i]["data_percent"],0)
                sprint(y['report'][0]['lv'][i]["metadata_percent"],0)
                sprint(y['report'][0]['lv'][i]["move_pv"],0)
                sprint(y['report'][0]['lv'][i]["mirror_log"],0)
                sprint(y['report'][0]['lv'][i]["copy_percent",0])
                sprint(y['report'][0]['lv'][i]["convert_lv"],0)
            lvList.append(str(lvname))
            i=i+1
        return (0,lvList)
    except Exception as err:
        sprint("lvdisplay except ",err)
        return (-1,lvList)

def getZFSdisks():
    ZFSlist=[]
    return ZFSlist
def PoolCreate (PoolName, PoolSize,PoolLevel, zfsCompression, zfsAcceleration, zfsDedup,PoolAccelerationStorage,PoolSystemName,Encryption,location,PerCent):

    sprint ("PoolCreate","step1")
    if PoolName == MegaRAID:
        UseList=[]
        sprint ("VG create",0)
        action='c'
        sprint ("PoolLevel=",PoolLevel)
        raid_level="raid0"
        volSize=PoolSize
        if (PoolLevel==str(0)):
            raid_level="raid0"
            Isize=int(PoolSize)
            size =float(Isize)*.99
            volSize=int(size)
        if (PoolLevel==str(1)):
            raid_level="raid5"
            Isize=int(PoolSize)
            size =float(Isize)*.75
            volSize=int(size)
        if (PoolLevel==str(2)):
            raid_level="raid6"
            Isize=int(PoolSize)
            size =float(Isize)*.5
            volSize=int(size)


        val=MegaRaidVol(action, PoolSystemName,volSize,raid_level)
        if val[0]==0:
            sprint("MegaRaidVol Created OK",val)
            UseList.append(val[1])
            UseList.append(val[2])
            SizeVol=str(val[3])
            sprint ("UseList",UseList)
            wErc=PoolCreate1(PoolName, SizeVol,PoolLevel, zfsCompression, zfsAcceleration, zfsDedup,PoolAccelerationStorage,PoolSystemName,Encryption,UseList,location,PerCent)
            if wErc !=0:
                try:
                    volSize='0'
                    action='d'
                    val=MegaRaidVol(action, PoolSystemName,volSize,raid_level)
                    if val[0]==0:
                        sprint("MegaRaidVol Delete OK",val)
                    else:
                        sprint("MegaRaidVol Delete NOT OK",val)
                    res=DB_PoolDelete(PoolSystemName)
                except Exception as err:
                    sprint("DB Update except ",err)
                sprint ("PoolCreate1",wErc)
                return wErc
            else:
                BackUpDB2SystemVolume()
                return 0
        else:
            sprint("MegaRaidVol Create NOT OK",val)
            return wErrCommandFailed

    elif (PoolName=='HDD POOL' or PoolName =='SSD POOL'):
        sprint ("PoolCreate","step2")
        UseList=[]
        sprint ("Create Pool Type",PoolName)
        wErc=PoolCreate1(PoolName, PoolSize,PoolLevel, zfsCompression, zfsAcceleration, zfsDedup,PoolAccelerationStorage,PoolSystemName,Encryption,UseList,location,PerCent)
        sprint ("PoolCreate","step3")
        if (wErc)==0:
            sprint ("Pool Created",0)
            return wErc
        else:
            sprint ("Pool NOT Created",wErc)
            return wErrCommandFailed
    return wErrCommandFailed 

def PoolCreate1(PoolName, PoolSize,PoolLevel, zfsCompression, zfsAcceleration, zfsDedup,PoolAccelerationStorage,PoolSystemName,Encryption,UseList,location,PerCent):
#process1 = subprocess.check_output(["zfs", zfs_cmd, vol])
# identfy all the drives available
# format the ZFS command
#execute the zfs command
#ls -lh /dev/disk/by-id/
    try:
        zpool_SSD_list=[]
        zpool_HDD_list=[]
        dev_byID_list=[]
        if len (UseList) ==0:
            sprint ("get Free disks",str(0))
            if (PoolName=='HDD POOL'):
                #rota=1
                rota="True"
            else:
                #rota=0
                rota="False"
            selector='wwn'
            zfsDisk='null'
            go=False
            res=GetFreeDisks(selector,zfsDisk,rota,poolname=None)
            if res[0]==0:
                wwn_size=res[2]
                zpool_HDD_list=res[1]
                dev_byID_list=res[1]

                total_disks=len(dev_byID_list)
                nb_disks=int(total_disks*PerCent)
                
                if (PoolLevel=='0' and nb_disks >= 2):
                    go=True
                elif (PoolLevel=='1' and nb_disks >= 3):
                    go=True
                elif (PoolLevel=='2' and nb_disks >= 4):
                    go=True
                elif (PoolLevel=='3' and nb_disks >= 5):
                    go=True
                else:
                    go=False
                    
                if go==True:
                    popDisks=total_disks-nb_disks
                    if popDisks==0:
                        popDisks=1
                    i=popDisks
                    sprint ('disk list',dev_byID_list)
                    while (i):
                        dev_byID_list.pop()
                        i=i-1

            else:
                print ('no disk list')
                return wErrCommandFailed
            
         
            #devList=getFreeDisks(rota,PerCent)
            #if devList[0]==0:
            #    zpool_HDD_list=devList[1]
            #    dev_byID_list=devList[2]
            #else:
            #    return wErrCommandFailed
        else:
            sprint ("Use supplied disks",0)
            zpool_HDD_list.append(UseList[0])
            dev_byID_list.append(UseList[1])

        #sprint ("Create Pool with",zpool_HDD_list)
        sprint ("Create Pool with",dev_byID_list)
        if (PoolName !="HDD POOL") and (PoolName !="SSD POOL")and (PoolName !="MegaRAID POOL"):
            sprint ("Unknown PoolName",0)
            return 108

        if StorageBackend=="LVM":
            #get the drives used in LVM
            sprint ("LVM backend --fixup",0)
            
        if StorageBackend=="zfs":        
            #get the drives used by ZFS sudo zpool status
            sprint ("zfs backend --fixup",0)
                     
        raid_level="none"
        sprint ("PoolLevel=",PoolLevel)
        if (PoolLevel=='1'):    #int(1)):
            raid_level="raidz1"
        elif (PoolLevel=='2'):  #int(2)):
            raid_level="raidz2"
        elif (PoolLevel=='3'):  #int(3)):
            raid_level="raidz3"

        if (PoolName=="HDD POOL"):
            sprint ("HDD Pool",0)
            disk_list=zpool_HDD_list
            disk_list=dev_byID_list
        if (PoolName=="SSD POOL"):
            sprint ("SSD Pool",0)
            disk_list=zpool_SSD_list

        if StorageBackend=="zfs":
            zfs_cmd='create'
            zfs_args='-f'
            sprint ("Pool=",PoolSystemName)
            sprint ("Raid Level=",raid_level)
            sprint ("Zpool Disk  List=",disk_list)
            try:
                if raid_level=="none":
                    process1 = subprocess.check_output(["zpool", zfs_cmd,zfs_args, PoolSystemName] + disk_list)                    
                #sudo zpool create -f pool1 raidz /dev/sda /dev/sdb /dev/sdc
                else:
                    process1 = subprocess.check_output(["zpool", zfs_cmd,zfs_args, PoolSystemName, raid_level] + disk_list)
                sprint (process1,0)
                #get the pool size.
                
            except Exception as err:
                sprint ("Pool create failed=",PoolSystemName)
                sprint ("error=",err) 
                return wErrCommandFailed
                
            #Yes (25%)
                if (zfsAcceleration==1):
                    sprint ("Mirror SSD",0) 
                else:
                    sprint ("No SSD Mirror",0)
                    
        elif StorageBackend=="LVM":
            if len(zpool_HDD_list)==0:
                sprint ("No Storage devices=", str(wErrCommandFailed))
                return wErrCommandFailed
            LVM_arg2=zpool_HDD_list[0]        
            LVM_arg1=PoolSystemName
            sprint ("zpool_HDD_list",zpool_HDD_list)
            sprint ("dev_byID_list",dev_byID_list)
            #del dev_byID_list[0]   #remove the first element        
            del zpool_HDD_list[0]   #remove the first element        
            try:
                #sudo vgcreat mrp1 /dev/sdb
                process1 = subprocess.check_output(["vgcreate",LVM_arg1,LVM_arg2])
                sprint (process1,0)                    
                #for hdd in dev_byID_list:
                for hdd in zpool_HDD_list:            
                    process1 = subprocess.check_output(["vgextend",LVM_arg1,hdd])
                    sprint (process1,0)
            except Exception as err:
                sprint("vgcreate except ",err)
                return wErrCommandFailed

        else:
            sprint ("No Storage BackEnd=", str(wErrBootDisk))
            return wErrCommandFailed
        try:
            sprint ("Updating DB Pool Create",0)
            conn=db_connect()
            conn.text_factory=str
            c=conn.cursor()
            query_SP = c.execute(
            "insert into multi_device(name,pool_storage,level,state,cr_date,edit_date,compression,acceleration,deduplication,acceleration_storage,system_name,encryption,calculatedraw,location) \
            values(?,?,?,0,datetime(),datetime(),?,?,?,?,?,?,?,?)",[PoolName, PoolSize, PoolLevel, zfsCompression, zfsAcceleration, zfsDedup,PoolAccelerationStorage,PoolSystemName,Encryption,PoolSize,location])
            conn.commit()
            poolID=c.lastrowid
            sprint ("Updating Disks",dev_byID_list)
            i=0
            for item in dev_byID_list:
                disk=dev_byID_list[i]
                sprint (disk,0)
                i=i+1
                wwn=str(disk.lstrip("/dev/disk/by-id/"))
                sprint ("Update Disks",wwn+str(poolID))
                query=c.execute("update disks set multi_device_id=? where wwn=?",[poolID,wwn])
                conn.commit()
            c.close()
            conn.close()
            return 0
        except Exception as err:
            sprint("DB Update except ",err)
            return 0        
            #return wErrDBnotFound        

    except Exception as err:
        sprint("PoolCreate1 except ",err)
        return 1  
        
            #return wErrDBnotFound     

#sudo /opt/MegaRAID/storcli/storcli64 /c0/e252/sall show all J > disk.txt        


def getMegaRAIDdrives():
    SlotList=[]
#sudo /opt/MegaRAID/storcli/storcli64 /c0/e252/sall show J
#sudo /opt/MegaRAID/storcli/storcli64 /c0 show all J
    try:
        storcli="/opt/MegaRAID/storcli/storcli64"
        storCLIlog="R600"
        argLog="logfile="+storCLIlog
        cmd="show"
        cx="/c0"
        arg1='/c0/e252/sall'
        #arg1='/c0'        
        argLast='J'
        #print storcli,cmd,cx,arg1,argLast
        process1 = subprocess.check_output([storcli, arg1,cmd, argLast])
        #print process1
        y = json.loads(process1)
        x=y['Controllers'][0]['Command Status']
        sprint (x["CLI Version"],0)
        sprint (x["Operating system"],0)
        sprint (x["Status"],0)
        sprint (x["Description"],0)
        x=y['Controllers'][0]['Response Data']['Drive Information']
        NbSlots=len(x)
        sprint ("NbSlots",NbSlots)
        i=0
        while i<NbSlots:
            slot=x[i]['EID:Slt']
            sprint ("slot=",slot)
            SlotList.append(slot)
            i=i+1
        return SlotList

    except Exception as err:
        sprint("getMegaRAIDdrives except ",err)

def getMegaRAIDslotList():

    slotList=[]
    try:
        storcli="/opt/MegaRAID/storcli/storcli64"
        storCLIlog="R600"
        argLog="logfile="+storCLIlog
        cmd="show"
        arg1='/c0/e252/sall'
        argLast='J'
        #sudo /opt/MegaRAID/storcli/storcli64 /c0/e252/sall show J
        #print storcli,cmd,cx,arg1,argLast
        process1 = subprocess.check_output([storcli, arg1,cmd, argLast])
        y = json.loads(process1)
        x=y['Controllers'][0]['Command Status']
        sprint (x['Status'],0)
        if str(x['Status'])=="Success":
            i=0
            j=0
            x=y['Controllers'][0]['Response Data']['Drive Information']
            NbSlots=len(x)
            while (i<NbSlots):
                if ((str(x[i]['State'])=='Onln') or (str(x[i]['State'])=="UGood")):
                    slotList.append(str(x[j]['EID:Slt']))
                    j=j+1
                i=i+1
    except Exception as err:
        sprint("getMegaRAIDslotList ",err)
        return -1,slotList  
        
    return 0,slotList


def getMegaRAIDdrivesInfo(slot,verbosity):
    DriveData=[]
#sudo /opt/MegaRAID/storcli/storcli64 /c0 show pdfailevents lastoneday
#sudo /opt/MegaRAID/storcli/storcli64 /c0/e252/sall show dpmstat type = RA logfile=filename
#sudo /opt/MegaRAID/storcli/storcli64 /c0 start dpm
#sudo /opt/MegaRAID/storcli/storcli64 /c0 stop dpm
#sudo /opt/MegaRAID/storcli/storcli64 /c0/e252/sall show dpmstat type = ALL
#RA 
#sudo /opt/MegaRAID/storcli/storcli64 /c0 delete dpmstat type = RA
#sudo /opt/MegaRAID/storcli/storcli64 /c0/e252/sall show J
#sudo /opt/MegaRAID/storcli/storcli64 /c0 show J
    try:
        storcli="/opt/MegaRAID/storcli/storcli64"
        #sudo /opt/MegaRAID/storcli/storcli64 /c0/e252/s4 show all J 
        storCLIlog="R600"
        argLog="logfile="+storCLIlog
        cmd="show"
        cx="/c0"
        arg1='/c0/e252/s'
        arg2='all'
        argLast='J'
        #print storcli,cmd,cx,arg1,argLast
        arg3=arg1+str(slot)
        process1 = subprocess.check_output([storcli, arg3,cmd, arg2, argLast])
        #print process1
        y = json.loads(process1)
        x=y['Controllers'][0]['Command Status']
        #print x["CLI Version"]
        #print x["Operating system"]
        #print x["Status"]
        #print x["Description"]
        x=y['Controllers'][0]['Response Data']
        #print "Step 0", arg3
        #print "step 1"
        Rarg1='Drive '+arg3
        if verbosity==1:
            j=0
            DriveData.insert(j,['EID:Slt',str(x[Rarg1][0]['EID:Slt'])])
            j=j+1
            DriveData.insert(j,['State',str(x[Rarg1][0]['State'])])
            j=j+1
            DriveData.insert(j,['Intf',str(x[Rarg1][0]['Intf'])])
            j=j+1            
            DriveData.insert(j,['Disk Size',str(x[Rarg1][0]['Size'])])
            j=j+1
            DriveData.insert(j,['Model',str(x[Rarg1][0]['Model'])])
            j=j+1
            Rarg2=Rarg1+' - Detailed Information'
            Rarg3= Rarg1+' Device attributes'
            DriveData.insert(j,['SN',str(x[Rarg2][Rarg3]['SN'])])
            j=j+1
            DriveData.insert(j,['WWN',str(x[Rarg2][Rarg3]['WWN'])])
            j=j+1
            Rarg4='Drive '+arg3+' State'
            DriveData.insert(j,['Firmware Revision',str(x[Rarg2][Rarg3]['Firmware Revision'])])
            j=j+1
            DriveData.insert(j,['Media Error Count',str(x[Rarg2][Rarg4]['Media Error Count'])])
            j=j+1
            DriveData.insert(j,['Other Error Count',str(x[Rarg2][Rarg4]['Other Error Count'])])
            j=j+1
            DriveData.insert(j,['Drive Temperature',str(x[Rarg2][Rarg4]['Drive Temperature'])])
            j=j+1
            DriveData.insert(j,['Predictive Failure Count',str(x[Rarg2][Rarg4]['Predictive Failure Count'])])
            j=j+1
            DriveData.insert(j,['S.M.A.R.T alert flagged by drive',str(x[Rarg2][Rarg4]['S.M.A.R.T alert flagged by drive'])])
            return 0,DriveData

        j=0
        DriveData.insert(j,['EID:Slt',str(x[Rarg1][0]['EID:Slt'])])
        j=j+1
        DriveData.insert(j,['State',str(x[Rarg1][0]['State'])])
        j=j+1
        DriveData.insert(j,['Disk Size',str(x[Rarg1][0]['Size'])])
        j=j+1
        DriveData.insert(j,['Model',str(x[Rarg1][0]['Model'])])
        j=j+1
        DriveData.insert(j,['Sector Size',str(x[Rarg1][0]['SeSz'])])
        j=j+1
        Rarg2=Rarg1+' - Detailed Information'
        Rarg4='Drive '+arg3+' State'
        #print "step 2"
        #print x[Rarg2]
        #Drive /c0/e252/s4 State
        DriveData.insert(j,['Media Error Count',str(x[Rarg2][Rarg4]['Media Error Count'])])
        j=j+1
        DriveData.insert(j,['Other Error Count',str(x[Rarg2][Rarg4]['Other Error Count'])])
        j=j+1
        DriveData.insert(j,['Drive Temperature',str(x[Rarg2][Rarg4]['Drive Temperature'])])
        j=j+1
        DriveData.insert(j,['Predictive Failure Count',str(x[Rarg2][Rarg4]['Predictive Failure Count'])])
        j=j+1
        DriveData.insert(j,['S.M.A.R.T alert flagged by drive',str(x[Rarg2][Rarg4]['S.M.A.R.T alert flagged by drive'])])
        j=j+1
        #print "step 3"
        Rarg3= Rarg1+' Device attributes'
        DriveData.insert(j,['SN',str(x[Rarg2][Rarg3]['SN'])])
        j=j+1        
        DriveData.insert(j,['Manufacturer Id',str(x[Rarg2][Rarg3]['Manufacturer Id'])])
        j=j+1
        DriveData.insert(j,['WWN',str(x[Rarg2][Rarg3]['WWN'])])
        j=j+1        
        DriveData.insert(j,['Firmware Revision',str(x[Rarg2][Rarg3]['Firmware Revision'])])
        j=j+1
        DriveData.insert(j,['Device Speed',str(x[Rarg2][Rarg3]['Device Speed'])])
        j=j+1
        DriveData.insert(j,['Link Speed',str(x[Rarg2][Rarg3]['Link Speed'])])
        j=j+1
        DriveData.insert(j,['Write Cache',str(x[Rarg2][Rarg3]['Write Cache'])])
        j=j+1
        DriveData.insert(j,['Connector Name',str(x[Rarg2][Rarg3]['Connector Name'])])
        j=j+1
        DriveData.insert(j,['Max lane width',str(x[Rarg2][Rarg3]['Max lane width'])])
        #print x[Rarg2][Rarg3]
        #print "step 4"
        Rarg4= Rarg1+' Policies/Settings'

        DriveData.insert(j,['SED Capable',str(x[Rarg2][Rarg4]['SED Capable'])])
        j=j+1
        DriveData.insert(j,['SED Enabled',str(x[Rarg2][Rarg4]['SED Enabled'])])
        j=j+1
        DriveData.insert(j,['Last Predictive Failure Event Sequence Number',str(x[Rarg2][Rarg4]['Last Predictive Failure Event Sequence Number'])])
        j=j+1
        DriveData.insert(j,['Successful diagnostics completion on',str(x[Rarg2][Rarg4]['Successful diagnostics completion on'])])
        j=j+1
        DriveData.insert(j,['Secured',str(x[Rarg2][Rarg4]['Secured'])])
        j=j+1
        DriveData.insert(j,['Cryptographic Erase Capable',str(x[Rarg2][Rarg4]['Cryptographic Erase Capable'])])
        j=j+1
        DriveData.insert(j,['Locked',str(x[Rarg2][Rarg4]['Locked'])])
        Rarg5='Inquiry Data'
        inq=x[Rarg2]['Inquiry Data']
        sprint ("Inquiry Data",inq)
        return 0,DriveData

    except Exception as err:
        sprint("getMegaRAIDdrivesInfo except ",err)
        return -1,DriveData



def MegaRaidVol(action, volName,volSize,level):
        msg =str(action+volName+str(volSize)+str(level))
        sprint ("MegaRaidVol ",msg)
        RaidVolByName="/dev/sdx"
        RaidVolById  ="/dev/disk/by-id/wwn-x"
        #action (c)reate, (d)elete
        storcli="/opt/MegaRAID/storcli/storcli64"
        if action=='c':
            cx="/c0"
            c='MegaRAID_c0'
            if c in volName:
               cx="/c0"
            c='MegaRAID_c1'
            if c in volName:
               cx="/c1"
            c='MegaRAID_c2'
            if c in volName:
               cx="/c2"
            sprint ("MegaRAID controller is",cx)
            cmd="add"
            raidLevel=level         #"raid0"
            argLast='J'
            object="vd"
            if str(volSize)!='0':
                size="size="+str(volSize)+"gb"
            else:
                size=""

            names="names="+volName
            #sudo /opt/MegaRAID/storcli/storcli64 /c0/dall show J
            #x= split "EID:Slot"
            drives="drives="
            list=getMegaRAIDslotList()
            SlotList=list[1]
            NbSlots=len(SlotList)
            i=0
            while (i<NbSlots):
                if i!=0:
                   drives+=','
                drives+=SlotList[i]
                i=i+1
            sprint ("Drives=",drives)
            try:
                msg=cx+cmd+object+raidLevel+size+names+drives+argLast
                sprint("MegaRaid cmd",msg)
                #max namelength is 15 chars
                #sudo /opt/MegaRAID/storcli/storcli64 /c0 add vd raid0 names=p2 drives=252:4,252:6,252:8,252:10 J
                #sudo /opt/MegaRAID/storcli/storcli64 /c0 add vd raid0 size=100 names=p9 drives=252:4,252:6,252:8,252:10 J
                #sudo /opt/MegaRAID/storcli/storcli64 /c0 add vd raid0 size=100 names=p8 drives=252:4,252:6,252:8,252:10 sed J
                #sudo /opt/MegaRAID/storcli/storcli64 /c0 add vd raid5 names=p2 drives=252:4,252:6,252:8,252:10 J
                #sudo /opt/MegaRAID/storcli/storcli64 /c0 set securitykey=Hello@123 pgs 236
                #sudo /opt/MegaRAID/storcli/storcli64 /c0 set secursed=ON pg 202
                #sudo /opt/MegaRAID/storcli/storcli64 /c0 compare securitykey=Hello@123
                #sudo /opt/MegaRAID/storcli/storcli64 /c0 set securitykey=on
                #sudo /opt/MegaRAID/storcli/storcli64 /c0 get config file=log.txt
                #sudo /opt/MegaRAID/storcli/storcli64/fall del|delete [securitykey=sssssssssss
                #sudo /opt/MegaRAID/storcli/storcli64/fall import [preview][securitykey=sssssssssss]
                #sudo /opt/MegaRAID/storcli/storcli64/fall show [all] [securitykey=sssssssssss]
                #sudo /opt/MegaRAID/storcli/storcli64 /c0 show vall

                process1 = subprocess.check_output([storcli,cx,cmd,object,raidLevel,size,names,drives,argLast])
                y = json.loads(process1)
                sprint ("MegaRaid response",y)
                x=y['Controllers'][0]['Command Status']
                if x['Status']=='Success':
                    time.sleep(2)
                    #GET THE RAW STORAGE OF THE RAID #############WOTEST####################
                    retVal=-1
                    val=getMegaRaidDisk()
                    sprint ("getMegaRaidDisk Val",val)
                    if val[0]==0:
                        retVal=0
                        RaidVolByName=str(val[1])
                        RaidVolById=str(val[2])
                        size=str(val[3])
                        #pvcreate
                        LVM_arg3="-v"
                        LVM_arg4="-ff"
                        dev=str(val[1])
                        #sudo pvcreate /dev/sdb -v -ff
                        try:
                            process1 = subprocess.check_output(["pvcreate",dev,LVM_arg3,LVM_arg4])
                            sprint (process1,0)
                        except Exception as err:
                            sprint("pvcreate except ",err)
                            retVal=-1
                        return (retVal,RaidVolByName,RaidVolById,size)
                    else:
                        sprint ("No getMegaRaidDisk",val)
                else:
                    retVal=-1
                return (retVal,RaidVolByName,RaidVolById,)
                
            except Exception as err:
                sprint("MegaRaidVol -C except ",err)
                retVal=-1
                return (retVal,RaidVolByName,RaidVolById)
                    
        elif action=='d':
            try:
                #argLog="logfile="+storCLIlog
                #sudo /opt/MegaRAID/storcli/storcli64 /c0/vall show J
                cx="/c0"
                c='MegaRAID_c0'
                if c in volName:
                    cx="/c0"
                c='MegaRAID_c1'
                if c in volName:
                    cx="/c1"
                c='MegaRAID_c2'
                if c in volName:
                    cx="/c2"
                sprint ("MegaRAID controller is",cx)
                #arg1="/c0/vall"
                arg1=cx+"/vall"
                cmd="show"
                argLast='J'
                process1 = subprocess.check_output([storcli,arg1,cmd,argLast])
                y = json.loads(process1)
                sprint ("# controllers",len (y['Controllers']))
                x=y['Controllers'][0]['Command Status']
                sprint (x["Description"],0)
                if x["Description"] != "No VD's have been configured.":
                    NbVD= len(y['Controllers'][0]['Response Data']["Virtual Drives"])
                    i=0
                    sprint ("NbVD=",str(NbVD))
                    x=y['Controllers'][0]['Response Data']["Virtual Drives"]
                    sprint (str(x),0)
                    while (i< NbVD): 
                        if x[i]["Name"]==volName:
                            DGVD=x[i]["DG/VD"]
                            sprint ("DG/VD",str(DGVD))
                            break
                        i=i+1
                    if DGVD=='0/0':                         #The Volume was not found
                        return -2,RaidVolByName,RaidVolById
                else:
                    return -2,RaidVolByName,RaidVolById     #There are no RAIDs configured
                    
            except Exception as err:
                sprint("MegaRaidVol -D  except ",err)
                return -1,RaidVolByName,RaidVolById
                
            x=DGVD.split("/")
            VDname="/c"+x[0]+"/"+"v"+x[1]
            VDname=cx+"/"+"v"+x[1]

            cmd="del"
            sprint ("VDname",VDname)
            force="force"                
            #sudo /opt/MegaRAID/storcli/storcli64 /c0/v239 del force J
            try:
                process1 = subprocess.check_output([storcli,VDname,cmd,force,argLast])
                sprint (process1,0)
            except Exception as err:
                sprint("MegaRaidVol -X except ",err)
                return -1,RaidVolByName,RaidVolById
                
        return 0,RaidVolByName,RaidVolById


def CheckPartition (part,timeout):
    count=0
    while (count!=timeout):
        process1 = subprocess.check_output(["cat","/proc/partitions"])
        my_index= process1.find(part,0,len(process1))
        if my_index !=-1:
            break
        time.sleep(.5)
        count=count+1
    if count==timeout:
        return 108
    return 0
    

       
def DB_DisplayHosts():
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    query=c.execute("select name from host")
    sprint (query,0)
    c.close()
    conn.close()
    return 0


def DB_DiskDelete(PoolSystemName):
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    query=c.execute("delete from  multi_device where system_name=?",[PoolSystemName])
    conn.commit()
    c.close()
    conn.close()  ###Fixup check
    return 0
    
def DB_PoolDelete(PoolSystemName):
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    query=c.execute("delete from  multi_device where system_name=?",[PoolSystemName])
    conn.commit()
    c.close()
    conn.close()  
    return 0

def DB_PoolUpdate(zfsPool, zfsCompression, zfsDeduplication):
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    query=c.execute("update multi_device set compression=?,deduplication=? where name=?",\
    [zfsCompression,zfsDeduplication,zfsPool])
    conn.commit()
    c.close()
    conn.close()
    return 0


def DB_UpdateHost(name,user_name,iqn,pw,protocol,host_type):

    ret =-1
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    try:
        query=c.execute("select id from host where name ='"+str(name)+"'")
        resp=c.fetchone()
        if str(resp)=="None":
            query_SP=c.execute("insert into  host (name,user_name,iqn,pw,protocol,host_type) values(?,?,?,?,?,?)",[name,user_name,iqn,pw,protocol,host_type])
            conn.commit()
            id=c.lastrowid
        else:
            id=resp[0]
        c.close()
        conn.close()
        return 0,id
    except Exception as err:
        sprint ("DB_UpdateHost except",err)
        c.close()
        conn.close()
        return(-1)
        
        
def DB_UpdateExport(PoolName,portId,volumeName,hostId,lun):
    try:
        ret =-1
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()

        query=c.execute("select id from multi_device where system_name ='"+str(PoolName)+"'")
        resp=c.fetchone()
        sprint ("DB_UpdateExport Resp",resp)
        if str(resp) != str("None"):
            multi_device_id = resp[0]
            #query_lan=c.execute("select count(*) from Volume where name='"+str(VolName)+"' and multi_device_id="+str( multi_device_id))
            #nameCount = c.fetchone()[0]
        query=c.execute("select id from volume where name ='"+str(volumeName)+"' and multi_device_id="+str( multi_device_id))
        resp=c.fetchone()
        volumeId=resp[0]
        
        query_SP=c.execute("delete from export where vol_id='"+str(volumeId)+"'")
        conn.commit()
        
        query_SP=c.execute("insert into export(port_id,vol_id,host_id,lun) values(?,?,?,?)",[portId,volumeId,hostId,lun])
        bs=":"
        msg=str(PoolName)+bs+str(volumeName)+bs+str(portId)+bs+str(volumeId)+bs+str(hostId)+bs+str(lun)
        sprint ("DB_UpdateExport step1",msg)
        conn.commit()
        ret=0
        conn.commit()
        c.close()
        conn.close()
        return ret
    except Exception as err:
        sprint ("DB_UpdateExport except",err)
        c.close()
        conn.close()
        return(ret)
        
def DB_UpdateVolumeSnapState(VolName,state):
    ret =-1
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    query_SP=c.execute("update volume_snapshot set state=?,edit_date=datetime() where name=?",[state,VolName])    
    ret=0
    conn.commit()
    c.close()
    conn.close()
    return ret
def DB_UpdateVolumeState(VolName,state):
    ret =-1
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    query_SP=c.execute("update volume set state=?,edit_date=datetime() where name=?",[state,VolName])    
    ret=0
    conn.commit()
    c.close()
    conn.close()
    return ret
def DB_UpdateVolumeSize(VolName,size):
    ret =-1
    try:
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        query_SP=c.execute("update volume set size=?,edit_date=datetime() where name=?",[size,VolName])    
        ret=0
        conn.commit()
        c.close()
        conn.close()
        return ret
    except Exception as err:
        sprint ("DB_UpdateVolumeSize except",err)
        c.close()
        conn.close()
        return(ret)
        


def DB_CreateVolume(PoolName,VolName,VolumeSize,zfsCompression, zfsDeduplication,Vtype,priority,lun):
    try:
        ret =-1
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        query=c.execute("select id from multi_device where system_name ='"+str(PoolName)+"'")
        resp=c.fetchone()
        sprint ("DB_CreateVolume Resp",resp)
        if str(resp) != str("None"):
            multi_device_id = resp[0]
            sprint  ("md id =" ,str(multi_device_id))
            state=4
            msg=str(VolName)+str(state)+str(VolumeSize)+str(multi_device_id)+str(zfsCompression)+ str(zfsDeduplication)+str(Vtype)+str(lun)
            sprint("Query=",msg)
            query=c.execute("insert into  volume(name,state,size,multi_device_id,compression,deduplication,type,priority,cr_date) values(?,?,?,?,?,?,?,?,datetime())",\
            [VolName,state,VolumeSize,multi_device_id,zfsCompression, zfsDeduplication,Vtype,priority])
            ret=0
            conn.commit()
        c.close()
        conn.close()
        return ret
    except Exception as err:
        sprint ("DB_CreateVolume except",err)
        c.close()
        conn.close()
        return(ret)

def DB_CreateVolumeBis(PoolName,VolName,VolumeSize,zfsCompression, zfsDeduplication,V_type,backup,thin,location,lun):
    volumeId=-1
    try:
        sprint ("step1",0)
        ret =-1
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        query=c.execute("select id from multi_device where system_name ='"+str(PoolName)+"'")
        resp=c.fetchone()
        sprint ("DB_CreateVolumeBis Resp",resp)
        if str(resp) != str("None"):
            #select count(*) from Volume where name='vtest' and multi_device_id=2;
            multi_device_id = resp[0]
            query_lan=c.execute("select count(*) from Volume where name='"+str(VolName)+"' and multi_device_id="+str( multi_device_id))
            nameCount = c.fetchone()[0]
            if nameCount==0:
                sprint  ("md id =" , str(multi_device_id))
                state=4
                sp=" "
                sprint ("Query=",str(VolName)+sp+str(state)+sp+str(VolumeSize)+sp+str(multi_device_id)+sp+str(zfsCompression)+sp+str(zfsDeduplication)+sp+str(V_type)+sp+str(backup)+sp+str(thin)+sp+str(location))
                query=c.execute("insert into  volume(name,state,size,multi_device_id,compression,deduplication,type,backup_device,thin,location,cr_date) values(?,?,?,?,?,?,?,?,?,?,datetime())",\
                [VolName,state,VolumeSize,multi_device_id,zfsCompression, zfsDeduplication,V_type,backup,thin,location])
                conn.commit()
                sprint ("DB_CreateVolumeBis Query complete",0)
                volumeId = c.lastrowid
            else:
                query_lan=c.execute("select id from Volume where name='"+ str(VolName)+"'")
                volumeId = c.lastrowid
        ret=0
        c.close()
        conn.close()
        #return (ret,volumeId)   
        return (ret)
    except Exception as err:
        sprint ("DB_CreateVolumeBis except",err)
        c.close()
        conn.close()
        return(ret,volumeId)

def DB_MakeSchedule(name,action,srcVolID,DstVolID):
    conn=sqlite3.connect(DBPath)
    conn.text_factory=str
    c=conn.cursor()
    
    status="stopped"
    done_percentage=0
    #endDate=T_next=None
    startDateFormat = "%Y-%m-%d"
    startTimeFormat = "%H:%M"
    startDate = endDate = str(datetime.datetime.utcnow().strftime(startDateFormat))
    startTime = str(datetime.datetime.utcnow().strftime(startTimeFormat))
    T_next = startDate+" "+startTime
    frequency = "Once Only"
    scheduleName=name
    volId = str(srcVolID)
    volDestId = str(DstVolID)
    dirs=",,"

    if action == "Local Backup" or action=="File Server Backup": 
        try:
            c.execute("select state from volume where id='"+volDestId+"'")
            volDestState = c.fetchone()[0]
            if (volDestState!=int(6) and volDestState!=int(8) and volDestState!=int(10) and volDestState!=int(12)):
                sprint ("Destination volume not in running state.",volDestState)
                c.close()
                conn.close()
                return -1
        except Exception as err:
            sprint ("MakeSchedule-1 except",err)
            c.close()
            conn.close()
            return -1
        try:   
            c.execute("select state from volume where id='"+volId+"'")
            volSrcState = c.fetchone()[0]
            if volSrcState!=int(6):
                sprint("Source volume not in running state.",volSrcState)
                c.close()
                conn.close()
                return -1
        except Exception as err:
            sprint ("MakeSchedule-2 except",err)
            c.close()
            conn.close()
            return -1
    else:
        sprint("Type should be 'Local Backup' or 'File Server Backup' ",0)
        c.close()
        conn.close()
        return -1
    try:
        query_lan=c.execute("select count(*) from schedule where name='"+ scheduleName+"' and isdeleted!=1")
        nameCount = c.fetchone()[0]
        conn.commit()
    
        if nameCount == 0:
            if scheduleName!="":
                query_lan=c.execute("insert into schedule (name,frequency,start_time,start_date,end_date,action,status,t_next,done_percentage,isdeleted,vol_id,vol_dest_id,dirs) values(?,?,?,?,?,?,?,?,?,0,?,?,?)",[scheduleName,frequency,startTime,startDate,endDate,action,status,T_next,done_percentage,volId,volDestId,dirs])
                conn.commit()
                sprint("Saved successfully ",scheduleName)
                c.close()
                conn.close()
                return 0
            
            else:
                sprint("Name can't be empty",0)
                c.close()
                conn.close()
                return -1
        else:
            sprint("Schedule Name Already Exists",scheduleName)
            query_lan=c.execute("update schedule set frequency=?,start_time=?,start_date=?,end_date=?,action=?,status=?,t_next=?,done_percentage=?,isdeleted=?,vol_id=?,vol_dest_id=?,dirs=? where name=scheduleName",[frequency,startTime,startDate,endDate,action,status,T_next,done_percentage,volId,volDestId,dirs,scheduleName])
            c.close()
            conn.close()
            return -1

        c.close()
        conn.close()
        return 0

    except Exception as err:
        sprint ("MakeSchedule-3 except",err)
        c.close()
        conn.close()
        return -1

def getAtInsertVolume():
    return -1,"None",0
    
    try:
        VolName="None"  
        DstVolID=0
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        frequency="At Canister Insert"
        query=c.execute("select count(*) from schedule where frequency=?",[frequency])
        count=c.fetchone()[0]
        sprint ("At Canister Insert schedule=",str(count))
        if count==0:
            return -1,VolName,DstVolID

        query=c.execute("select vol_dest_id from schedule where frequency=?",[frequency])
        DstVolID=c.fetchone()[0]
        if DstVolID != None:
            query=c.execute("select name from volume where id=?",[DstVolID])
            VolName=c.fetchone()
        else:
            sprint ("No DstVolID ",0)
            return -1,"None",0

        sprint ("DstVol name=",str(VolName))   
        if str(VolName) != None:
            c.close()
            conn.close()
            return 0,VolName,DstVolID
        else:
            c.close()
            conn.close()
            return -1,"None",0
            
    except Exception as err:
        sprint ("getAtInsertVolume except",err)
        c.close()
        conn.close()
        return -1,"None",0

def DB_UpdateAtInsertSchedule():
    
    sprint ("DB_UpdateAtInsertSchedule","step1")   
    res=getAtInsertVolume()
    if res[0]==0:
        VolName=res[1]
        DstVolID=res[2]
    else:
        return -1
    
    sprint ("DB_UpdateAtInsertSchedule","step2")    
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    try:
        VolType="Foreign"                
        query = c.execute("select id,name from volume where type=?",[VolType])
        vols=c.fetchall()
        for col in vols:
            srcVolID=col[0]
            vol=col[1]
            name="AtInsert_"+str(vol)
            action="Local Backup"
            sprint ("DB_UpdateAtInsertSchedule ", name+" "+action+" "+str(srcVolID)+" "+str(DstVolID))
            res=DB_MakeSchedule(name,action,srcVolID,DstVolID)
        c.close()
        conn.close()
        return (0)
        
        
    except Exception as err:
        sprint ("DB_UpdateAtInsertSchedule except",err)
        c.close()
        conn.close()
        return (-1)
  

        
def DB_UpdateVolume(PoolName,VolName,VolumeSize,zfsCompression, zfsDeduplication,priority):
    ret =-1
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    query=c.execute("update volume set compression=?,deduplication=?,priority=?,edit_date=datetime() where name=?",[zfsCompression, zfsDeduplication,priority,VolName])
    ret=0
    conn.commit()
    c.close()
    conn.close()
    return ret

def VolumeStartSnap(PoolName, VolumeName,ProtID,VolSnap):
    sprint ("Volume SNAP Start called" , VolSnap + PoolName)
    result=VolumeStart(PoolName, VolumeName, ProtID,VolSnap)
    return result

def GetSerialByVol(VolumeName,tid):
    s="080958"+str(tid)+"110956"
    return  s

def VolumeStart(PoolName, VolumeName, ProtID,VolSnap):
    try:
    
        sprint ("Volume Start called" , str(VolumeName+"/"+PoolName))
        #step 1 find the exports for the Volume
        if (ProtID==cifs):
            result=VolumeStartCIFS(PoolName, VolumeName, ProtID,VolSnap)
            return result
        elif (ProtID==ftp):
            result=VolumeStartFTP(PoolName, VolumeName, ProtID,VolSnap)
            return result
        elif (ProtID==nfs):
            result=VolumeStartNFS(PoolName, VolumeName, ProtID,VolSnap)
            return result
        elif (ProtID==S3):
            result=VolumeStartS3(PoolName, VolumeName, ProtID,VolSnap)
            return result
            
        UserList=DB_GetUsersByVol(VolumeName)
        sprint ("UserList",UserList)
        #step 2 create the target
        sprint ("gTarget=",gTarget)
        if gTarget=="iet":
            process1 = subprocess.check_output(["systemctl", "restart","iscsitarget"])
        #elif gTarget=="tgt":
            #process1 = subprocess.check_output(["systemctl", "restart","tgt"])
        
        lun=DB_GetLunByVol(VolumeName)
        #tid=DB_GetTidByVol(VolumeName)
        tid=DB_GetTid()
        serial=GetSerialByVol(VolumeName,tid)

        if (StorageBackend=="zfs"):
            ret=zvol_GetDevice(PoolName,VolumeName)
            sprint ("Zvol Device",ret[1])
            if ret[0]==0:
                device=ret[1]
            else:
                DB_UpdateVolumeState(VolumeName,gVolOff)
                return -1
        if (StorageBackend=="LVM"):
            device=PoolName+"/"+VolumeName
        
        res=iSCSI_CreateTarget(str(tid),VolumeName,ProtID)
        if res!=0:
            DB_UpdateVolumeState(VolumeName,gVolOff)
            return (-1)
        
        rev=SoftwareVersion
        msg=str(tid)+" "+str(lun)+" "+str(device)+" "+str(serial)+" "+str(ProtID)+" "+str(rev)
        res=iSCSI_CreateLun(str(tid),str(lun),device,serial,ProtID,rev)
        if res!=0:
            DB_UpdateVolumeState(VolumeName,gVolOff)
            return (-1)
            
        if (ProtID==iSCSI_Chap or ProtID==iSER_Chap):
            UserList=DB_GetUsersByVol(VolumeName)
            sprint ("UserList",UserList)
            for user in UserList:
                sprint (user[0],user[1])
                iSCSI_AddChapUser(str(tid),user[0],user[1],ProtID)
                #Step1 Find all Hosts mapped to lun0
                #Step2 find Volume Mapped to lun0
                #DB_DisplayHosts()
                #process1 = subprocess.check_output(["cat","/proc/partitions", "|" ,"grep", "z"])
        
        res=DB_GetIQNByVol(VolumeName)
        if res[0]==0:
            ipAdr=res[1]
        else:
            ipAdr="ALL"
        
        iSCSI_AddIP(str(tid),ipAdr,ProtID)

        if gTarget=="iet":
            process1 = subprocess.check_output(["cat","/proc/partitions"])
            sprint (process1,0)
            process1 = subprocess.check_output(["cat", "/proc/net/iet/volume"])
            sprint (process1,0)
            process1 = subprocess.check_output(["cat", "/proc/net/iet/session"])
            sprint (process1,0)

        DB_UpdateVolumeState(VolumeName,gVolOn)
        sprint ("VolumeStart complete",msg)
        return 0

    except Exception as err:
        sprint ("VolumeStart except",err)
        return (-1)
   
def VolumeStopSnap(zfsPool, VolumeName,ProtID,VolSnap):
    res=VolumeStop(zfsPool, VolumeName,ProtID,VolSnap)
    return res

def VolumeStop(Pool, VolumeName,ProtID,VolSnap):
    sprint ("Volume Stop called" , str(str(VolumeName) + str(Pool)))
    if (ProtID==cifs):
        result=VolumeStopCIFS(Pool, VolumeName,ProtID,VolSnap)
        if result !=0:
            sprint ("result",str(result))
    elif (ProtID==nfs):
        result=VolumeStopNFS(Pool, VolumeName,ProtID,VolSnap)
        if result !=0:
            sprint ("result",str(result))
    elif (ProtID==S3):
        result=VolumeStopS3(Pool, VolumeName,ProtID,VolSnap)
        if result !=0:
            sprint ("result",str(result))
    elif ((ProtID==iSCSI_Chap) or (ProtID==iSCSI_NoChap) or (ProtID==iSER_NoChap) or (ProtID==iSER_Chap)):
        result=vol_DeleteLun(Pool,VolumeName,ProtID)
        if result !=0:
            sprint ("result",str(result))
    return result
    
def DB_VolumeDelete(VolumeName):
    #print('DB_VolumeDelete',VolumeName)
    try:
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        query=c.execute("delete from  volume where name=?",[VolumeName])
        conn.commit()
        c.close()
        conn.close()
        return 0
    except Exception as err:
        sprint ("except DB_VolumeDelete",err)
    c.close()
    conn.close()
    return 0
    
def DB_UpdateSnapShotVolume(VolName,SnapShotVolume):
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    query=c.execute("select id from volume where name ='"+str(VolName)+"'")
    resp=c.fetchone()
    if resp!="none":
        VolID=resp[0]
        sprint  ("VolID =" , str(VolID))
        SS_state=gVolOff
        query=c.execute("insert into  volume_snapshot (name,state,vol_id,cr_date) values(?,?,?,datetime())",\
        [SnapShotVolume, SS_state,VolID])
        conn.commit()
    c.close()
    conn.close()
    return 0

    
def DB_SnapShotDelete(VolumeName):
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    query=c.execute("delete from  volume_snapshot where name=?",[VolumeName])
    conn.commit()
    c.close()
    conn.close()
    return 0
    

def DB_CheckElement(element, name):
# Returns 0 if name does not exist
# Returns -1 if name does exist
# Returns poolName if 'pool'
    if element=="pool":
        poolName="null"
        id=name
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        query=c.execute("select system_name from multi_device where id='"+ str(id)+"'")
        resp = c.fetchone()
        if str(resp) != str("None"):
            poolName= resp[0]
            sprint ("poolName=",poolName)

        c.close()
        conn.close()
        return poolName

    else:
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        if element=="multi_device":
            query=c.execute("select count(*) from " +element +" where system_name='"+ str(name)+"'")
        else:
            query=c.execute("select count(*) from " +element +" where name='"+ str(name)+"'")
        nameCount = c.fetchone()[0]
        sprint ("nameCount",nameCount)
        c.close()
        conn.close()
        if nameCount == 0:
            sprint ("NameCount=0",name)
            return 0
        else:
            sprint ("NameCount!=0",name)
            return -1
def DB_GetElementState(element,name):
# Returns 0 if name does not exist
# Returns -1 if name does exist

    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    query=c.execute("select state from " +element +" where name='"+ str(name)+"'")
    state = c.fetchone()[0]
    c.close()
    conn.close()

    if int(state) == int(gVolOn):
        sprint ("State on",0)
    else:
        sprint ("State not on",state)
    return state

def DB_DeleteExport(element,name):
# Returns 0 if name does not exist
# Returns -1 if name does exist
    #print('DB_DeleteExport',element,name)
    try:
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        #select id from volume where name='wo2';
        query=c.execute("select id from Volume where name='"+str(name)+"'") #works
        resp=c.fetchone()
        volId=resp[0]
        sprint ("vol_id = ",str(volId))
        query=c.execute("delete from export where vol_id=?",[volId])
        conn.commit()
        return 0
    except Exception as err:
        sprint ("except DB_DeleteExport",err)
        
    c.close()
    conn.close()
    return 0


    
def vDiskCreate(zfsPool,VolName,VolumeSize,zfsCompression, zfsDedup,priority):
    VolType="F"
    type="Native"
    res=VolumeCreate(zfsPool,VolName,VolumeSize,zfsCompression, zfsDedup,VolType,type,priority)
    return res
    # create the link to the VMid
    
def vDiskDelete(zfsPool,VolName):
    VolType="F"
    type="Native"
    res=VolumeDelete(zfsPool,VolName)
    return res
    # create the link to the VMid
    
def vDiskUpdate(zfsPool,VolName,VolumeSize,zfsCompression, zfsDedup,priority):
    VolType="F"
    type="Native"
    res=VolumeUpdate(zfsPool,VolName,VolumeSize,zfsCompression, zfsDedup,VolType,priority)
    return res
    # create the link to the VMid
    
def getVolumeDetails(SnapShotVolume):
    db_open = False
    try:
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        db_open = True

        query=c.execute("select vol_id from  volume_snapshot where name=?",[SnapShotVolume])
        vol_id = c.fetchone()[0]

        query = c.execute("""
                select v.location,v.size,v.compression,v.deduplication,v.backup_device,v.thin,v.priority,ex.port_id,ex.vol_id,ex.host_id 
                from volume v 
                left join export ex on v.id=ex.vol_id 
                where v.id=?""",[vol_id]
        )
        volumeData = c.fetchone()
        if not volumeData:
            if db_open:
                c.close()
                conn.close()
            return None

        response = {
            "location" : volumeData[0],
            "size" : volumeData[1],
            "compression" : volumeData[2],
            "deduplication" : volumeData[3],
            "backup_device" : volumeData[4],
            "thin" : volumeData[5],
            "priority" : volumeData[6],
            "port_id" : volumeData[7],
            "vol_id" : volumeData[8],
            "host_id" : volumeData[9]
        }

        if db_open:
            c.close()
            conn.close()
        return response
    except Exception as e:
        sprint("Error in getVolumeDetails:", e)
        if db_open:
            c.close()
            conn.close()
        return None

def getFreeVolumeLun():
    db_open = False
    try:
        conn = db_connect()
        conn.text_factory = str
        c = conn.cursor()
        db_open = True

        # Fetch all used LUNs
        c.execute("SELECT lun FROM export")
        used_luns = c.fetchall()
        sprint ('used_luns',used_luns)
        # Convert to set for fast lookup
        import builtins
        used_luns_set = builtins.set([row[0] for row in used_luns])
        sprint ('used_luns_set',used_luns_set)
        # Find first free LUN between 0–128
        for lun in range(1, 129):
            if lun not in used_luns_set:
                if db_open:
                    c.close()
                    conn.close()
                return lun

        # If all LUNs are used
        if db_open:
            c.close()
            conn.close()
        return None

    except Exception as e:
        sprint("Error in getFreeLun:", e)
        if db_open:
            c.close()
            conn.close()
        return None
 
def CloneVolumeCreate(zfsPool,VolName, SnapShotVolume,SnapPath):
   #snap name =wo1-ss1
   #snap path = wo1/wo1-ss1
   #zfsPool =p1
    try:
        
        src=zfsPool+'/'+SnapPath
        zfs_cmd='clone'
        sprint(zfs_cmd,src)
        dst=zfsPool+'/'+VolName
        process1 = subprocess.check_output(["zfs", zfs_cmd, src,dst])
        zfsCmd='set'
        arg1="mountpoint="+"/mnt/"+VolName
        #sudo zfs set mountpoint=/mnt/wo2 p11/wo1

        process1 = subprocess.check_output(["zfs", zfsCmd,arg1,dst])
        sprint (process1,0)

        volumeData = getVolumeDetails(SnapShotVolume)
        if not volumeData:
            VolumeSize='false'
            zfsCompression='false'
            zfsDeduplication='false'
            priority=1
            backup='false'
            thin=''
            location='cx'
        else:
            VolumeSize=volumeData['size']
            zfsCompression=volumeData['compression']
            zfsDeduplication=volumeData["deduplication"]
            priority=volumeData["priority"]
            backup=volumeData["backup_device"]
            thin=volumeData["thin"]
            location=volumeData["location"]

        lun=getFreeVolumeLun()
        sprint('Clone Lun',lun)
        if lun is None:
            lun = 100


        V_type='clone'
        #Add in LUN and priority
        result=DB_CreateVolumeBis(zfsPool,VolName,VolumeSize,zfsCompression, zfsDeduplication,V_type,backup,thin,location,lun)
        if (result!=0):
            sprint ("DB_CreateVolumeBis for clone Failed",str(result))
        else:
            sprint ("DB_CreateVolumeBis for clone Passed",str(result))
            res=GetVolDefaultValues('nfs')
            portId=volumeData["port_id"]
            host=volumeData["host_id"]
            protocol=0
            if res[0]==0:
                protocol=[4]
            bs=' '
            msg=str(zfsPool)+bs+str(portId)+bs+str(VolName)+bs+str(host)+bs+str(lun)
            sprint ("Update Export",msg)
            DB_UpdateExport(zfsPool,portId,VolName,host,lun)

    except Exception as err:
        sprint ("except creating Clone",err)
        return(wErrCommandFailed)

    return 0
    
def SnapShotVolumeCreate(zfsPool,VolName, SnapShotVolume):
    element="volume_snapshot"
    name=SnapShotVolume
    result=DB_CheckElement(element, name)
    if (result!=0):
        sprint ("wErrDuplicateName",name)
        return(wErrDuplicateName)
    element="volume"
    name=VolName
    result=DB_CheckElement(element, name)
    if (result==0):
        sprint ("wErrNameNotFound",name)
        return(wErrNameNotFound)        
    element="multi_device"
    name=zfsPool
    result=DB_CheckElement(element, name)
    if (result==0):
        sprint ("wErrNameNotFound",name)
        return(wErrNameNotFound)
    
    zfsSnapShotVol=zfsPool+"/"+VolName+"@"+SnapShotVolume
    sprint ("zfsSnapShotVol=",zfsSnapShotVol)
    zfs_cmd='snapshot'
    #sudo zfs snapshot p1/vm1@ss2
    try:
        process1 = subprocess.check_output(["zfs", zfs_cmd, zfsSnapShotVol])
    except Exception as err:
        sprint ("except creating SNAP",err)
        return(wErrCommandFailed)
    #zfs set snapdir=visible p3/V2
    zfs_cmd='set'
    arg1="snapdir=hidden"
    zfsSnapShotVol=zfsPool+"/"+VolName
    #process1 = subprocess.check_output(["zfs", zfs_cmd, arg1, zfsSnapShotVol])
    
    result=DB_UpdateSnapShotVolume(VolName,SnapShotVolume)
    return result


def SnapShotVolumeDelete(zfsPool, VolName, SnapShotVolume):
    try:
        #wErrNameNotFound=109
        #wErrCommandFailed=120
        
        element="volume_snapshot"
        name=SnapShotVolume
        result=DB_CheckElement(element, name)
        if (result==0):
            sprint ("wErrNameNotFound",name)
            return(wErrNameNotFound)
        element="volume"
        name=VolName
        result=DB_CheckElement(element, name)
        if (result==0):
            sprint ("wErrNameNotFound",name)
            return(wErrNameNotFound+1)
        element="multi_device"
        name=zfsPool
        result=DB_CheckElement(element, name)
        if (result==0):
            sprint ("wErrNameNotFound",name)
            return(wErrNameNotFound+2)
        #sudo rm -rf /mnt/wo1/.zfs/snapshot/wo1-ss1
        #zfs list -t snapshot -o name,clones p1/wo1@wo1-ss1
        zfsSnapShotVol=zfsPool+"/"+VolName+"@"+SnapShotVolume
        process= subprocess.check_output(["zfs", 'list', '-H', '-t', 'snapshot', '-o', 'name,clones', zfsSnapShotVol])
        result=process.decode("utf-8").split()
        print ('nb_parts',len (result))
        if len(result) !=1:
            vals= result[1].split(",")
            print ('vals=', vals)
            for clone in vals:
                print ('clone',clone)
                #cp1/navte-ss1-clone1
                zfs_cmd='promote'
                process1 = subprocess.check_output(["zfs", zfs_cmd, clone])
        else:
            zfs_cmd='destroy'
            #sudo zfs destroy p1/vm1@ss2
            zfsSnapShotVol=zfsPool+"/"+VolName+"@"+SnapShotVolume
            zfsSnapShotDir="/"+zfsPool+"/"+VolName+"/.zfs/snapshot/"+SnapShotVolume
            
            try:
                process1 = subprocess.check_output(["zfs", zfs_cmd, zfsSnapShotVol])
                process1 = subprocess.check_output(["rm", "-rf", zfsSnapShotDir])
                #sudo rm -rf /mnt/wo1/.zfs/snapshot/wo1-ss1
            except Exception as err:
                sprint ("except 1 Deleting SNAP",err)
                res=DB_SnapShotDelete(SnapShotVolume)
                return(res)
            
            try:
                zfs_cmd='promote'
                zfsDir=zfsPool+"/"+VolName
                process1 = subprocess.check_output(["zfs", zfs_cmd, zfsDir])

            except Exception as err:
                sprint ("except 2 promoting volume",err)
   
        result=DB_SnapShotDelete(SnapShotVolume)
        return result
    except Exception as err:
        sprint ("except 2 Deleting SNAP",err)
        res=DB_SnapShotDelete(SnapShotVolume)
        return(res)
        
        
        
def ForeignVolumeCreate():

    ForeignDbFileName="/mnt/system/quantumDB.db"
    res=CheckSerial(ForeignDbFileName)
    sprint ("CheckSerial res=",res)
    if res!=0:
        sprint ("Canister is foreign =",res)
        
        res=DB_UpdateHost("localNFS","","127.0.0.1","",nfs,"Single Host")
        if res[0]==0:
            LocalNFS_Host=res[1]
            
        res=DB_UpdateHost("localCIFS","sanuyi","127.0.0.1","hello123",cifs,"Single Host")
        if res[0]==0:
            LocalCIFS_Host=res[1]
            
        res=DB_UpdateHost("localiSCSI","","127.0.0.1","",iSCSI_NoChap,"Single Host")
        if res[0]==0:
            LocaliSCSI_Host=res[1]

        msg=str(LocalNFS_Host)+str(LocalCIFS_Host)+str(LocaliSCSI_Host)
        sprint ("HostIDs ",msg)
        BackupPortID=4
        lun=getFreeVolumeLun()
        ForeignDbFileName="/mnt/system/quantumDB.db"
        conn=sqlite3.connect(ForeignDbFileName)
        conn.execute('pragma foreign_keys=ON')
        c=conn.cursor()
        try:
            sprint ("ForeignVolumeCreate","step1")
            query=c.execute("select id, name,multi_device_id,state,type,location from volume")
            resp= c.fetchall()
            sprint ("Foreign Vols to start",resp)
            if resp !="None":
                for col in resp:
                    VolID=col[0]
                    VolName=col[1]
                    PoolID=col[2]
                    state=col[3]
                    vtype=col[4]
                    location=col[5]
                    element ="volume"
                    sprint ("vol=",VolName)
                    duplicate=False
                    if vtype!="Remote":
                        result=DB_CheckElement(element, VolName)
                        if (result!=0):
                            sprint ("wErrDuplicateName",VolName)
                            duplicate=True
                        query=c.execute("select system_name from multi_device where id=?",[PoolID])
                        resp=c.fetchone()
                        if str(resp) != str("None"):
                            PoolName = resp[0]
                            sprint ("PoolName=",PoolName)
                        query=c.execute("select host_id from export where vol_id=?",[VolID])
                        resp=c.fetchone()
                        if str(resp) != str("None"):
                            HostID = resp[0]
                            sprint ("HostID=",HostID)
                            query=c.execute("select protocol from host where id=?",[HostID])
                            resp=c.fetchone()
                            if str(resp) != str("None"):
                                ProtID = resp[0]        
                                sprint ("protocol=",ProtID)
                            portId=BackupPortID
                            if (ProtID ==nfs or ProtID ==nfs_RDMA):
                                LocalHostId=LocalNFS_Host
                            elif (ProtID ==cifs or ProtID ==cifs_RDMA):
                                LocalHostId=LocalCIFS_Host
                            elif ((ProtID==iSCSI_Chap) or (ProtID==iSCSI_NoChap) or (ProtID==iSER_NoChap) or (ProtID==iSER_Chap)):
                                LocalHostId=LocaliSCSI_Host
                            VolumeSize=100
                            V_type="Foreign"
                            zfsCompression="false"
                            zfsDedup="false"
                            backup="false"
                            thin="false"
                            sprint ("Calling DB_CreateVolumeBis",0)
                            if duplicate==False:
                                result=DB_CreateVolumeBis(PoolName,VolName,VolumeSize,zfsCompression, zfsDedup,V_type,backup,thin,location,lun)
                                if (result!=0):
                                     sprint ("DB_CreateVolumeBis Failed",str(result))
                                else:
                                    sprint ("DB_CreateVolumeBis Passed",str(result)) 
                                    msg=str(portId)+str(VolName)+str(LocalHostId)+str(lun)
                                    sprint ("Update Export",msg)
                                    DB_UpdateExport(PoolName,portId,VolName,LocalHostId,lun)
                                    lun=lun+1
                        if (ProtID ==nfs or ProtID ==nfs_RDMA or ProtID ==cifs or ProtID ==cifs_RDMA):
                            try:
                                arg1="-p"
                                mount="/mnt/"+VolName
                                sprint ("mkdir ",mount)
                                process1 = subprocess.check_output(["mkdir",arg1,mount])
                                sprint(process1,0)
                            except Exception as err:
                                sprint("mkdir except ",err)
                            try:
                                dev="/dev/"+PoolName+"/"+VolName
                                process1 = subprocess.check_output(["mount",dev,mount])
                                sprint ("mount ",dev+mount)
                                sprint(process1,0)
                            except Exception as err:
                                sprint("mount except ",err)
                            try:
                                arg2=mount
                                sprint ("Check mountpoint ",mount)
                                process1 = subprocess.check_output(["mountpoint",arg2]) #Check if mountpoint exists
                                sprint (process1,0)           
                            except Exception as err:
                                sprint("mountpoint except ",err)
                            try:
                                sprint ("Update scheduler ",VolName)
                                #MakeSchedule(name,action,srcVolID,DstVolID)

                            except Exception as err:
                                sprint("DB_ScheduleUpdate except ",err)
                        else:
                            sprint ("Volume is a block device ",VolName)
                    else:
                        sprint ("Volume is a remote device ",VolName)
            sprint ("End of for loop ",resp)           
            c.close()
            conn.close()
            return(0)
        
        except Exception as err:
            sprint ("except ForeignVolumeCreate",err)
            c.close()
            conn.close()
            return(wErrCommandFailed)

    return (0)


def VolumeCreate(zfsPool,VolName,VolumeSize,zfsCompression, zfsDedup,VolType,Vtype,priority):
# Check DB entry is available.
    element ="volume"
    result=DB_CheckElement(element, VolName)
    if (result!=0):
        sprint ("wErrDuplicateName",VolName)
        return(wErrDuplicateName)
    #exit with error
    #response="duplicate name"
    #ccmSendResponse(element,name,response)
    can='canx'
    location=getCanisterByPool(zfsPool)
    if location=='c0':
        can='can0/'
    elif location=='c1':
        can='can1/'
    elif location=='c2':
        can='can2/'
    lun=getFreeVolumeLun()
    if StorageBackend=="zfs":
        if VolumeSize==0:
            try:
                
                msg=str('system')+str(VolName)+str(VolumeSize)+str(zfsCompression)+str(zfsDedup)+str(Vtype)+str(priority)
                sprint ("Default DB Update Volume",msg)
                result=DB_CreateVolume('system',VolName,VolumeSize,zfsCompression, zfsDedup,Vtype,priority,lun)
                sprint ("DB Result",result)
                if (result!=0):
                    sprint ("wErrUpdateFailed", result)
                    return(wErrUpdateFailed)
                else:
                    sprint ("ZFS Default volume create OK",0)
                    return (0) 
            except Exception as err:
                sprint("Default DB except ",err)
                return(wErrCommandFailed)

        if (VolType=="F"):
            zfsCmd='create'
            Vol=zfsPool+"/"+VolName
            sprint ("creating zfs fs",VolName+str(VolumeSize))
            try:
                #zfs create wo2
                process1 = subprocess.check_output(["zfs", zfsCmd,Vol])
                sprint (process1,0)
                zfsCmd='set'
                arg1="mountpoint="+"/mnt/"+VolName
                arg2=Vol
                #sudo zfs set mountpoint=/mnt/wo2 p11/wo1
                process1 = subprocess.check_output(["zfs", zfsCmd,arg1,arg2])
                sprint (process1,0)
            except Exception as err:
                sprint ("except creating zfs fs",err)
                return(wErrCommandFailed)
                
            zfsCmd='set'
            zfsQuota="quota="+str(VolumeSize)+"G"
            sprint ("creating zfs quota =",zfsQuota+":"+Vol)
            #zfs set quota=10G tankcreating zfs quota/home/bonwick
            try:
                process1 = subprocess.check_output(["zfs", zfsCmd, zfsQuota,Vol])
                sprint (process1,0)
            except Exception as err:
                sprint ("except creating zfs quota",err)
                return(wErrCommandFailed)
                
        elif (VolType=="B"):
            zfsCmd='create'
            #zfs create -V 1G tank/disk1
            #zfs create -s -V 100g zonepool/thinvol2
            Vol=zfsPool+"/"+VolName
            sprint ("creating ZVOL ",VolName+str(VolumeSize))
            zfsArg1="-V"
            zfsSize=str(VolumeSize)+"G"
            sprint ("zfsSize",zfsSize)
            try:
                process1 = subprocess.check_output(["zfs", zfsCmd, zfsArg1,zfsSize, Vol])
                sprint (process1,0)
            except Exception as err:
                sprint ("except creating ZVOL",err)
                return(wErrCommandFailed)
        else:
            sprint ("Unknown Volume Type",VolType)
            return(wErrUpdateFailed)
    # Create DB entry and set its state.

        result=DB_CreateVolume(zfsPool,VolName,VolumeSize,zfsCompression, zfsDedup,Vtype,priority,lun)
        if (result!=0):
            sprint ("wErrUpdateFailed",result)
            return(wErrUpdateFailed)
        #exit with error
        #response="duplicate name"
        #ccmSendResponse(errLevel,element,name,response)
        #VolumeDelete(zfsPool,VolName)
        zfsCmd="set"
        try:
            if (zfsCompression=="false"):
                process1 = subprocess.check_output(["zfs", zfsCmd, "compression=off",Vol])
                sprint (process1,0)
            else:
                process1 = subprocess.check_output(["zfs", zfsCmd, "compression=lz4",Vol])
                sprint (process1,0)

            if (zfsDedup=="false"):
                process1 = subprocess.check_output(["zfs", zfsCmd, "dedup=off",Vol])
                sprint (process1,0)
            else:
                process1 = subprocess.check_output(["zfs", zfsCmd, "dedup=on",Vol])
                sprint (process1,0)
        except Exception as err:
            sprint ("except setting ZFS properties",err)
            return(wErrCommandFailed)
        return 0

    elif StorageBackend=="LVM":
        #https://habr.com/en/company/hetmansoftware/blog/547086/
        #https://landoflinux.com/linux_lvm_command_examples.html
        #zfsPool,VolName,VolumeSize,zfsCompression, zfsDedup,VolType
        vgName=zfsPool
        sprint ("Volume Name",VolName)
        VolSize=str(VolumeSize)+"G"
        sprint ("Volume size",str(VolSize))
        LVM_arg1="-n"
        LVM_arg2=VolName
        LVM_arg3="-L"
        LVM_arg4=VolSize
        LVM_arg5=vgName
        LVM_arg6="-y"
        if str(VolumeSize)!='0':
            try:
                #lvcreate -n rlv0 -L 500G pool_p2 -y
                msg=vgName+VolName+VolSize
                sprint ("lv create",msg)
                process1 = subprocess.check_output(["lvcreate",LVM_arg1,LVM_arg2,LVM_arg3,LVM_arg4,LVM_arg5,LVM_arg6])
                proc1="lvcreate"+str(process1)
                sprint(proc1,0)
                msg=str(zfsPool)+str(VolName)+str(VolumeSize)+str(zfsCompression)+str(zfsDedup)+str(Vtype)
                sprint ("DB Update Volume",msg)
                result=DB_CreateVolume(zfsPool,VolName,VolumeSize,zfsCompression, zfsDedup,Vtype,priority,lun)
                sprint ("DB Result",result)
                if (result!=0):
                    sprint ("wErrUpdateFailed", result)
                    return(wErrUpdateFailed)
            #zfsPool,VolName,VolumeSize,zfsCompression, zfsDedup,VolType
            except Exception as err:
                sprint("lvcreate except ",err)
                return(wErrCommandFailed)

            if (VolType=="F"):
                sprint ("File System",VolType) # Block device
                dev="/dev/"+vgName+"/"+VolName
                sprint ("device=",dev)
                LVM_arg1="-t"
                LVM_arg2="ext4"
                #mkfs.ext4 -O uninit_bg=1 -E lazy_itable_init=1
                try:
                    process1 = subprocess.check_output(["mkfs",LVM_arg1,LVM_arg2,dev])
                    sprint(process1,0)
                except Exception as err:
                    sprint("mkfs except ",err)
                    return(wErrCommandFailed)
                #Now mount the device
                #mkdir /mnt/lvstuffbackup
                #mount /dev/vgpool/lvstuffbackup /mnt/lvstuffbackup
                mount=LVMmnt+can+VolName
                try:
                    arg1="-p"
                    process1 = subprocess.check_output(["mkdir",arg1,mount])
                    sprint(process1,0)
                except Exception as err:
                    sprint("mkdir except ",err)
                    return(wErrCommandFailed)
                try:
                    process1 = subprocess.check_output(["mount",dev,mount])
                    sprint(process1,0)
                except Exception as err:
                    sprint("mount except ",err)
                    return(wErrCommandFailed)
                try:
                    arg2=mount
                    process1 = subprocess.check_output(["mountpoint",arg2]) #Check if mountpoint exists
                    sprint(process1,0)            
                except Exception as err:
                    sprint("mountpoint except ",err)
                    return(wErrCommandFailed)
                
            elif (VolType=="B"):
                sprint ("Block Device",VolType) # Block device
        else:
            try:
                
                msg=str('system')+str(VolName)+str(VolSize)+str(zfsCompression)+str(zfsDedup)+str(Vtype)
                sprint ("Default DB Update Volume",msg)
                result=DB_CreateVolume('system',VolName,VolumeSize,zfsCompression, zfsDedup,Vtype,priority,lun)
                sprint ("DB Result",result)
                if (result!=0):
                    sprint ("wErrUpdateFailed", result)
                    return(wErrUpdateFailed)
            except Exception as err:
                sprint("Default DB except ",err)
                return(wErrCommandFailed)
        return(0)

def VolumeUpdate(zfsPool,VolName,VolumeSize,zfsCompression, zfsDedup,priority):
    # Check DB entry is available.
    element ="volume"
    result=CheckDBElement(element, VolName)
    if (result==0):
        return(errNameNotFound)
    #exit with error
    #response="duplicate name"
    #ccmSendResponse(element,name,response)

    Vol=zfsPool+"/"+VolName
    sprint (Vol,VolumeSize)
    zfsCmd='set'
    zfsQuota="quota="+str(VolumeSize)+"G"
    sprint ("creating zfs quota =",zfs_quota)
    process1 = subprocess.check_output(["zfs", zfs_cmd, zfs_quota,vol])

    if (zfsCompression=="false"):
        process1 = subprocess.check_output(["zfs", zfs_cmd, "compression=off",vol])
        sprint (process1,0)
    else:
        process1 = subprocess.check_output(["zfs", zfs_cmd, "compression=lz4",vol])
        sprint (process1,0)

    if (zfsDedup=="false"):
        process1 = subprocess.check_output(["zfs", zfs_cmd, "dedup=off",vol])
        sprint (process1,0)
    else:
        process1 = subprocess.check_output(["zfs", zfs_cmd, "dedup=on",vol])
        sprint (process1,0)

    # Create DB entry and set its state.
    result=DB_UpdateVolume(zfsPool,VolName,VolumeSize,zfsCompression, zfsDedup,priority)
    if (result!=0):
        return(result)
    else:
        return 0
     
    #exit with error
    #response="duplicate name"
    #ccmSendResponse(errLevel,element,name,response)
    #VolumeDelete(zfsPool,VolName)
    
def VolumeDelete(zfsPool,VolName,protocol):
    Vol=zfsPool+"/"+VolName
    vgName=zfsPool
    sprint ("VolumeDelete",Vol)
    element ="volume"
    origin='null' 
    #sudo rm -rf /p1/wo1/.zfs to clear out any old snaps
    result=DB_GetElementState(element, VolName)
    if (int(result)==int(gVolOn)):
        sprint ("wErrVolumeInUse",VolName)
        return(wErrVolumeInUse)    
    
    if StorageBackend=="zfs":
        try:
            sprint ("VolumeDelete step -1",0)
            #zfs list -Hrt snapshot p1/wo1
            cmd = ["zfs", "list", "-Hrt", "snapshot",zfsPool+'/'+VolName]
            result = subprocess.run(cmd, capture_output=True, text=True)
            sprint ('snaps=',result)
            if result.returncode != 0:
                print("Error getting SNAPS:", result.stderr)
            else:
                vals=result.stdout.strip().split()
                LenSnaps=len(vals)
                print ('len snaps=',LenSnaps)
                print ('Snaps=',vals)
                i=0
                while (i<LenSnaps):
                    zfsSnapDir=vals[i]
                    zfsSnapx=zfsSnapDir.split('@')
                    parts=zfsSnapx[0].split('-')
                    print ('parts=',parts)
                    zfsRoot=parts[0]
                    #process1 = subprocess.check_output(["zfs", 'destroy', zfsSnapDir])
                    print ('zfsRoot',zfsRoot)
                    zfsSnap=zfsRoot+'@'+zfsSnapx[1]
                    print ('zfsSnapDir',zfsRoot,zfsSnap,zfsSnapDir)
                    i=i+5
                    
                if LenSnaps !=0:
                    sprint ('LenSnaps',LenSnaps)
                    #return(wErrVolumeInUse)
        except Exception as err:
            sprint ("except checking Snaps",err)


        #zfs get origin -H  p1/wo4-ss1-clone1
        try:
            sprint ("VolumeDelete step 0",0)
            cmd = ["zfs", "get", "origin", "-H",zfsPool+'/'+VolName]
            result = subprocess.run(cmd, capture_output=True, text=True)
            sprint ('result',result)
            if result.returncode != 0:
                print("Error zfs :", result.stderr)
            else:
                vals=result.stdout.strip().split()
                origin= vals[2]
                print ('origin1=',str(origin))
                my_index= origin.find("@",0,len(origin))
                print ('my_index=',my_index,len (origin))
                if my_index !=-1:
                    origin='-'
                print ('origin2=',origin)
                if origin!='-':
                    origin='dep'
        except Exception as err:
            sprint ("except checking Origen",err)
            origin='null'
            
        if origin =='dep' and LenSnaps !=0:  
            sprint ("wErrDependents",origin)
            return(wErrDependents)
        else:
            #return(-1)
            if origin!='null':
                sprint ("VolumeDelete step 3",0)
                #Check the state of this Volume
                #Check if exports on this volume
                #Check if VMs using this volume
                # sudo zfs destroy -fr p2/vm4
                zfsCmd="destroy"
                Vol=zfsPool+"/"+VolName
                sprint ("deleting zfs",Vol)
                zfs_args="-R"
                zfs_args="-fr"
                
                try:
                    if LenSnaps!=0:
                        process1 = subprocess.check_output(["zfs", 'promote', zfsRoot])
                    process1 = subprocess.check_output(["zfs", zfsCmd, zfs_args, Vol])
                    if LenSnaps!=0:
                        process1 = subprocess.check_output(["zfs", zfsCmd, zfs_args, zfsSnap])
                    sprint (process1,0)
                    mp='/mnt'+"/"+VolName
                    process1 = subprocess.check_output(["rm",'-rf' , mp])
                    sprint (process1,mp)
                    sprint ("VolumeDelete step 4",0)
                except Exception as err:
                    sprint ("except deleting ZFS Vol",err)
                    return(wErrVolumeInUse)
        try:
            sprint ("VolumeDelete step 5",0)
            DB_DeleteExport(element, VolName)
            sprint ("VolumeDelete step 6",0)
            DB_VolumeDelete(VolName)
            sprint ("VolumeDelete step 7",0)
            mp='/mnt'+"/"+VolName
            process1 = subprocess.check_output(["rm",'-rf' , mp])
            sprint (process1,mp)
            sprint ("VolumeDelete step 8",0)
        except Exception as err:
            sprint ("except VolumeDelete MP",err)

        return 0

        
    elif StorageBackend=="LVM":
    #zfsPool,VolName,protocol
        try:
            sprint ("deleting LVM Volume",VolName)
            #umount /mnt/lvstuff
            #lvremove /dev/vgpool/lvstuff
            #vgremove vgpool
            #pvremove /dev/sdb1 /dev/sdc1
            # check if volume is mounted
            val=getlvList()
            sprint ("lv list=", str(val[0])+str(val[1]))
            mount=LVMmnt+can+VolName
            arg2=mount
            isdir = os.path.isdir(mount)
            sprint ("isdir",isdir)
            if isdir==True:
                sprint ("removing mounts",arg2)
                try:
                    process1 = subprocess.check_output(["mountpoint",arg2]) #Check if mountpoint exists
                    sprint (process1,0)
                    mp=True
                except Exception as err:
                    process1 = subprocess.check_output(["rm","-rf", arg2])
                    mp=False
                    sprint ("mountpoint except ",err)
                    
                if mp==True:
                    try:
                        process1 = subprocess.check_output(["umount",'-f','-l',arg2])
                        sprint (process1,0)
                        time.sleep(2)
                        #needs to poll here until mountpoint is gone
                    except Exception as err:
                        sprint ("umount except ",err)
                   
                try:
                    #sudo rmdir -p /mnt/nfs_backup
                    arg1="-p"
                    arg2=mount
                    sprint ("rmdir",arg2)
                    process1 = subprocess.check_output(["rmdir",arg1,arg2])
                except Exception as err:
                    sprint ("rmdir except ",err)

            try:
                dev="/dev/"+vgName+"/"+VolName
                LVM_arg1="-y"
                process1 = subprocess.check_output(["lvremove",LVM_arg1,dev])
                #sudo lvremove /dev/p1/nfs1
            except Exception as err:
                sprint("lvremove except ",err)
            isdir = os.path.isdir(dev)
            sprint ("lvm isdir",(isdir))
            if isdir==False: 
                sprint ("deleting db export",VolName)
                DB_DeleteExport(element, VolName)
                sprint ("deleting db Volume",VolName)
                DB_VolumeDelete(VolName)
        except Exception as err:
            sprint ("VolumeDelete except  ",err)
            return -1
            
        return 0
        
def CheckCanisterVolumes(location):

    try:
        res=GetPools(location)
        if res[0]==0:
            pools=res[1]
            sprint("Pools detected",pools)
            if len(pools)!=0:
                for pool in pools:
                    vols=OrphanVolumeCreate(pool,location)
                    sprint ("Updated OrphanVolumes()",vols)
            else:
                sprint ("No Pools Detected",0)
        else:
            sprint ("Error reading Pools Detected",0)
        return (0)
        
    except Exception as err:
        sprint ("VolumeDelete except  ",err)
        return -1
            
def GetSmartData(disk):

    mockdata    = [{"id":0,"headerData":{"HealthStatus":"Normal","Temprature":"53deg C","TestResult":"Success","SectorErrorCount":89},"Attributes":[{"Name":"Start/Stop Count","value":"3","Normalized":"26","Threshold":"1","worst":"99","Type":"Old Age","Assessment":"OK"},{"Name":"Spin Retry Count","value":"35","Normalized":"66","Threshold":"6","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Power On Time","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Read error Rate","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Seek error rate","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Power On errors","value":"3","Normalized":"45","Threshold":"9","worst":"87","Type":"Pre Fail","Assessment":"OK"},{"Name":"SSD Erase fail count","value":"44","Normalized":"37","Threshold":"99","worst":"7","Type":"Pre Fail","Assessment":"OK"},{"Name":"Power loss protection failure","value":"32","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Head stablility","value":"34","Normalized":"66","Threshold":"9","worst":"80","Type":"Pre Fail","Assessment":"OK"},{"Name":"High fly writes","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Load cycle count","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"G sense error rate","value":"3","Normalized":"1","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"Fail"}]},
                   {"id":1,"headerData":{"HealthStatus":"Good","Temprature":"4deg C","TestResult":"Success","SectorErrorCount":50},"Attributes":[{"Name":"Start/Stop Count","value":"3","Normalized":"26","Threshold":"1","worst":"99","Type":"Old Age","Assessment":"OK"},{"Name":"Spin Retry Count","value":"8","Normalized":"66","Threshold":"6","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Power On Time","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Read error Rate","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Seek error rate","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Power On errors","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"SSD Erase fail count","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Power loss protection failure","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Head stablility","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"High fly writes","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Load cycle count","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"G sense error rate","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"}]},
                   {"id":2,"headerData":{"HealthStatus":"Weak","Temprature":"53deg C","TestResult":"Success","SectorErrorCount":8},"Attributes":[{"Name":"Start/Stop Count","value":"3","Normalized":"26","Threshold":"1","worst":"99","Type":"Old Age","Assessment":"OK"},{"Name":"Spin Retry Count","value":"76","Normalized":"66","Threshold":"6","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Power On Time","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Read error Rate","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Seek error rate","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Power On errors","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"SSD Erase fail count","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Power loss protection failure","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Head stablility","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"High fly writes","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Load cycle count","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"G sense error rate","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"}]},
                   {"id":3,"headerData":{"HealthStatus":"Good","Temprature":"3deg C","TestResult":"Success","SectorErrorCount":45},"Attributes":[{"Name":"Start/Stop Count","value":"3","Normalized":"26","Threshold":"1","worst":"99","Type":"Old Age","Assessment":"OK"},{"Name":"Spin Retry Count","value":"35","Normalized":"66","Threshold":"6","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Power On Time","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Read error Rate","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Seek error rate","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Power On errors","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"SSD Erase fail count","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Power loss protection failure","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Head stablility","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"High fly writes","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Load cycle count","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"G sense error rate","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"}]},
                   {"id":4,"headerData":{"HealthStatus":"Normal","Temprature":"33deg C","TestResult":"Success","SectorErrorCount":40},"Attributes":[{"Name":"Start/Stop Count","value":"3","Normalized":"26","Threshold":"1","worst":"99","Type":"Old Age","Assessment":"OK"},{"Name":"Spin Retry Count","value":"35","Normalized":"66","Threshold":"6","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Power On Time","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Read error Rate","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Seek error rate","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Power On errors","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"SSD Erase fail count","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Power loss protection failure","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Head stablility","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"High fly writes","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Load cycle count","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"G sense error rate","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"}]},
                   {"id":5,"headerData":{"HealthStatus":"Fail","Temprature":"100deg C","TestResult":"Fail","SectorErrorCount":9},"Attributes":[{"Name":"Start/Stop Count","value":"3000","Normalized":"26","Threshold":"1","worst":"99","Type":"Old Age","Assessment":"OK"},{"Name":"Spin Retry Count","value":"35","Normalized":"66","Threshold":"6","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Power On Time","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Read error Rate","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Seek error rate","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Power On errors","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"SSD Erase fail count","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Power loss protection failure","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Head stablility","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"High fly writes","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"Load cycle count","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"},{"Name":"G sense error rate","value":"3","Normalized":"66","Threshold":"9","worst":"99","Type":"Pre Fail","Assessment":"OK"}]},
                   ]
    return mockdata



def gui_name(table_name,gui_Dpname):
    suffix=1
    db_name=gui_Dpname
    conn=db_connect()
    conn.text_factory=str
    c=conn.cursor()
    c.execute("select name from "+table_name+"  where id=(SELECT MAX(ID)  FROM "+table_name+")")
    name=c.fetchone()
    conn.commit()
    try:
        if not name:
            gui_name = db_name+"_"+str(suffix)
        else:
            c.execute("select name from "+table_name+" where id=(SELECT MAX(ID)  FROM "+table_name+")")
            conn.commit()
            append_int=int(c.fetchone()[0].split("_")[1])
            append=suffix+append_int
            gui_name = db_name+"_"+str(append)
    except Exception as e:
        c.execute("select id from "+table_name+" where id=(SELECT MAX(ID) FROM "+table_name+")")
        max_id = c.fetchone()
        conn.commit()
        gui_name = db_name+"_"+str(max_id)

    c.close()
    conn.close()
    return gui_name


def DB_UpdateFan(fanSystemName,fanSpeed,fanState,fanAction,fanName,fanLocation):
    if fanName == '' or fanName==None:
        name=gui_name("fan","Fan")
    else:
        name = fanName
    #print"IN DB_UPDATE FAN systemName:ServerName",name,fanSystemName
    if name=="Fan#F1":
        low_threshold=2000      #########################WOTEST###############is this correct?
        hi_threshold=9500
    elif name=="Fan#F2":
        low_threshold=2000
        hi_threshold=9500
    elif name=="Fan#R1":
        low_threshold=2000
        hi_threshold=17000
    elif name=="Fan#CPU":
        low_threshold=1000
        hi_threshold=7000
    
    
    elif name == "Fan1":
        low_threshold=1000
        hi_threshold=9500
    elif name == "Fan2":
        low_threshold=1000
        hi_threshold=9500
    elif name == "FanA":
        low_threshold=1000
        hi_threshold=9500
        
    else:
        low_threshold = 1000
        hi_threshold = 9000
    
        
    conn=db_connect()
    conn.text_factory = str
    c=conn.cursor()
    query=c.execute("select id,low_threshold,hi_threshold from fan where system_name='"+fanSystemName+"'")
    resp=c.fetchall()
    sprint (resp,0)
    msg=fanSystemName+fanSpeed+fanState+fanAction+fanName+fanLocation
    sprint ("Fan Update",msg)
    if resp == [] or resp ==None:
        #queryInsert  =c.execute("select from fan low_threshold,low_threshold where n(name,system_name,speed,state,cr_date,edit_date,controller_id,low_threshold,hi_threshold,location) values(?,?,?,?,datetime(),datetime(),1,?,?,?)",[name,fanSystemName,fanSpeed,fanState,low_threshold,hi_threshold,fanLocation])
        #conn.commit()
        queryInsert  =c.execute("insert into fan(name,system_name,speed,state,cr_date,edit_date,controller_id,low_threshold,hi_threshold,location) values(?,?,?,?,datetime(),datetime(),1,?,?,?)",[name,fanSystemName,fanSpeed,fanState,low_threshold,hi_threshold,fanLocation])
        conn.commit()
    else:
        if resp[0][1]!=None:
            low_threshold=resp[0][1]
        if resp[0][2]!=None:
            hi_threshold=resp[0][2]
    sprint (fanSpeed,hi_threshold+low_threshold)
    if int(fanSpeed) < int(hi_threshold):
        if int(fanSpeed) > int(low_threshold):
               fanState=0
        else: 
                fanState=2
    else:
        fanState=2
    queryUpdate = c.execute("update fan set name=?,state=?,speed=?,location=? where system_name=?",[name,fanState,fanSpeed,fanLocation,fanSystemName])
    conn.commit()
    sprint ("Update Fan Successfully",0)
    c.close()
    conn.close()


def DB_UpdatePSU(psuSystemName,psuState,psuAction,DC_Status):
    name=gui_name("psu","PSU")
    conn=db_connect()
    conn.text_factory = str
    c=conn.cursor()
    query=c.execute("select count(*) from psu where system_name='"+psuSystemName+"'")
    count = c.fetchone()[0]
    if count==0:
        queryInsert = c.execute("insert into psu(name,system_name,state,cr_date,edit_date,dc_status,controller_id) values(?,?,?,datetime(),datetime(),?,1)",[name,psuSystemName,psuState,DC_Status])
        conn.commit()
    else:
        queryUpdate = c.execute("update psu set dc_status=? where system_name=?",[DC_Status,psuSystemName])
        conn.commit()
    c.close()
    conn.close()

def DB_UpdateTempProbes(probeName,probeSysName,probeState,probeAction,probeTemp):
    tempLow="10"
    tempHigh="90"
    conn=db_connect()
    conn.text_factory = str
    c=conn.cursor()
    query=c.execute("select count(*) from temp_probes where system_name='"+probeSysName+"'")
    count = c.fetchone()[0]
    if count==0:
        queryInsert  =c.execute("insert into temp_probes(name,system_name,temp,state,cr_date,edit_date,controller_id,low_threshold,hi_threshold) values(?,?,?,?,datetime(),datetime(),1,?,?)",[probeName,probeSysName,probeTemp,probeState,tempLow,tempHigh])
        conn.commit()
    else:
        queryUpdate = c.execute("update temp_probes set temp=? where system_name=?",[probeTemp,probeSysName])
        conn.commit()
    c.close()
    conn.close()

def updateController(V_3V,V_3VSB,V_5V,V_5VSB,V_12V,V_VCCP,name):
    conn = db_connect()
    conn.text_factory = str
    c = conn.cursor()
    #print "Executing the Controller Query"
    try:
        query = c.execute("update controller set 'V_3.3V'=?,'V_3.3V-SB'=?,V_5V=?,V_5V_SB=?,V_12V=?,V_VCCP=?,edit_date=datetime()",[V_3V,V_3VSB,V_5V,V_5VSB,V_12V,V_VCCP])
        conn.commit()
    except Exception as e:
        sprint ("updateController error",e)
    c.close()
    conn.close()

#def loggerArgs(element,elementName,loglevel,action):
#        print "in loggerArgs"
#        loggerArgs={}
#        loggerArgs['element']=element
#        loggerArgs['elementname']=elementName
#        loggerArgs['LogLevel']=loglevel
#        loggerArgs['action']=action
#        return loggerArgs
#######################################################
#shutdown
def shutdown():
    
    sprint ("Shutdown called",0)
    if StorageBackend=="zfs":
        sprint ("ZFS is enabled",0)
        res=GetPools("cx")
        if res[0]==0:
            pools=res[1]
            sprint ("zfs pools=",pools)
            arg1="export"
            for pool in pools:
                if pool !='system':
                    try:
                        process = subprocess.check_output(["zpool",arg1,pool])
                        sprint (process,0)
                    except Exception as err:    
                        sprint ("zfs export error",err)
                        continue
            arg2="list"
            process = subprocess.check_output(["zpool",arg2])
            sprint (process,0)
        else:
            sprint ("ZFS not enabled",0)
    try:
        #service docker stop
        process = subprocess.check_output(["service","docker","stop"])
    except Exception as err:
        msg1= "service docker stop except="
        sprint (msg1,err)
        
        
        
def SIGTERM_iterrupt(signalNumber, frame):
    global G15
    
    res=CheckBaseBoard("X570D4I-2T")    #R6000 standard baseboard
    if res==0:
       WDen=True
       sprint ("R6000 detected",0)  
    else:
       WDen=False
 
    res=CheckBaseBoard("015C68")
    if res==0:
       WDen=True
       sprint ("DELL detected",0) 
       
    sprint("Handling interrupt",signalNumber)
    if signalNumber==0:
        return(0)
    try:
        if signalNumber==15:
            if G15==True:
                sprint("G15 is True, re-entered SIGTERM, returning to caller",signalNumber)
                return(0)
            else:
                G15=True
                sprint("Setting G15 to True",signalNumber)
    except Exception as e:
        sprint ("SIGTERM_iterrupt except",e)
      

    #stop the watchdog 
    
    BackUpDB2SystemVolume()
    res=PoolStop('MegaRAID',all,'none')
    shutdown()
        
    redis_conn=Redis()
    workers = Worker.all(connection=redis_conn)
    Q=True
    loop=0
    sprint("Handling interrupt",signalNumber)
    while Q==True:
        workers = Worker.all(connection=redis_conn)
        nbWorkers=len(workers)
        if nbWorkers==0:
            sprint ("No More Workers",0)
            try:
                file="/mnt/data/boot.crm"
                msg="delete crumb="+file
                sprint (msg,0)
                process = subprocess.check_output(["rm",file])
            except Exception as e:
                sprint (msg,e)
            try:
                msg="stopping Threads except"
                Tthread.terminate()
                Ithread.terminate()
                wd("stop",0,WDen)
                time.sleep(2)
                wd("stop",0,WDen)
                arg1="stop"
                arg2="apache2.service"
                sprint ("Stopping Apache2", arg2)
                process = subprocess.check_output(["systemctl",arg1,arg2])
                #stop rest services
            except Exception as e:
                sprint (msg,e)
                
            if (signalNumber==0 and frame==0):
                sprint ("Exiting to sys from SIGTERM_iterrupt",signalNumber)
                exit(0)
            else:
                sprint ("Returning to caller from SIGTERM_iterrupt",signalNumber)
                exit(0)

        for w in workers:
            name=w.name.split(".")
            pid = int(w.pid)
            sprint ("pid",pid)
            os.kill(pid, signal.SIGINT)
            sprint ("loop",loop)
            loop=loop+1
            time.sleep(2)

def SIGHUP_iterrupt (signalNumber, frame):
    sprint ("SIGHUP_iterrupt",signalNumber)
    time.sleep(10)
    exit(0)
     
def receiveSignal(signalNumber, frame):
    sprint("Handling interrupt",signalNumber)
    time.sleep(10)    
    exit(0)

def CheckBoot():
    return 0
    
    

def getAllLVMbyIdDisks():
        LVM_arg1="-C"
        LVM_arg2="--noheadings"
        LVM_arg3="--reportformat"
        LVM_arg4="json"
        PVlist=[]
        #mega
        #sudo pvdisplay -C --noheadings --reportformat json
        process1 = subprocess.check_output(["pvdisplay",LVM_arg1,LVM_arg2,LVM_arg3,LVM_arg4])
        #print(process1)
        y = json.loads(process1)
        NbPv= len(y['report'][0]['pv'])
        i=0
        sprint ("NbPv",NbPv)
        while (i < NbPv):
            dev=str(y['report'][0]['pv'][i]['pv_name'])
            PVlist.append(dev)
            i=i+1
        sprint ("PVlist",PVlist)
        i=0
        return 0,PVlist
        
def DeleteOnStart():
    md_id=0
    try:
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        query=c.execute("select reset_on_db from system")
        resp=c.fetchone()
        conn.commit()
        roe='no'
        if str(resp) != None:
            roe=resp[0]
        sprint ("reset_on_start",roe)
        if roe=='yes':
            query=c.execute("delete from  volume where size !=0")
            conn.commit()
            query=c.execute("select id from  volume where size =0")
            resp=c.fetchone()
            conn.commit()
            sprint ("vol id resp=",resp)
            if str(resp) != None:
                vol_id=resp[0]
                # select id from from volume where size=0
                #delete all exports except default exports.
                query=c.execute("delete from export where vol_id !=?",[vol_id])
                conn.commit()
            else:
                query=c.execute("delete from export ")
                conn.commit()
            
            system='system'            
            query=c.execute("select id from  multi_device where system_name=?",[system])
            resp=c.fetchone()
            conn.commit()
            sprint ("system id resp=",resp)
            if str(resp) != None:
                md_id=resp[0]
            system_id=md_id
            sprint ("system id=",system_id)
            query=c.execute("delete from  multi_device where id !=?",[system_id])
            conn.commit()
        c.close()
        conn.close()
        sprint ("DeleteOnStart completed",0)
    except Exception as e:
        c.close()
        conn.close()
        sprint ("DeleteOnStart except",e)
        
def DeleteOnExtraction(cx):
#Only delete CX resources
    sprint ("DeleteOnExtraction start",cx)
    md_id=0
    if cx=='/c0':
        location='c0'
    elif cx=='/c1':
        location='c1'
    elif cx=='/c2':
        location='c2'
   
    try:
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        query=c.execute("select reset_on_extraction from system")
        resp=c.fetchone()
        conn.commit()
        roe='no'
        if str(resp) != None:
            roe=resp[0]
        sprint ("reset_on_extraction=",roe)
        if roe=='yes':
            #step1 select pools with location = cx
            query=c.execute("select id from  multi_device where location=?",[location])
            resp = c.fetchall()
            sprint ("Multi Device values",resp)
            if resp !="None":
                for col in resp:
                    pool_id=col[0]
                    query=c.execute("select id from  volume where multi_device_id=?",[pool_id])
                    resp1 = c.fetchall()
                    sprint ("Volume IDs to delete=",resp1)
                    for col1 in resp1:
                        vol_id=col1[0]
                        sprint ("Volume ID to delete=",vol_id)
                        query=c.execute("delete from export where vol_id=?",[vol_id])
                        conn.commit()
                        sprint ("Volume ID to delete=",vol_id)
                        query=c.execute("delete from volume where id=?",[vol_id])                
                        conn.commit()
                    query=c.execute("delete from  multi_device where id=?",[pool_id])
                    conn.commit()
            Do=False
            if Do==True:
                query=c.execute("select id from  volume where size =0")
                resp=c.fetchone()
                conn.commit()
                sprint ("default vol id resp=",resp)
                if str(resp) !=None:
                    vol_id=resp[0]
                    # select id from from volume where size=0
                    #delete all exports except default exports.
                    query=c.execute("delete from export where vol_id !=?",[vol_id])
                    conn.commit()
                else:
                    query=c.execute("delete from export ")
                    conn.commit()
            
                system='system'            
                query=c.execute("select id from  multi_device where system_name=?",[system])
                resp=c.fetchone()
                conn.commit()
                sprint ("system id resp=",resp)
                if str(resp) !=None:
                    md_id=resp[0]
                    system_id=md_id
                    sprint ("system id=",system_id)
                    query=c.execute("delete from  multi_device where id !=?",[system_id])
                    conn.commit()
        c.close()
        conn.close()
        sprint ("DeleteOnExtraction completed",0)
    except Exception as e:
        c.close()
        conn.close()
        sprint ("DeleteOnExtraction except",e)

#CanisterReset
#ResetCanister
def factory(element):
    vglist=[]
    #PVlist=[]
    WDen = True
    wd("stop",0,WDen)
    try:
        res=0
        conn=db_connect()
        conn.text_factory=str
        c=conn.cursor()
        if element=='volume':
            SetVolumesOnOff('off','c0')
            SetVolumesOnOff('off','c1')
            SetVolumesOnOff('off','c2')
            SetDevicesOnOff('off')
            query=c.execute("delete from  volume")
            conn.commit()
            query = c.execute("delete from export")
            conn.commit()
        if element=='pool':
            query=c.execute("delete from  multi_device")
            conn.commit()
        if element=='MegaRAID':
            res=PoolStop('MegaRAID','factory','none') ##This will be the st.py poolstop

            LVM_arg1="-C"
            LVM_arg2="--noheadings"
            LVM_arg3="--reportformat"
            LVM_arg4="json"
            #sudo vgdisplay -C --noheadings --reportformat json
            process1 = subprocess.check_output(["vgdisplay",LVM_arg1,LVM_arg2,LVM_arg3,LVM_arg4]).decode("utf-8")
            sprint("## vgdisplay ###",0)
            #print(process1)
            sprint(process1,0)
            y = json.loads(process1)
            NbVg= len(y['report'][0]['vg'])
            i=0
            sprint ("NbVg",NbVg)
            #print (y['report'])
            i=0
            while (i < NbVg):
                #print (y['report'][0]['vg'])
                PoolName=y['report'][0]['vg'][i]['vg_name']
                i=i+1
                #PVlist.append(PoolName)
                vglist.append(PoolName)
            
            for vg in vglist:
                #LVM_arg1="-q"
                LVM_arg2="-ff"
                LVM_arg3 = "-y"
                sprint ("VG Remove",vg)
                #sudo vgremove -q -ff -y pa
                #process1 = subprocess.check_output(["vgremove",LVM_arg1,LVM_arg2,LVM_arg3,vg]).decode("utf-8")
                process1 = subprocess.check_output(["vgremove",LVM_arg2,LVM_arg3,vg]).decode("utf-8")
                sprint("#### vgremove ####",0)
                sprint(process1,0)

                #############
            val=getAllLVMbyIdDisks()
            print (val)
            LVM_arg1="-y"
            LVM_arg2="-v"
            LVM_arg3="-ff"
            if val[0]==0:
                pvlist =val[1]
                for pv in pvlist:
                #sudo pvremove /dev/sdb -v -ff
                    sprint ("pvremove args=",pv)
                    try:
                        process1 = subprocess.check_output(["pvremove",pv,LVM_arg1,LVM_arg2,LVM_arg3])
                        sprint("### pvremove ###",0)
                        sprint(process1,0)
                    except Exception as e:
                        sprint ("pvremove except",e)
                
            storcli="/opt/MegaRAID/storcli/storcli64"
            #sudo /opt/MegaRAID/storcli/storcli64 /c0/vall delete J
            MR_list = ['/c0', '/c1', '/c2']
            for cx in MR_list:
                try:
                    arg1=cx+"/vall"
                    cmd="delete"
                    argLast='J'
                    process1 = subprocess.check_output([storcli,arg1,cmd,argLast])
                    sprint (process1,0)
                except Exception as e:
                    sprint ("storcli delete except",e)
            res = 0
            location='c0'
            FakePoolCreate("system","system",0,0,location) 
        c.close()
        conn.close()
        
    except Exception as e:
        c.close()
        conn.close()
        sprint ("factory except",e)
        res = -1
    wd("stop",0,WDen)  
    #conn.commit()
    #c.close()
    #conn.close()
    return (res)

def createNetwork(name,cidr,dhcp):
    db_open = False
    try:
        conn=db_connect()
        db_open = True
        conn.text_factory = str
        c=conn.cursor()
        query_setup_network = c.execute(" insert into network(name,cidr,enable_dhcp,state,cr_date,edit_date) values(?,?,?,?,datetime(),datetime())",\
                                        (name, cidr, dhcp, 0))
        conn.commit()
        print("network created")
        db_open = False
        c.close()
        conn.close()
        return 0
    except Exception as e:
        if db_open:
            try:
                c.close()
                conn.close()
            except Exception:
                pass
        return -1

def deleteNetwork(ntwID):
    db_open = False
    try:
        conn=db_connect()
        db_open = True
        conn.text_factory = str
        c=conn.cursor()
        dlt_ntw = c.execute("delete from network where id={}".format(ntwID))
        conn.commit()
        db_open = False
        c.close()
        conn.close()
        return 0
    except Exception as e:
        if db_open:
            try:
                c.close()
                conn.close()
            except Exception:
                pass
        return -1

def editNetwork(ntwID,ntwName,cidr,dhcp):
    db_open = False
    try:
        conn=db_connect()
        db_open = True
        conn.text_factory = str
        c=conn.cursor()
        query_update_network = c.execute("update network set name=?,cidr=?,enable_dhcp=?,edit_date=datetime() where id=?",\
                                        (ntwName, cidr, dhcp, ntwID))
        conn.commit()
        db_open = False
        c.close()
        conn.close()
        return 0
    except Exception as e:
        if db_open:
            try:
                c.close()
                conn.close()
            except Exception:
                pass
        return -1


def run_restore_in_background(scheduleId, schHistoryId, schRestorPoint, schSourceVol, schDestinationVol, schDestVolName, schDestVolId, sourceDirectories):
    loop = 0
    MaxLoop = 20
    transferredPer = '0'
    remote_share = '/mnt'
    backup_folder_name = schDestinationVol+"/"+schSourceVol
    backup_path = os.path.join(remote_share, backup_folder_name)
    source_root_dir = remote_share + "/" + schDestVolName  + "/restore/" + schSourceVol

    DB_Open = False
    BkUp_Error = True

    try:
        conn=sqlite3.connect(DBPath,check_same_thread=False)
        conn.text_factory=str
        c=conn.cursor()
        DB_Open = True

        c.execute("select action from schedule where id = ?",(str(scheduleId),))
        schedule = c.fetchone()
        if not schedule:
            print("Schedule not found")
            return
        
        action = schedule[0]

        query_lan=c.execute("select * from schedule_history where id="+str(schHistoryId)+"")
        result = c.fetchone()
        conn.commit()

        date_part = result[2]
        time_part = result[3]
        
        dt_obj = datetime.datetime.strptime(date_part, "%Y-%m-%d")
        formatted_date = dt_obj.strftime("%d-%m-%Y")

        folder_prefix = f"bkp {formatted_date} {time_part}"   
        
        backp_folder_name = None

        if action == "Differential Backup":
            diff_bkp_path = os.path.join(backup_path, "diff_bkp")
            subfolders = [f for f in os.listdir(diff_bkp_path) if os.path.isdir(os.path.join(diff_bkp_path, f))]
            if not subfolders:
                print("No folders found under diff_bkp")
                return
            dstBkpPath = os.path.join(diff_bkp_path, subfolders[0])
            source_root_dir = os.path.join(source_root_dir, "diff_bkp")
        else:
            for folder in os.listdir(backup_path):
                if folder == folder_prefix:
                    backp_folder_name = folder
            
            if not backp_folder_name:
                print("Backup folder not found")
                return
                    
            dstBkpPath = os.path.join(backup_path, backp_folder_name)
            source_root_dir = os.path.join(source_root_dir, "full_bkp")

        current_date = datetime.datetime.now()
        timestamp = current_date.strftime('%d-%m-%Y_%H-%M-%S')
        restore_file_name = f"res_{timestamp}"
        source_root_dir = os.path.join(source_root_dir, restore_file_name)

        sourceDirectories=sourceDirectories.split(',,')[:-1]

        sourceDirs = ''
        for x in sourceDirectories:
            if not x.strip():
                continue
            name = x.strip("/")
            full_path = os.path.join(dstBkpPath, name)

            if os.path.isdir(full_path):
                sourceDirs += f'--include "/{name}/**" '
            else:
                sourceDirs += f'--include "/{name}" '
        if not sourceDirs:
            sourceDirs = '--include "**" '

        c.execute("""INSERT INTO restore_info (name,schedule_id,vol_dest_id,complete_date,complete_time,result) VALUES(?,?,?,?,?,?)""",[restore_file_name,scheduleId,schDestVolId,current_date.strftime('%Y-%m-%d'), current_date.strftime('%H:%M'),'In Progress'])
        conn.commit()
        restore_id = c.lastrowid
        
        command = f'sudo rclone copy "{dstBkpPath}/" "{source_root_dir}" {sourceDirs} --create-empty-src-dirs -P'
        proc = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE,stderr=subprocess.STDOUT)

        while True:
            line = proc.stdout.readline().decode("utf-8")
            if not line:
                time.sleep(0.5)
                loop += 1
                if loop == MaxLoop:
                    BkUp_Error = True
                    break
                continue

            if 'Transferred' in line.strip() and 'ETA' in line.strip():
                transferredPer = line.rstrip().split('Transferred',1)[-1].split(',')[1].strip().split('%')[0].strip()

                c.execute("UPDATE restore_info SET result=? WHERE id=?", 
                          [transferredPer, restore_id])
                conn.commit()
                if transferredPer == '100':
                    BkUp_Error = False
                    c.execute("UPDATE restore_info SET result=? WHERE id=?", 
                              ['Success', restore_id])
                    conn.commit()
                    break

            if 'Errors' in line:
                BkUp_Error = True
                break

            time.sleep(0.1)
        
        if BkUp_Error:
            c.execute("UPDATE restore_info SET result=? WHERE id=?", 
                      ['Failed', restore_id])
            conn.commit()

        if DB_Open:
            c.close()
            conn.close()
            DB_Open = False

    except Exception as err:
        if DB_Open:
            c.close()
            conn.close()
            DB_Open = False
        print(f"Restore failed: {err}")

def server_manager(p,q):
    global Tthread
    global Ithread
    global PowerOff
    global ST_logger
    global STCON_logger
    global G15
    global DelOnExtraction
    global raptor
    
    SetStorageBackend()
    PowerOff=False
    DelOnExtraction=True
    Tthread=p
    Ithread=q
    MyCanister='/c0'
    CanisterPresent=[False,False,False]
    CheckCanister=[True,True,True]
    CanisterPresent[0]=True
    CanisterPresent[1]=True
    CanisterPresent[2]=True
    #CanisterPresent=True
 
    res=GetBaseBoard()
    if res[0]==0:
        if res[1]=="X570D4I-2T":
            CheckCanister=[True,True,True]
        elif res[1]=="H12SSL-I":
            CheckCanister=[True,True,True]
            raptor=True
        else:
            if res[1]=="X13SAV-LVDS" :
                CheckCanister=[True,True,True]
            else: 
                CheckCanister=[False,False,False]
    G15=False
    sprint ("Server Step ",1)
    signal.signal(signal.SIGTERM, SIGTERM_iterrupt)
    signal.signal(signal.SIGHUP, SIGHUP_iterrupt)
    signal.signal(signal.SIGINT, receiveSignal)
    signal.signal(signal.SIGQUIT, receiveSignal)
    signal.signal(signal.SIGILL, receiveSignal)
    signal.signal(signal.SIGTRAP, receiveSignal)
    signal.signal(signal.SIGABRT, receiveSignal)
    signal.signal(signal.SIGBUS, receiveSignal)
    signal.signal(signal.SIGFPE, receiveSignal)
    signal.signal(signal.SIGUSR1, receiveSignal)
    signal.signal(signal.SIGSEGV, receiveSignal)
    signal.signal(signal.SIGUSR2, receiveSignal)
    signal.signal(signal.SIGPIPE, receiveSignal)
    signal.signal(signal.SIGALRM, receiveSignal)

    rm_logs()
    #ST_logger=init_logger("ST")
    sprint (ST_logger[0],ST_logger[1])
    sprint (STCON_logger[0],STCON_logger[1])
    #touch /run/casper-no-prompt
    process1= subprocess.check_output(['touch','/run/casper-no-prompt'])
    sprint (process1,0)
    TimerLoop=0
    log_elt="SERVER Manager"
    #initLogging(log_elt)
    log_eltName="SM"
    STlogLevel=20
    LogAction="Init CCM Logging"
    LogMsg="Init"
    dArgs=loggerArgs(log_elt,log_eltName,STlogLevel,LogAction)
    ccmLogger(INFO,LogMsg,dArgs)
    res=CheckBoot()
    if res !=0:
        LogAction="Checking restart"
        LogMsg="Reboot from unscheduled power down"
        dArgs=loggerArgs(log_elt,log_eltName,STlogLevel,LogAction)
        ccmLogger(ccmINFO,LogMsg,dArgs)
    else:
        LogAction="Checking restart"
        LogMsg="Reboot from scheduled power down"
        dArgs=loggerArgs(log_elt,log_eltName,STlogLevel,LogAction)
        ccmLogger(ccmCRITICAL,LogMsg,dArgs)
    # Legacy auto-create of docker1 bridge at boot – now disabled because
    # Docker networks are managed via GUI (element=docker/NetworkCreate).
    if False:
        try:
            netName = 'docker1'
            cidr = getNetworkCIDR(netName)
            # NOTE: we previously hard-coded gw='192.168.128.71' which can be outside cidr.
            # Fix/normalize the gateway to live inside the CIDR (first usable if invalid).
            desired_gw = '192.168.128.71'  # keep whatever default you had
            gw = _fix_gateway_for_cidr(cidr, desired_gw)

            if gw != desired_gw:
                sprint(f"[NET] Adjusted gateway to {gw} to match {cidr} (was {desired_gw})", 0)

            sprint('DCK step 1', cidr)
            rc = DockerNetworkCreate(cidr, gw, netName, "BOOT")
            sprint('DCK step 2', rc)
            sprint('DockerNetworkCreate=', f"{cidr}/{gw}/{netName}")

            if rc == -14:
                sprint("[ERR] DockerNetworkCreate: invalid CIDR", 0)
            elif rc == -15:
                # Can be invalid gateway OR CIDR rejected by policy (overlap with host/restricted)
                sprint("[WARN] DockerNetworkCreate: invalid gateway or CIDR rejected by policy (overlap)", 0)
            elif rc == -16:
                sprint("[ERR] DockerNetworkCreate: Docker API error (name conflict/overlap/engine error)", 0)
            elif rc == 0:
                sprint('DCK step 2 rc=', rc)

        except Exception as err:
            sprint('[EXC] DockerNetworkCreate raised', repr(err))
            sprint(traceback.format_exc(), 0)
    #choice=raw_input("<c> to continue <x> exit")
    server_address=uds_socket_path #defined in globalSettings.py
    response="<rsp>0x1234,0x1234,"
    try:
        os.unlink(server_address)
    except OSError:
        if os.path.exists(server_address):
            raise
    sock=socket.socket(socket.AF_UNIX,socket.SOCK_STREAM)
    #logging.debug("Starting upon %s,"%server_address)
    sock.bind(server_address)
    countMessage = 0
    my_job_id=0
    redis=True
    if redis==True:
        set_gRun_ftp(1)
        redis_conn=Redis()
        workers = Worker.all(connection=redis_conn)
        for w in workers:
            sprint (w.name,0)
            name=w.name.split(".")
            #pid = int(name[1])     #Fixup
            #os.kill(pid, signal.SIGINT)

        workers = Worker.all(connection=redis_conn)
        for w in workers:
                sprint ("worket state ",w.get_state())
                sprint ("worker  name ",w.name)
                sprint ("worket death ",w.register_death())

        recheck = "false"
        if recheck=="true":
            sprint ("Rechecking workers",0)
            workers = Worker.all(connection=redis_conn)
            sprint ("workers=",workers)
            for w in workers:
                    sprint ("worket state ",w.get_state())
                    sprint ("worker  name ",w.name)
                    sprint ("worket death ",w.register_death())

        q1=Queue('q_logs',connection=redis_conn)
        q2=Queue('q_vm',connection=redis_conn)
        q3=Queue('q_system',connection=redis_conn)
        q4=Queue('q_vol',connection=redis_conn)
        q5=Queue('q_disk',connection=redis_conn)    
        q6=Queue('q_backup',connection=redis_conn)    
        failed = Queue('failed',connection=redis_conn)
        failed.empty()
        q1.empty()
        q2.empty()
        q3.empty()
        q4.empty()
        q5.empty()
        q6.empty()
        init_job_queue(q1,q2,q3,q4,q5,q6)

        process1 = subprocess.Popen(['rq','worker','q_logs'])
        process1 = subprocess.Popen(['rq','worker','q_vm'])
        process1 = subprocess.Popen(['rq','worker','q_system'])
        process1 = subprocess.Popen(['rq','worker','q_vol'])
        process1 = subprocess.Popen(['rq','worker','q_disk'])
        process1 = subprocess.Popen(['rq','worker','q_backup'])
        
        # Need to restart SAMBA if Not Running
        # Need to restart CollectD if Not Running
        #sudo service collectd stop
        #sudo service collectd start
        # Need to restart xxxxxxxxxxxxd if Not Running
        #sudo service smbd start
        time.sleep(3)
        
    sprint ("Server Step ",2)
    sock.listen(1)
    sprint ("Server Step ",3)
    
    while True:
        #if checkT()!=TRUE:
        if LicenceState==0:
            sprint ("LicenceState is OK",0)
        else:
            sprint ("LicenceState is NOT OK",0)
        log_elt="SERVER Manager"
        log_eltName=" "
        connection,client_address=sock.accept()
        try:
            data_header=connection.recv(0x0a)
            body_length = data_header[6:]
            data_body=ccm_recv_msg(body_length,connection)

            #server_args=loggerArgs(log_elt,data_body,70,"received")
            #ccmLogger(4,"Received Message body Request from Client",server_args)

            if data_body.startswith('get'):
                message = data_body[:-6]
                message_list=message.split(',')
                index=0

                for uid in message_list:
                    if uid.startswith("uuid"):
                        uuid_index=message_list.index(uid)
                        del message_list[uuid_index]
                        
                for i in message_list:
                    if 'element=' in i:
                        table=i.split('=')[1]
                    if 'element_name=' in i:
                        element_name=i.split('=')[1]
                    if 'args' in i:
                        break
                    else:
                        index=index+1
                attributes=message_list[index+1:]
                attributes=",".join(attributes)
                Db=""
                DB_Connect=select(table,attributes,element_name)
                if DB_Connect:
                    Db=Db+",".join(map(str,DB_Connect[0]))+','
                Db=Db[:-1]
                body_res123=""
                for j in zip(attributes.split(','),Db.split(',')):
                    body_res123=body_res123+", "+"=".join(j)
                #ccm_logging(log_elt,10,"Sending Response to the Client")
#                time.sleep(2)
#                response=response+"get,"+table+","+element_name+body_res123+"</rsp>"
                response="get,"+table+","+element_name+body_res123+"</rsp>"
                connection.send(response)

            elif data_body.startswith('set'):

                message_list=data_body[:-6].split(',')[1:]
                attribute_names=[]
                attribute_values=[]
                element=message_list[0].split('=')[1]
                server_args=loggerArgs(log_elt,str(element),70,"received")
                #ccmLogger(4,"parsing element",server_args)
                sprint ("element=",element)
                if element == "fan":
                    for i in message_list[1:]:
                        cell_vals=i.split('=')
                        names=cell_vals[0]

                        if names=='element_name':
                            names="sysName"
                        else:
                            pass
                        values=str(cell_vals[1])
                        attribute_names.append(names)
                        attribute_values.append(values)
                        if names=="sysName":
                            fanSystem_name=str(values)
                        elif names=="action":
                            fanAction=str(values)
                        elif names=="State":
                            fanState=str(values)
                        elif names=="Speed":
                            fanSpeed=str(values)
                        elif names == "name":
                            fanName = str(values)
                        elif names == "location":
                            fanLocation = str(values)
                    sprint("Fan GUI Name: Fan SysName ",fanName+" : "+fanSystem_name)
                    DB_UpdateFan(fanSystem_name,fanSpeed,fanState,fanAction,fanName,fanLocation)


                elif element=="psu":
                    for i in message_list[1:]:
                        cell_vals=i.split('=')
                        names=cell_vals[0]
                        if names=="element_name":
                            names="name"
                        else:
                            pass
                        values=str(cell_vals[1])
                        attribute_names.append(names)
                        attribute_values.append(values)
                        if names=="name":
                            psuSystem_name=str(values)
                        elif names=="action":
                            psuAction=str(values)
                        elif names=="State":
                            psuState=str(values)
                        elif names=="dc_status":
                            dc_status = str(values)

                    attribute_names.pop(1)
                    attribute_values.pop(1)
                    attribute_names=','.join(attribute_names)
                    attribute_values=','.join(attribute_values)
                    DB_UpdatePSU(psuSystem_name,psuState,psuAction,dc_status)

                elif element=="cpu":
                    for i in message_list[1:]:
                        cell_vals=i.split('=')
                        names=cell_vals[0]
                        if names=="element_name":
                            names="sysName"
                        else:
                            pass
                        values=str(cell_vals[1])
                        attribute_names.append(names)
                        attribute_values.append(values)
                        if names=="sysName":
                            cpuSys_name=str(values)
                        elif names == "name":
                            cpuName = str(values)
                        elif names=="action":
                            cpuAction=str(values)
                        elif names=="State":
                            cpuState=str(values)
                        elif names=="Temp":
                            cpuTemp=str(values)

                    attribute_names.pop(1)
                    attribute_values.pop(1)
                    attribute_names=','.join(attribute_names)
                    attribute_values=','.join(attribute_values)
                    DB_UpdateCPU(cpuName,cpuSys_name,cpuState,cpuAction,cpuTemp)


                elif element=="temp_probes":
                    for i in message_list[1:]:
                        cell_vals=i.split('=')
                        names=cell_vals[0]
                        if names=="element_name":
                            names="sysName"
                        else:
                            pass
                        values=str(cell_vals[1])
                        attribute_names.append(names)
                        attribute_values.append(values)
                        if names=="sysName":
                            probeSystem_name=str(values)
                        elif names == "name":
                            probeName = str(values)
                        elif names=="action":
                            probeAction=str(values)
                        elif names=="State":
                            probeState=str(values)
                        elif names=="Temp":
                            probeTemp=str(values)

                    attribute_names.pop(1)
                    attribute_values.pop(1)
                    attribute_names=','.join(attribute_names)
                    attribute_values=','.join(attribute_values)
                    DB_UpdateTempProbes(probeName,probeSystem_name,probeState,probeAction,probeTemp)

                elif element=="controller":
                    sprint ("Controller",0)
                    for i in message_list[1:]:
                        cell_vals = i.split('=')
                        names = cell_vals[0]
                        values=str(cell_vals[1])
                        if names == "element_name":
                            names = "name"
                        else:
                            pass
                        if names == "V_3.3V":
                            V_3V = str(values)
                        elif names == "V_3.3V-SB":
                            V_3VSB = str(values)
                        elif names == "V_5V":
                            V_5V = str(values)
                        elif names == "V_5V_SB":
                            V_5VSB = str(values)
                        elif names == "V_12V":
                            V_12V = str(values)
                        elif names == "V_VCCP":
                            V_VCCP = str(values)
                        elif names == "action":
                            cont_Action = str(values)
                        elif names == "name":
                            cont_Name = str(values)
                    if cont_Action == "update_Controller":
                        updateController(V_3V,V_3VSB,V_5V,V_5VSB,V_12V,V_VCCP,cont_Name)
                        
                    elif cont_Action == "reset_controller":
                        logMsg = "Restarting Controller"
                        sprint (logMsg,0)
                        cmd='shutdown'
                        json_res = json.JSONEncoder().encode({"status": "success", "description": "Command scheduled: {}".format(cmd)})
                        connection.sendall(json_res.encode())
                        LogLevel=20
                        CCM_Alert(ccmCRITICAL,LogLevel,logMsg)
                        BackUpDB2SystemVolume()
                        SetVolumesOnOff('off','cx')
                        shutdown()
                        res=PoolStop('MegaRAID',all,'none')
                        time.sleep(3)
                        #sudo shutdown -r
                        arg1="-h"
                        arg1="-r"
                        arg2="now"
                        process1 = subprocess.check_output([cmd, arg1,arg2])
                        sprint ("command completed=",cmd)
                        
                    elif cont_Action == "poff_controller":
                        logMsg = "Powering Off Controller"
                        sprint (logMsg,0)
                        arg1="poweroff"
                        json_res = json.JSONEncoder().encode({"status": "success", "description": "Command scheduled: {}".format(arg1)})
                        connection.sendall(json_res.encode())
                        LogLevel=20
                        CCM_Alert(ccmCRITICAL,LogLevel,logMsg)
                        BackUpDB2SystemVolume()
                        SetVolumesOnOff('off','cx')
                        res=PoolStop('MegaRAID',all,'none')
                        shutdown()
                        time.sleep(3)
                        PowerOff=True
                        SIGTERM_iterrupt(0, 0)
                        process1 = subprocess.check_output(['systemctl', arg1])
                        sprint ("command completed=",arg1)


                elif element=="disks":
                    #ccm_logging(log_elt,20,"disks")
                    sprint ("Element is disks !!!!",0)
                    for i in message_list[1:]:
                        cell_vals=i.split('=')
                        names=cell_vals[0]
                        if names=="element_name":
                            names="name"
                        else:
                            pass
                        values=str(cell_vals[1])
                        #message="set,element={0},element_name='{1}',args=6,vid='{2}',pid='{3}',prl='{4}',serial='{5}',d_id='{6}',state={7},cr_date='{8}',edit_date='{9}'</msg>"\
                        if names=="pid":
                            pid=str(values)
                        elif names=="vid":
                            vid=str(values)
                        elif names=="prl":
                            prl=str(values)
                        elif names=="serial":
                            serial=str(values)
                        elif names=="d_id":
                            d_id=str(values)
                        elif names=="state":
                            state=(values)
                        elif names=="location":
                            location=str(values)
                        elif names=="sysName":
                            sysName=str(values)
                        elif names=="action":
                            action==str(values)
                        if names=="name":
                            disk=str(values)

                    if action=="smartData":
                        json_res=GetSmartData(disk)
                        sprint ("command completed",action)
                        connection.sendall(json_res.encode())
                    else:
                        sprint ("insert into DB=",sysName)
                        DB_updateDisk(sysName,location,pid,vid,prl,serial,d_id,state)
                        json_res = json.JSONEncoder().encode({"status": "success", "description": "Disk Updated: {}".format(sysName)})
                        connection.sendall(json_res.encode())
                        
                elif element=='eth_ports':
                    #print "ELEMENT Starts with ETH_PORTS"
                    sprint ("Client message received",0)
                    # print "data Body",data_body
                    data_list = data_body[4:-6].split(',')[1:]
                    sprint ("data_list",data_list)
                    conn = db_connect()
                    conn.text_factory = str
                    c = conn.cursor()
                    date = datetime.date.today().strftime("%Y-%m-%d")
                    attribute_names = []
                    attribute_values = []
                    for i in data_list:  # str(message_list_ntw)[1:-1].split(","):
                        # print i
                        cell_vals = i.split('=')
                        # print cell_vals
                        names = str(cell_vals[0])
                        values = str(cell_vals[1])
                        attribute_names.append(names)
                        attribute_values.append(values)

                    action = attribute_values[2]
                    if action in ['update_WAN','update_LAN', 'update_ADM','update_M12']:
                        name = attribute_values[0]
                        netmask = attribute_values[3]
                        ip_address = attribute_values[4]
                        dhcp = attribute_values[6]
                        port = attribute_values[5]
                        # print "ntw_id,name,cidr,dhcp",ntw_id,ntw_name,cidr_addr,dhcp
                        result_addNtw = []
                        try:
                            # print "Sending query"
                            query_lan = c.execute(
                                "update eth_ports set ip = ?,netmask=?,dhcp_enabled=?,enable_port=? where name=?",
                                (ip_address, netmask, dhcp, port, name))
                            conn.commit()
                            json_res = json.JSONEncoder().encode(
                                {"status": "success", "description": "Successfully Updated "+str(action[-3:])})
                        except Exception as e:
                            json_res = json.JSONEncoder().encode(
                                {"status": "fail", "description": "DB update failed in server: {}".format(e)})
                        finally:
                            c.close()
                            conn.close()
                            # result_addNtw.append(json_res)
                            sprint ("Response to client", json_res)
                            #ccm_logging(log_elt, 10, "Sending Response to the Client")
                            connection.sendall(json_res.encode())
                    elif action == 'update_MGT':
                        name = attribute_values[0]
                        netmask = attribute_values[3]
                        ip_address = attribute_values[4]
                        gateway = attribute_values[5]
                        dhcp = attribute_values[6]
                        dns = attribute_values[7]
                        # print "ntw_id,name,cidr,dhcp",ntw_id,ntw_name,cidr_addr,dhcp
                        result_addNtw = []
                        try:
                            # print "Sending query"
                            query_net_dhcp=c.execute("update eth_ports set ip = ?,netmask=?,dhcp_enabled=? where name=?",(ip_address,netmask,dhcp,name))
                            conn.commit()
                            query_gw_dns=c.execute("update gateway set default_gateway_ip = ?,dns_server=? where name=?",(gateway,dns,name))
                            conn.commit()
                            json_res = json.JSONEncoder().encode(
                                #{"status": "success", "description": "Successfully Updated MGT port"})
                                {'status':'success','description':'Saved successfully'})
                        except Exception as e:
                            json_res = json.JSONEncoder().encode(
                                {"status": "fail", "description": "DB update failed in server: {}".format(e)})
                        finally:
                            c.close()
                            conn.close()
                            # result_addNtw.append(json_res)
                            sprint ("Response to client", json_res)
                            #ccm_logging(log_elt, 10, "Sending Response to the Client")
                            connection.sendall(json_res.encode())
                    elif action == "update_portStatus":
                        port_enable="Yes"
                        for i in message_list[1:]:
                            cell_vals = i.split("=")
                            names= cell_vals[0]
                            if names == "element_name":
                                names = "name"
                            else:
                                pass
                            values = cell_vals[1]
                            if names == "name":
                                portName = str(values)                            
                            if names == "system_name":
                                portSysName = str(values)
                            elif names == "action":
                                portAction = str(values)
                            elif names == "monitor_port":
                                MonitorPort = str(values)
                            elif names == "state":
                                portState = str(values)
                            elif names == "current_state":
                                CurrentState = str(values)
                            elif names == "port_enable":
                                port_enable=str(values)
                        sprint ("update_portStatus",portSysName+portAction+CurrentState+portState)
                        if CurrentState != portState:
                            if CurrentState=='1':
                                if MonitorPort=="1":
                                    msg =("Port has gone online,Port=")+portName + ",system name="+portSysName
                                    sprint (msg,0)
                                    LogType=ccmINFO
                                    LogLevel=20
                                    CCM_Alert(LogType,LogLevel,msg)
                                sprint ("Call Netplan Apply",0)
                                process = subprocess.check_output(["netplan","apply"])
                                sprint (process,0)
                            else:
                                if port_enable=="Yes" and MonitorPort=="1":
                                    msg =("Enabled Port has gone offline,Port=")+portSysName
                                    LogType=ccmCRITICAL
                                    LogLevel=20
                                    CCM_Alert(LogType,LogLevel,msg)
                                elif port_enable=="No" and MonitorPort=="1":
                                    msg = ("Port Disabled ,Port=")+portSysName
                                    LogType=ccmCRITICAL
                                    LogLevel=20
                                    CCM_Alert(LogType,LogLevel,msg)
                                else:
                                    pass
                        else:
                            pass

                        try:
                            if port_enable=="No":
                                portState="0"
                            msg= "setting state of Port="+portSysName+"="+portState
                            sprint (msg,0)
                            query = c.execute("update eth_ports set state=? where system_name=?",[portState,portSysName])
                            conn.commit()
                            query = c.execute("update gateway set state=? where system_name=?",[portState,portSysName])
                            conn.commit()
                        except Exception as e:
                            sprint("Port update exception",e)
                        finally:
                            c.close()
                            conn.close()

                    else:
                        json_res = json.JSONEncoder().encode(
                            {"status": "fail", "description": "Invalid action sent by client: {}".format(action)})
                        c.close()
                        conn.close()
                        # result_addNtw.append(json_res)
                        sprint ("Response to client", json_res)
                        #ccm_logging(log_elt, 10, "Sending Response to the Client")
                        connection.sendall(json_res.encode())


################################ Host ########################################
                elif element=='host':
                    sprint ("Client message received",0)
                    # print "data Body",data_body
                    data_list = data_body[4:-6].split(',')[1:]
                    # print "data_list",data_list
                    conn = db_connect()
                    conn.text_factory = str
                    c = conn.cursor()
                    date = datetime.date.today().strftime("%Y-%m-%d")
                    attribute_names = []
                    attribute_values = []
                    for i in data_list:  # str(message_list_ntw)[1:-1].split(","):
                        # print i
                        cell_vals = i.split('=')
                        # print cell_vals
                        names = str(cell_vals[0])
                        values = str(cell_vals[1])
                        attribute_names.append(names)
                        attribute_values.append(values)

                    action = attribute_values[2]
                    if action == 'create_Host':
                        hostName = attribute_values[0]
                        protocol = attribute_values[3]
                        user = attribute_values[4]
                        iqn = attribute_values[5]
                        password = attribute_values[6]
                        wwn = attribute_values[7]
                        # print "ntw_id,name,cidr,dhcp",ntw_id,ntw_name,cidr_addr,dhcp
                        result_addNtw = []
                        try:
                            query_SP = c.execute(
                                "insert into  host(name,protocol,user_name,iqn,pw,wwn,cr_date) values(?,?,?,?,?,?,datetime())",
                                [hostName, protocol, user, iqn, password, wwn])
                            conn.commit()
                            json_res = json.JSONEncoder().encode(
                                {"status": "success", "description": "Successfully Created Host"})
                        except Exception as e:
                            json_res = json.JSONEncoder().encode(
                                {"status": "fail", "description": "DB update failed in server: {}".format(e)})
                        finally:
                            c.close()
                            conn.close()
                            # result_addNtw.append(json_res)
                            sprint ("Response to client", json_res)
                            #ccm_logging(log_elt, 10, "Sending Response to the Client")
                            connection.sendall(json_res.encode())
                    elif action == 'update_Host':
                        hostName = attribute_values[0]
                        protocol = attribute_values[3]
                        user = attribute_values[4]
                        iqn = attribute_values[5]
                        password = attribute_values[6]
                        wwn = attribute_values[7]
                        hostId = attribute_values[8]

                        # print "ntw_id,name,cidr,dhcp",ntw_id,ntw_name,cidr_addr,dhcp
                        result_addNtw = []
                        try:
                            query_SP = c.execute(
                                "update host set name=?,protocol=?,user_name=?,iqn=?,pw=?,wwn=?,cr_date=datetime() where id=?",
                                [hostName, protocol, user, iqn, password, wwn, hostId])
                            conn.commit()
                            json_res = json.JSONEncoder().encode(
                                {"status": "success", "description": "Successfully Updated Host"})
                        except Exception as e:
                            json_res = json.JSONEncoder().encode(
                                {"status": "fail", "description": "DB update failed in server: {}".format(e)})
                        finally:
                            c.close()
                            conn.close()
                            # result_addNtw.append(json_res)
                            sprint ("Response to client", json_res)
                            #ccm_logging(log_elt, 10, "Sending Response to the Client")
                            connection.sendall(json_res.encode())
                    elif action == 'delete_Host':
                        hostId = attribute_values[0]
                        # print "ntw_id,name,cidr,dhcp",ntw_id,ntw_name,cidr_addr,dhcp
                        result_addNtw = []
                        try:
                            query = "Delete from Host where id in (" + str(hostId) + ")"
                            query_FT = c.execute(query)
                            conn.commit()
                            json_res = json.JSONEncoder().encode(
                                {"status": "success", "description": "Successfully Deleted Host"})
                        except Exception as e:
                            json_res = json.JSONEncoder().encode(
                                {"status": "fail", "description": "DB update failed in server: {}".format(e)})
                        finally:
                            c.close()
                            conn.close()
                            # result_addNtw.append(json_res)
                            sprint ("Response to client", json_res)
                            #ccm_logging(log_elt, 10, "Sending Response to the Client")
                            connection.sendall(json_res.encode())
                    else:
                        json_res = json.JSONEncoder().encode(
                            {"status": "fail", "description": "Invalid action sent by client: {}".format(action)})
                        c.close()
                        conn.close()
                        # result_addNtw.append(json_res)
                        sprint ("Response to client", json_res)
                        #ccm_logging(log_elt, 10, "Sending Response to the Client")
                        connection.sendall(json_res.encode())
############### NETWORKS ###########################
                elif element=="network":
                    #print("network msg",message_list)
                    for i in message_list[1:]:
                        cell_vals=i.split('=')
                        names=cell_vals[0]
                        if names=="element_name":
                            names="name"
                        values=str(cell_vals[1])
                        if names=="action":
                            NtwCmd=str(values)
                        elif names=="cidr":
                            NtwCIDR=str(values)
                        elif names=="enable_dhcp":
                            enableDHCP=str(values)
                        elif names=="network_id":
                            NtwID=str(values)
                        elif names=="name":
                            NtwName=str(values)
                    msg_code = ""
                    if NtwCmd == 'create_Network':
                        res = createNetwork(NtwName,NtwCIDR,enableDHCP)
                        msg_code = "added"
                    elif NtwCmd == 'delete_Network':
                        res = deleteNetwork(NtwID)
                        msg_code = "deleted"
                    elif NtwCmd == 'edit_Network':
                        res = editNetwork(NtwID,NtwName,NtwCIDR,enableDHCP)
                        msg_code = "edited"
                    if res == 0:
                        json_res = json.JSONEncoder().encode(
                                {"status": "success", "description": "Successfully {} Network".format(msg_code)})
                    else:
                        json_res = json.JSONEncoder().encode(
                            {"status": "fail", "description": "DB update failed in server: {}".format(res)})
                    connection.sendall(json_res.encode())
                
                elif element=="schedule_restore":
                    sprint ("schedule_restore msg",message_list)
                    for i in message_list[1:]:
                        if "=" not in i:  # skip empty/invalid entries
                            continue
                        cell_vals=i.split('=')
                        names=cell_vals[0]
                        values=str(cell_vals[1])
                        if names=="scheduleId":
                            scheduleId=int(values)
                        elif names=="schHistoryId":
                            schHistoryId=int(values)
                        elif names=="schRestorPoint":
                            RestorPoint=str(values)
                        elif names=="schSourceVol":
                            SourceVol=str(values)
                        elif names=="schDestinationVol":
                            DestinationVol=str(values)
                        elif names=="schDestVolName":
                            DestVolName=str(values)
                        elif names=="schDestVolId":
                            DestVolId=int(values)
                        elif names=="sourceDirectories":
                            sourceDirectories=str(values.replace(";", ","))
                        elif names=="action":
                            sds_cmd=str(values)
                        elif names=="uuid":
                            cmd_Id=str(values)
                    params = (scheduleId, schHistoryId, RestorPoint, SourceVol, DestinationVol, DestVolName, DestVolId, sourceDirectories)
                    print(params)
                    
                    if sds_cmd=="restore_volume":
                        params = (scheduleId, schHistoryId, RestorPoint, SourceVol, DestinationVol, DestVolName, DestVolId, sourceDirectories)
                        threading.Thread(
                            target=run_restore_in_background,
                            args=(scheduleId, schHistoryId, RestorPoint, SourceVol, DestinationVol, DestVolName, DestVolId, sourceDirectories),
                            daemon=True
                        ).start()
                        json_res = json.JSONEncoder().encode({"status": "success", "description": "Restore started in background"})
############## SETUP- USER#############
                elif element=="user":
                    sprint ("user message received",0)
                    #print "data Body",data_body
                    data_list = data_body[4:-6].split(',')[1:]
                    # print "data_list",data_list
                    conn = db_connect()
                    conn.text_factory = str
                    c = conn.cursor()
                    date = datetime.date.today().strftime("%Y-%m-%d")
                    attribute_names = []
                    attribute_values = []
                    for i in data_list:  # str(message_list_ntw)[1:-1].split(","):
                        # print i
                        cell_vals = i.split('=')
                        # print cell_vals
                        names = str(cell_vals[0])
                        values = str(cell_vals[1])
                        attribute_names.append(names)
                        attribute_values.append(values)
                    action = attribute_values[2]
                # Create_USEr
                    if action == 'CreateUser':
                        userName = attribute_values[0]
                        FirstName = attribute_values[3]
                        LastName = attribute_values[4]
                        userEmail = attribute_values[5]
                        password = attribute_values[6]
                        Department = attribute_values[7]
                        Phone = attribute_values[8]
                        GroupId = attribute_values[9]
                        result_addNtw = []
                        try:
                            query_SP = c.execute( "insert into user(userName,FirstName,LastName,userEmail,password,"
                                                  "Department,Phone,GroupId,cr_date,edit_date) "
                                                  "values(?,?,?,?,?,?,?,?,?,?)",
                                    [userName, FirstName, LastName, userEmail, password, Department, Phone,
                                     GroupId, date,date])
                            conn.commit()
                            json_res = json.JSONEncoder().encode(
                                {"status": "success", "description": "Successfully added User"})
                        except Exception as e:
                            json_res = json.JSONEncoder().encode(
                                {"status": "fail", "description": "DB update failed in server: {}".format(e)})
                        finally:
                            c.close()
                            conn.close()
                            sprint ("Response to client", json_res)
                            #ccm_logging(log_elt, 10, "Sending Response to the Client")
                            connection.sendall(json_res.encode())
                #UpdateUSer( it should be edit_User)
                    if action == 'UpdateUser':
                        userName = attribute_values[0]
                        FirstName = attribute_values[3]
                        LastName = attribute_values[4]
                        userEmail = attribute_values[5]
                        password = attribute_values[6]
                        Department = attribute_values[7]
                        Phone = attribute_values[8]
                        GroupId = attribute_values[9]
                        UserId = attribute_values[10]
                        result_addNtw = []
                        try:
                            query_SP = c.execute("update user set userName=?,FirstName=?,LastName=?,userEmail=?,"
                                                 "password=?,Department=?,Phone=?,GroupId=?,edit_date=?"
                                                 "where id=?",
                                [userName, FirstName, LastName, userEmail, password, Department, Phone, GroupId, date,
                                 str(UserId)])

                            conn.commit()
                            json_res = json.JSONEncoder().encode(
                                {"status": "success", "description": "Successfully updated User"})
                        except Exception as e:
                            json_res = json.JSONEncoder().encode(
                                {"status": "fail", "description": "DB update failed in server: {}".format(e)})
                        finally:
                            c.close()
                            conn.close()
                            sprint ("Response to client", json_res)
                            #ccm_logging(log_elt, 10, "Sending Response to the Client")
                            connection.sendall(json_res.encode())
                #DELETEUser
                    if action == 'DeleteUser':
                        userName = attribute_values[0]
                        try:
                            query_FT = c.execute("delete from  user where id=?", [str(userName)])
                            conn.commit()
                            json_res = json.JSONEncoder().encode(
                                {"status": "success", "description": "Successfully deleted User"})
                        except Exception as e:
                            json_res = json.JSONEncoder().encode(
                                {"status": "fail", "description": "DB update failed in server: {}".format(e)})
                        finally:
                            c.close()
                            conn.close()
                            sprint ("Response to client", json_res)
                            #ccm_logging(log_elt, 10, "Sending Response to the Client")
                            connection.sendall(json_res.encode())
######################SETUP-ORG GROUP #####################

                elif element=="OrgGroup":
                    sprint ("OrgGroup message received",0)
                    # print "data Body",data_body
                    data_list = data_body[4:-6].split(',')[1:]
                    # print "data_list",data_list
                    conn = db_connect()
                    conn.text_factory = str
                    c = conn.cursor()
                    date = datetime.date.today().strftime("%Y-%m-%d")
                    attribute_names = []
                    attribute_values = []
                    for i in data_list:  # str(message_list_ntw)[1:-1].split(","):
                        # print i
                        cell_vals = i.split('=')
                        # print cell_vals
                        names = str(cell_vals[0])
                        values = str(cell_vals[1])
                        attribute_names.append(names)
                        attribute_values.append(values)
                    action = attribute_values[2]
                    # print "action",action
                    if action == 'CreateGroup':
                        GroupName = attribute_values[0]
                        GroupDescription = attribute_values[3]
                        try:
                            query_SP = c.execute(
                                    "insert into OrgGroup(Name,Description,cr_date,edit_date) values(?,?,?,?)",
                                    [GroupName, GroupDescription,date,date])
                            conn.commit()
                            json_res = json.JSONEncoder().encode(
                                {"status": "success", "description": "Successfully added Group"})
                        except Exception as e:
                            json_res = json.JSONEncoder().encode(
                                {"status": "fail", "description": "DB update failed in server: {}".format(e)})
                        finally:
                            c.close()
                            conn.close()
                            sprint ("Response to client", json_res)
                            #ccm_logging(log_elt, 10, "Sending Response to the Client")
                            connection.sendall(json_res.encode())
                    if action == 'UpdateGroup':
                        GroupId =  attribute_values[0]
                        GroupName = attribute_values[3]
                        GroupDescription = attribute_values[4]
                        try:
                            query_SP = c.execute("update OrgGroup set Name=?,Description=?,edit_date=? where id=?",
                                                 [GroupName, GroupDescription, date, GroupId])
                            conn.commit()
                            json_res = json.JSONEncoder().encode(
                                {"status": "success", "description": "Successfully updated Group"})
                        except Exception as e:
                            json_res = json.JSONEncoder().encode(
                                {"status": "fail", "description": "DB update failed in server: {}".format(e)})
                        finally:
                            c.close()
                            conn.close()
                            sprint ("Response to client", json_res)
                            #ccm_logging(log_elt, 10, "Sending Response to the Client")
                            connection.sendall(json_res.encode())
                    if action == 'DeleteGroup':
                        GroupId = attribute_values[0]
                        try:
                            query_FT = c.execute("delete from  OrgGroup where id=?", [GroupId])
                            conn.commit()
                            json_res = json.JSONEncoder().encode(
                                {"status": "success", "description": "Successfully deleted Group"})
                        except Exception as e:
                            json_res = json.JSONEncoder().encode(
                                {"status": "fail", "description": "DB update failed in server: {}".format(e)})
                        finally:
                            c.close()
                            conn.close()
                            sprint ("Response to client", json_res)
                            #ccm_logging(log_elt, 10, "Sending Response to the Client")
                            connection.sendall(json_res.encode())

#################### SETUP-SERVICES#################
                elif element=="services":
                    sprint ("services message received",0)
                    #print "data Body",data_body
                    data_list = data_body[4:-6].split(',')[1:]
                    #print "data_list",data_list
                    conn = db_connect()
                    conn.text_factory = str
                    c = conn.cursor()
                    date = datetime.date.today().strftime("%Y-%m-%d")
                    attribute_names = []
                    attribute_values = []
                    for i in data_list:  # str(message_list_ntw)[1:-1].split(","):
                        #print i
                        cell_vals = i.split('=')
                        #print cell_vals
                        names = str(cell_vals[0])
                        values = str(cell_vals[1])
                        attribute_names.append(names)
                        attribute_values.append(values)
                    #print  "attribute values",attribute_values
                    action = attribute_values[2]
                    #print "action",action
                    if action == 'SaveEmail':
                        #print "attribute_values",attribute_values
                        sender = attribute_values[0]
                        emailRecipient = attribute_values[3]
                        password = attribute_values[4]
                        smtpServer = attribute_values[5]
                        portNumber = attribute_values[6]
                        alertType = attribute_values[7]
                        #print "Saving email"
                        try:
                            query_lan = c.execute("delete from email_logs")
                            conn.commit()
                            query_lan = c.execute(
                                "insert into email_logs (sender_email,recipient_email,password,smtp_server,port,alert_type) values(?,?,?,?,?,?)",
                                [sender, emailRecipient, password, smtpServer, portNumber, alertType])
                            conn.commit()
                            json_res = json.JSONEncoder().encode(
                                {"status": "success", "description": "Updated Successfully"})
                        except Exception as e:
                            json_res = json.JSONEncoder().encode(
                                {"status": "fail", "description": "DB update failed in server: {}".format(e)})
                        finally:
                            c.close()
                            conn.close()
                            sprint ("Response to client", json_res)
                            #ccm_logging(log_elt, 10, "Sending Response to the Client")
                            connection.sendall(json_res.encode())
                    if action == 'SaveService':
                        BackupDest = attribute_values[0]
                        IPAddress = attribute_values[3]
                        AccountName = attribute_values[4]
                        bckPassword = attribute_values[5]
                        Certificate = attribute_values[6]
                        try:
                            query_lan = c.execute("delete from backup where destination_name='" + str(BackupDest) + "'")
                            conn.commit()
                            query_lan = c.execute(
                                "insert into backup (ip_address,account_name,password,certificate_path,destination_name) values(?,?,?,?,?)",
                                [IPAddress, AccountName, bckPassword, Certificate, BackupDest])
                            conn.commit()
                            json_res = json.JSONEncoder().encode(
                                {"status": "success", "description": "Successfully saved Service"})
                        except Exception as e:
                            json_res = json.JSONEncoder().encode(
                                {"status": "fail", "description": "DB update failed in server: {}".format(e)})
                        finally:
                            c.close()
                            conn.close()
                            sprint ("Response to client", json_res)
                            #ccm_logging(log_elt, 10, "Sending Response to the Client")
                            connection.sendall(json_res.encode())

#############TIMER #############
                elif element=="timer":
                    values="null"
                    for i in message_list[1:]:
                        cell_vals=i.split('=')
                        names=cell_vals[0]
                        if names=="element_name":
                            names="name"
                        else:
                            pass
                        values=str(cell_vals[1])
                        sprint (values,0)

                    msg="Timer event="  + str(values)
                    sprint (msg,0)
                    print ("Timer Msg",msg)
                    if LicenceState!=0:
                        CheckLicence()
                    Rsyslog=False
                    if Rsyslog==True:
                        msg="ST: Timer message received loop="+str(TimerLoop)
                        process1 = subprocess.check_output(['logger', msg])
                    if TimerLoop < 1:
                        LogLevel=20
                        CCM_Alert(ccmINFO,LogLevel,msg)
                        if LicenceState!=0:
                            err="No Licence was found"
                            CCM_Alert(ccmCRITICAL,LogLevel,err)
                    TimerLoop=TimerLoop+1
                    #check megaRaid
                    NbDisks=0
                    cx=MyCanister
                    k=0
                    if cx=='/c0':
                        location='c0'
                        MyCanister='/c1'
                        k=0
                    elif cx=='/c1':
                        location='c1'
                        MyCanister='/c2'
                        k=1
                    elif cx=='/c2':
                        MyCanister='/c0'
                        location='c2'
                        k=2
                    msg="step1:Checking Canister, k="+str(k)+' '
                    sprint (msg,cx)
                    q=False
                    if CheckCanister[k]==True:
                        list=CheckMegaRAIDDrives(cx)
                        if list[0]==0:
                            NbDisks=len(list[1])
                            sprint ("NbDisks", NbDisks)
                            if NbDisks==0:
                                CanisterPresent[k]=False
                                LogLevel=20
                                err = "TimerCheck Canister has no disks=" + cx
                                CCM_Alert(ccmCRITICAL,LogLevel,err)                            
                                sprint (err,MyCanister)
                                FakePoolUpdate("critical",location)
                                SetVolumesOnOff('off',location)
                                SetDevicesOnOff('off')
                                sprint (err,0)
                                DeleteDisk('mrx',cx)
                                DelOnExtraction=True            #BUG 
                                if DelOnExtraction==True:
                                    DeleteOnExtraction(cx)

                        else: #No Canister
                            err = "TimerCheck Canister Disks removed=" + cx
                            sprint (err,0)
                            if CanisterPresent[k]==True:
                                CanisterPresent[k]=False
                                LogLevel=20
                                CCM_Alert(ccmCRITICAL,LogLevel,err)
                                FakePoolUpdate("critical",location)
                                SetVolumesOnOff('off',location)
                                SetDevicesOnOff('off')
                                sprint (err,0)
                                DeleteDisk('mrx',cx)
                                try:
                                    #sudo umount /mnt/system
                                    arg1="/mnt/system"
                                    sprint ("umount", arg1)
                                    process1 = subprocess.check_output(['umount', arg1])
                                    sprint (process1,0)
                                    sprint ("rm -rf ", arg1)
                                    arg2='-rf'
                                    process1 = subprocess.check_output(['rm',arg2,arg1])
                                    sprint (process1,0)
                                    time.sleep(2)
                                    CheckBackUpOnInsert("extract")
                                    DelOnExtraction=True
                                    if DelOnExtraction==True:
                                        DeleteOnExtraction(cx)
                                except Exception as err:
                                    sprint("umount except ",err)
                                    
                        if (CanisterPresent[k]==False and NbDisks==4):
                            err = "TimerCheck Canister re-inserted="+cx
                            LogLevel=20
                            sprint ("Restart 1",0)
                            res=RestartMegaRAID(cx,"quiet",q)
                            if res==0:
                                old=True
                                msg = "Canister imported correctly 1=" +cx
                                sprint (msg,0)
                                CCM_Alert(ccmCRITICAL,LogLevel,msg)
                                CanisterPresent[k]=True
                                if old==True:
                                    res=QuiescePools(False)
                                    sprint ("res QuiescePools",res)
                                    res=CheckCanisterVolumes(location)
                                    sprint ("res CheckCanisterVolumes",res)
                                    RefreshPools(True)
                                    time.sleep(5)
                                    setAllOnOff('on')
                                DB_UpdateAtInsertSchedule()
                                FakePoolUpdate("OK",location)
                                #CheckBackUpOnInsert("insert")
                            else:
                                err = "TimerCheck Canister failed to import correctly=" +cx
                                sprint (err,0)
                                CCM_Alert(ccmCRITICAL,LogLevel,err)
                                res=QuiescePools(True)
                                CanisterPresent[k]=False
                                
                        else:
                            if CanisterPresent[k]==True:
                                msg = "Canister present , disks="
                            else:
                                msg = "Canister absent, disks="
                            sprint (msg,  NbDisks)
                        
                    runJobs=True
                    if runJobs==True:
                        sprint("run_ftp",0)
                        run_ftp()
                        sprint("get_jobList",0)
                        get_jobList()

                elif element=="timer_job_download":
                    message_list=data_body.split(",")
                    for i in message_list:
                        if "element_id=" in i:
                            element_id=i.split("=")[1]
                    #schedule_thread.dwnld_myApp(element_id)
                    dwnld_myApp(element_id)
                    
                elif element=="PushButton":
                    k=0
                    sprint ("PushButton",message_list)
                    PBTaction="Null"
                    for i in message_list[1:]:
                        cell_vals=i.split('=')
                        names=cell_vals[0]
                        if names=="element_name":
                            names="name"
                        else:
                            pass
                        values=str(cell_vals[1])
                        sprint (values,0)
                        if names=="action":
                            PBTaction=str(values)
                        if names=="canister":
                            canx=str(values)
                            # canister dk_data bp_data
                            #   1       0xb0    0xb8 = /c1
                            #   2       0xb2    0xba = /c2
                            #   3       0xb4    0xbc = /c0
                                
                            if canx=='can0':
                                locx='c0'
                                cxx='/c0'
                                k=0
                            elif canx=='can1':
                                locx='c1'
                                cxx='/c1'
                                k=1
                            elif canx=='can2':
                                locx='c2'
                                cxx='/c2'
                                k=2
                        attribute_names.append(names)
                        attribute_values.append(values)
                    attribute_names.pop(1)
                    attribute_values.pop(1)
                    attribute_names=','.join(attribute_names)
                    attribute_values=','.join(attribute_values)
                    sprint (attribute_names,0)
                    #raptor=True
                    if raptor==True:
                        if k==0:
                            dk_dataAdr='0xB4'
                        elif k==1:
                            dk_dataAdr='0xB0'
                        elif k==2:
                            dk_dataAdr='0xB2'
                    else:   
                        if k==0:
                            dk_dataAdr='0xB0'
                        elif k==1:
                            dk_dataAdr='0xB2'
                        elif k==2:
                            dk_dataAdr='0xB4'
     
                    if PBTaction=="softRTP":
                        CheckCanister[k]=False
                        sprint ("SOFT PBT RTP message received",locx)
                        LogLevel=20
                        err = "SOFT PBT RTP message received"
                        BackUpDB2SystemVolume()
                        CCM_Alert(ccmCRITICAL,LogLevel,err)
                        SetVolumesOnOff('off',locx)
                        SetDevicesOnOff('off')
                        PoolStop('MegaRAID',all,'none',locx)
                     
                        FakePoolUpdate("critical",locx)
                        #PowerOnOff('off')
                        DeleteDisk('mrx',cxx)
                        DelOnExtraction=True
                        if DelOnExtraction==True:
                            DeleteOnExtraction(cxx)

                    elif PBTaction=="RTP":
                        CheckCanister[k]=False
                        sprint ("PBT RTP message received",0)
                        LogLevel=20
                        msg = "PBT RTP message received"+canx
                        sprint ("############################################## CALLING PBT RTP ACK0 #########################",0)
                        BackUpDB2SystemVolume()
                        sprint ("############################################## CALLING PBT RTP ACK1 #########################",0)
                        CCM_Alert(ccmCRITICAL,LogLevel,msg)
                        SetVolumesOnOff('off',locx)
                        sprint ("############################################## CALLING PBT RTP ACK2 #########################",0)
                        SetDevicesOnOff('off')
                        sprint ("############################################## CALLING PBT RTP ACK3 #########################",0)
                        PoolStop('MegaRAID',all,'none')
                        sprint ("############################################## CALLING PBT RTP ACK4 #########################",0)
                        FakePoolUpdate("critical",locx)
                        sprint ("############################################## CALLING PBT RTP ACK5 #########################",0)
                        PowerOnOff('off')
                        sprint ("############################################## CALLING PBT RTP ACK6 #########################",0)
                        DeleteDisk('mrx',cxx)
                        sprint ("############################################## CALLING PBT RTP ACK7 #########################",0)
                        ret=pbtAck(dk_dataAdr)
                        sprint ("############################################## CALLING PBT RTP ACK8 #########################",ret)
                        DelOnExtraction=True
                        if DelOnExtraction==True:
                            DeleteOnExtraction(cxx) 
                    elif PBTaction=="pulled":
                        sprint ("PBT pulled message received",0)
                        LogLevel=20
                        err = "Canister unexpectedly removed"
                        CCM_Alert(ccmCRITICAL,LogLevel,err)
                        SetVolumesOnOff('off',locx)
                        SetDevicesOnOff('off')
                        PoolStop('MegaRAID',all,'none',locx)
                        FakePoolUpdate("critical",locx)
                        PowerOnOff('off')
                        DeleteDisk('mrx',cxx)
                        DelOnExtraction=True
                        if DelOnExtraction==True:
                            DeleteOnExtraction(cxx)

                        
                    elif PBTaction=="insert":
                        sprint ("PBT insert message received",cxx)
                        try:
                            LogLevel=20
                            sprint ("Restart 2",0)
                            res=RestartMegaRAID(cxx,"quiet",q)
                            if res==0:
                                old=True
                                msg = "Canister imported correctly 2"
                                sprint (msg,0)
                                CCM_Alert(ccmCRITICAL,LogLevel,msg)
                                CanisterPresent[k]=True
                                if old==True:
                                    err = "Canister imported correctly 3"
                                    sprint (err,0)
                                    CCM_Alert(ccmCRITICAL,LogLevel,err)
                                    CanisterPresent[k]=True
                                    res=QuiescePools(False)
                                    sprint ("res QuiescePools",res)
                                    res=CheckCanisterVolumes(location)
                                    sprint ("res CheckCanisterVolumes",res)
                                    RefreshPools(True)
                                    time.sleep(5)
                                    SetVolumesOnOff('on',locx)
                                    SetDevicesOnOff('on')
                                    FakePoolUpdate("OK",locx)
                                DB_UpdateAtInsertSchedule()
                                CheckCanister[k]=True
                            else:
                                err = "Canister failed to import correctly="+cxx
                                sprint (err,0)
                                CCM_Alert(ccmCRITICAL,LogLevel,err)
                                res=QuiescePools(True)
                                RestartServices()
                        except Exception as err:
                            sprint("PushButton (insert) except ",err)

                    elif PBTaction=="extract":
                        LogLevel=20
                        err = "Canister extracted=" +cxx
                        CCM_Alert(ccmCRITICAL,LogLevel,err)
                        sprint ("PBT extract message received",cxx)
                        
                    elif PBTaction=="extractTO":
                        sprint ("PBT extract TimeOut message received",cxx)
                        try:
                            LogLevel=20
                            sprint ("Restart 3",0)
                            res=RestartMegaRAID(cxx,"quiet",q)
                            if res==0:
                                old=True
                                msg = "Canister imported correctly 4=" +cxx
                                sprint (msg,0)
                                CCM_Alert(ccmCRITICAL,LogLevel,msg)
                                CanisterPresent[k]=True
                                if old==True:
                                    err = "Canister imported correctly 5"
                                    sprint (err,0)
                                    CCM_Alert(ccmCRITICAL,LogLevel,err)
                                    CanisterPresent[k]=True
                                    res=QuiescePools(False)
                                    sprint ("res QuiescePools",res)
                                    res=CheckCanisterVolumes(location)
                                    sprint ("res CheckCanisterVolumes",res)
                                    RefreshPools(True)
                                    SetVolumesOnOff('on',locx)
                                    SetDevicesOnOff('on')
                                    FakePoolUpdate("OK",locx)
                                DB_UpdateAtInsertSchedule()
                                CheckCanister[k]=True
                            else:
                                err = "Canister failed to import correctly="+cxx
                                CCM_Alert(ccmCRITICAL,LogLevel,err)
                                CanisterPresent[k]=False
                                res=QuiescePools(True)
                                SetVolumesOnOff('off',locx)
                                SetDevicesOnOff('off')
                                FakePoolUpdate("critical",locx)
                        except Exception as err:
                            sprint("PushButton (insert) except ",err)
                    else:
                        sprint ("PBT NULL message received",0)


###########SCHEDULE################################################## WO tested

                elif element=="schedule":
                    sprint ("schedule message received","schedule step 1")
                    state = None
                    for i in message_list[1:]:
                        cell_vals = i.split("=")
                        names= cell_vals[0]
                        if names == "element_name":
                            names = "name"
                        else:
                            pass
                        values = cell_vals[1]
                        if names == "name":
                            ScheduleName = str(values)
                        elif names == "Action":
                            ScheduleAction = str(values)
                        elif names == "frequency":
                            ScheduleFreq = str(values)
                        elif names == "startTime":
                            ScheduleTime = str(values)
                        elif names == "startDate":
                            ScheduleStartDate = str(values)
                        elif names == "endDate":
                            ScheduleEndDate = str(values)
                        elif names == "action":
                            ScheduleJobAction = str(values)
                        elif names == "backup":
                            ScheduleBackUp = str(values)
                        elif names == "status":
                            ScheduleStatus = str(values)
                        elif names == "VMIds":
                            ScheduleVM = str(values)
                        elif names == "T_next":
                            ScheduleNext = str(values)
                        elif names == "done_percentage":
                            SchedulePercentage = str(values)
                        elif names == "volId":
                            ScheduleVol = str(values)
                        elif names == "scheduleId":
                            ScheduleId = str(values)
                        elif names == "state":
                            state = str(values)
                    SchNameMsg="Schedule name="+str(ScheduleName)
                    ActionMsg="Action Cmd/Data="+ScheduleAction+"/"+SchedulePercentage
                    scheduleArgs = loggerArgs(element,SchNameMsg,30,ActionMsg)
                    sprint ("scheduleArgs",scheduleArgs)
                    sprint ("ScheduleAction",ScheduleAction)
                    res=-1
                    if ScheduleAction == "check" or ScheduleAction == "check_schedule":
                        sprint ("ScheduleAction == check",ScheduleName+SchedulePercentage+ScheduleStatus)
                        jobDone_percentage(ScheduleName,SchedulePercentage,ScheduleStatus)
                        msg="Task percentage completed="+str(SchedulePercentage)
                        ccmLogger(4,msg,scheduleArgs)
                        if state is not None and str(state) == '1':
                            ccmLogger(3,"Email Logs Schedule. Email has not been validated - failed to send an email",scheduleArgs)
                        elif state is not None and str(state) == '2':
                            ccmLogger(3,"Email Logs Schedule. Email could not be validated - failed to send an email",scheduleArgs)
                        if ScheduleStatus == 'failed':
                            ccmLogger(3,"Email Logs Schedule. Email Configuartion is not set in the DB- failed to send an email",scheduleArgs)

                    elif ScheduleAction == "save" or ScheduleAction == "save_schedule":
                        sprint ("schedule save",0)
                        res=ScheduleCreate(ScheduleName,ScheduleFreq,ScheduleTime,ScheduleStartDate,ScheduleEndDate,ScheduleJobAction,ScheduleBackUp,ScheduleStatus,\
                            ScheduleVM,ScheduleNext,SchedulePercentage,ScheduleVol)

                        if res==0:
                            json_res = json.JSONEncoder().encode({"status": "success", "description": "Schedule Action OK Code: {}".format(res)})
                            sprint ("command Passed OK",0)
                            connection.sendall(json_res.encode())
                            ccmLogger(4,"Schedule OK",scheduleArgs) 
                        else:
                            json_res = json.JSONEncoder().encode({"status": "fail", "description": "Schedule Action Error Code: {}".format(res)})
                            sprint ("command Failed",res)
                            connection.sendall(json_res.encode()) 
                            ccmLogger(3,"Schedule Error",scheduleArgs)

                    elif ScheduleAction == "update"  or ScheduleAction == "update_schedule":
                        sprint ("schedule update",0)                    
                        res=ScheduleUpdate(ScheduleName,ScheduleFreq,ScheduleTime,ScheduleStartDate,ScheduleEndDate,ScheduleJobAction,ScheduleBackUp,\
                            ScheduleVM,ScheduleVol,ScheduleId)
                        if res==0:
                            json_res = json.JSONEncoder().encode({"status": "success", "description": "Schedule Action OK Code: {}".format(res)})
                            sprint ("command Passed",0)
                            connection.sendall(json_res.encode()) 
                            ccmLogger(4,"Schedule  OK",scheduleArgs) 
                        else:
                            json_res = json.JSONEncoder().encode({"status": "fail", "description": "Schedule Action Error Code: {}".format(res)})
                            sprint ("command Failed",0)
                            connection.sendall(json_res.encode()) 
                            ccmLogger(3,"Schedule Error",scheduleArgs)

                    elif ScheduleAction =="delete" or ScheduleAction == "delete_schedule":
                        sprint ("schedule delete",0)
                        scheduleId = ScheduleName
                        res = ScheduleDelete(scheduleId)
                        if res==0:
                            json_res = json.JSONEncoder().encode({"status": "success", "description": "Schedule Action OK Code: {}".format(res)})
                            sprint ("command Passed",ScheduleAction)
                            connection.sendall(json_res.encode()) 
                            ccmLogger(4,"Schedule OK",scheduleArgs) 
                        else:
                            json_res = json.JSONEncoder().encode({"status": "fail", "description": "Schedule Action Error Code: {}".format(res)})
                            sprint ("command Failed",res)
                            connection.sendall(json_res.encode())
                            ccmLogger(3,"Schedule Action Error",scheduleArgs)
                    else:
                        json_res = json.JSONEncoder().encode({"status": "fail", "description": "Schedule Invalid Action Error Code: {}".format(res)})
                        sprint ("Invalid Action",ScheduleAction)
                        connection.sendall(json_res.encode())
                        ccmLogger(3,"Schedule Invalid Action Error Code",scheduleArgs)


############### SCHEDULE HISTORY ##################

                elif element=="schedule_history":
                    sprint ("schedule_history message received",0)
                    #Arg=loggerArgs(element," ",20,"Receive")
                    #ccmLogger(0,"Received scheduler history request",Arg)
                    SchStatus="OK"
                    sysHlthCheck = None
                    sys_hlth_mail = ""
                    state = None
                    for i in message_list[1:]:
                        cell_vals = i.split("=")
                        names = cell_vals[0]
                        values = cell_vals[1]
                        if names == "element_name":
                            names = "name"
                        else:
                            pass
                        if names == "action":
                            SchHistoryAction = str(values)
                        elif names == "name":
                            SchHistoryName = str(values)
                        elif names == "schedule_id":
                            ScheduleId = str(values)
                        elif names == "complete_date":
                            SchCompleteDate = str(values)
                        elif names == "complete_time":
                            SchCompleteTime = str(values)
                        elif names == "status":
                            SchStatus = str(values)
                        elif names == "shc_status":
                            sysHlthCheck = int(values)
                        elif names =="email_sent":
                            sys_hlth_mail = str(values)
                        elif names =="state":
                            state = str(values)
                    schHistoryArgs=loggerArgs(element,SchHistoryName,22,SchHistoryAction+" "+SchStatus)

                    if SchHistoryAction == "create_schHistory":
                        res = ScheduleHistoryCreate(ScheduleId,SchCompleteDate,SchCompleteTime,SchStatus)
                        msg="Task percentage completed=100%"
                        sprint(msg,0)
                        ccmLogger(4,msg,schHistoryArgs)
                    else:
                        pass

                    #if sysHlthCheck in [0,1,2] and SchStatus=="stopped":
                    if sysHlthCheck == None and sys_hlth_mail == "": #SchStatus=="stopped":
                        pass                 
                    elif sysHlthCheck != None and SchStatus=="stopped":
                        sprint ("sysHealthCheck",sysHlthCheck)
                        if sys_hlth_mail == "yes":
                            if sysHlthCheck == 0:
                                statusArgs = loggerArgs(element,SchHistoryName,20,"System Health Check")
                                ccmLogger(0,"System-Health Check All Ok",statusArgs)
                            else:
                                statusArgs = loggerArgs(element,SchHistoryName,20,"System Health Check")
                                ccmLogger(1,"System-Health-Check Warning/Error",statusArgs)
                        elif sys_hlth_mail == "no":
                            if sysHlthCheck == 0:
                                if state is not None and str(state) == '1':
                                    ccmLogger(3,"System-Health Check All Ok. Email has not been validated - failed to send an email",schHistoryArgs)
                                elif state is not None and str(state) == '2':
                                    ccmLogger(3,"System-Health Check All Ok. Email could not be validated - failed to send an email",schHistoryArgs)
                                else:
                                    statusArgs = loggerArgs(element,SchHistoryName,20,"SystemHealthCheck")
                                    ccmLogger(2,"System-Health Check All Ok, no email Configured, no email sent",statusArgs)
                            else:
                                if state is not None and str(state) == '1':
                                    ccmLogger(3,"System-Health-Check Warning/Error. Email has not been validated - failed to send an email",schHistoryArgs)
                                elif state is not None and str(state) == '2':
                                    ccmLogger(3,"System-Health-Check Warning/Error. Email could not be validated - failed to send an email",schHistoryArgs)
                                else:
                                    statusArgs = loggerArgs(element,SchHistoryName,20,"SystemHealthCheck")
                                    ccmLogger(3,"System-Health-Check Warning/Error, no email Configured, no email sent",statusArgs)
                            
                        else:
                            pass
                        
                    else:
                        pass




################# VIRTUALMACHINE ################
                
                elif element=="virtualmachine":
                    data_list=data_body[4:].split(',')[1:]
                    
                    conn=db_connect()
                    conn.text_factory=str 
                    c=conn.cursor()
                    
                    attribute_values=[]
                    attribute_names=[]
                    for i in data_list:
                        cell_vals=i.split("=")
                        names=str(cell_vals[0])
                        values=str(cell_vals[1])
                        attribute_names.append(names)
                        attribute_values.append(values)

                    action=attribute_values[2]
                    
                    if action=="start_App":
                        sprint ("start app",0)
                        app_Name=attribute_values[0]
                        app_Id=attribute_values[3]
                        app_State=attribute_values[4]
                        app_Start_Date=datetime.datetime.now().strftime("%Y-%m-%d")
                        sprint (attribute_values,0)
                        query=c.execute("update virtualmachine set state={0},started_date='{1}' where name='{2}'".format(app_State,app_Start_Date,app_Name))
                        conn.commit()
                        c.close()
                        conn.close()
                        resources_vm_running()

                    if action=="stop_App":
                        app_Name=attribute_values[0]
                        app_Id=attribute_values[3]
                        app_State=attribute_values[4]
                        app_Start_Date=datetime.datetime.now().strftime("%Y-%m-%d")
                        sprint (attribute_values,0)
                        query=c.execute("update virtualmachine set state={0} where name='{1}'".format(app_State,app_Name))
                        conn.commit()
                        c.close()
                        conn.close()
                        resources_vm_running()

##################################volume_Snapshot#####################################################
                elif element=="volume_snapshot":
                    sprint ("volume_Snapshot message received",0)
                    data_list=data_body[4:].split(",")[1:]
                    sprint (data_list,0)

                    conn=db_connect()
                    conn.text_factory=str 
                    c=conn.cursor()

                    attribute_values=[]
                    for i in data_list:
                        cell_vals=i.split("=")
                        #names=str(cell_vals[0])
                        values=str(cell_vals[1])
                        #attribute_names.append(names)
                        attribute_values.append(values)
                    action=attribute_values[2]

                    if action=="create_VolSnapshot":
                        vol_SnapName=attribute_values[0]
                        vol_SnapState=attribute_values[1]
                        vol_ParentID=attribute_values[3]

                        query=c.execute("insert into  volume_snapshot(name,state,vol_id,cr_date) values(?,?,?,datetime())",[vol_SnapName,vol_SnapState,vol_ParentID])
                        conn.commit()
                        c.close()
                        conn.close()

#############JOB(THIS code should be removed)########################

                elif element=="job":
                    conn=db_connect()
                    c=conn.cursor()
                    message_list=data_body.split(",")
                    #print message_list
                    for i in message_list:
                        if "element_id=" in i:
                            element_id=i.split("=")[1]
                        if "done_percentage=" in i:
                            done_percentage=i.split("=")[1]
                        if "status=" in i:
                            status=i.split("=")[1]
                        if "element_job=" in i:
                            job_type=i.split("=")[1]
                        if "element_name=" in i:
                            backupName=i.split("=")[1]
                        if "App_ID=" in i:
                            vmID=i.split("=")[1]
                        if "remoteSavedPath=" in i:
                            SavedPath=i.split("=")[1]
                        if "localSavedPath=" in i:
                            local_path=i.split("=")[1]
                        if "App_State=" in i:
                            vmState=i.split("=")[1]
                        if "uuid=" in i:
                            uID=i.split("=")[1]

                    if job_type=="Email_Logs":
                        jobDone_percentage(element_id,done_percentage,status)

                    if job_type=="Backup_App_Server":
                        backupName=backupName+"_"+uID

                        query_count_name=c.execute("select BackupName from BackupHistory where BackupName='"+backupName+"'")
                        nameCount=c.fetchall()
                        if not nameCount:
                            query_insert=c.execute('''insert into BackupHistory(BackupName,VMId,download_path,cr_date,edit_date,backup_time,download_state,vm_group_id,image_cost,support_cost,state,BackupServerID,uuid)
                                values(?,?,?,date(),date(),time('now'),'no',16,'free',10,0,1,?) ''',[backupName,vmID,SavedPath,uID])
                            conn.commit()
                            jobDone_percentage(element_id,done_percentage,status)
                            #print "inserted Backup"
                        else:
                            query_update=c.execute("update BackupHistory set edit_date=date(),backup_time=time('now') where BackupName='"+backupName+"'")
                            query = "update virtualmachine set last_remote_backup=Date() where id="+str(vmID)
                            conn.commit()
                            jobDone_percentage(element_id,done_percentage,status)
                            #print "updated Backup"
                        c.close()
                        conn.close()


                    if job_type == "Download_MyApp_Server":
                        conn=db_connect()
                        conn.text_factory=str
                        c=conn.cursor()

                        query_update_backup=c.execute("update BackupHistory set local_path=?,download_state=?,download_percentage=? where id=?",(local_path,status,done_percentage,element_id))
                        conn.commit()
                        c.close()
                        conn.close()

############# MUTLIDEVICE #########################
#action={1}
#PoolLevel={2}
#Dedup={3}
#Compression={4}
#Acceleration={5}
#AccelerationStorage={6}
#SystemName={7}
#Percentage={8}
#CalculatedRaw={9}

                elif element=="multi_device":
                    sprint ("multi_device element",0)
                    Encryption="Yes"
                    LogLevel=20
                    sprint ("message=",message_list)
                    for i in message_list[1:]:
                        cell_vals=i.split('=')
                        names=cell_vals[0]
                        if names=="element_name":
                            names="name"
                        else:
                            pass
                        values=str(cell_vals[1])
                        attribute_names.append(names)
                        attribute_values.append(values)
                        if names=="name":
                            PoolType=str(values)
                        elif names=="Compression":
                            zfsCompression=str(values)
                        elif names=="Dedup":
                            zfsDedup=str(values)
                        elif names=="Acceleration":
                            zfsAcceleration=str(values)
                        elif names=="PoolLevel":
                            PoolLevel=str(values)
                        elif names=="action":
                            PoolAction=str(values)
                        elif names=="AccelerationStorage":
                            PoolAccelerationStorage=str(values)
                        elif names=="SystemName":
                            PoolSystemName=str(values)
                        elif names=="pool_storage":
                            PoolStorage=str(values)
                        elif names=="Encryption":
                            Encryption=str(values)
                        elif names=="CalculatedRaw":
                            PoolSize=str(values)
                        elif names=="Percentage":
                            PerCent=str(values)
                            
                    attribute_names.pop(1)
                    attribute_values.pop(1)
                    attribute_names=','.join(attribute_names)
                    attribute_values=','.join(attribute_values)
                    sprint ("multi device",attribute_names+attribute_values)
                    res=wErrUnknownCmd
                    if LicenceState!=0:
                        PoolAction="NoLicence"
                        res=-2
                    location=getPoolLocation(PoolSystemName)
                    sprint ("PoolType =",PoolType)
                    sprint ("PoolSystemName=",PoolSystemName)
                    if (PoolAction=="PoolCreate"):
                        
                        if int(PerCent) > 90:
                           PoolSize=0
                        PC1=int(PerCent)
                        PC=float(PerCent)/100
                        sprint ('PC=',PC)
                        res=PoolCreate(PoolType, PoolSize, PoolLevel, zfsCompression, zfsAcceleration, zfsDedup,PoolAccelerationStorage,PoolSystemName,Encryption,location,PC)

                    elif (PoolAction=="PoolDelete"):
                        res=PoolDelete(PoolType,PoolSystemName)
                        
                    elif (PoolAction=="PoolUpdate"):
                        res=PoolUpdate(PoolType, zfsCompression, zfsAcceleration, zfsDedup,PoolSystemName)
                        
                    elif (PoolAction=="PoolStop"):
                        res=PoolStop(PoolType, PoolSystemName,"none")
                        
                    elif (PoolAction=="PoolInfo"):
                        res=PoolInfo(PoolType,PoolSystemName)

                    if res==-2:
                        json_res = json.JSONEncoder().encode({"status": "fail", "description": "No Licence Error Code: {}".format(res)})
                        sprint ("command Failed no Licence",res)
                        logMsg = str("Pool") +" command Failed no Licence, Cmd/Error Code="+str(PoolAction)+"/"+str(res)
                        CCM_Alert(ccmINFO,LogLevel,logMsg)
                    if res!=0:
                        json_res = json.JSONEncoder().encode({"status": "fail", "description": "Pool Action Error Code: {}".format(res)})
                        sprint ("command Failed",res)
                        logMsg = str("Pool") +" command Failed, Cmd/Error Code="+str(PoolAction)+"/"+str(res)
                        CCM_Alert(ccmINFO,LogLevel,logMsg)
                    else:
                        json_res = json.JSONEncoder().encode({"status": "success", "description": "Pool Action OK Code: {}".format(res)})
                        sprint ("command Passed",res)
                        logMsg = str("Pool") +" command succesfull , Cmd/Pool Code="+str(PoolAction)+"/"+str(PoolSystemName)
                        CCM_Alert(ccmINFO,LogLevel,logMsg)
                    connection.sendall(json_res.encode())                   

#################Docker##################
                elif element=="docker":
                    LogLevel = 20
                    ERRTEXT = {
                        -3:  "Docker storage not configured or not mounted. Create a Volume with Protocol=Docker and mount it.",
                        -12: "Host port is already allocated.",
                        -13: "Selected Docker network was not found.",
                        # --- NEW: Docker network specific codes ---
                        -14: "Invalid CIDR for Docker network.",
                        -15: "Network CIDR/gateway rejected by policy (overlap/reserved range).",
                        -16: "Docker engine/network API error.",
                        # ------------------------------------------
                        -21: "Invalid or insufficient parameters.",
                        -22: "Backup failed",
                    }
                    # --- Initialize all D* locals before parsing ---
                    Dname = Dcmd = Dimage = Dmemory = Dcpu = Ddisk = Dnetwork = Dport = Dtype = Dcmd_Id = Dpartition = None
                    Dcidr = Dgateway = Dsnapshot = None
                    DbackupServer = DbackupName = Ddest = None
                    DbackupVolume = DbackupVolumeId = None
                    Dinclude = None
                    DbackupGroup = None
                    DbackupType  = None
                    Dsnapshot_ids_list = []
                    Dbackupids = None
                    Dbackup_ids_list = []
                    Dvolume_name = None
                    Dvolume_id   = None
                    Dtarget      = None
                    DkeepBackups   = None
                    DkeepSnapshots = None

                    sprint("docker msg", message_list)
                    _dbg_dump_tokens("[GUI]", message_list)
                    idx = 1
                    while idx < len(message_list):
                        cell_vals = message_list[idx].split('=', 1)
                        names = cell_vals[0]

                        if names == "element_name":
                            names = "name"
                        if names == "args":
                            idx += 1
                            continue

                        values = str(cell_vals[1]) if len(cell_vals) > 1 else ""
                        _dbg_log_token(names, values)
                        if names.lower() in ("disk", "disk_gb", "storage", "storage_gb"):
                            sprint(f"[DISK-FIELD] Seen '{names}' with value {repr(values)}", 0)
                        sprint("values", values)

                        # ---- stitch network=[...] that may be split across tokens ----
                        if names == "network":
                            val = values.strip()
                            # Only stitch if it looks like a list (starts with '[')
                            if val.startswith('['):
                                net_expr = val
                                while ']' not in net_expr and (idx + 1) < len(message_list):
                                    idx += 1
                                    frag = message_list[idx]
                                    if not net_expr.rstrip().endswith(','):
                                        net_expr += ','
                                    net_expr += frag
                                net_expr = net_expr.strip()
                                try:
                                    try:
                                        parsed = ast.literal_eval(net_expr)
                                    except Exception:
                                        parsed = json.loads(net_expr.replace("'", '"'))
                                    # Handle nested-string case "['docker2']" that arrived as a single string
                                    if isinstance(parsed, str) and parsed.startswith('[') and parsed.endswith(']'):
                                        parsed = ast.literal_eval(parsed)
                                    if isinstance(parsed, list):
                                        Dnetwork = [str(x).strip() for x in parsed if str(x).strip()]
                                    else:
                                        Dnetwork = [str(parsed).strip()]
                                except Exception:
                                    inner = net_expr.lstrip('[').rstrip(']')
                                    toks = [t.strip(" '\"") for t in inner.replace(',', ' ').split() if t.strip(" '\"")]
                                    Dnetwork = toks or ([net_expr] if net_expr else [])
                            else:
                                # scalar or "none"
                                Dnetwork = None if val.lower() in ("", "none") else [val]

                            attribute_names.append("network")
                            attribute_values.append("" if Dnetwork is None else ",".join(Dnetwork))
                            idx += 1
                            continue

                        if names == "action":
                            Dcmd = values
                        elif names == "image":
                            Dimage = values
                        elif names == "memory":
                            Dmemory = values
                        elif names == "cpus":
                            Dcpu = values
                        elif names == "disk":
                            Ddisk = values
                        elif names == "port":
                            Dport = values
                        elif names == "type":
                            Dtype = values
                        elif names == "uuid":
                            Dcmd_Id = values
                        elif names == "partition":
                            Dpartition = values
                        elif names == "name":
                            Dname = values
                        elif names == "cidr":
                            Dcidr = values
                        elif names == "gateway":
                            Dgateway = values
                        elif names == "snapshot_name":
                            Dsnapshot = values
                        elif names in ("snapshot_ids", "snapshot_ids[]"):
                            sprint(f"[DBG] snapshot_ids token seen: {names}={values}", 0)
                            if values.strip():
                                Dsnapshot_ids_list.append(values.strip())
                            idx += 1
                            continue
                        elif names == "backupServer":
                            DbackupServer = values
                        elif names in ("backup_name", "backupName"):
                            DbackupName = values
                        elif names == "dest":
                            Ddest = values
                        elif names == "backupVolume":
                            DbackupVolume = values
                        elif names == "backupVolumeId":
                            DbackupVolumeId = values
                        elif names == "backupType":
                            DbackupType = values
                        elif names == "backupGroup":
                            DbackupGroup = values
                        elif names == "keepBackups":
                            DkeepBackups = values
                        elif names == "keepSnapshots":
                            DkeepSnapshots = values
                        elif names in ("backup_ids", "backup_ids[]"):
                            if values.strip():
                                Dbackup_ids = values.strip()
                                Dbackup_ids_list.append(values.strip())
                        elif names in ("volume_name", "volume"):
                            Dvolume_name = values
                        elif names in ("volume_id", "volumeId"):
                            Dvolume_id = values
                        elif names in ("target", "mount", "path", "container_path"):
                            Dtarget = values
                        elif Dcmd == "create_Network":
                            Dcmd = "NetworkCreate"
                        elif Dcmd == "edit_Network":
                            Dcmd = "NetworkEdit"
                        elif Dcmd == "update_Network":
                            Dcmd = "NetworkEdit"
                        elif Dcmd == "delete_Network":
                            Dcmd = "NetworkDelete"

                        elif names == "include":
                            val = values.strip()
                            if val.startswith('['):
                                inc_expr = val
                                # keep consuming tokens until we see a closing ']'
                                while ']' not in inc_expr and (idx + 1) < len(message_list):
                                    idx += 1
                                    frag = message_list[idx]
                                    # add a comma between fragments if needed (mirrors network stitching)
                                    if not inc_expr.rstrip().endswith(','):
                                        inc_expr += ','
                                    inc_expr += frag
                                Dinclude = inc_expr.strip()
                            else:
                                Dinclude = val

                            attribute_names.append("include")
                            attribute_values.append(Dinclude if Dinclude is not None else "")
                            idx += 1
                            continue

                        attribute_names.append(names)
                        attribute_values.append(values)
                        idx += 1
                    attribute_names = ','.join(attribute_names)
                    attribute_values = ','.join(attribute_values)
                    sprint("attribute_names", attribute_names)
                    try:
                        sprint("[RAW ATTR] names=" + attribute_names, 0)
                        sprint("[RAW ATTR] values=" + attribute_values, 0)
                    except Exception:
                        pass
                    # ---- Normalize and debug the collected args ----
                    Dname      = _to_str_or_none(Dname)
                    Dcmd       = _to_str_or_none(Dcmd)
                    Dimage     = _normalize_image(Dimage)          # friendly for DB/logging
                    Dmemory    = _to_str_or_none(Dmemory)
                    Dcpu       = _to_str_or_none(Dcpu)
                    Ddisk      = _to_str_or_none(Ddisk)
                    Dnetwork   = _parse_network_arg(Dnetwork)      # "netA" or ["netA","netB"]
                    Dport      = _to_int_or_none(Dport)
                    Dtype      = _to_str_or_none(Dtype)
                    Dcmd_Id    = _to_str_or_none(Dcmd_Id)
                    Dpartition = _to_str_or_none(Dpartition)
                    Dcidr      = _to_str_or_none(Dcidr)
                    Dgateway   = _to_str_or_none(Dgateway)
                    Dimage_ref = _resolve_docker_ref(Dimage)       # actual docker ref
                    Dsnapshot = _to_str_or_none(Dsnapshot)
                    DbackupServer  = _to_str_or_none(DbackupServer)
                    DbackupName    = _to_str_or_none(DbackupName)
                    Ddest          = _to_str_or_none(Ddest)
                    DbackupVolume  = _to_str_or_none(DbackupVolume)
                    DbackupVolumeId = _to_str_or_none(DbackupVolumeId)
                    Dinclude = _to_str_or_none(Dinclude)
                    DbackupGroup = _to_str_or_none(DbackupGroup)
                    DbackupType  = _to_str_or_none(DbackupType)
                    Dbackup_ids = ",".join(Dbackup_ids_list) if "Dbackup_ids_list" in locals() and Dbackup_ids_list else None
                    Dvolume_name = _to_str_or_none(Dvolume_name)
                    Dvolume_id   = _to_str_or_none(Dvolume_id)
                    Dtarget      = _to_str_or_none(Dtarget)
                    # normalize invalid ports
                    if Dport is not None and Dport <= 0:
                        Dport = None
                    Dsnapshot_ids = ",".join(Dsnapshot_ids_list) if Dsnapshot_ids_list else None

                    DkeepBackups   = _to_str_or_none(DkeepBackups)
                    DkeepSnapshots = _to_str_or_none(DkeepSnapshots)

                    _dbg_var("Dname", Dname)
                    _dbg_var("Dcmd", Dcmd)
                    _dbg_var("Dimage", Dimage)
                    _dbg_var("Dimage_ref(used)", Dimage_ref)
                    _dbg_var("Dmemory", Dmemory)
                    _dbg_var("Dcpu", Dcpu)
                    _dbg_var("Ddisk", Ddisk)
                    _dbg_var("Dnetwork", Dnetwork)
                    _dbg_var("Dport", Dport)
                    _dbg_var("Dtype", Dtype)
                    _dbg_var("Dcmd_Id", Dcmd_Id)
                    _dbg_var("Dpartition", Dpartition)
                    _dbg_var("Dcidr", Dcidr)
                    _dbg_var("Dgateway", Dgateway)
                    _dbg_var("Dsnapshot", Dsnapshot)
                    _dbg_var("Dsnapshot_ids", Dsnapshot_ids)
                    _dbg_var("Dsnapshot_ids_list", Dsnapshot_ids_list)
                    _dbg_var("DbackupServer", DbackupServer)
                    _dbg_var("DbackupName", DbackupName)
                    _dbg_var("Ddest", Ddest)
                    _dbg_var("DbackupVolume", DbackupVolume)
                    _dbg_var("DbackupVolumeId", DbackupVolumeId)
                    _dbg_var("Dinclude", Dinclude)
                    _dbg_var("DbackupGroup", DbackupGroup)
                    _dbg_var("DbackupType", DbackupType)
                    _dbg_var("Dbackup_ids", Dbackup_ids)
                    _dbg_var("Dvolume_name", Dvolume_name)
                    _dbg_var("Dvolume_id",   Dvolume_id)
                    _dbg_var("Dtarget",      Dtarget)

                    _dbg_var("DkeepBackups",   DkeepBackups)
                    _dbg_var("DkeepSnapshots", DkeepSnapshots)

                    # ---- Local safety helper: does CIDR overlap any host IPv4 interface? ----
                    def _cidr_overlaps_host(cidr_str):
                        try:
                            import ipaddress, subprocess, json as _json
                            net = ipaddress.ip_network(str(cidr_str).strip(), strict=False)
                            r = subprocess.run(
                                ["ip", "-j", "-4", "addr"],
                                capture_output=True, text=True, check=True
                            )
                            data = _json.loads(r.stdout)
                            for link in data:
                                for ai in link.get("addr_info", []):
                                    if ai.get("family") == "inet":
                                        hostnet = ipaddress.ip_network(
                                            f"{ai.get('local')}/{ai.get('prefixlen')}", strict=False
                                        )
                                        if net.overlaps(hostnet):
                                            return True
                        except Exception:
                            pass
                        return False

                    # ---- Docker action with guarded try/except ----
                    res = -2
                    json_res = None
                    try:
                        if Dcmd == "Create":
                            # ------------------------------------------------------------------
                            # Guard 1: refuse create if retained backups/snapshots exist
                            # for a previous VM with the same name.
                            # ------------------------------------------------------------------
                            try:
                                from Docker import has_retained_backups_or_snapshots

                                if has_retained_backups_or_snapshots(Dname):
                                    sprint(
                                        f"[Create] Refusing to create VM '{Dname}' – "
                                        f"retained backups/snapshots exist for this name.",
                                        0,
                                    )
                                    res = -21
                                    ERRTEXT[-21] = (
                                        "Cannot create a new VM with this name because there are "
                                        "retained backups and/or snapshots for a previous VM with "
                                        "the same name. Please delete or rename them first."
                                    )
                                else:
                                    # ------------------------------------------------------------------
                                    # Guard 2: Capacity guard for create (similar to Resize)
                                    # ------------------------------------------------------------------
                                    ERRTEXT.setdefault(-21, "Insufficient capacity to satisfy request")
                                    try:
                                        caps = _system_caps_db() or {}
                                        # Desired absolute targets coming in as strings
                                        tgt_cpu  = None if (Dcpu    is None or str(Dcpu).strip()    == "") else float(Dcpu)
                                        tgt_mem  = None if (Dmemory is None or str(Dmemory).strip() == "") else float(Dmemory)
                                        tgt_disk = None if (Ddisk   is None or str(Ddisk).strip()   == "") else float(Ddisk)

                                        # For create, deltas == absolutes (no current allocations yet)
                                        delta_cpu  = 0.0 if tgt_cpu  is None else tgt_cpu
                                        delta_mem  = 0.0 if tgt_mem  is None else tgt_mem
                                        delta_disk = 0.0 if tgt_disk is None else tgt_disk

                                        block = []
                                        if delta_cpu  > caps.get("free_vcpu", 0.0)  + 1e-9:
                                            block.append("vCPU capacity exceeded")
                                        if delta_mem  > caps.get("free_mem", 0.0)   + 1e-9:
                                            block.append("Memory capacity exceeded")
                                        if delta_disk > caps.get("free_store", 0.0) + 1e-9:
                                            block.append("Storage capacity exceeded")

                                        if block:
                                            res = -21
                                            ERRTEXT[-21] = "; ".join(block)
                                        else:
                                            if Dport is None:
                                                sprint(
                                                    "[WARN] No host port provided; container will only "
                                                    "be reachable by container IP",
                                                    0,
                                                )
                                            sprint("[DBG] Calling DockerCreate(...) with args shown above", 0)
                                            res = DockerCreate(
                                                Dname,
                                                Dcmd,
                                                Dimage_ref,
                                                Dmemory,
                                                Dcpu,
                                                Ddisk,
                                                Dnetwork,
                                                Dport,
                                                Dcmd_Id,
                                            )
                                    except Exception as e:
                                        sprint(f"[CAPACITY GUARD Create] warn: {e}", 0)
                                        sprint("[DBG] Calling DockerCreate(...) after guard exception", 0)
                                        res = DockerCreate(
                                            Dname,
                                            Dcmd,
                                            Dimage_ref,
                                            Dmemory,
                                            Dcpu,
                                            Ddisk,
                                            Dnetwork,
                                            Dport,
                                            Dcmd_Id,
                                        )

                            except Exception as e:
                                # If the retained-artifacts check itself blows up, log and fall back
                                sprint(f"[Create] retained-artifact guard failed for '{Dname}': {e}", 0)
                                ERRTEXT.setdefault(
                                    -21,
                                    "Internal check failed while validating retained backups/snapshots"
                                )
                                try:
                                    # Fall back to the pure capacity guard + create
                                    ERRTEXT.setdefault(-21, "Insufficient capacity to satisfy request")
                                    caps = _system_caps_db() or {}
                                    tgt_cpu  = None if (Dcpu    is None or str(Dcpu).strip()    == "") else float(Dcpu)
                                    tgt_mem  = None if (Dmemory is None or str(Dmemory).strip() == "") else float(Dmemory)
                                    tgt_disk = None if (Ddisk   is None or str(Ddisk).strip()   == "") else float(Ddisk)

                                    delta_cpu  = 0.0 if tgt_cpu  is None else tgt_cpu
                                    delta_mem  = 0.0 if tgt_mem  is None else tgt_mem
                                    delta_disk = 0.0 if tgt_disk is None else tgt_disk

                                    block = []
                                    if delta_cpu  > caps.get("free_vcpu", 0.0)  + 1e-9:
                                        block.append("vCPU capacity exceeded")
                                    if delta_mem  > caps.get("free_mem", 0.0)   + 1e-9:
                                        block.append("Memory capacity exceeded")
                                    if delta_disk > caps.get("free_store", 0.0) + 1e-9:
                                        block.append("Storage capacity exceeded")

                                    if block:
                                        res = -21
                                        ERRTEXT[-21] = "; ".join(block)
                                    else:
                                        if Dport is None:
                                            sprint(
                                                "[WARN] No host port provided; container will only "
                                                "be reachable by container IP",
                                                0,
                                            )
                                        sprint("[DBG] Calling DockerCreate(...) with args shown above", 0)
                                        res = DockerCreate(
                                            Dname,
                                            Dcmd,
                                            Dimage_ref,
                                            Dmemory,
                                            Dcpu,
                                            Ddisk,
                                            Dnetwork,
                                            Dport,
                                            Dcmd_Id,
                                        )
                                except Exception as e2:
                                    sprint(f"[Create] fallback capacity guard failed for '{Dname}': {e2}", 0)
                                    sprint("[DBG] Calling DockerCreate(...) after fallback exception", 0)
                                    res = DockerCreate(
                                        Dname,
                                        Dcmd,
                                        Dimage_ref,
                                        Dmemory,
                                        Dcpu,
                                        Ddisk,
                                        Dnetwork,
                                        Dport,
                                        Dcmd_Id,
                                    )
                        elif Dcmd == "Start":
                            try:
                                nets = _normalize_network_names(Dnetwork)
                                if nets:
                                    if not _replace_vm_network_links(Dname, nets):
                                        sprint(f"[WARN] Start: failed to persist GUI networks for {Dname}", 0)
                                    else:
                                        sprint(f"[DBG] Start: persisted GUI networks {Dname} -> {nets}", 0)
                            except Exception as e:
                                sprint(f"[WARN] Start: failed to persist GUI networks for {Dname}: {e}", 0)

                            sprint("[DBG] Calling DockerStart(...) with desired networks from GUI", 0)
                            res = DockerStart(Dname, Dcmd, Dcmd_Id)

                        elif Dcmd == "Stop":
                            sprint("[DBG] Calling DockerStop(...)", 0)
                            res = DockerStop(Dname, Dcmd, Dcmd_Id)

                        elif Dcmd == "Delete":
                            res = 0

                        elif Dcmd == "Resize":
                            # Parse incoming absolute targets (blank/None => no change)
                            tgt_cpu  = None if (Dcpu    is None or str(Dcpu).strip()    == "") else float(Dcpu)
                            tgt_mem  = None if (Dmemory is None or str(Dmemory).strip() == "") else float(Dmemory)
                            tgt_disk = None if (Ddisk   is None or str(Ddisk).strip()   == "") else float(Ddisk)

                            # Current VM allocations from DB
                            cur_cpu, cur_mem, cur_disk = _current_vm_limits_db(Dname)

                            # ---- hard guard: refuse shrink (target_disk < current_disk) ----
                            if tgt_disk is not None and cur_disk is not None and tgt_disk < float(cur_disk) - 1e-9:
                                res = -21
                                ERRTEXT[-21] = (
                                    f"Shrinking storage is not supported "
                                    f"(current {float(cur_disk):.0f} GB → requested {tgt_disk:.0f} GB). "
                                    f"Please recreate the VM with a smaller disk."
                                )
                            else:
                                # System free capacities
                                caps = _system_caps_db() or {}
                                free_cpu  = caps.get("free_vcpu",  0.0)
                                free_mem  = caps.get("free_mem",   0.0)
                                free_sto  = caps.get("free_store", 0.0)

                                # OFF-state semantics: CPU/MEM deltas are absolute vs 0
                                delta_cpu  = 0.0 if tgt_cpu  is None else max(0.0, tgt_cpu - 0.0)
                                delta_mem  = 0.0 if tgt_mem  is None else max(0.0, tgt_mem - 0.0)
                                # Storage only consumes the increase
                                delta_disk = 0.0 if tgt_disk is None else max(0.0, tgt_disk - (cur_disk or 0.0))

                                ERRTEXT.setdefault(-21, "Insufficient capacity to satisfy request")
                                block = []
                                if tgt_cpu is not None and delta_cpu > free_cpu + 1e-9:
                                    block.append(f"Not enough vCPU: need {tgt_cpu:.2f}, free {free_cpu:.2f}")
                                if tgt_mem is not None and delta_mem > free_mem + 1e-9:
                                    block.append(f"Not enough Memory: need {tgt_mem:.2f} GB, free {free_mem:.2f} GB")
                                if delta_disk > free_sto + 1e-9:
                                    block.append(f"Not enough Storage: need +{delta_disk:.2f} GB, free {free_sto:.2f} GB")

                                if block:
                                    res = -21
                                    ERRTEXT[-21] = "; ".join(block)
                                else:
                                    sprint("[DBG] Calling DockerResize(...) with args shown above", 0)
                                    res = DockerResize(Dname, Dcmd, Dimage_ref, Dmemory, Dcpu, Ddisk, Dnetwork, Dport, Dcmd_Id)
                        # ---------- NEW: Docker NetworkCreate from GUI ----------
                        elif Dcmd in ("NetworkCreate", "NetCreate", "create_Network"):
                            try:
                                from Docker import EnsureDockerNetworkFromArgs
                                sprint(f"[NET][UI] EnsureDockerNetworkFromArgs for name={Dname}, cidr={Dcidr}", 0)
                                rc = EnsureDockerNetworkFromArgs(
                                        Dname or "",
                                        Dcidr or "",
                                        Dgateway or None,
                                        cmd_id=Dcmd_Id or "UI"
                                     )
                                res = rc
                            except Exception as e:
                                sprint(f"[NET][UI] EnsureDockerNetworkFromArgs exception for '{Dname}': {e}", 0)
                                res = -2
                        # ---------- NEW: Docker NetworkEdit from GUI ----------
                        elif Dcmd in ("NetworkEdit", "NetEdit", "edit_Network"):
                            try:
                                from Docker import EnsureDockerNetworkFromArgs
                                sprint(
                                    f"[NET][UI] EnsureDockerNetworkFromArgs (edit) for name={Dname}, cidr={Dcidr}",
                                    0
                                )
                                # Use the CIDR coming from the UI / CCM, not from DB
                                rc = EnsureDockerNetworkFromArgs(Dname or "", Dcidr or "", Dcmd_Id or "UI")
                                res = rc
                            except Exception as e:
                                sprint(
                                    f"[NET][UI] EnsureDockerNetworkFromArgs exception (edit) for '{Dname}': {e}",
                                    0
                                )
                                res = -2
                        # ---------- NEW: Docker NetworkDelete from GUI ----------
                        elif Dcmd in ("NetworkDelete", "NetDelete", "delete_Network"):
                            try:
                                from Docker import DockerNetworkDelete
                                sprint(f"[NET][UI] DockerNetworkDelete for name={Dname}", 0)
                                rc = DockerNetworkDelete(Dname or "", cmd_id=Dcmd_Id or "UI")
                                res = rc
                            except Exception as e:
                                sprint(f"[NET][UI] DockerNetworkDelete exception for '{Dname}': {e}", 0)
                                res = -2
                        elif Dcmd == "Pause":
                            sprint("[DBG] Calling DockerPause(...)", 0)
                            res = DockerPause(Dname, Dcmd, Dcmd_Id)
                        elif Dcmd == "UnPause":
                            sprint("[DBG] Calling DockerUnPause(...)", 0)
                            res = DockerUnPause(Dname, Dcmd, Dcmd_Id)
                        elif Dcmd == "SnapshotCreate":
                            import re
                            # 1) normalize input (allow auto if empty)
                            snap = (Dsnapshot or "").strip()
                            auto_mode = (snap == "")

                            if not auto_mode:
                                # force lowercase; UI already forbids uppercase, but be safe
                                snap = snap.lower()
                                # 2) name rules: 3..63, allowed, start/end alnum
                                if not (3 <= len(snap) <= 63):
                                    res = -21
                                    ERRTEXT[-21] = "Snapshot name must be 3–63 characters"
                                elif not re.fullmatch(r"[a-z0-9](?:[a-z0-9-]*[a-z0-9])?", snap):
                                    res = -21
                                    ERRTEXT[-21] = "Only lowercase letters, digits, and dashes; must start/end alphanumeric"
                                else:
                                    res = 0  # tentatively OK
                            else:
                                res = 0

                            # bail early on invalid name
                            if res == -21:
                                pass
                            else:
                                # 3) duplicate check against existing snapshots for this VM
                                try:
                                    existing = DockerSnapshotList(Dname)  # list of dicts
                                    existing_names = { (s.get("snapshot") or s.get("image_name") or "").strip().lower()
                                                       for s in existing }
                                except Exception:
                                    existing_names = set()

                                # 4) if name given and already exists -> error
                                if (not auto_mode) and (snap in existing_names):
                                    res = -21
                                    ERRTEXT[-21] = f"Snapshot '{snap}' already exists"
                                else:
                                    # 5) ask backend to create; pass empty to auto-generate
                                    rc = DockerSnapshotCreate(Dname, "" if auto_mode else snap)
                                    if rc == 0:
                                        json_res = json.JSONEncoder().encode({
                                            "status": "success",
                                            "message": f"Snapshot '{(snap or 'auto')}' created for {Dname}"
                                        })
                                        res = 0
                                    elif rc == -21:
                                        # backend also detected duplicate or invalid
                                        res = -21
                                        ERRTEXT[-21] = ERRTEXT.get(-21, "Snapshot already exists or invalid")
                                    else:
                                        res = -2

                        elif Dcmd == "SnapshotList":
                            try:
                                from Docker import _db_vm_id
                                vm_id = _db_vm_id(Dname)

                                raw_snaps = DockerSnapshotList(Dname)  # list of dicts

                                # ---- adapt to UI table shape ----
                                rows = []
                                for i, s in enumerate(raw_snaps, start=1):
                                    created = s.get("created") or ""
                                    rows.append({
                                        "id": i,
                                        "image_name": s.get("snapshot") or "",
                                        "tag": "docker",
                                        "savedPath": s.get("path") or "N/A",   # <— column shown in your table
                                        "state": 1,
                                        "cr_date": created,
                                        "edit_date": created,
                                        "vm_id": vm_id,
                                        "result": "success"
                                    })

                                # ⚠️ Return the array directly (legacy UI expects a top-level list)
                                json_res = json.JSONEncoder().encode(rows)
                                res = 0

                            except Exception as e:
                                sprint(f"[SNAP] list exception: {e}", 0)
                                res = -2

                        elif Dcmd == "SnapshotDelete":
                            snapname = (Dsnapshot or "").strip() if Dsnapshot else ""

                            # If no explicit name, try to map snapshot_ids -> name
                            if (not snapname) and Dsnapshot_ids:
                                try:
                                    s = str(Dsnapshot_ids).strip()
                                    ids = []

                                    if s.startswith("[") and s.endswith("]"):
                                        # JSON array like "[3,5]"
                                        try:
                                            ids = [int(x) for x in json.loads(s)]
                                        except Exception:
                                            ids = []
                                    else:
                                        # Drop any "snapshot_ids[]=" prefix if present
                                        eq = s.find("=")
                                        if eq != -1:
                                            s = s[eq + 1 :]

                                        # Normalize separators to commas
                                        s = s.replace("|", ",").replace(" ", ",")
                                        ids = [int(tok) for tok in s.split(",") if tok.isdigit()]

                                    if ids:
                                        # raw = DockerSnapshotList(Dname)  # may be list OR {"snapshots":[...]}
                                        # snaps = raw.get("snapshots", raw) if isinstance(raw, dict) else raw

                                        # # UI IDs are 1..N in the same order we list
                                        # target = ids[0]
                                        # idx = 0
                                        # for row in snaps:
                                        #     idx += 1
                                        #     if idx == target:
                                        #         snapname = (row.get("snapshot") or row.get("image_name") or "").strip()
                                        #         break

                                        import sqlite3
                                        conn = sqlite3.connect(DBPath); 
                                        cur = conn.cursor()
                                        try:
                                            placeholders = ",".join("?" * len(ids))
                                            query = f"""
                                                SELECT image_name FROM virtualmachine_snapshot
                                                WHERE id IN ({placeholders})
                                            """
                                            cur.execute(query, ids)
                                            rows = cur.fetchall()
                                            snap_names = [r[0] for r in rows if r[0]]
                                        except Exception as e:
                                            snap_names = []
                                        finally:
                                            cur.close(); 
                                            conn.close()
                                        
                                        snapname = ",".join(snap_names)
                                except Exception as e:
                                    sprint(f"[SNAP] delete mapping exception: {e}", 0)

                            if not snapname:
                                res = -21
                                json_res = json.JSONEncoder().encode({
                                    "status": "fail",
                                    "message": "snapshot_name or snapshot_ids is required",
                                    "code": -21
                                })
                            else:
                                rc = DockerSnapshotDelete(Dname, snap_names)
                                if rc == 0:
                                    json_res = json.JSONEncoder().encode({
                                        "status": "success",
                                        "message": f"Snapshot '{snapname}' deleted"
                                    })
                                    res = 0
                                else:
                                    res = -22
                                    json_res = json.JSONEncoder().encode({
                                        "status": "fail",
                                        "message": "Snapshot delete failed",
                                        "code": -22
                                    })

                        elif Dcmd == "BackupStart":
                            # Expect: snapshot_name (Dsnapshot), backupServer (Dbackup), optional backupName (DbackupName)
                            # Parse tokens earlier like others:
                            #   elif names == "snapshot_name": Dsnapshot = values
                            #   elif names == "backupServer":  Dbackup = values
                            #   elif names == "backupName":    DbackupName = values

                            snap = Dsnapshot
                            bdest = DbackupServer
                            bname = DbackupName
                            bvol  = DbackupVolume
                            bvol_id_str = DbackupVolumeId
                            bvol_id = int(bvol_id_str) if (bvol_id_str and bvol_id_str.isdigit()) else None

                            if not snap or (not bdest and not bvol and not bvol_id):
                                res = -21
                                ERRTEXT.setdefault(-21, "Missing snapshot_name and no destination specified")
                            else:
                                rc = DockerBackupStart(Dname, snap, backup_dest_name=bdest,
                                                       backup_name=bname, backup_volume_name=bvol,
                                                       backup_volume_id=bvol_id )
                                if rc == 0:
                                    json_res = json.JSONEncoder().encode({
                                        "status": "success",
                                        "message": f"Backup started for '{Dname}'"
                                    })
                                    res = 0
                                elif rc == -21:
                                    res = -21
                                    ERRTEXT[-21] = "Invalid backup request"
                                else:
                                    res = -2

                        elif Dcmd == "BackupStatus":
                            st = DockerBackupStatus(Dname)
                            json_res = json.JSONEncoder().encode(st)
                            res = 0 if st.get("status") == "success" else -2
                        elif Dcmd in ("BackupLocal", "BackupFull"):
                            extra_paths = []
                            v = (DbackupVolume or "").strip()
                            if v and v.lower() != "none":
                                p = f"/mnt/{v}".rstrip("/")
                                if os.path.isdir(p):
                                    extra_paths = [p]
                            rc, out = DockerBackupFull(
                                Dname,
                                backup_name=DbackupName,
                                dest=Ddest,
                                cmd_id=Dcmd_Id,
                                backupType=DbackupType,
                                volume=DbackupVolume,
                                include_disk=True,
                                extra_host_paths=extra_paths,
                            )
                            if rc == 0:
                                json_res = json.JSONEncoder().encode({
                                    "status": "success",
                                    "message": f"Full Backup created: {out}"
                                })
                                res = 0
                            else:
                                sprint(f"[BackupLocal/Full] rc={rc} msg={out}", 0)
                                res = -22
                                json_res = json.JSONEncoder().encode({
                                    "status": "fail",
                                    "message": out,
                                    "code": -22
                                 })
                        elif Dcmd == "BackupCustom":
                            # NOTE: builtins.set() avoids collision with st.py's set(...)
                            import builtins, re

                            # Safely read the parsed include string
                            include_csv = _to_str_or_none(locals().get("Dinclude", None))

                            # Normalize include list:
                            # - Accept "a,b,c" or "a|b|c"
                            # - Accept bracketed formats like "[a,b,c]"
                            # - Whitespace-insensitive
                            wanted = builtins.set()
                            if include_csv:
                                s = include_csv.strip()
                                if s.startswith("[") and s.endswith("]"):
                                    s = s[1:-1]
                                # split on comma or pipe
                                for tok in re.split(r"[,\|]+", s):
                                    t = tok.strip().lower()
                                    if t:
                                        wanted.add(t)
                            else:
                                wanted = {"data_export", "container_config"}

                            # Map to booleans for the backend
                            opts = {
                                "include_data_export":      ("data_export"      in wanted),
                                "include_disk_image":       ("disk_image"       in wanted),
                                "include_container_config": ("container_config" in wanted),
                                "include_bind_mounts":      ("bind_mounts"      in wanted),
                                "include_logs":             ("logs"             in wanted),
                                "include_snapshots_meta":   ("snapshots_meta"   in wanted),
                            }

                            # Refuse empty selection
                            if not any(opts.values()):
                                res = -21
                                json_res = json.JSONEncoder().encode({
                                    "status": "fail",
                                    "message": "Invalid backup request (no components selected)",
                                    "code": -21
                                })
                            else:
                                extra_paths = []
                                if DbackupVolume:
                                    p = f"/mnt/{DbackupVolume}".rstrip("/")
                                    if os.path.exists(p):
                                        extra_paths = [p]
                                rc, out = DockerBackupCustom(
                                    Dname,
                                    backup_name=DbackupName,
                                    dest=Ddest,
                                    cmd_id=Dcmd_Id,
                                    backupType=DbackupType,
                                    volume=DbackupVolume,
                                    extra_host_paths=extra_paths,
                                    **opts
                                )
                                if rc == 0:
                                    json_res = json.JSONEncoder().encode({
                                        "status": "success",
                                        "message": f"Custom backup created: {out}"
                                    })
                                    res = 0
                                elif rc == -21:
                                    res = -21
                                    json_res = json.JSONEncoder().encode({
                                        "status": "fail",
                                        "message": "Invalid backup request (no components selected)",
                                        "code": -21
                                    })
                                else:
                                    res = -22
                                    json_res = json.JSONEncoder().encode({
                                        "status": "fail",
                                        "message": "Backup failed",
                                        "code": -22
                                    })

                        elif Dcmd == "BackupDelete":
                            # Accept either: backup_name=<name>  OR  backup_ids / backup_ids[]=...
                            # Avoid regex to sidestep any shadowing issues.
                            # 1) Gather raw IDs string from either scalar or collected list
                            raw_ids = None
                            if Dbackup_ids is not None and str(Dbackup_ids).strip():
                                raw_ids = str(Dbackup_ids).strip()
                            elif Dbackup_ids_list:
                                try:
                                    raw_ids = ",".join([str(x).strip() for x in Dbackup_ids_list if str(x).strip()])
                                except Exception:
                                    raw_ids = None

                            # 2) Normalize to a list of ints
                            ids = []
                            if raw_ids:
                                s = str(raw_ids).strip()
                                if s.startswith("[") and s.endswith("]"):
                                    s = s[1:-1]
                                if "backup_ids[]=" in s:
                                    s = s.split("backup_ids[]=", 1)[1]
                                elif "backup_ids=" in s:
                                    s = s.split("backup_ids=", 1)[1]
                                for tok in s.replace(" ", "").split(","):
                                    if tok.isdigit():
                                        try:
                                            ids.append(int(tok))
                                        except Exception:
                                            pass

                            bname = (DbackupName or "").strip() if DbackupName else ""

                            if not ids and not bname:
                                res = -21
                                json_res = json.JSONEncoder().encode({
                                    "status": "fail",
                                    "message": "backup_ids or backup_name is required",
                                    "code": -21
                                })
                            else:
                                try:
                                    from Docker import DockerBackupDelete
                                    rc, payload = DockerBackupDelete(
                                        name=Dname,                   # may be None — now supported
                                        backup_ids=ids if ids else None,
                                        backup_name=bname if bname else None
                                    )
                                    if rc == 0:
                                        json_res = json.JSONEncoder().encode({
                                            "status": "success",
                                            "deleted": payload
                                        })
                                        res = 0
                                    elif rc == -21:
                                        res = -21
                                        json_res = json.JSONEncoder().encode({
                                            "status": "fail",
                                            "message": payload.get("message", "No matching backups found"),
                                            "code": -21
                                        })
                                    else:
                                        res = -22
                                        msg = payload.get("message") if isinstance(payload, dict) else "Backup delete failed"
                                        json_res = json.JSONEncoder().encode({
                                            "status": "fail",
                                            "message": msg,
                                            "code": -22
                                        })
                                except Exception as e:
                                    sprint(f"[BACKUP] delete exception: {e}", 0)
                                    res = -2
                                    json_res = json.JSONEncoder().encode({
                                        "status": "fail",
                                        "message": f"Exception: {e}",
                                        "code": -2
                                    })

                        elif Dcmd == "ListAttachedVolumes":
                            try:
                                from Docker import DockerListContainerVolumes
                                rc, payload = DockerListContainerVolumes(Dname)
                                if rc == 0:
                                    json_res = json.JSONEncoder().encode({"status": "success", "volumes": payload})
                                    res = 0
                                else:
                                    json_res = json.JSONEncoder().encode({"status": "fail", "message": payload.get("message","error")})
                                    res = -2
                            except Exception as e:
                                sprint(f"[VOLS] list exception: {e}", 0)
                                json_res = json.JSONEncoder().encode({"status":"fail","message":f"Exception: {e}"})
                                res = -2

                        # ---------------- AttachVolume ----------------
                        elif Dcmd == "AttachVolume":
                            try:
                                if not Dname:
                                    sprint("[AttachVolume] missing VM/container name", 20)
                                    json_res = json.JSONEncoder().encode({
                                        "status": "fail",
                                        "message": "Missing container name",
                                        "code": -21
                                    })
                                    res = -21
                                else:
                                    # Helper to pick the first non-empty value
                                    def _pick(*vals):
                                        for v in vals:
                                            if v is None:
                                                continue
                                            s = str(v).strip()
                                            if s != "":
                                                return v
                                        return None

                                    # Accept either volume_name or volume_id
                                    vol_sel = _pick(locals().get("Dvolume_name"),
                                                    locals().get("Dvolume_id"))
                                    if vol_sel is None:
                                        sprint("[AttachVolume] missing volume_name or volume_id", 20)
                                        json_res = json.JSONEncoder().encode({
                                            "status": "fail",
                                            "message": "Missing volume name or ID",
                                            "code": -21
                                        })
                                        res = -21
                                    else:
                                        target = _pick(locals().get("Dtarget"), None)
                                        mode   = str(_pick(locals().get("Dmode"), "rw")).lower()   # rw|ro
                                        mkdir  = str(_pick(locals().get("Dmkdir"), "0"))           # "0"|"1"

                                        # Normalize selector -> vol_id or vol_name
                                        vol_id = None
                                        vol_name = None
                                        try:
                                            if str(vol_sel).isdigit():
                                                vol_id = int(vol_sel)
                                            else:
                                                vol_name = str(vol_sel)
                                        except Exception:
                                            vol_name = str(vol_sel)

                                        # Backend call
                                        rc, detail = DockerAttachVolume(
                                            Dname,
                                            cmd="AttachVolume",
                                            cmd_id=Dcmd_Id,
                                            vol_id=vol_id,
                                            vol_name=vol_name,
                                            target=target,
                                            mode=mode,
                                            mkdir=mkdir,
                                        )
                                        if rc == 0:
                                            json_res = json.JSONEncoder().encode(detail)
                                            res = 0
                                        elif rc == -21:
                                            json_res = json.JSONEncoder().encode({
                                                "status": "fail",
                                                "message": detail.get("message") or "Invalid parameters",
                                                "code": -21
                                            })
                                            res = -21
                                        else:
                                            json_res = json.JSONEncoder().encode({
                                                "status": "fail",
                                                "message": detail.get("message") or "Attach failed",
                                                "code": -2
                                            })
                                            res = -2

                            except Exception as e:
                                sprint(f"[AttachVolume] Exception: {e}", 20)
                                json_res = json.JSONEncoder().encode({
                                    "status": "fail",
                                    "message": f"Exception: {e}",
                                    "code": -2
                                })
                                res = -2

                        # ---------------- DetachVolume ----------------
                        elif Dcmd == "DetachVolume":
                            try:
                                if not Dname:
                                    sprint("[DetachVolume] missing VM/container name", 20)
                                    json_res = json.JSONEncoder().encode({
                                        "status": "fail",
                                        "message": "Missing container name",
                                        "code": -21
                                    })
                                    res = -21
                                else:
                                    def _pick(*vals):
                                        for v in vals:
                                            if v is None:
                                                continue
                                            s = str(v).strip()
                                            if s != "":
                                                return v
                                        return None

                                    # Can target by container path, volume_name or volume_id
                                    tgt      = _pick(locals().get("Dtarget"))   # optional
                                    vol_sel  = _pick(locals().get("Dvolume_name"),
                                                     locals().get("Dvolume_id"))

                                    vol_id = None
                                    vol_name = None
                                    if vol_sel is not None:
                                        try:
                                            if str(vol_sel).isdigit():
                                                vol_id = int(vol_sel)
                                            else:
                                                vol_name = str(vol_sel)
                                        except Exception:
                                            vol_name = str(vol_sel)

                                    # Backend call
                                    rc, detail = DockerDetachVolume(
                                        Dname,
                                        cmd="DetachVolume",
                                        cmd_id=Dcmd_Id,
                                        vol_id=vol_id,
                                        vol_name=vol_name,
                                        target=tgt
                                    )
                                    if rc == 0:
                                        json_res = json.JSONEncoder().encode(detail)
                                        res = 0
                                    elif rc == -21:
                                        json_res = json.JSONEncoder().encode({
                                            "status": "fail",
                                            "message": detail.get("message") or "Volume not attached or invalid reference",
                                            "code": -21
                                        })
                                        res = -21
                                    else:
                                        json_res = json.JSONEncoder().encode({
                                            "status": "fail",
                                            "message": detail.get("message") or "Detach failed",
                                            "code": -2
                                        })
                                        res = -2

                            except Exception as e:
                                sprint(f"[DetachVolume] Exception: {e}", 20)
                                json_res = json.JSONEncoder().encode({
                                    "status": "fail",
                                    "message": f"Exception: {e}",
                                    "code": -2
                                })
                                res = -2

                        else:
                            sprint(f"[ERR] Unknown Docker command: {repr(Dcmd)}", 0)
                            res = -2

                    except Exception as e:
                        sprint("[EXC] Docker action raised exception: " + repr(e), 0)
                        sprint("[EXC] Traceback follows:", 0)
                        sprint(traceback.format_exc(), 0)
                        res = -2

                    # ---- DB sync on success ----
                    if res == 0:
                        if Dcmd == "Create":
                            _ = _insert_vm_row(Dname, Dcpu, Dmemory, Ddisk, Dimage, Dport, ssh_port=None)
                            try:
                                    # normalize the user’s selection
                                nets = _normalize_network_names(Dnetwork)  # returns list[str]
                                if not _replace_vm_network_links(Dname, nets):
                                    raise RuntimeError("DB link replace returned False")
                                sprint(f"[DBG] Linking VM→networks {Dname} -> {nets}", 0)
                            except Exception as e:
                                sprint(f"[WARN] vm↔network DB link failed for {Dname}: {e}", 0)
                        elif Dcmd == "Start":
                            _ = _update_vm_state(Dname, new_state=6, set_started_date=True)
                        elif Dcmd == "Stop":
                            _ = _update_vm_state(Dname, new_state=4)
                        elif Dcmd == "Pause":
                            _ = _update_vm_state(Dname, new_state=7)
                        elif Dcmd == "UnPause":
                            _ = _update_vm_state(Dname, new_state=6)
                        elif Dcmd == "Delete":
                            # NEW: interpret keep flags (treat None as "no" = delete)
                            kb = (str(DkeepBackups).strip().lower()
                                  if DkeepBackups is not None else "no")
                            ks = (str(DkeepSnapshots).strip().lower()
                                  if DkeepSnapshots is not None else "no")

                            vm_id = None
                            try:
                                from Docker import _db_vm_id
                                vm_id = _db_vm_id(Dname)
                            except Exception:
                                vm_id = None

                            # --- 1) Docker container + disk cleanup ---
                            try:
                                from Docker import DockerDelete
                                DockerDelete(
                                    Dname,
                                    "Delete",
                                    Dcmd_Id,
                                    keep_backups   = (kb in ("yes", "true", "1")),
                                    keep_snapshots = (ks in ("yes", "true", "1")),
                                )
                            except Exception as e:
                                sprint(f"[Delete] DockerDelete exception: {e}", 0)

                            # --- 2) Backups: delete OR DETACH (VMId -> NULL) ---
                            try:
                                from Docker import (
                                    _db_delete_backups_for_vm,
                                    _db_detach_backups_for_vm,
                                )

                                if kb in ("yes", "true", "1"):
                                    bcount = _db_detach_backups_for_vm(Dname, Dcmd_Id)
                                    sprint(f"[Delete] detached {bcount} backups for {Dname}", 0)
                                else:
                                    bcount = _db_delete_backups_for_vm(Dname, Dcmd_Id)
                                    sprint(f"[Delete] removed {bcount} backups for {Dname}", 0)
                            except Exception as e:
                                sprint(f"[Delete] backup cleanup warn: {e}", 0)

                            # --- 3) Snapshots: delete OR DETACH (vm_id -> NULL) ---
                            try:
                                from Docker import (
                                    _db_delete_snapshots_for_vm,
                                    _db_detach_snapshots_for_vm,
                                )
                                if ks in ("yes", "true", "1"):
                                    scount = _db_detach_snapshots_for_vm(Dname, Dcmd_Id)
                                    sprint(f"[Delete] detached {scount} snapshots for {Dname}", 0)
                                else:
                                    scount = _db_delete_snapshots_for_vm(Dname, Dcmd_Id)
                                    sprint(f"[Delete] removed {scount} snapshots for {Dname}", 0)
                            except Exception as e:
                                sprint(f"[Delete] snapshot cleanup warn: {e}", 0)

                            # --- 4) vm_storage cleanup ---
                            try:
                                from Docker import _db_clear_vm_storage_for_vm
                                _db_clear_vm_storage_for_vm(Dname, Dcmd_Id)
                                sprint(f"[Delete] cleared vm_storage rows for {Dname}", 0)
                            except Exception as e:
                                sprint(f"[Delete] vm_storage cleanup warn: {e}", 0)

                            # --- 5) Finally remove the VM row ---
                            try:
                                _ = _delete_vm_row(Dname)
                            except Exception as e:
                                sprint(f"[Delete] VM DB row delete warn: {e}", 0)
                        # NetworkCreate does not alter VM rows; nothing to sync here.

                    # ---- Build response ----
                    invalid_hint = ""
                    if Dcmd == "Create":
                        if Dimage and (' ' in Dimage or Dimage.endswith(':') or Dimage.count(':') > 1):
                            invalid_hint += " Hint: UI image had spaces; resolved to a Docker ref."
                        if isinstance(Dnetwork, str) and Dnetwork.startswith('['):
                            invalid_hint += " Hint: network looks like a stringified list; ensure it's a real list."

                    if res == 0:
                        if Dcmd == "Create":
                            json_res = json.JSONEncoder().encode({
                                "status": "success",
                                "message": "App has been configured",
                                "name": Dname
                            })
                        elif Dcmd == "Start":
                            json_res = json.JSONEncoder().encode({
                                "status": "success",
                                "description": "Virtual Machine is ON",
                                "state": "6"
                            })
                        elif Dcmd == "Stop":
                            json_res = json.JSONEncoder().encode({
                                "status": "success",
                                "description": "Virtual Machine is OFF",
                                "state": "4",
                                "sleepTime": 5
                            })
                        elif Dcmd == "Resize":
                            json_res = json.JSONEncoder().encode({
                                "status": "success",
                                "message": f"VM '{Dname}' updated successfully"
                            })
                        elif Dcmd == "Pause":
                            json_res = json.JSONEncoder().encode({
                                "status": "success",
                                "Description": "VirtualMachine is Paused",
                                "currentState": 7
                            })
                        elif Dcmd == "UnPause":
                            json_res = json.JSONEncoder().encode({
                                "status": "success",
                                "Description": "VirtualMachine is Reset to ON",
                                "currentState": 6
                            })
                        elif Dcmd == "Delete":
                            json_res = json.JSONEncoder().encode({
                                "status": "success",
                                "Description": "Virtual Machine deleted Successfully"
                            })
                            sprint("[UI] Delete success JSON", 0)
                            sprint(json_res, 0)
                        elif Dcmd in ("NetworkCreate", "NetCreate"):
                            json_res = json.JSONEncoder().encode({
                                "status": "success",
                                "message": f"Network '{Dname}' ensured",
                                "cidr": Dcidr,
                                "gateway": Dgateway
                            })
                        elif Dcmd in ("SnapshotCreate","SnapshotList","SnapshotDelete"):
                            json_res = json_res
                        elif Dcmd in ("BackupStart","BackupStatus","BackupLocal","BackupFull"):
                            json_res = json_res
                        else:
                            if json_res is None:
                                json_res = json.JSONEncoder().encode({
                                    "status": "success",
                                    "description": f"Docker Action OK Code: {res}"
                                })
                        sprint("command Passed", res)
                        CCM_Alert(ccmINFO, LogLevel,
                                  f"Docker command succesfull , Cmd/Volume Code={Dcmd}/{Dname}")

                    elif res == -2:
                        json_res = json.JSONEncoder().encode({
                            "status": "fail",
                            "message": f"Unknown or failed command '{Dcmd}'. Code: {res}.{invalid_hint}",
                            "code": res
                        })
                        sprint("command Failed unknown", res)
                        CCM_Alert(ccmINFO, LogLevel,
                                  f"Docker command Failed unknown, Cmd/Error Code={Dcmd}/{res}")

                    else:
                        # ---- Roll back bad network rows on failed NetworkCreate ----
                        if Dcmd in ("NetworkCreate", "NetCreate") and Dname and Dcidr:
                            try:
                                import sqlite3
                                conn = sqlite3.connect(DBPath)
                                cur = conn.cursor()
                                cur.execute(
                                    "DELETE FROM network WHERE TRIM(name)=? AND cidr=?",
                                    (Dname.strip(), Dcidr.strip())
                                )
                                conn.commit()
                                cur.close()
                                conn.close()
                                sprint(
                                    f"[NET][UI] rolled back DB row for network '{Dname}' ({Dcidr}) after rc={res}",
                                    0
                                )
                            except Exception as e:
                                sprint(
                                    f"[NET][UI] rollback delete failed for '{Dname}' ({Dcidr}): {e}",
                                    0
                                )

                        # ---- Existing error message logic ----
                        if Dcmd in ("NetworkCreate", "NetCreate") and Dcidr and _cidr_overlaps_host(Dcidr):
                            desc = f"NetworkCreate refused: subnet {Dcidr} overlaps host interfaces"
                        else:
                            desc = ERRTEXT.get(res, f"Docker Action Error Code: {res}")
                        json_res = json.JSONEncoder().encode({
                            "status": "fail",
                            "message": desc,
                            "code": res
                        })
                        sprint("command Failed", res)
                        CCM_Alert(ccmINFO, LogLevel,
                                  f"Docker command Failed, Cmd/Error Code={Dcmd}/{res}")
                    connection.sendall(json_res.encode())
################# VOLUME ###########################
                elif element=="volume":
                    PoolID=-1
                    LogLevel=20
                    zfsPool="null"
                    sprint ("volume msg",message_list)
                    for i in message_list[1:]:
                        cell_vals=i.split('=')
                        names=cell_vals[0]
                        if names=="element_name":
                            names="name"
                        else:
                            pass
                        values=str(cell_vals[1])
                        sprint ("values",values)
                        if names=="action":
                            VolAction=str(values)
                        elif names=="name":
                            VolName=str(values)
                        elif names=="SnapName":
                            SnapVolName=str(values)
                        elif names=='SnapPath':
                            SnapPath=str(values)
                        elif names=="PoolID":
                            PoolID=int(values)
                        elif names=="VolSize":
                            VolumeSize=int(values)
                        elif names=="PoolName":
                            zfsPool=str(values)
                        elif names=="Compression":
                            zfsCompression=str(values)
                        elif names=="Dedup":
                            zfsDedup=str(values)
                        elif names=="VolType":
                            VolType=str(values)
                        elif names=="prot":
                            ProtocolID=int(values)
                        elif names=="type":
                            type=str(values)
                        elif names=="thin":
                            thin=str(values)
                        elif names=="priority":
                            priority=str(values)

                        attribute_names.append(names)
                        attribute_values.append(values)
                    attribute_names.pop(1)
                    attribute_values.pop(1)
                    attribute_names=','.join(attribute_names)
                    attribute_values=','.join(attribute_values)
                    sprint ("attribute_names",attribute_names)
                    res=wErrUnknownCmd
                    # check is it a create command
                    # check is it a delete command
                    # check is it a edit conmand

                    if PoolID !=-1:
                        element ="pool"
                        zfsPool=DB_CheckElement(element, PoolID)
                        if zfsPool =="null":
                            sprint ("Pool wErrNameNotFound",PoolID)
                            res=wErrNameNotFound
                            VolAction="VolNull"
                        else:
                            sprint ("volume cmd, zfs pool=",zfsPool)
                    if LicenceState!=0:
                        VolAction="NoLicence"
                        res=-2
                    if (VolAction=="VolCreate"):
                        res=VolumeCreate(zfsPool,VolName,VolumeSize,zfsCompression, zfsDedup,VolType,type,priority)

                    elif (VolAction=="VolStart"):
                        SnapVolName="null"
                        res=VolumeStart(zfsPool,VolName, ProtocolID,SnapVolName)
                        
                    elif (VolAction=="VolStop"):
                        SnapVolName="null"
                        res=VolumeStop(zfsPool,VolName,ProtocolID,SnapVolName)
                        
                    elif (VolAction=="VolDelete"):
                        res= VolumeDelete(zfsPool,VolName,ProtocolID)

                    elif (VolAction=="VolUpdate"):
                        res=VolumeUpdate(zfsPool,VolName,VolumeSize,zfsCompression, zfsDedup,priority)
                    
                    elif (VolAction=="vDiskCreate"):
                       res=VdiskCreate(zfsPool,VolName,VolumeSize,zfsCompression, zfsDedup,priority)

                    elif (VolAction=="vDiskDelete"):
                        res=VdiskDelete(zfsPool,VolName)

                    elif (VolAction=="vDiskUpdate"):
                        res=VdiskUpdate(zfsPool,VolName,VolumeSize,zfsCompression, zfsDedup,priority)

                    elif (VolAction=="VolInfo"):
                        res=VolInfo(VolName,ProtocolID)
                        
                    elif (VolAction=="VolCreateSnap"):
                        res=SnapShotVolumeCreate(zfsPool,VolName, SnapVolName)
                        
                    elif (VolAction=="VolDeleteSnap"):
                        res=SnapShotVolumeDelete(zfsPool,VolName,SnapVolName)
                        
                    elif (VolAction=="VolStartSnap"):
                        res=VolumeStartSnap(zfsPool,VolName,ProtocolID,SnapVolName)
                        
                    elif (VolAction=="VolStopSnap"):
                        res=VolumeStopSnap(zfsPool,VolName,ProtocolID,SnapVolName)
                        
                    elif (VolAction=="VolCloneCreate"):
                        res=CloneVolumeCreate(zfsPool,VolName,SnapVolName,SnapPath)
                        
                    elif (VolAction=="VolNull"):
                        sprint ("VolNull",0)
                        
                    if res==-2:
                        json_res = json.JSONEncoder().encode({"status": "fail", "description": "No Licence Error Code: {}".format(res)})
                        sprint ("command Failed no Licence",res)
                        logMsg = "Volume" +" command Failed no Licence, Cmd/Error Code="+str(VolAction)+"/"+str(res)
                        CCM_Alert(ccmINFO,LogLevel,logMsg)

                    if res!=0:
                        json_res = json.JSONEncoder().encode({"status": "fail", "description": "Volume Action Error Code: {}".format(res)})
                        sprint ("command Failed",res)
                        logMsg = "Volume" +" command Failed, Cmd/Error Code="+str(VolAction)+"/"+str(res)
                        CCM_Alert(ccmINFO,LogLevel,logMsg)
                    else:
                        json_res = json.JSONEncoder().encode({"status": "success", "description": "Volume Action OK Code: {}".format(res)})
                        sprint ("command Passed",res)
                        logMsg = str("Volume") +" command succesfull , Cmd/Volume Code="+str(VolAction)+"/"+str(VolName)
                        CCM_Alert(ccmINFO,LogLevel,logMsg)
                    
                    connection.sendall(json_res.encode())
################### STOR_MAN ###################

                elif element=="StorMan":
                    StorCmd="StorNull"
                    StorName="null"
                    StorProt=0
                    HostID=0
                    HostName="null"
                    HostIQN="0.0.0.0"
                    StorManID=0
                    DeviceID=0
                    action="x"
                    share="null"
                    LogLevel=20
                    sprint("StorMan msg",message_list)
                    StorAction="StorNull"
                    for i in message_list[1:]:
                        cell_vals=i.split('=')
                        names=cell_vals[0]
                        if names=="element_name":
                            names="name"
                        else:
                            pass
                        values=str(cell_vals[1])
                        sprint (values,0)
                        if names=="cmd":
                            StorCmd=str(values)
                        elif names=="name":
                            StorName=str(values)
                        elif names=="prot":
                            StorProt=str(values)
                        elif names=="HostID":
                            HostID=int(values)
                        elif names=="HostName":
                            HostName=str(values)
                        elif names=="HostIQN":
                            HostIQN=str(values)
                        elif names=="StorManID":
                            StorManID=int(values)
                        elif names=="DeviceID":
                            DeviceID=int(values)
                        elif names=="action":
                            action=str(values)
                        elif names=="Share":
                            share=str(values)
                        attribute_names.append(names)
                        attribute_values.append(values)
                    attribute_names.pop(1)
                    attribute_values.pop(1)
                    attribute_names=','.join(attribute_names)
                    attribute_values=','.join(attribute_values)
                    sprint (attribute_names,0)
                    res=wErrUnknownCmd
#'create_Storage'x 
#'read_Storage'
#'OnOff_Device'
#'delete_Storage'x
#'ConnectDisconnectSM_Storage'xx
#'update_Storage'
# create, poll,device,connect,disconnect,delete
#message="set,element=StorMan,element_name={0},args=8,cmd={1},action={2},HostID={3},HostName={4},HostIQN={5},Share={6},prot={7},uuid={8}".\
                    try:
                        msg=StorName+str(StorManID)+str(HostID)+str(HostIQN)+str(StorProt)+str(action)+str(share)
                        if LicenceState!=0:
                            StorCmd="NoLicence"
                            res=-2

                        elif (StorCmd=="create"):
                            sprint ("StorMan create",msg)
                            res=StorManCreate(StorName,StorManID,HostID,StorProt)

                        elif (StorCmd=="discover"):
                            sprint ("StorMan discover",msg)
                            res=StorManDiscover(StorName,StorManID,HostID,HostIQN,StorProt,action,share)

                        elif (StorCmd=="device"):
                            sprint ("StorMan discover",msg)
                            res=DeviceConnect(DeviceID,action)

                        elif (StorCmd=="connect"):
                            sprint ("Storman connect",msg)
                            res=StorManConnect(StorName,StorManID,HostID,HostIQN,StorProt,action,share)

                        elif (StorCmd=="disconnect"):
                            sprint ("Storman dis-connect",msg)
                            res=StorManConnect(StorName,StorManID,HostID,HostIQN,StorProt,action,share)

                        elif (StorCmd=="delete"):
                            sprint ("Storman delete",msg)
                            res=StorManDelete(StorName,StorManID,HostID,StorProt)
      
                        elif (StorCmd=="StorNull"):
                            sprint ("Stor Null Action",msg)
                            res=-1

                        if res==-2:
                            json_res = json.JSONEncoder().encode({"status": "fail", "description": "No Licence Error Code: {}".format(res)})
                            sprint ("command Failed no Licence",res)
                            logMsg = str(element) +" command Failed no Licence, Cmd/Error Code="+str(StorCmd)+"/"+str(res)
                            CCM_Alert(ccmINFO,LogLevel,logMsg)
                            connection.sendall(json_res.encode())

                            
                        elif res!=0:
                            json_res = json.JSONEncoder().encode({"status": "fail", "description": "Storage Manager Error Code: {}".format(res)})
                            sprint ("Storman command Failed ",res)
                            logMsg = str(element) +" command Failed, Cmd/Error Code="+str(StorCmd)+"/"+str(res)
                            CCM_Alert(ccmINFO,LogLevel,logMsg)
                        else:
                            json_res = json.JSONEncoder().encode({"status": "success", "description": "Storage Manager OK Code: {}".format(res)})
                            logMsg = str(element) +" command succeded, command/name="+str(StorCmd)+"/"+str(StorName)
                            sprint ("Storman command Passed",res)
                        connection.sendall(json_res.encode())
                    except Exception as err:
                        sprint("StorMan except ",err)
                        res=-3
                        json_res = json.JSONEncoder().encode({"status": "fail", "description": "Storage Manager Error Code: {}".format(res)})
                        connection.sendall(json_res.encode())
                        
                elif element == "packageUpload":
                    sprint ("recieved packageUpload Request",message_list)
                    for i in message_list:
                        cell_vals=i.split('=')
                        names=cell_vals[0]
                        if names=="element_name":
                            names="name"
                        else:
                            pass
                        values=str(cell_vals[1])
                        sprint (values,0)
                        if names=="Action":
                            UploadAction=str(values)
                        elif names=="tempPath":
                            FolderUploadPath=str(values)
                        elif names == "version":
                            zipFileName = str(values)
                            version = zipFileName.split(".zip")[0]
                    sprint ("UploadAction",UploadAction)
                    message = ''
                    status = 'fail'

                    if UploadAction == "upload":
                        sprint ("UploadAction upload",0)
                        stat, mssg = unpackage.unpack(FolderUploadPath,zipFileName,version)
                        message = mssg
                        status = stat
                        message = message.capitalize()
                        response = {"status":status,"description":message.replace("<br>","",1)}
                        json_res = json.JSONEncoder().encode(response)
                        LogLevel=20
                        logMsg = "FW  Uploaded, status="+str(status)+" "+str(status)
                        CCM_Alert(ccmINFO,LogLevel,logMsg)
                        connection.sendall(json_res.encode())
                        sprint ("FW Upload Response Sent",response)
                        
                    elif UploadAction == "upload_iso":
                        sprint ("UploadAction upload iso",0)
                        stat, mssg = unpackage.unpack_iso(FolderUploadPath,zipFileName,version)
                        message = mssg
                        status = stat
                        message = message.capitalize()
                        response = {"status":status,"description":message.replace("<br>","",1)}
                        json_res = json.JSONEncoder().encode(response)
                        LogLevel=20
                        logMsg = "ISO Uploaded, status="+str(status)+" "+str(status)
                        CCM_Alert(ccmINFO,LogLevel,logMsg)
                        connection.sendall(json_res.encode())
                        sprint ("ISO Upload Response Sent",response)
                    elif UploadAction == "upload_ssl":
                        sprint ("UploadAction upload SSL",0)
                        stat, mssg = unpackage.unpack_sslCertificate(FolderUploadPath,zipFileName)
                        message = mssg
                        status = stat
                        message = message.capitalize()
                        response = {"status":status,"description":message.replace("<br>","",1)}
                        json_res = json.JSONEncoder().encode(response)
                        LogLevel=20
                        logMsg = "SSL Uploaded, status="+str(status)+" "+str(status)
                        CCM_Alert(ccmINFO,LogLevel,logMsg)
                        connection.sendall(json_res.encode())
                        sprint ("SSL Upload Response Sent",response)
                    elif UploadAction == "upload_sanuyi_package":
                        sprint ("UploadAction upload sanuyi package",0)
                        stat, mssg = unpackage.sanuyiUnpack(FolderUploadPath,zipFileName)
                        message = mssg
                        status = stat
                        message = message.capitalize()
                        response = {"status":status,"description":message.replace("<br>","",1)}
                        json_res = json.JSONEncoder().encode(response)
                        LogLevel=20
                        logMsg = "Sanuyi Package Uploaded, status="+str(status)+" "+str(status)
                        CCM_Alert(ccmINFO,LogLevel,logMsg)
                        connection.sendall(json_res.encode())

                elif element == "cbaServer":
                    sprint ("cbaServer Request Received",message_list)
                    for i in message_list:
                        cell_vals=i.split('=')
                        names=cell_vals[0]
                        if names=="element_name":
                            names="name"
                        else:
                            pass
                        values=str(cell_vals[1])
                        if names=="Action":
                            ServiceAction=str(values)
                        elif names=="enableCBA":
                            enableCBA = str(values)
                        elif names == "enableSSH":
                            enableSSH = str(values)
                        elif names == "cbaUpload":
                            cbaUpload = values
                        elif names == "cbaUpdate":
                            cbaUpdate = values
                        elif names == "cbaUploadType":
                            cbaUploadType = str(values)
                        elif names == "cbaUpdateType":
                            cbaUpdateType = str(values)
                        elif names == "reverseSSH":
                            reverseSSH = str(values)
                            
                    #print "ServiceAction",ServiceAction
                    if ServiceAction == "update_cba":
                        #res = updateCBA_SSH(enableCBA,enableSSH,cbaUpload,cbaUpdate,cbaUploadType,cbaUpdateType)
                        res = updateCBA(enableCBA,cbaUpload,cbaUpdate,cbaUploadType,cbaUpdateType)
                        if res==0:
                            LogLevel=20
                            logMsg = "CBA service updated"
                            CCM_Alert(ccmINFO,LogLevel,logMsg)
                            json_res = json.JSONEncoder().encode({"status": "success", "description": "Saved successfully"})
                            sprint ("update_cba command Passed",0)
                        else:
                            LogLevel=20
                            logMsg = "CBA service update failure, Error Code="+str(res)
                            CCM_Alert(ccmINFO,LogLevel,logMsg)
                            json_res = json.JSONEncoder().encode({"status": "fail", "description": "Fill All mandatory fields"})
                            sprint ("update_cba command Failed",res)
                        print (json_res.encode())
                        connection.sendall(json_res.encode())
                    elif ServiceAction == "update_ssh_reverse":
                        sprint ("update_reverse_ssh step1",0)
                        res = updateReverse_SSH(enableSSH, reverseSSH)
                        if res==0:
                            LogLevel=20
                            logMsg = "Reverse SSH service updated"
                            CCM_Alert(ccmINFO,LogLevel,logMsg)
                            json_res = json.JSONEncoder().encode({"status": "success", "description": "Saved successfully"})
                            sprint ("update_reverse_ssh command Passed",0)
                        else:
                            LogLevel=20
                            logMsg = "Reverse SSH service update failure, Error Code="+str(res)
                            CCM_Alert(ccmINFO,LogLevel,logMsg)
                            json_res = json.JSONEncoder().encode({"status": "fail", "description": "Fill All mandatory fields"})
                            sprint ("update_reverse_ssh command Failed",res)
                        print (json_res.encode())
                        connection.sendall(json_res.encode())
                        



################### TEST RESPONSE ######################
                elif element=="test_response":
                    sprint ("test_response Request Received",message_list)
                    user="none"
                    pw="none"
                    for i in message_list:
                        cell_vals=i.split('=')
                        names=cell_vals[0]
                        if names=="element_name":
                            names="name"
                        else:
                            pass
                        values=str(cell_vals[1])
                        if names=="action":
                            Action=str(values)
                        elif names=="name":
                            cmd=str(values)
                        elif names=="user":
                            user=str(values)
                        elif names=="pw":
                            pw=str(values)

                    if cmd=="License":
                        CheckLicence()
                        if LicenceState==0:
                            L_state="OK"
                            json_res = json.JSONEncoder().encode({"status": "success", "description": "CCM state: OK, License state: {}".format(L_state)})
                        else:
                            L_state="Not OK"
                            json_res = json.JSONEncoder().encode({"status": "fail", "description": "CCM state: OK, License state: {}".format(L_state)})
                    elif cmd=="CCM":
                            L_state="OK"
                            json_res = json.JSONEncoder().encode({"status": "success", "description": "CCM state: {}".format(L_state)})
                            
                    elif cmd=="UpdatePW":
                            L_state="OK"
                            updateLinuxPwd(user,pw)
                            json_res = json.JSONEncoder().encode({"status": "success", "description": "Password updated: {}".format(L_state)})
                    elif cmd=="CanisterStatus":
                    
                            if CanisterPresent[k]==True:
                                    res=CheckSerial("/mnt/system/quantumDB.db")
                                    sprint ("Canister CheckSerial res=",res)
                                    if res!=0:
                                        sprint ("Canister is Foreign =",res)
                                        canister_state="Foreign" 
                                    else:
                                        canister_state="Native" 
                                        sprint ("Canister is Native =",res)
                            else:
                                canister_state = "Checking"
                                sprint ("Canister is Checking =",0)
                                
                            json_res = json.JSONEncoder().encode({"status": "success", "description":"{0}".format(canister_state)})
                            
                    elif cmd == "Factory":
                        L_state = "OK"
                        vol_res = factory('volume')
                        pool_res =factory('pool')
                        res =factory('MegaRAID')
                        print("Factory Reset",res)
                        if res == 0:                            
                            json_res = json.JSONEncoder().encode({"status": "success", "description":"Factory Reset Action :{0}".format(res)})
                        else:
                           json_res = json.JSONEncoder().encode({"status":"fail","description":"Factory Reset Action code:{} ".format(res)}) 
                        #retVal=factory('MegaRAID')

                            
                    else:
                            json_res = json.JSONEncoder().encode({"status": "fail", "description": "Unknown command: {}".format(cmd)})
                            
                    msg= "CCM state: OK, License state: "+ L_state + "command="+cmd
                    sprint (msg,0)
                    connection.sendall(json_res.encode())
            else:
                sprint ("Data body starts with nulldb",0)
                args=loggerArgs("server"," ",20,"received")
                ccmLogger(2,"Data Body starts with null",server_args)

        except Exception as err:
            element="unknown"
            server_args=loggerArgs(log_elt,str(element),70,err)
            ccmLogger(2,err,server_args)
            sprint ("Server Exception Error",err)
        finally:
            time.sleep(.5)
            connection.close()

STtest=False
if STtest ==True:
    from timer_thread import *
    from ipmi_thread import ipmi_manager
    InitGlobals()
    InitSTlogger()
    try:
        sprint("[BOOT] Reconciling Docker networks from DB …", 0)
        _bootstrap_docker_networks_from_db()
    except Exception as e:
        import traceback
        sprint(f"[BOOT][EXC] Docker network reconcile: {e}", 0)
        sprint(traceback.format_exc(), 0)
    p = Process(target=time_manager)
    p.start()
    q = Process(target=ipmi_manager)
    q.start()
    time.sleep(1)
    server_manager(p,q)


#https://github.com/agrover/python-lvm/blob/master/example.py
