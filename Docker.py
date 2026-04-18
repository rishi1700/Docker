#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import os
import re
import json
import shutil
import subprocess
import docker
import ipaddress
import sqlite3
import logging
import traceback
import builtins
import time
import io
import hashlib
import tarfile
import tempfile
from typing import Optional, List, Dict, Set, Tuple, Any
from docker.types import Mount
from docker.errors import NotFound, APIError
from io import BytesIO
import threading

logger = logging.getLogger(__name__) if 'logger' not in globals() else logger

# --- Console/logger helper (safe if logRoutine not present) ---
try:
    from logRoutine import init_CONlogger as _init_CONlogger
except Exception:
    _init_CONlogger = None

DOCKER_ThreadDebug = 1
DOCKERCONhandler   = "CONDOCKER"
DOCKERCONLogger    = None

def DOCKERCONLoggerInit(arg: int = 0):
    global DOCKERCONLogger
    if DOCKERCONLogger is None and arg == 0 and _init_CONlogger:
        try:
            DOCKERCONLogger = _init_CONlogger(DOCKERCONhandler)
        except Exception:
            DOCKERCONLogger = None
    return DOCKERCONLogger

def sprint_docker(a, b=0):
    if DOCKER_ThreadDebug != 1:
        return
    msg = f"{a}" if b == 0 else f"{a},{b}"
    try:
        print(a if b == 0 else (a, b))
    except Exception:
        pass
    try:
        tup = DOCKERCONLoggerInit(1)
        if tup and tup[0]:
            tup[0].info(f"{DOCKERCONhandler}: {msg}")
    except Exception:
        pass

def InitDOCKER():
    DOCKERCONLoggerInit(0)

try:
    InitDOCKER()
except Exception:
    pass

# ------------ constants ------------
DB_PATH = "/mnt/data/quantumDB.db"
STATE_RUNNING = 6
STATE_STOPPED = 4
STATE_DELETED = 0
ALLOCATOR_BIN = "/home/sanuyi/san/storage_allocator.py"
CONTAINER_DATA_MOUNT = "/mnt/root"
# We compute the actual base dynamically from DockerRootDir's mountpoint at runtime.
# This constant is only the *relative* directory we will create under that mountpoint.
DEFAULT_ALLOCATOR_SUBDIR = "docker-storage"
BASE_STORAGE = None

# label keys (first one that exists wins) for EXPOSE order hints
EXPOSE_ORDER_LABEL_KEYS = [
    "com.app.expose-order",
    "org.opencontainers.image.expose-order",
    "com.quantum.expose-order",
]

# ------------ helpers ------------
try:
    import docker
    from docker.errors import APIError, NotFound
except Exception:
    docker = None
    APIError = Exception
    NotFound = Exception

# try to use sprint from st.py if present
try:
    from st import sprint as _st_sprint  # type: ignore
    def sprint(msg: str, lvl: int = 0) -> None:
        try:
            _st_sprint(msg, lvl)
        except Exception:
            print(msg)
except Exception:
    def sprint(msg: str, lvl: int = 0) -> None:
        print(msg)

def _parse_disk_gb(val) -> Optional[float]:
    """
    Accepts None, 'None', '', '0', '0.0', numbers/strings.
    Returns float GB if > 0, else None.
    """
    if val is None:
        return None
    s = str(val).strip().lower()
    if s in ("", "none", "null"):
        return None
    try:
        gb = float(s)
    except Exception:
        return None
    return gb if gb > 0 else None

def _normalize_networks(net_in):
    """
    Accepts: "netA" or ["netA","netB"] -> (primary, extras)
    """
    if not net_in:
        return (None, [])
    if isinstance(net_in, list):
        nets = [str(n).strip() for n in net_in if str(n).strip()]
        if not nets:
            return (None, [])
        return (nets[0], nets[1:])
    return (str(net_in).strip(), [])

# --- host + policy overlap checks ---

def _host_ipv4_networks():
    """Return a list of ipaddress.IPv4Network configured on the host (best-effort)."""
    nets = []
    try:
        r = subprocess.run(["ip", "-j", "-4", "addr"], capture_output=True, text=True, check=True)
        data = json.loads(r.stdout)
        for link in data:
            for addr in link.get("addr_info", []):
                if addr.get("family") == "inet":
                    ip_str = addr.get("local")
                    plen = addr.get("prefixlen")
                    if ip_str and plen is not None:
                        nets.append(ipaddress.ip_network(f"{ip_str}/{plen}", strict=False))
    except Exception:
        pass
    return nets

def _db_list_restricted_subnets():
    """
    Read restricted subnets from DB table 'restricted_subnets(cidr TEXT)'.
    Fallback to env DOCKER_RESTRICTED_SUBNETS='cidr1,cidr2,...'.
    """
    cidrs = []
    # DB first
    try:
        conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
        cur.execute("SELECT cidr FROM restricted_subnets")
        rows = cur.fetchall() or []
        for (cidr,) in rows:
            try:
                cidrs.append(ipaddress.ip_network(str(cidr).strip(), strict=False))
            except Exception:
                pass
        cur.close(); conn.close()
    except Exception:
        pass
    # Env fallback (comma-separated list)
    try:
        env_raw = os.environ.get("DOCKER_RESTRICTED_SUBNETS", "")
        if env_raw.strip():
            for tok in env_raw.split(","):
                tok = tok.strip()
                if not tok:
                    continue
                try:
                    cidrs.append(ipaddress.ip_network(tok, strict=False))
                except Exception:
                    pass
    except Exception:
        pass
    return cidrs

def _overlaps_any(net: ipaddress.IPv4Network, others):
    """True if net overlaps any network in 'others'."""
    try:
        for n in others:
            try:
                if net.overlaps(n):
                    return True
            except Exception:
                continue
    except Exception:
        pass
    return False

def _validate_cidr_policy(cidr_str: str) -> Tuple[bool, str]:
    """Validate a requested IPv4 CIDR against host + policy constraints.

    Returns (ok, reason). If ok is False, reason contains a short message
    describing why the CIDR is rejected (invalid, overlaps host, or
    overlaps restricted ranges from DB/env).
    """
    try:
        net = ipaddress.ip_network(str(cidr_str).strip(), strict=False)
    except Exception as e:
        return False, f"invalid CIDR '{cidr_str}': {e}"

    # Host interface networks (from `ip -j -4 addr`)
    host_nets = _host_ipv4_networks()
    # Policy-restricted networks (DB table + env DOCKER_RESTRICTED_SUBNETS)
    restricted = _db_list_restricted_subnets()

    if _overlaps_any(net, host_nets):
        return False, f"subnet {net} overlaps host interfaces"

    if _overlaps_any(net, restricted):
        return False, f"subnet {net} overlaps restricted ranges"

    return True, ""

def _emit(msg: str, lvl: int = 20) -> None:
    try:
        level = {10: logging.DEBUG, 20: logging.INFO, 30: logging.WARNING, 40: logging.ERROR}.get(lvl, logging.INFO)
        logger.log(level, msg)
    except Exception:
        pass
    try:
        sprint(msg, 0)
    except Exception:
        pass


def _fmt_ports_for_log(ns_ports):
    try:
        if not ns_ports:
            return "[]"
        flat = []
        for cport, binds in ns_ports.items():
            if not binds:
                flat.append(f"{cport}->(none)")
            else:
                for b in binds:
                    flat.append(f"{b.get('HostIp','0.0.0.0')}:{b.get('HostPort','?')}->{cport}")
        return "[" + ", ".join(flat) + "]"
    except Exception as e:
        return f"<ports-format-error:{e!r}>"

def _fmt_nets_for_log(nets):
    try:
        if not nets:
            return "[]"
        out = []
        for n, cfg in nets.items():
            ip = (cfg or {}).get("IPAddress") or "-"
            out.append(f"{n}({ip})")
        return "[" + ", ".join(out) + "]"
    except Exception as e:
        return f"<nets-format-error:{e!r}>"

def _snap(c):
    a = c.attrs or {}
    st = (a.get("State") or {})
    ns = (a.get("NetworkSettings") or {})
    return dict(
        status = st.get("Status"),
        running = st.get("Running"),
        pid = st.get("Pid"),
        exit_code = st.get("ExitCode"),
        error = st.get("Error"),
        ports = _fmt_ports_for_log(ns.get("Ports")),
        nets  = _fmt_nets_for_log(ns.get("Networks") or {}),
        image = (a.get("Config") or {}).get("Image"),
        name  = a.get("Name"),
    )

def _client():
    return docker.from_env()

def _parse_memory(mem):
    if mem is None: return None
    s = str(mem).strip().lower()
    try:
        if s.endswith("g"): return int(float(s[:-1]) * (1024**3))
        if s.endswith("m"): return int(float(s[:-1]) * (1024**2))
        if s.endswith("k"): return int(float(s[:-1]) * 1024)
        if "." in s:       return int(float(s) * (1024**3))  # bare float → GB
        v = int(s)         # bare int → GB
        return v * (1024**3)
    except Exception:
        return None

def _db_set_state(name, state):
    try:
        conn = sqlite3.connect(DB_PATH)
        cur  = conn.cursor()
        cur.execute("UPDATE virtualmachine SET state=? WHERE TRIM(name)=?", (int(state), name.strip()))
        conn.commit()
    except Exception as e:
        try: sprint_docker("_db_set_state warn:", str(e))
        except Exception: print(f"_db_set_state warn: {e}")
    finally:
        try: cur.close()
        except: pass
        try: conn.close()
        except: pass

def _db_sum_used_running():
    try:
        conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
        cur.execute("SELECT COALESCE(SUM(num_cores),0), COALESCE(SUM(memory_GB),0) FROM virtualmachine WHERE state=6")
        row = cur.fetchone() or (0, 0)
        cur.close(); conn.close()
        return float(row[0] or 0), float(row[1] or 0)
    except Exception as e:
        print(f"_db_sum_used_running: {e}")
        return 0.0, 0.0

def _db_vm_current(name):
    try:
        conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
        cur.execute("SELECT COALESCE(num_cores,0), COALESCE(memory_GB,0) FROM virtualmachine WHERE TRIM(name)=?", (name.strip(),))
        row = cur.fetchone() or (0, 0)
        cur.close(); conn.close()
        return float(row[0] or 0), float(row[1] or 0)
    except Exception as e:
        print(f"_db_vm_current: {e}")
        return 0.0, 0.0
    
def _active_storage_base() -> Optional[str]:
    """Where container disks live (e.g., /mnt/dockervol)."""
    try:
        base = _db_get_docker_storage_base_from_volume()
        return base if base and os.path.isdir(base) else None
    except Exception:
        return None

def _sum_reserved_diskimgs_bytes(base: str) -> int:
    """
    Reserved capacity = sum of logical sizes of every <vm>/disk.img under base.
    We use os.path.getsize (logical length) so sparse files count against quota.
    """
    total = 0
    for root, dirs, files in os.walk(base):
        if "disk.img" in files:
            p = os.path.join(root, "disk.img")
            try:
                total += os.path.getsize(p)
            except Exception:
                pass
    return total

def _refresh_system_used():
    import sqlite3, shutil, os
    try:
        conn = sqlite3.connect(DB_PATH); cur = conn.cursor()

        # used CPU / MEM from RUNNING (state=6)
        cur.execute("SELECT COALESCE(SUM(num_cores),0) FROM virtualmachine WHERE state=6")
        used_vcpu = int(cur.fetchone()[0] or 0)

        cur.execute("SELECT COALESCE(SUM(memory_GB),0.0) FROM virtualmachine WHERE state=6")
        try:
            used_mem = float(cur.fetchone()[0] or 0.0)
        except Exception:
            used_mem = 0.0

        # total storage from mounted base
        total_storage_gb = 0.0
        try:
            base = _storage_base_for_cleanup() or _db_get_docker_storage_base_from_volume()
        except Exception:
            base = None
        if base and os.path.isdir(base):
            total_b, _u, _f = shutil.disk_usage(base)
            total_storage_gb = round(total_b / (1024**3), 2)

        # used storage: sum of vm_disk_size for RUNNING VMs only
        cur.execute("SELECT COALESCE(SUM(vm_disk_size),0.0) FROM virtualmachine WHERE state=6")
        try:
            used_storage_gb = float(cur.fetchone()[0] or 0.0)
        except Exception:
            used_storage_gb = 0.0

        # ---- safety clamps to avoid negative UI "Available" ----
        if total_storage_gb < 0:
            total_storage_gb = 0.0
        if used_storage_gb < 0:
            used_storage_gb = 0.0
        if used_storage_gb > total_storage_gb:
            # clamp to total to prevent negative available due to rounding/unit drift
            used_storage_gb = total_storage_gb

        cur.execute(
            "UPDATE system SET used_vcpu=?, used_memoryGB=?, total_storageGB=?, used_storageGB=?",
            (used_vcpu, used_mem, total_storage_gb, used_storage_gb)
        )
        conn.commit()
    except Exception as e:
        print(f"_refresh_system_used warning: {e}")
    finally:
        try: cur.close()
        except: pass
        try: conn.close()
        except: pass

# ========== Port selection that honors EXPOSE order via label ==========
def _parse_expose_order_label(labels):
    if not labels: return []
    raw = None
    for k in EXPOSE_ORDER_LABEL_KEYS:
        v = labels.get(k)
        if v:
            raw = v
            break
    if not raw: return []
    items = []
    for tok in str(raw).replace(",", " ").split():
        tok = tok.strip()
        if not tok: continue
        if "/" not in tok:
            tok = f"{tok}/tcp"
        items.append(tok.lower())
    return items

def _select_container_port_from_image(img):
    attrs   = getattr(img, "attrs", {}) or {}
    cfg     = attrs.get("Config") or {}
    labels  = cfg.get("Labels") or {}
    exposed = cfg.get("ExposedPorts") or {}
    exposed_tcp = set()
    for key in (exposed.keys() if exposed else []):
        try:
            p, proto = key.split("/", 1)
            if proto.lower() == "tcp":
                exposed_tcp.add(f"{int(p)}/tcp")
        except Exception:
            continue
    if not exposed_tcp:
        return None
    preferred_order = _parse_expose_order_label(labels)
    for k in preferred_order:
        if k in exposed_tcp:
            return k
    def port_int(k): return int(k.split("/", 1)[0])
    return sorted(exposed_tcp, key=port_int)[0]

def _build_port_bindings_for_single_host_port(image_obj, host_port):
    if host_port in (None, "", "None"):
        return None
    try:
        hp = int(str(host_port))
    except Exception:
        return None
    container_key = _select_container_port_from_image(image_obj)
    if not container_key:
        container_key = f"{hp}/tcp"
    return {container_key: hp}

def _is_kdenlive_image_name(image_name) -> bool:
    try:
        return "kdenlive" in str(image_name).lower()
    except Exception:
        return False

def _force_single_host_port_binding(port_map, target_container_port):
    """
    Rewrite a single published host port to a specific container port.
    If multiple published ports exist, leave the mapping unchanged.
    """
    if not port_map:
        return port_map
    if target_container_port in port_map:
        return port_map

    published = []
    for ckey, host_binding in (port_map or {}).items():
        if host_binding not in (None, "", [], {}):
            published.append((ckey, host_binding))

    if len(published) != 1:
        return port_map

    _old_key, host_binding = published[0]
    return {target_container_port: host_binding}

def _gather_existing_binds(info_attrs):
    vols = {}
    for m in info_attrs.get("Mounts", []) or []:
        if m.get("Type") == "bind":
            src = m.get("Source"); dst = m.get("Destination")
            if src and dst:
                vols[src] = {"bind": dst, "mode": "rw" if m.get("RW", True) else "ro"}
    return vols

def _extract_ports(info_attrs):
    bindings = {}
    ports_obj = (info_attrs.get("NetworkSettings") or {}).get("Ports") or {}
    for container_port, host_list in ports_obj.items():
        if host_list:
            hp = host_list[0].get("HostPort")
            if hp and hp.isdigit():
                bindings[container_port] = int(hp)
            else:
                bindings[container_port] = host_list
        else:
            bindings[container_port] = None
    return bindings

def _host_config_limits(info_attrs):
    hc = info_attrs.get("HostConfig") or {}
    mem = hc.get("Memory") or None
    nano = hc.get("NanoCpus") or None
    out = {}
    if mem and int(mem) > 0:
        out["mem_limit"] = int(mem)
    if nano and int(nano) > 0:
        out["nano_cpus"] = int(nano)
    return out

def _set_nano_cpus_cli(name, cpus_value):
    try:
        r = subprocess.run(
            ["docker", "update", "--cpus", str(cpus_value), name],
            check=False, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
        )
        print(f"DockerResize: docker update --cpus {cpus_value} rc={r.returncode}")
        if r.stdout: print(f"DockerResize: stdout: {r.stdout.strip()}")
        if r.stderr: print(f"DockerResize: stderr: {r.stderr.strip()}")
        if r.returncode != 0:
            return False
        cli = _client()
        c = cli.containers.get(name)
        c.reload()
        desired = int(float(cpus_value) * 1_000_000_000)
        actual = int(c.attrs.get("HostConfig", {}).get("NanoCpus") or 0)
        print(f"DockerResize: verify NanoCpus actual={actual} desired={desired}")
        return actual == desired
    except Exception as e:
        print(f"DockerResize: _set_nano_cpus_cli exception: {e}")
        return False

# ------------ storage allocator integration ------------
def _allocate_persistent_path(vm_name, size_gb):
    try:
        if size_gb is None or str(size_gb).strip() == "":
            print("allocator: disk size empty; skipping")
            return None

        size_str = str(size_gb).strip()
        try:
            size_num = float(size_str[:-1]) if size_str.lower().endswith(("g","m","k")) else float(size_str)
        except Exception:
            size_num = float(size_str)

        # --- get base from DB (testvolume rule) ---
        base = _db_get_docker_storage_base_from_volume()
        if not base:
            print("allocator: NO_STORAGE_BASE_FOUND (unable to resolve allocator base)")
            return None

        # extra safety: ensure base lives on some mounted filesystem.
        # NOTE: base is typically a normal directory (e.g. /mnt/xdata/docker-storage)
        # and NOT a mountpoint itself. So we use `findmnt -T <path>`.
        r = subprocess.run(["findmnt", "-T", base, "-no", "TARGET"], text=True, capture_output=True)
        mp = (r.stdout or "").strip()
        if r.returncode != 0 or not mp:
            print(f"allocator: base not on a mounted filesystem -> {base}")
            return None

        cmd = [
            "python3", ALLOCATOR_BIN,
            "--vm-name", vm_name,
            "--size-gb", str(size_num),
            "--strategy", "loopback",
            "--base", base,
            "--db", DB_PATH,
            "--owner", "0:0",
            "--mode", "755",
        ]
        print(f"allocator: running: {' '.join(cmd)}")
        r = subprocess.run(cmd, text=True, capture_output=True)
        print(f"allocator: rc={r.returncode}")
        if r.stdout: print(f"allocator: stdout: {r.stdout.strip()}")
        if r.stderr: print(f"allocator: stderr: {r.stderr.strip()}")

        if r.returncode != 0:
            return None

        out = (r.stdout or "").strip()
        try:
            obj = json.loads(out)
            host_path = obj.get("mount_path") or obj.get("host_path")
            if host_path and os.path.isdir(host_path):
                # The allocator returns a mount path (e.g. <base>/<vm>/mnt). Validate it's mounted.
                rr = subprocess.run(["findmnt", "-T", host_path, "-no", "TARGET"], text=True, capture_output=True)
                mp = (rr.stdout or "").strip()
                if rr.returncode == 0 and mp and os.path.ismount(host_path):
                    print(f"allocator: mount OK -> {host_path}")
                    return host_path
            print(f"allocator: mount not ready -> {host_path}")
        except Exception as e:
            print(f"allocator: JSON parse failed: {e}; raw: {out}")
        return None
    except Exception as e:
        print(f"allocator exception: {e}")
        return None

def _is_mounted(path: str) -> bool:
    try:
        r = subprocess.run(["findmnt", "-no", "TARGET", path], text=True, capture_output=True)
        return r.returncode == 0 and (r.stdout or "").strip() == path
    except Exception:
        return False

def _db_get_docker_storage_base_from_volume():
    """Resolve the allocator storage base directory.

    Current behavior (dynamic, no DB volume dependency):
      - Ask Docker for DockerRootDir (works with symlinks and --data-root)
      - Find the filesystem mountpoint containing DockerRootDir
      - Use <mountpoint>/docker-storage as the base (created if missing)

    This intentionally keeps our storage OUTSIDE DockerRootDir while still
    following the same underlying disk as Docker.

    Future: a DB-driven NFS/Docker volume selection template is kept below
    (commented out) if we ever need to re-enable it.
    """
    try:

        # ------------------------------------------------------------------
        # 1) PRIMARY: dynamic system storage base (follows Docker's filesystem)
        # ------------------------------------------------------------------
        # Goal: place our allocator storage on the same underlying filesystem
        # that Docker uses, but NOT inside DockerRootDir.
        # Example:
        #   DockerRootDir=/mnt/xdata/docker  -> mountpoint=/mnt/xdata
        #   base=/mnt/xdata/docker-storage
        def _pick_if_usable(path: str) -> Optional[str]:
            """Return path if it is a usable directory on a mounted filesystem."""
            path = (path or "").strip()
            if not path:
                return None
            try:
                os.makedirs(path, exist_ok=True)
            except Exception:
                return None
            try:
                if not os.path.isdir(path):
                    return None
            except Exception:
                return None
            # Ensure the path resolves to some mounted target (e.g., "/" or "/mnt/xdata")
            try:
                r = subprocess.run(["findmnt", "-T", path, "-no", "TARGET"], text=True, capture_output=True)
                if r.returncode == 0 and (r.stdout or "").strip():
                    return path
            except Exception:
                pass
            return None

        # 1a) Ask Docker for its root dir (supports symlinks and --data-root)
        docker_root = None
        try:
            rr = subprocess.run(
                ["docker", "info", "--format", "{{.DockerRootDir}}"],
                text=True, capture_output=True
            )
            if rr.returncode == 0:
                docker_root = (rr.stdout or "").strip()
        except Exception:
            docker_root = None

        # 1b) Resolve mountpoint of DockerRootDir (filesystem target)
        mountpoint = None
        if docker_root:
            try:
                rm = subprocess.run(
                    ["findmnt", "-T", docker_root, "-no", "TARGET"],
                    text=True, capture_output=True
                )
                if rm.returncode == 0:
                    mountpoint = (rm.stdout or "").strip()
            except Exception:
                mountpoint = None

        # 1c) Build our base under that mountpoint
        if mountpoint:
            base = os.path.join(mountpoint.rstrip("/"), DEFAULT_ALLOCATOR_SUBDIR)
            base = _pick_if_usable(base)
            if base:
                return base

        # 1d) Fallback: use root filesystem mountpoint ("/")
        base = _pick_if_usable(os.path.join("/", DEFAULT_ALLOCATOR_SUBDIR))
        if base:
            return base

        # 1e) Optional legacy variable (if set elsewhere)
        base = _pick_if_usable(BASE_STORAGE)
        if base:
            return base

        print("[STORAGE] No suitable storage base found (docker info/findmnt unavailable)")
        return None

    except Exception as e:
        print(f"[STORAGE] base resolution failed: {e}")
        return None

    # ------------------------------------------------------------------
    # FUTURE TEMPLATE: DB-driven volume selection (disabled for now)
    # ------------------------------------------------------------------
    # If you ever need to allocate container storage on a specific Volume of
    # type NFS/Docker again, re-enable a DB lookup here behind a feature flag.
    # Keep the dynamic DockerRootDir mountpoint approach as the default.

def _storage_base_for_cleanup():
    """Return the active allocator base used for cleanup.

    This uses the same dynamic resolution as allocation (DockerRootDir mountpoint
    + DEFAULT_ALLOCATOR_SUBDIR).
    """
    try:
        base = _db_get_docker_storage_base_from_volume()
        if base and os.path.isdir(base):
            return base
    except Exception as e:
        print(f"[CLEANUP] storage base lookup warn (dynamic): {e}")
    return None

def _log_cleanup(msg, lvl=20):
    # mirror your existing logging style
    try: logger.log({10:logging.DEBUG,20:logging.INFO,30:logging.WARNING,40:logging.ERROR}.get(lvl, logging.INFO), msg)
    except: pass
    try: sprint(msg, 0)
    except: pass
    try: sprint_docker(msg, 0)
    except: pass

def release_container_disk(vm_name: str, keep_snapshots: bool = False) -> bool:
    """
    Cleanup per-container disk image, loop device, and mountpoint.

    Layout assumed from allocator:
      <BASE>/<vm_name>/
        ├─ disk.img
        ├─ mnt/          (mountpoint)
        └─ snapshots/    (optional snapshot images)

    If keep_snapshots=True, we will NOT delete the vm_root directory,
    so that <BASE>/<vm_name>/snapshots/ stays on disk.
    """
    try:
        base_root = _storage_base_for_cleanup()
        if not base_root:
            _log_cleanup(f"[CLEANUP] no storage base found; skip vm={vm_name}", 30)
            return False

        vm_root   = os.path.join(base_root, vm_name)
        img_path  = os.path.join(vm_root, "disk.img")
        mnt_path  = os.path.join(vm_root, "mnt")

        _log_cleanup(f"[CLEANUP] begin vm={vm_name} base={base_root}")
        _log_cleanup(f"[CLEANUP] paths: img={img_path} mnt={mnt_path}")

        # 1) Unmount (best effort; try a few strategies)
        if os.path.ismount(mnt_path):
            for args in (["umount", mnt_path],
                         ["umount", "-l", mnt_path],
                         ["umount", "-f", mnt_path]):
                r = subprocess.run(args, text=True, capture_output=True)
                _log_cleanup(
                    f"[CLEANUP] umount {' '.join(args[1:])} rc={r.returncode} "
                    f"out={r.stdout.strip()} err={r.stderr.strip()}"
                )
                if not os.path.ismount(mnt_path):
                    break

        # 2) Detach loop device that backs this disk.img
        try:
            out = subprocess.check_output(["losetup", "-a"], text=True)
            for line in out.splitlines():
                if f"({img_path})" not in line:
                    continue
                loopdev = line.split(":", 1)[0].strip()
                rr = subprocess.run(
                    ["losetup", "-d", loopdev],
                    text=True,
                    capture_output=True
                )
                _log_cleanup(
                    f"[CLEANUP] losetup -d {loopdev} rc={rr.returncode} "
                    f"out={rr.stdout.strip()} err={rr.stderr.strip()}"
                )
        except subprocess.CalledProcessError as e:
            _log_cleanup(f"[CLEANUP] losetup -a error: {e}", 30)
        except Exception as e:
            _log_cleanup(f"[CLEANUP] losetup scan warn: {e}", 30)

        # 3) Remove disk image
        if os.path.exists(img_path):
            try:
                os.remove(img_path)
                _log_cleanup(f"[CLEANUP] removed {img_path}")
            except Exception as e:
                _log_cleanup(f"[CLEANUP] remove {img_path} warn: {e}", 30)

        # 4) Remove mount dir
        try:
            if os.path.isdir(mnt_path):
                shutil.rmtree(mnt_path, ignore_errors=True)
                _log_cleanup(f"[CLEANUP] rmtree {mnt_path}")
        except Exception as e:
            _log_cleanup(f"[CLEANUP] rmtree warn (mnt): {e}", 30)

        # 5) VM root: only remove if NOT keeping snapshots
        try:
            if os.path.isdir(vm_root):
                if keep_snapshots:
                    _log_cleanup(
                        f"[CLEANUP] preserving vm_root {vm_root} (keep_snapshots=True)",
                        20
                    )
                else:
                    shutil.rmtree(vm_root, ignore_errors=True)
                    _log_cleanup(f"[CLEANUP] rmtree {vm_root}")
        except Exception as e:
            _log_cleanup(f"[CLEANUP] rmtree warn (vm_root): {e}", 30)

        _log_cleanup(f"[CLEANUP] done vm={vm_name}")
        return True
    except Exception as e:
        _log_cleanup(f"[CLEANUP] FAILED vm={vm_name}: {e}", 40)
        return False


def _db_update_vm_targets(vm_name: str, vcpu: Optional[float]=None, mem_gb: Optional[float]=None):
    try:
        sets, vals = [], []
        if vcpu is not None:
            sets.append("num_cores = ?");   vals.append(float(vcpu))
        if mem_gb is not None:
            sets.append("memory_GB = ?");   vals.append(float(mem_gb))
        if not sets:
            return True
        vals.append(vm_name.strip())
        conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
        cur.execute(f"UPDATE virtualmachine SET {', '.join(sets)} WHERE TRIM(name)=?", vals)
        conn.commit(); cur.close(); conn.close()
        return True
    except Exception as e:
        print(f"[DB] _db_update_vm_targets err: {e}")
        return False
    
# --- DB helpers to persist VM↔Network links (veth_port / vm_network) ---

def _db_q_one(query, args=()):
    try:
        conn = sqlite3.connect(DB_PATH); c = conn.cursor()
        c.execute(query, args)
        row = c.fetchone()
        c.close(); conn.close()
        return row
    except Exception as e:
        print(f"[DB] _db_q_one err: {e} :: {query} :: {args}")
        return None

def _db_q_all(query, args=()):
    try:
        conn = sqlite3.connect(DB_PATH); c = conn.cursor()
        c.execute(query, args)
        rows = c.fetchall()
        c.close(); conn.close()
        return rows or []
    except Exception as e:
        print(f"[DB] _db_q_all err: {e} :: {query} :: {args}")
        return []

def _db_exec(query, args=()):
    try:
        conn = sqlite3.connect(DB_PATH); c = conn.cursor()
        c.execute(query, args)
        conn.commit()
        last_id = c.lastrowid
        c.close(); conn.close()
        return last_id
    except Exception as e:
        print(f"[DB] _db_exec err: {e} :: {query} :: {args}")
        return None

def _vm_id_by_name(vm_name: str):
    row = _db_q_one("SELECT id FROM virtualmachine WHERE TRIM(name)=?", (vm_name.strip(),))
    return row[0] if row else None

def _network_ids_by_names(names):
    if not names:
        return {}
    placeholders = ",".join("?" for _ in names)
    rows = _db_q_all(f"SELECT id,name FROM network WHERE name IN ({placeholders})", tuple(names))
    return {name: nid for (nid, name) in rows}


def _ensure_veth(network_id: int, veth_name: str):
    # idempotent by (name, network_id)
    row = _db_q_one("SELECT id FROM veth_port WHERE name=? AND network_id=?", (veth_name, network_id))
    if row:
        return row[0]
    return _db_exec(
        "INSERT INTO veth_port(name,state,cr_date,edit_date,ip,netmask,network_id) "
        "VALUES(?, 1, datetime('now'), datetime('now'), NULL, NULL, ?)",
        (veth_name, network_id)
    )

def _ensure_vm_veth_link(vm_id: int, veth_id: int):
    row = _db_q_one("SELECT id FROM vm_network WHERE vm_id=? AND veth_id=?", (vm_id, veth_id))
    if row:
        return row[0]
    return _db_exec("INSERT INTO vm_network(vm_id, veth_id) VALUES(?,?)", (vm_id, veth_id))

def _ensure_vm_network_links(vm_name: str, network_names: list) -> bool:
    """
    Ensure DB rows exist to link a VM to one or more docker networks.

    - Dedupes network_names while preserving order
    - Reuses existing veth_port / vm_network rows (no duplicates)
    - Creates veth_port names like "<vm>-eth0", "<vm>-eth1", ...; if a name
      already exists for a different network, it appends "-1", "-2", ... to keep unique.
    """
    try:
        conn = sqlite3.connect(DB_PATH)
        cur  = conn.cursor()

        # --- resolve vm.id ---
        row = cur.execute("SELECT id FROM virtualmachine WHERE TRIM(name)=?", (vm_name.strip(),)).fetchone()
        if not row:
            sprint(f"[DB] WARN: VM '{vm_name}' not found; cannot persist network links", 0)
            cur.close(); conn.close()
            return False
        vm_id = row[0]

        # --- normalize incoming names (list-like, dedupe, strip empties) ---
        norm_names = []
        seen = set()
        for n in (network_names or []):
            s = str(n).strip()
            if not s: 
                continue
            if s in seen:
                continue
            seen.add(s)
            norm_names.append(s)

        if not norm_names:
            sprint(f"[DB] INFO: no network names provided for VM '{vm_name}'", 0)
            cur.close(); conn.close()
            return True  # nothing to do is still "ok"

        # --- map network names -> ids that exist in DB ---
        placeholders = ",".join("?" for _ in norm_names)
        rows = cur.execute(f"SELECT id,name FROM network WHERE name IN ({placeholders})", tuple(norm_names)).fetchall()
        name_to_id = {name: nid for (nid, name) in rows}

        # warn about missing networks
        for n in norm_names:
            if n not in name_to_id:
                sprint(f"[DB] WARN: network '{n}' not present in DB; skipping", 0)

        # --- process (in order) ---
        for idx, net_name in enumerate(norm_names):
            net_id = name_to_id.get(net_name)
            if not net_id:
                continue

            # already linked? (any veth_port for this vm to this network)
            already = cur.execute("""
                SELECT vmn.id
                FROM vm_network vmn
                JOIN veth_port vp ON vp.id = vmn.veth_id
                WHERE vmn.vm_id=? AND vp.network_id=?
            """, (vm_id, net_id)).fetchone()
            if already:
                sprint(f"[DBG] VM '{vm_name}' already linked to '{net_name}' — skip", 0)
                continue

            # ensure a veth_port row for this VM & network
            # try "<vm>-eth{idx}" then "<vm>-eth{idx}-1", "-2", ...
            base_veth = f"{vm_name}-eth{idx}"
            veth_name = base_veth
            attempt   = 0
            veth_id   = None

            while True:
                vp = cur.execute("SELECT id, network_id FROM veth_port WHERE name=?", (veth_name,)).fetchone()
                if not vp:
                    # name not taken -> create for this network
                    cur.execute("""
                        INSERT INTO veth_port(name, state, cr_date, edit_date, ip, netmask, network_id)
                        VALUES(?, 1, datetime('now'), datetime('now'), NULL, NULL, ?)
                    """, (veth_name, net_id))
                    veth_id = cur.lastrowid
                    break

                # name exists
                existing_id, existing_net_id = vp
                if int(existing_net_id) == int(net_id):
                    # perfect match; reuse this veth_port
                    veth_id = existing_id
                    break

                # same name but different network -> try a new suffix
                attempt += 1
                veth_name = f"{base_veth}-{attempt}"

            # ensure vm_network link
            link = cur.execute("SELECT id FROM vm_network WHERE vm_id=? AND veth_id=?", (vm_id, veth_id)).fetchone()
            if not link:
                cur.execute("INSERT INTO vm_network(vm_id, veth_id) VALUES(?,?)", (vm_id, veth_id))
                sprint(f"[DBG] Linked VM '{vm_name}' -> network '{net_name}' via veth '{veth_name}'", 0)
            else:
                sprint(f"[DBG] Link exists VM '{vm_name}' -> veth_id {veth_id}", 0)

        conn.commit()
        cur.close(); conn.close()
        return True

    except Exception as e:
        try:
            cur.close(); conn.close()
        except Exception:
            pass
        sprint(f"[ERR] _ensure_vm_network_links exception: {e}", 0)
        return False

def _db_clear_vm_storage_for_vm(vm_name: str, cmd_id: str = ""):
    try:
        conn = sqlite3.connect(DB_PATH)
        cur = conn.cursor()
        cur.execute("SELECT id FROM virtualmachine WHERE TRIM(name)=?", (vm_name,))
        row = cur.fetchone()
        if not row:
            return
        vm_id = int(row[0])
        cur.execute("DELETE FROM vm_storage WHERE vm_id=?", (vm_id,))
        conn.commit()
        cur.close()
        conn.close()
        sprint(f"[VM-STORAGE][{cmd_id}] cleared vm_storage for {vm_name} (vm_id={vm_id})", 0)
    except Exception as e:
        sprint(f"[VM-STORAGE][{cmd_id}] warn: {e}", 0)
        
def _desired_networks_for_vm(vm_name: str):
    """
    Read desired docker network names for a VM from DB:
      virtualmachine -> vm_network -> veth_port -> network.name
    Returns a de-duplicated, ordered list of names.
    """
    try:
        conn = sqlite3.connect(DB_PATH); c = conn.cursor()
        rows = c.execute("""
            SELECT n.name
            FROM virtualmachine vm
            JOIN vm_network vn ON vn.vm_id = vm.id
            JOIN veth_port vp ON vp.id = vn.veth_id
            JOIN network n ON n.id = vp.network_id
            WHERE TRIM(vm.name)=?
        """, (vm_name.strip(),)).fetchall()
        c.close(); conn.close()
        seen, out = set(), []
        for r in rows:
            if not r or not r[0]:
                continue
            n = str(r[0]).strip()
            if n and n not in seen:
                out.append(n); seen.add(n)
        return out
    except Exception as e:
        print(f"[DB] _desired_networks_for_vm error: {e}")
        try: c.close(); conn.close()
        except Exception: pass
        return []

def _grow_container_disk(vm_name: str, new_size_gb: float) -> bool:
    """
    Grow the VM's loopback image and ext4 filesystem to at least new_size_gb.
    Layout:
      <BASE>/<vm_name>/
        ├─ disk.img   (ext4 inside)
        └─ mnt/       (mountpoint)
    Returns True on success, False otherwise.
    """
    import os, subprocess, shutil, time

    def _run(cmd, check=True):
        return subprocess.run(cmd, text=True, capture_output=True, check=check)

    try:
        base = _active_storage_base() or _db_get_docker_storage_base_from_volume() or _storage_base_for_cleanup()
        if not base or not os.path.isdir(base):
            print("[GROW] no storage base; abort")
            return False

        vm_root = os.path.join(base, vm_name)
        img     = os.path.join(vm_root, "disk.img")
        mnt     = os.path.join(vm_root, "mnt")

        if not os.path.isfile(img):
            print(f"[GROW] missing image: {img}")
            return False

        # sizes
        try:
            tgt_bytes = int(float(new_size_gb) * (1024**3))
        except Exception:
            print("[GROW] invalid target size")
            return False
        cur_bytes = os.path.getsize(img)
        if tgt_bytes <= cur_bytes + 4096:
            print(f"[GROW] current={cur_bytes} >= requested={tgt_bytes}; nothing to do")
            return True

        # Which loop device backs this image?
        loopdev = None
        try:
            q = subprocess.check_output(["losetup", "-j", img], text=True)
            for line in (q or "").splitlines():
                if ":" in line and "(" in line and img in line:
                    loopdev = line.split(":", 1)[0].strip()
                    break
        except Exception:
            pass

        # Stop container if running (so mount is free)
        was_running = False
        try:
            cli = _client()
            c = cli.containers.get(vm_name)
            c.reload()
            st = (c.attrs.get("State") or {}).get("Running")
            if st:
                was_running = True
                print("[GROW] stopping container to unmount")
                try:
                    c.stop(timeout=10)
                except Exception as e:
                    print(f"[GROW] stop warn: {e}")
        except Exception:
            pass

        # Unmount if mounted
        try:
            if os.path.ismount(mnt):
                print(f"[GROW] umount {mnt}")
                _run(["umount", mnt])
        except Exception as e:
            print(f"[GROW] umount warn: {e}")
            return False

        # Detach/re-attach loop cleanly to avoid "busy"
        if loopdev:
            try:
                _run(["losetup", "-d", loopdev], check=False)
                time.sleep(0.2)
            except Exception:
                pass
            loopdev = None

        # Enlarge sparse file (use truncate; fallocate can behave oddly on ZFS)
        print(f"[GROW] truncate {img} -> {tgt_bytes} bytes")
        _run(["truncate", "-s", str(tgt_bytes), img])

        # Re-attach loop
        try:
            loopdev = subprocess.check_output(["losetup", "--find", "--show", img], text=True).strip()
        except subprocess.CalledProcessError as e:
            print(f"[GROW] losetup attach failed: {e.stderr if hasattr(e, 'stderr') else e}")
            return False

        # Fsck (preen) then resize
        try:
            print(f"[GROW] e2fsck -pf {loopdev}")
            _run(["e2fsck", "-pf", loopdev], check=False)
        except Exception as e:
            print(f"[GROW] fsck warn: {e}")

        print(f"[GROW] resize2fs {loopdev}")
        r = _run(["resize2fs", loopdev], check=False)
        print(f"[GROW] resize2fs rc={r.returncode} out={r.stdout.strip()} err={r.stderr.strip()}")
        if r.returncode != 0:
            print("[GROW] resize2fs failed")
            return False

        # Remount
        try:
            os.makedirs(mnt, exist_ok=True)
            print(f"[GROW] mount {loopdev} {mnt}")
            _run(["mount", loopdev, mnt])
        except Exception as e:
            print(f"[GROW] mount fail: {e}")
            return False

        # Verify
        try:
            sz = int(subprocess.check_output(["blockdev", "--getsize64", loopdev], text=True).strip())
            df = subprocess.check_output(["df", "-hT", mnt], text=True)
            print(f"[GROW] loop bytes now={sz}; df:\n{df}")
            if sz + 4096 < tgt_bytes:  # allow tiny slop
                print("[GROW] verification mismatch; grow incomplete")
                return False
        except Exception as e:
            print(f"[GROW] verify warn: {e}")

        # Restart container if it was running
        if was_running:
            try:
                cli = _client()
                c = cli.containers.get(vm_name)
                c.start()
            except Exception as e:
                print(f"[GROW] restart warn: {e}")

        return True

    except Exception as e:
        print(f"[GROW] exception: {e}")
        return False


def _db_delete_snapshots_for_vm(vm_name: str, cmd_id: str = "") -> int:
    """
    Delete all virtualmachine_snapshot rows linked to the VM with this name.
    Returns the number of rows deleted, or -1 on error.
    """
    try:
        conn = sqlite3.connect(DB_PATH)
        cur  = conn.cursor()

        # Resolve vm_id from name
        cur.execute("SELECT id FROM virtualmachine WHERE TRIM(name)=?", (vm_name,))
        row = cur.fetchone()
        if not row:
            cur.close()
            conn.close()
            return 0  # nothing to clean

        vm_id = int(row[0])

        cur.execute("DELETE FROM virtualmachine_snapshot WHERE vm_id=?", (vm_id,))
        deleted = cur.rowcount
        conn.commit()
        cur.close()
        conn.close()

        try:
            logger.info(f"[DockerDelete][{cmd_id}] deleted {deleted} snapshot rows for VM '{vm_name}' (vm_id={vm_id})")
        except Exception:
            pass

        return deleted

    except Exception as e:
        try:
            logger.warning(f"[DockerDelete][{cmd_id}] snapshot DB cleanup failed for '{vm_name}': {e}")
        except Exception:
            print(f"[DockerDelete][{cmd_id}] snapshot DB cleanup failed for '{vm_name}': {e}")
        try:
            cur.close()
            conn.close()
        except Exception:
            pass
        return -1



# ----DockerBackupDBDelete Helpers ---------------------
def _db_delete_backups_for_vm(vm_name: str, cmd_id: str = "") -> int:
    """
    Remove all myBackups rows linked to this VM (by VMId) AND
    delete their archive files from disk (local_path), if present.

    Returns: number of DB rows deleted (for logging).
    """
    import os

    deleted_rows = 0
    try:
        conn = sqlite3.connect(DB_PATH)
        cur = conn.cursor()

        # 1) Resolve VM id
        cur.execute("SELECT id FROM virtualmachine WHERE TRIM(name)=?", (vm_name,))
        row = cur.fetchone()
        if not row:
            _log_cleanup(
                f"[DockerDelete][{cmd_id}] myBackups cleanup: no VM row for '{vm_name}'",
                20
            )
            cur.close()
            conn.close()
            return 0

        vm_id = row[0]

        # 2) Fetch all backups + paths for this VM
        cur.execute(
            "SELECT id, local_path FROM myBackups WHERE VMId=?",
            (vm_id,)
        )
        rows = cur.fetchall()

        # 3) Try to delete the archive files
        file_deleted = 0
        last_backups_dir = None
        for bid, path in rows:
            if not path:
                continue
            p = str(path).strip()
            if not p:
                continue
            # Best-effort: delete archive AND its companion .tar.manifest.json
            # (The manifest can remain even if the archive is already gone.)
            try:
                # remember directory for later pruning
                try:
                    last_backups_dir = os.path.dirname(p)
                except Exception:
                    pass

                # derive manifest path from the archive name
                base = os.path.basename(p)
                d    = os.path.dirname(p)

                if base.lower().endswith(".tar.gz"):
                    stem = base[:-7]
                elif base.lower().endswith(".tar"):
                    stem = base[:-4]
                else:
                    stem = os.path.splitext(base)[0]

                mpath = os.path.join(d, f"{stem}.tar.manifest.json")

                # delete archive if present
                if os.path.isfile(p):
                    os.remove(p)
                    file_deleted += 1
                    _log_cleanup(
                        f"[DockerDelete][{cmd_id}] removed backup file {p} (id={bid})",
                        20
                    )
                else:
                    _log_cleanup(
                        f"[DockerDelete][{cmd_id}] backup file missing (id={bid}): {p}",
                        20
                    )

                # delete companion manifest if present
                if os.path.isfile(mpath):
                    try:
                        os.remove(mpath)
                        _log_cleanup(
                            f"[DockerDelete][{cmd_id}] removed backup manifest {mpath} (id={bid})",
                            20
                        )
                    except Exception as e_m:
                        _log_cleanup(
                            f"[DockerDelete][{cmd_id}] remove backup manifest failed (id={bid}, path={mpath}): {e_m}",
                            30
                        )
            except Exception as e2:
                _log_cleanup(
                    f"[DockerDelete][{cmd_id}] remove backup file/manifest failed (id={bid}, path={p}): {e2}",
                    30
                )

        # 4) Delete DB rows
        if rows:
            ids = [r[0] for r in rows]
            placeholders = ",".join("?" * len(ids))
            cur.execute(
                f"DELETE FROM myBackups WHERE id IN ({placeholders})",
                ids
            )
            deleted_rows = cur.rowcount if hasattr(cur, "rowcount") else len(ids)

        conn.commit()
        cur.close()
        conn.close()

        _log_cleanup(
            f"[DockerDelete][{cmd_id}] removed {deleted_rows} myBackups rows "
            f"for VM '{vm_name}' (deleted_files={file_deleted})",
            20
        )
        # Best-effort prune empty dirs: .../<vm>/backups and then .../<vm>
        try:
            if last_backups_dir and os.path.isdir(last_backups_dir):
                try:
                    if not os.listdir(last_backups_dir):
                        os.rmdir(last_backups_dir)
                except Exception:
                    pass

                vm_dir = os.path.dirname(last_backups_dir)
                try:
                    if vm_dir and os.path.isdir(vm_dir) and not os.listdir(vm_dir):
                        os.rmdir(vm_dir)
                except Exception:
                    pass
        except Exception:
            pass
    except Exception as e:
        _log_cleanup(
            f"[DockerDelete][{cmd_id}] myBackups cleanup failed for '{vm_name}': {e}",
            30
        )

    return deleted_rows

def _db_prune_orphan_backups(cmd_id: str = "PRUNE") -> int:
    """
    One-off maintenance:
    Delete myBackups rows that point to a VMId which no longer exists
    in virtualmachine. Returns number of rows deleted.
    """
    try:
        conn = sqlite3.connect(DB_PATH)
        cur  = conn.cursor()

        # Find orphan IDs
        cur.execute("""
            SELECT id
            FROM myBackups
            WHERE VMId IS NOT NULL
              AND VMId NOT IN (SELECT id FROM virtualmachine)
        """)
        rows = cur.fetchall()
        if not rows:
            _log_cleanup(f"[PruneBackups][{cmd_id}] no orphan backup rows found", 20)
            cur.close()
            conn.close()
            return 0

        ids = [r[0] for r in rows]
        placeholders = ",".join("?" * len(ids))

        cur.execute(f"DELETE FROM myBackups WHERE id IN ({placeholders})", ids)
        deleted = cur.rowcount if hasattr(cur, "rowcount") else len(ids)
        conn.commit()
        cur.close()
        conn.close()

        _log_cleanup(
            f"[PruneBackups][{cmd_id}] deleted {deleted} orphan myBackups rows (ids={ids})",
            20
        )
        return deleted
    except Exception as e:
        _log_cleanup(f"[PruneBackups][{cmd_id}] FAILED: {e}", 40)
        return -1



# --- Helper: check for retained backups or snapshots for a VM name ---
def has_retained_backups_or_snapshots(vm_name: str) -> bool:
    """
    Return True if there are *orphaned* snapshots or backups for this VM name:
      - vm_id / VMId is NULL  OR
      - vm_id / VMId points to a non-existent VM row

    This is used by the Create path (st.py) to block reusing a name when
    a previous VM with that name was deleted but its artifacts were kept.
    """
    name = (vm_name or "").strip()
    if not name:
        return False

    conn = None
    cur = None
    try:
        conn = sqlite3.connect(DB_PATH)
        cur = conn.cursor()

        snap_pattern = f"%/{name}/snapshots/%"
        # ---- Orphan snapshots ----
        cur.execute(
            """
            SELECT 1
              FROM virtualmachine_snapshot
             WHERE savedPath LIKE ?
               AND (
                     vm_id IS NULL
                     OR vm_id NOT IN (SELECT id FROM virtualmachine)
                   )
             LIMIT 1
            """,
            (snap_pattern,)
        )
        if cur.fetchone() is not None:
            return True

        bkp_pattern = f"%/{name}/backups/%"
        # ---- Orphan backups ----
        cur.execute(
            """
            SELECT 1
              FROM myBackups
             WHERE (local_path    LIKE ?
                    OR download_Path LIKE ?)
               AND (
                     VMId IS NULL
                     OR VMId NOT IN (SELECT id FROM virtualmachine)
                   )
             LIMIT 1
            """,
            (bkp_pattern, bkp_pattern)
        )
        if cur.fetchone() is not None:
            return True

    except Exception as e:
        try:
            sprint(f"[CHECK] retained-artifact check failed for '{name}': {e}", 0)
        except Exception:
            pass
    finally:
        try:
            cur.close()
        except Exception:
            pass
        try:
            conn.close()
        except Exception:
            pass

    return False

def _db_detach_snapshots_for_vm(vm_name: str, cmd_id: str = "") -> int:
    """
    Detach all snapshots for the VM with this name by setting vm_id = NULL.

    This keeps them in the DB and on disk, but they will never match any
    real VM (the UI queries with vm_id=<current_vm_id>).
    """
    conn = None
    cur = None
    try:
        conn = sqlite3.connect(DB_PATH)
        cur  = conn.cursor()

        cur.execute("SELECT id FROM virtualmachine WHERE TRIM(name)=?", (vm_name,))
        row = cur.fetchone()
        if not row:
            return 0

        vm_id = int(row[0])

        cur.execute(
            "UPDATE virtualmachine_snapshot SET vm_id = NULL WHERE vm_id = ?",
            (vm_id,)
        )
        orphaned = cur.rowcount or 0
        conn.commit()

        try:
            logger.info(
                f"[DockerDelete][{cmd_id}] detached {orphaned} snapshot rows "
                f"for VM '{vm_name}' (vm_id={vm_id} → NULL)"
            )
        except Exception:
            pass

        return orphaned

    except Exception as e:
        try:
            logger.warning(
                f"[DockerDelete][{cmd_id}] snapshot detach failed for "
                f"'{vm_name}': {e}"
            )
        except Exception:
            print(
                f"[DockerDelete][{cmd_id}] snapshot detach failed for "
                f"'{vm_name}': {e}"
            )
        return -1
    finally:
        try:
            cur.close()
        except Exception:
            pass
        try:
            conn.close()
        except Exception:
            pass
def _db_detach_backups_for_vm(vm_name: str, cmd_id: str = "") -> int:
    """
    Detach all backups for the VM with this name by setting VMId = NULL.

    This keeps myBackups rows and backup files, but they are no longer
    associated with any VM (so they won't appear in per-VM backup lists).
    """
    conn = None
    cur = None
    try:
        conn = sqlite3.connect(DB_PATH)
        cur  = conn.cursor()

        cur.execute("SELECT id FROM virtualmachine WHERE TRIM(name)=?", (vm_name,))
        row = cur.fetchone()
        if not row:
            return 0

        vm_id = int(row[0])

        cur.execute(
            "UPDATE myBackups SET VMId = NULL WHERE VMId = ?",
            (vm_id,)
        )
        detached = cur.rowcount or 0
        conn.commit()

        try:
            logger.info(
                f"[DockerDelete][{cmd_id}] detached {detached} myBackups rows "
                f"for VM '{vm_name}' (VMId={vm_id} → NULL)"
            )
        except Exception:
            pass

        return detached

    except Exception as e:
        try:
            logger.warning(
                f"[DockerDelete][{cmd_id}] backup detach failed for "
                f"'{vm_name}': {e}"
            )
        except Exception:
            print(
                f"[DockerDelete][{cmd_id}] backup detach failed for "
                f"'{vm_name}': {e}"
            )
        return -1
    finally:
        try:
            cur.close()
        except Exception:
            pass
        try:
            conn.close()
        except Exception:
            pass

# --- SNAPSHOT HELPERS -------------------------------------------------------

def _vm_base_paths(vm_name: str):
    """Return (base, vm_dir, img_path, mnt_path, snapshots_dir) for a VM."""
    try:
        base = _active_storage_base()
    except Exception:
        base = None
    if not base:
        base = _db_get_docker_storage_base_from_volume()
    if not base or not os.path.isdir(base):
        raise RuntimeError("No active storage base mounted")

    vm_dir = os.path.join(base, vm_name)
    img    = os.path.join(vm_dir, "disk.img")
    mnt    = os.path.join(vm_dir, "mnt")
    snaps  = os.path.join(vm_dir, "snapshots")
    return base, vm_dir, img, mnt, snaps

def _safe_snap_name(s: Optional[str]) -> str:
    if not s or not str(s).strip():
        return time.strftime("snap-%Y%m%d-%H%M%S")
    s = re.sub(r"[^A-Za-z0-9._-]", "_", s.strip())
    return s[:64]  # keep it sane

def _cp_reflink_sparse(src: str, dst: str):
    """Best-effort fast copy: try cp --reflink --sparse, else fallback to copy2."""
    cp = shutil.which("cp")
    if cp:
        try:
            subprocess.run(
                [cp, "--reflink=auto", "--sparse=always", src, dst],
                check=True, text=True, capture_output=True
            )
            return
        except Exception:
            pass
    shutil.copy2(src, dst)

def _snapshot_meta(vm_name: str) -> dict:
    meta = {}
    try:
        conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
        row = cur.execute("""
            SELECT num_cores, memory_GB, vm_disk_size, vm_image_id, type
            FROM virtualmachine
            WHERE TRIM(name)=?
        """, (vm_name,)).fetchone()
        cur.close(); conn.close()
        if row:
            meta = {
                "vcpus": row[0], "memory_GB": row[1], "disk_GB": row[2],
                "image_id": row[3], "type": row[4]
            }
    except Exception:
        pass
    return meta

# --- Backup helpers ----------------------------------------------------------

def _snapshot_img_path(vm_name: str, snap_name: str) -> str:
    base = _active_storage_base()  # e.g., /mnt/dockervol2
    if not base or not os.path.isdir(base):
        raise RuntimeError("Docker storage base not mounted")
    return os.path.join(base, vm_name, "snapshots", f"{snap_name}.img")

def _fetch_backup_server_row(backup_dest_name: str):
    """
    Returns tuple (ip_address, account_name, password, id) from backup table
    for given destination_name. Raises on not found.
    """
    import sqlite3
    conn = sqlite3.connect(DB_PATH)
    cur  = conn.cursor()
    row = cur.execute("""
        SELECT ip_address, account_name, password, id
          FROM backup
         WHERE destination_name=?
         LIMIT 1
    """, (backup_dest_name,)).fetchone()
    cur.close(); conn.close()
    if not row:
        raise RuntimeError(f"Backup destination '{backup_dest_name}' not found")
    return row  # host, user, pwd, backupServerId

def _file_size_bytes(p: str) -> int:
    return os.path.getsize(p)

def _upload_via_ftp(host: str, user: str, pwd: str, remote_dir: str, local_path: str, dest_file: str):
    """
    Minimal FTP upload (to match current environment). You can swap to ftplib.FTP_TLS
    or paramiko (SFTP) later; the call signature stays the same.
    """
    import ftplib
    import posixpath
    # Normalize remote_dir -> no double slashes
    remote_dir = (remote_dir or "").strip()
    if not remote_dir.endswith("/"):
        remote_dir = remote_dir + "/"
    with ftplib.FTP(host=host, user=user, passwd=pwd, timeout=60) as ftp:
        # ensure cwd (will fail if the directory is missing)
        ftp.cwd(remote_dir)
        with open(local_path, "rb") as fh:
            ftp.storbinary(f"STOR {dest_file}", fh)
    return posixpath.join(remote_dir, dest_file)

def DockerBackupStart(vm_name: str,
                      snapshot_name: str,
                      backup_dest_name: Optional[str] = None,
                      backup_name: Optional[str] = None,
                      backup_volume_name: Optional[str] = None,
                      backup_volume_id: Optional[int] = None) -> int:
    """
    Uploads snapshot to either:
      - remote backup server (FTP-like) if backup_dest_name is provided, or
      - local backup volume (filesystem path) if backup_volume_* is provided, or
      - both, if you pass both (first copy locally, then upload the local file).

    Returns 0 on success, -2 on generic failure, -21 for validation error.
    """
    import sqlite3, datetime, json, shutil, os

    try:
        if not vm_name or not snapshot_name:
            print("[BACKUP] missing vm_name/snapshot_name")
            return -21

        snap_img = _snapshot_img_path(vm_name, snapshot_name)
        if not os.path.isfile(snap_img):
            print(f"[BACKUP] snapshot image not found: {snap_img}")
            return -21

        # Derive filename
        _, ext = os.path.splitext(snap_img)
        if not ext:
            ext = ".img"
        final_name = (backup_name.strip().replace(" ", "_") + ext) if backup_name else (snapshot_name + ext)

        # Optional local backup volume destination (copy)
        written_local_path = None
        if backup_volume_name or backup_volume_id:
            try:
                if backup_volume_name:
                    vol_path = _fetch_backup_volume_path_by_name(backup_volume_name)
                else:
                    vol_path = _fetch_backup_volume_path_by_id(int(backup_volume_id))

                if not os.path.isdir(vol_path):
                    raise RuntimeError(f"Backup volume path not a directory: {vol_path}")

                os.makedirs(vol_path, exist_ok=True)
                dst = os.path.join(vol_path, final_name)
                print(f"[BACKUP] copying locally: {snap_img} -> {dst}")
                # Use copy2 to preserve times; hardlink could be used if same FS
                shutil.copy2(snap_img, dst)
                written_local_path = dst
            except Exception as e:
                print(f"[BACKUP] local volume copy failed: {e}")
                return -2

        # Optional remote server upload
        remote_path = None
        backup_server_id = None
        if backup_dest_name:
            try:
                host, user, pwd, backup_server_id = _fetch_backup_server_row(backup_dest_name)
                src_for_upload = written_local_path or snap_img  # prefer local copy if we made one
                remote_dir = RemoteFTPPath  # from globalSettings
                print(f"[BACKUP] uploading {src_for_upload} -> {host}:{remote_dir}{final_name}")
                remote_path = _upload_via_ftp(host, user, pwd, remote_dir, src_for_upload, final_name)
            except Exception as e:
                print(f"[BACKUP] remote upload failed: {e}")
                return -2

        # Record history in DB — you can write one or two rows if both destinations used.
        conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
        vm_row = cur.execute("SELECT id FROM virtualmachine WHERE TRIM(name)=?", (vm_name.strip(),)).fetchone()
        vm_id = int(vm_row[0]) if vm_row else 0

        file_sz = _file_size_bytes(snap_img)

        # Write a row for local copy (if any)
        if written_local_path:
            cur.execute("""
                INSERT INTO myBackups
                    (BackupServerId, VMId, download_Path, backup_time, BackupName,
                     cr_date, edit_date, vm_group_id, vm_image_size)
                VALUES (?, ?, ?, date(), ?, date(), date(), 16, ?)
            """, (None, vm_id, written_local_path, backup_name or snapshot_name, file_sz))

        # Write a row for remote copy (if any)
        if remote_path:
            cur.execute("""
                INSERT INTO myBackups
                    (BackupServerId, VMId, download_Path, backup_time, BackupName,
                     cr_date, edit_date, vm_group_id, vm_image_size)
                VALUES (?, ?, ?, date(), ?, date(), date(), 16, ?)
            """, (backup_server_id, vm_id, remote_path, backup_name or snapshot_name, file_sz))

        # Update last_remote_backup only if remote was used; you can add last_local_backup if desired
        if remote_path:
            cur.execute("UPDATE virtualmachine SET last_remote_backup=Date() WHERE TRIM(name)=?", (vm_name.strip(),))

        conn.commit(); cur.close(); conn.close()
        print("[BACKUP] completed")
        return 0

    except Exception as e:
        print(f"[BACKUP] exception: {e}")
        return -2

def DockerBackupStatus(vm_name: str) -> dict:
    """
    Returns latest backup entries for the VM (lightweight status for GUI).
    """
    import sqlite3
    try:
        conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
        row = cur.execute("SELECT id FROM virtualmachine WHERE TRIM(name)=?", (vm_name.strip(),)).fetchone()
        if not row:
            cur.close(); conn.close()
            return {"status": "fail", "message": "VM not found"}
        vm_id = int(row[0])

        rows = cur.execute("""
            SELECT BackupName, download_Path, backup_time, vm_image_size
              FROM myBackups
             WHERE VMId=?
             ORDER BY id DESC
             LIMIT 10
        """, (vm_id,)).fetchall()
        cur.close(); conn.close()

        data = [{
            "backupName": r[0],
            "path":       r[1],
            "time":       r[2],
            "size_bytes": int(r[3] or 0),
        } for r in rows]

        return {"status": "success", "backups": data}
    except Exception as e:
        return {"status": "fail", "message": str(e)}

def _fetch_backup_volume_path_by_name(vol_name: str) -> str:
    """
    Example resolution by 'destination_name' in backup table to a local mount path.
    If you instead store a path in 'volume' or 'storagepath', adjust the query.
    """
    import sqlite3
    conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
    # Option A: a dedicated table that maps a friendly name to a mount path
    row = cur.execute("""
        SELECT location
          FROM storagepath
         WHERE name=?
         LIMIT 1
    """, (vol_name,)).fetchone()
    cur.close(); conn.close()
    if not row:
        raise RuntimeError(f"Backup volume '{vol_name}' not found")
    return row[0]  # e.g., "/backup_pool"
    

def _fetch_backup_volume_path_by_id(vol_id: int) -> str:
    import sqlite3
    conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
    # Option B: resolve path by ID (storagepath.id)
    row = cur.execute("""
        SELECT location
          FROM storagepath
         WHERE id=?
         LIMIT 1
    """, (vol_id,)).fetchone()
    cur.close(); conn.close()
    if not row:
        raise RuntimeError(f"Backup volume id={vol_id} not found")
    return row[0]


# --- Backup helpers ----------------------------------------------------------
import os, sqlite3, datetime, shutil

def _resolve_local_backup_paths(vm_name: str,
                                prefer_volume_name: str = 'bkpsrvrvol',
                                subdir: str = 'backups',
                                dest_override: Optional[str] = None,
                                backup_name: Optional[str] = None) -> dict:
    """
    Returns dict with:
      vm_id, image_type, src_dir, src_file, dst_dir, dst_file, base
    If dest_override is provided (e.g. '/mnt/bkpsrvrvol'), it is used as base.
    Otherwise, uses volume.backup_device='Y' or volume.name=prefer_volume_name.
    """
    conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
    try:
        row = cur.execute("""
            SELECT v.id, v.saved_path, v.name, COALESCE(i.image_type,'img')
            FROM virtualmachine v
            LEFT JOIN vm_image i ON i.id = v.vm_image_id
            WHERE TRIM(v.name)=?
        """, (vm_name.strip(),)).fetchone()
        if not row:
            raise RuntimeError(f"VM '{vm_name}' not found")
        vm_id, saved_path, vmname, img_type = row
        src_dir  = (saved_path or "").rstrip("/")
        src_file = os.path.join(src_dir, f"{vmname}.{img_type}")

        if dest_override and str(dest_override).strip():
            base = str(dest_override).rstrip("/")
        else:
            row = cur.execute("""
                SELECT COALESCE(v.location,'')    AS vol_loc,
                       COALESCE(md.location,'')   AS pool_loc,
                       COALESCE(md.alt_location,'') AS pool_alt
                FROM volume v
                LEFT JOIN multi_device md ON md.id = v.multi_device_id
                WHERE v.backup_device='Y' OR v.name=?
                ORDER BY (v.backup_device='Y') DESC, v.id ASC
                LIMIT 1
            """, (prefer_volume_name,)).fetchone()
            if not row:
                raise RuntimeError("No backup volume found (set volume.backup_device='Y' or create 'bkpsrvrvol').")
            vol_loc, pool_loc, pool_alt = row
            base = (vol_loc or pool_loc or pool_alt).rstrip("/")
        if not base:
            raise RuntimeError("Backup base path empty or not mounted.")

        dst_dir = os.path.join(base, vmname, subdir)
        os.makedirs(dst_dir, exist_ok=True)

        # If UI provided a backup name, use it as the actual archive filename.
        # Otherwise, keep the legacy <vm>-<timestamp> naming.
        if backup_name and str(backup_name).strip():
            bn = str(backup_name).strip()
            # sanitize to a safe filename (no paths, limited charset)
            bn = os.path.basename(bn)
            bn = re.sub(r"[^A-Za-z0-9._-]", "_", bn)
            bn = bn[:120] if len(bn) > 120 else bn

            # Ensure it ends with the expected image_type extension (e.g. tar.gz)
            img_ext = str(img_type).lstrip(".")
            if not bn.lower().endswith(img_ext.lower()):
                bn = f"{bn}.{img_ext}"
            dst_file = os.path.join(dst_dir, bn)
        else:
            stamp = datetime.datetime.now().strftime("%Y%m%d%H%M")
            dst_file = os.path.join(dst_dir, f"{vmname}-{stamp}.{img_type}")

        return {
            "vm_id": vm_id,
            "image_type": img_type,
            "src_dir": src_dir,
            "src_file": src_file,
            "dst_dir": dst_dir,
            "dst_file": dst_file,
            "base": base,
        }
    finally:
        try: cur.close()
        except: pass
        try: conn.close()
        except: pass

import subprocess, shutil

def DockerBackupLocal(name, backup_name=None, dest=None, cmd_id=None):
    """
    Copy <saved_path>/<vm>.<ext> to <backup_volume>/<vm>/backups/<vm>-<ts>.<ext>.
    If the source export is missing, create it first (offline) from <base>/<vm>/mnt.
    Returns (0, dst) on success; otherwise (-2, message).
    """

    try:
        # 1) Resolve where to read and write
        paths = _resolve_local_backup_paths(
            name,
            prefer_volume_name='bkpsrvrvol',
            subdir='backups',
            dest_override=dest,
            backup_name=backup_name,
        )
        src = paths["src_file"]
        dst = paths["dst_file"]

        # 2) Ensure the export exists; create if missing
        if not os.path.isfile(src):
            rc, msg = DockerExportLocal(name, mode="offline")
            if rc != 0:
                return (-2, f"Export failed: {msg}")
            # re-resolve in case the ext/path normalized during export
            paths = _resolve_local_backup_paths(
                name,
                prefer_volume_name='bkpsrvrvol',
                subdir='backups',
                dest_override=dest,
                backup_name=backup_name,
            )
            src = paths["src_file"]
            dst = paths["dst_file"]
            if not os.path.isfile(src):
                return (-2, f"Export did not create source: {src}")

        # 3) Ensure destination directory
        os.makedirs(os.path.dirname(dst), exist_ok=True)

        # 4) Copy with robust fallbacks
        try:
            cp_bin = shutil.which("cp") or "/bin/cp"
            subprocess.run(
                ["sudo", cp_bin, "--reflink=auto", "--sparse=always", src, dst],
                check=True, text=True, capture_output=True
            )
        except (subprocess.CalledProcessError, FileNotFoundError):
            # try sparse dd (works across filesystems)
            try:
                dd_bin = shutil.which("dd") or "/bin/dd"
                subprocess.run(
                    ["sudo", dd_bin, f"if={src}", f"of={dst}", "bs=16M", "status=none", "conv=sparse"],
                    check=True, text=True
                )
            except (subprocess.CalledProcessError, FileNotFoundError) as e2:
                # final fallback: Python stream copy (no sudo)
                try:
                    with open(src, "rb") as rf, open(dst, "wb") as wf:
                        shutil.copyfileobj(rf, wf, length=16 * 1024 * 1024)
                except Exception as e3:
                    return (-2, f"copy failed (dd:{e2}) (python:{e3})")

        # 5) Best-effort DB record (local backup only) — UPSERT by (VMId, BackupName)
        try:
            conn = sqlite3.connect(DB_PATH); cur = conn.cursor()

            # Compute size (best-effort)
            try:
                size_bytes = os.path.getsize(dst)
            except Exception:
                size_bytes = 0

            backup_name_eff = (backup_name or os.path.basename(dst))
            vm_id_eff = paths["vm_id"]

            # Check if a row already exists for this VM + BackupName
            cur.execute("""
                SELECT id FROM myBackups
                 WHERE VMId=? AND BackupName=?
                 ORDER BY id DESC
                 LIMIT 1
            """, (vm_id_eff, backup_name_eff))
            row = cur.fetchone()

            if row:
                # UPDATE existing record
                cur.execute("""
                    UPDATE myBackups
                       SET local_path      = ?,
                           vm_image_size   = ?,
                           edit_date       = datetime(),
                           backup_time     = datetime(),
                           upload_state    = 0,     -- local copy present
                           state           = 1      -- active/ok (aligns with existing rows)
                     WHERE id = ?
                """, (dst, int(size_bytes), int(row[0])))
            else:
                # INSERT new record
                cur.execute("""
                    INSERT INTO myBackups
                        (BackupName, uuid, cr_date, edit_date, local_path, vm_type,
                         VMId, vm_image_size, vm_group_id, state, upload_state, backup_time)
                    VALUES(?, ?, datetime(), datetime(), ?, ?, ?, ?, 16, 1, 0, datetime())
                """, (
                    backup_name_eff,
                    (cmd_id or ""),
                    dst,
                    "docker",
                    vm_id_eff,
                    int(size_bytes),
                ))

            conn.commit()
        except Exception as db_e:
            try: sprint(f"[BACKUP] DB record warn (upsert): {db_e}", 0)
            except Exception: pass
        finally:
            try: cur.close()
            except: pass
            try: conn.close()
            except: pass

        return (0, dst)

    except Exception as e:
        return (-2, f"{e}")

# --- FULL BACKUP (no snapshots) ---------------------------------------------
def _docker_inspect_dict(name: str) -> dict:
    cli = _client()
    c = cli.containers.get(name)
    c.reload()
    return c.attrs

def _docker_mounts(name: str) -> list:
    info = _docker_inspect_dict(name)
    return (info.get("Mounts") or [])

def _volume_mountpoint(volume_name: str) -> Optional[str]:
    try:
        import docker
        dc = docker.from_env()
        v = dc.volumes.get(volume_name)
        return (v.attrs or {}).get("Mountpoint")
    except Exception:
        try:
            r = subprocess.run(
                ["docker", "volume", "inspect", volume_name, "--format", "{{.Mountpoint}}"],
                capture_output=True, text=True, check=True
            )
            return r.stdout.strip()
        except Exception:
            return None

def _tar_add_path(tar: tarfile.TarFile, src_path: str, arc_prefix: str):
    base = arc_prefix.rstrip("/")
    src_path = os.path.abspath(src_path)
    if not os.path.exists(src_path):
        return
    if os.path.isfile(src_path):
        tar.add(src_path, arcname=f"{base}/{os.path.basename(src_path)}", recursive=False)
        return
    for root, _dirs, files in os.walk(src_path):
        rel = os.path.relpath(root, src_path)
        arcdir = base if rel == "." else f"{base}/{rel}"
        tar.add(root, arcname=arcdir, recursive=False)
        for f in files:
            tar.add(os.path.join(root, f), arcname=f"{base}/{rel}/{f}", recursive=False)

def _resolve_full_backup_target(vm_name: str,
                                dest_override: Optional[str] = None,
                                backup_name: Optional[str] = None) -> Tuple[str, str, int]:
    paths = _resolve_local_backup_paths(vm_name, dest_override=dest_override, backup_name=backup_name)
    dst_dir = paths["dst_dir"]
    vm_id   = paths["vm_id"]

    # If UI provided backup_name, use it. Otherwise keep legacy <vm>-<ts>.full.tar
    if backup_name and str(backup_name).strip():
        bn = os.path.basename(str(backup_name).strip())
        bn = re.sub(r"[^A-Za-z0-9._-]", "_", bn)
        bn = bn[:120] if len(bn) > 120 else bn
        if not bn.lower().endswith(".tar") and not bn.lower().endswith(".tar.gz"):
            bn = bn + ".tar"
        dst_file = os.path.join(dst_dir, bn)
    else:
        stamp = datetime.datetime.now().strftime("%Y%m%d%H%M")
        dst_file = os.path.join(dst_dir, f"{vm_name}-{stamp}.full.tar")

    return (dst_dir, dst_file, vm_id)

def DockerBackupAll(name: str,
                    backup_name: Optional[str],
                    dest: Optional[str],
                    cmd_id: Optional[str]) -> Tuple[int, str]:
    """
    Full backup: one tar containing:
      meta/inspect.json
      rootfs/export.tar
      binds/<dest>/...
      volumes/<name>/...
      extras/dynamic-storage/... (if found)
    """
    try:
        dst_dir, dst_file, vm_id = _resolve_full_backup_target(name, dest_override=dest, backup_name=backup_name)
        os.makedirs(dst_dir, exist_ok=True)

        info = _docker_inspect_dict(name)  # raises if container missing

        # Detect your per-VM loopback mount (best effort)
        dynamic_host_mount = None
        for p in (f"/mnt/dockervol2/{name}/mnt", f"/mnt/dynamic-storage/{name}"):
            if os.path.isdir(p):
                dynamic_host_mount = p
                break

        with tarfile.open(dst_file, "w") as tar:
            # meta
            meta_bytes = json.dumps(info, indent=2).encode("utf-8")
            ti = tarfile.TarInfo("meta/inspect.json")
            ti.size = len(meta_bytes); ti.mtime = int(time.time())
            tar.addfile(ti, io.BytesIO(meta_bytes))

            # rootfs/export.tar (via docker export)
            tmp_export = dst_file + ".tmp.export.tar"
            try:
                with open(tmp_export, "wb") as wf:
                    p = subprocess.run(["docker", "export", name], stdout=wf)
                    if p.returncode != 0:
                        raise RuntimeError("docker export failed")
                tar.add(tmp_export, arcname="rootfs/export.tar")
            finally:
                try: os.remove(tmp_export)
                except Exception: pass

            # mounts: binds + volumes
            for m in _docker_mounts(name):
                mtype = (m.get("Type") or "").lower()
                desti = (m.get("Destination") or "").strip()
                if mtype == "bind":
                    src = m.get("Source") or ""
                    if src and os.path.exists(src):
                        _tar_add_path(tar, src, f"binds{desti}")
                elif mtype == "volume":
                    vol_name = (m.get("Name") or m.get("Source") or "").strip()
                    mp = _volume_mountpoint(vol_name) if vol_name else None
                    if mp and os.path.exists(mp):
                        safe = re.sub(r"[^A-Za-z0-9._@+-]", "_", vol_name or "volume")
                        _tar_add_path(tar, mp, f"volumes/{safe}")

            # extras: dynamic storage
            if dynamic_host_mount and os.path.isdir(dynamic_host_mount):
                _tar_add_path(tar, dynamic_host_mount, "extras/dynamic-storage")

        # DB record (local_path only)
        try:
            sz = os.path.getsize(dst_file)
        except Exception:
            sz = 0
        try:
            conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
            cur.execute("""
                INSERT INTO myBackups
                    (BackupName, uuid, cr_date, edit_date, local_path, vm_type,
                     VMId, vm_image_size, vm_group_id, state, upload_state)
                VALUES(?, ?, datetime(), datetime(), ?, ?, ?, ?, 16, 1, 0)
            """, (
                (backup_name or os.path.basename(dst_file)),
                (cmd_id or ""),
                dst_file,
                "docker",
                vm_id,
                int(sz)
            ))
            conn.commit()
        except Exception as e:
            sprint(f"[BACKUP-DB] warn: {e}", 0)
        finally:
            try: cur.close()
            except: pass
            try: conn.close()
            except: pass

        return (0, dst_file)
    except Exception as e:
        return (-2, f"{e}")

def _resolve_export_artifact(vm_name: str):
    # returns {"vm_id", "saved_path", "vmname", "img_type", "artifact"}
    conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
    try:
        row = cur.execute("""
            SELECT v.id, v.saved_path, v.name, COALESCE(i.image_type,'tar.gz')
            FROM virtualmachine v
            LEFT JOIN vm_image i ON i.id = v.vm_image_id
            WHERE TRIM(v.name)=?
        """, (vm_name.strip(),)).fetchone()
        if not row:
            raise RuntimeError(f"VM '{vm_name}' not found")
        vm_id, saved_path, vmname, img_type = row
        saved_path = (saved_path or "").rstrip("/")
        if not saved_path:
            raise RuntimeError("saved_path is empty in DB")
        os.makedirs(saved_path, exist_ok=True)
        artifact = os.path.join(saved_path, f"{vmname}.{img_type}")
        return {"vm_id": vm_id, "saved_path": saved_path, "vmname": vmname,
                "img_type": img_type, "artifact": artifact}
    finally:
        try: cur.close()
        except: pass
        try: conn.close()
        except: pass

def _collect_container_metadata(vm_name: str) -> dict:
    meta = {
        "image_ref": None,
        "resources": {"cpus": None, "memory_gb": None, "disk_gb": None},
        "ports": [],
        "networks": [],
        "env": {}
    }
    try:
        import docker, json, sqlite3, os
        cli = docker.from_env()
        c = cli.containers.get(vm_name)
        c.reload()
        info = c.attrs or {}
        cfg  = info.get("Config") or {}
        hc   = info.get("HostConfig") or {}
        ns   = (info.get("NetworkSettings") or {})
        # image
        meta["image_ref"] = cfg.get("Image")
        # resources
        nano = int(hc.get("NanoCpus") or 0)
        mem  = int(hc.get("Memory") or 0)
        meta["resources"]["cpus"]      = (nano / 1_000_000_000.0) if nano else None
        meta["resources"]["memory_gb"] = (mem / (1024**3)) if mem else None
        # disk from DB
        try:
            import sqlite3
            conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
            row = cur.execute("SELECT vm_disk_size FROM virtualmachine WHERE TRIM(name)=?", (vm_name.strip(),)).fetchone()
            if row and row[0] is not None:
                meta["resources"]["disk_gb"] = float(row[0])
            cur.close(); conn.close()
        except Exception:
            pass
        # ports
        ports_obj = (ns.get("Ports") or {})
        for cport, binds in ports_obj.items():
            if not binds:
                continue
            for b in binds:
                meta["ports"].append(f"{b.get('HostIp','0.0.0.0')}:{b.get('HostPort','?')}->{cport}")
        # networks
        nets = (ns.get("Networks") or {})
        meta["networks"] = [n for n in nets.keys() if n]
        # env
        for item in (cfg.get("Env") or []):
            if "=" in item:
                k, v = item.split("=", 1)
                meta["env"][k] = v
    except Exception:
        pass
    return meta
def _write_manifest_for_backup(vm_id: int, vm_name: str, src_path: str, dst_path: str,
                               image_type: str, backup_name: str) -> str:
    def _sha256(p: str) -> str:
        h = hashlib.sha256()
        with open(p, "rb") as f:
            for chunk in iter(lambda: f.read(1024*1024), b""):
                h.update(chunk)
        return h.hexdigest()
    man = {
        "version": 1,
        "created_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "vm": {"id": vm_id, "name": vm_name, "vm_type": "docker"},
        "source": {"saved_path": os.path.dirname(src_path), "export_file": src_path, "image_type": image_type},
        "archive": {
            "local_path": dst_path,
            "size_bytes": os.path.getsize(dst_path),
            "sha256": _sha256(dst_path),
            "backup_name": backup_name
        },
        "docker": _collect_container_metadata(vm_name),
        "volumes": [],
        "notes": "Created by DockerBackupFull"
    }
    man_path = os.path.splitext(dst_path)[0] + ".manifest.json"
    with open(man_path, "w") as f:
        json.dump(man, f, indent=2)
    return man_path

def _db_vm_id(name):
    conn = sqlite3.connect(DB_PATH)
    try:
        cur = conn.cursor()
        row = cur.execute(
            "SELECT id FROM virtualmachine WHERE TRIM(name)=?",
            (name,)
        ).fetchone()
        return row[0] if row else None
    finally:
        try: cur.close()
        except: pass
        conn.close()

def _snap_dir_for(vm_name: str) -> str:
    _, _, _, _, snaps = _vm_base_paths(vm_name)
    return snaps

def _snap_exists(vm_name: str, snap: str) -> bool:
    try:
        d = _snap_dir_for(vm_name)
        return os.path.exists(os.path.join(d, f"{snap}.img"))
    except Exception:
        return False

def _resolve_volume_path(vol_name_or_id):
    """
    Return the host mount path for a configured volume.
    Fallback to /mnt/<name> if not found in DB.
    """
    try:
        name = (vol_name_or_id or "").strip()
        if not name:
            return None
        # Most installs mount volumes at /mnt/<name>
        base = os.path.join("/mnt", name)
        return base if os.path.isdir(base) else None
    except Exception:
        return None

def _archiware_devices_for_create(info_like) -> list:
    """
    Return device specs for docker.create(devices=[...]) if image looks like Archiware.
    Example: ['/dev/st0:/dev/st0:rwm', '/dev/sg13:/dev/sg13:rwm']
    - Detects via image ref containing any of: 'archiware', 'awp5', 'p5server', 'p5-'
    - Uses `lsscsi -g` when available, falls back to /dev/st*
    - Skips devices already present in HostConfig.Devices
    """
    try:
        import os, glob, subprocess

        cfg  = (info_like or {}).get("Config") or {}
        hc   = (info_like or {}).get("HostConfig") or {}
        img  = (cfg.get("Image") or "").lower()

        # Be generous with matching so new tags still work
        if not any(tok in img for tok in ("archiware", "awp5", "p5server", "p5-")):
            return []

        # Already-present device paths (avoid duplicates)
        existing = set()
        for d in (hc.get("Devices") or []):
            # docker-py may give dicts like {'PathOnHost': ..., 'PathInContainer': ..., 'CgroupPermissions': 'rwm'}
            ph = d.get("PathOnHost") or d.get("PathInContainer")
            if ph:
                existing.add(str(ph))

        found = []

        # Prefer lsscsi -g (gets both /dev/st* and /dev/sg*)
        try:
            r = subprocess.run(["lsscsi", "-g"], text=True, capture_output=True, check=False)
            if (r.stdout or "").strip():
                for line in (r.stdout or "").splitlines():
                    if "tape" in line.lower():
                        for tok in line.split():
                            if tok.startswith("/dev/st") or tok.startswith("/dev/sg"):
                                if os.path.exists(tok):
                                    found.append(tok)
        except Exception:
            pass

        # Fallback: at least the character tape nodes
        if not found:
            found.extend(sorted(glob.glob("/dev/st*")))

        # De-dup and filter out already-present
        out = []
        seen = set()
        for p in found:
            if p in existing:
                continue
            if p and p not in seen and os.path.exists(p):
                out.append(f"{p}:{p}:rwm")
                seen.add(p)

        return out

    except Exception:
        return []

# --- helper: extract exact port bindings from inspect info ---
def _port_bindings_from_info(info: dict):
    """
    Return (ports_arg, port_bindings_arg) suitable for docker.create().
    - ports_arg is a list of container ports (e.g., ["8000/tcp"]) needed to expose
    - port_bindings_arg maps "8000/tcp" -> [{"HostIp":"", "HostPort":"7743"}, ...]
    We prefer HostConfig.PortBindings to keep the exact host port/IP.
    """
    ports_arg = []
    port_bindings_arg = {}

    hostcfg = (info or {}).get("HostConfig") or {}
    hb = hostcfg.get("PortBindings") or {}

    # If we have PortBindings, use them verbatim
    if hb:
        for ckey, lst in hb.items():           # ckey like "8000/tcp"
            ports_arg.append(ckey)
            if isinstance(lst, list) and lst:
                # Keep exact ip/port tuples (string ports are fine)
                port_bindings_arg[ckey] = []
                for ent in lst:
                    host_ip = (ent or {}).get("HostIp", "")
                    host_port = (ent or {}).get("HostPort", "")
                    port_bindings_arg[ckey].append({"HostIp": host_ip, "HostPort": str(host_port)})
        return ports_arg, port_bindings_arg

    # Fallback: read from NetworkSettings.Ports (may miss HostIp)
    ns = (info or {}).get("NetworkSettings") or {}
    pmap = ns.get("Ports") or {}
    for ckey, lst in (pmap or {}).items():
        ports_arg.append(ckey)
        if isinstance(lst, list) and lst:
            port_bindings_arg[ckey] = [{"HostIp": (lst[0].get("HostIp") or ""),
                                        "HostPort": str(lst[0].get("HostPort") or "")}]
        else:
            port_bindings_arg[ckey] = [{"HostIp": "", "HostPort": ""}]
    return ports_arg, port_bindings_arg

# Convert (ports_arg, port_bindings_arg) -> docker SDK high-level "ports" dict
def _to_highlevel_ports(ports_arg, port_bindings_arg):
    """
    Return a dict acceptable to docker.containers.create(ports=...),
    preserving the same host port numbers. (HostIp is ignored by high-level API.)
    If you must preserve HostIp or multiple host bindings, use the low-level API
    (see Option B in the call site).
    """
    out = {}
    for ckey in (ports_arg or []):
        binds = (port_bindings_arg or {}).get(ckey) or []
        if binds:
            hp = (binds[0] or {}).get("HostPort")
            if hp is not None and str(hp) != "":
                out[ckey] = int(hp) if str(hp).isdigit() else hp
            else:
                out[ckey] = None
        else:
            out[ckey] = None
    return out

# ------------ public API (int codes) ------------
def DockerCreate(name, cmd, image, memory, cpus, disk, network, port, cmd_id):
    import traceback
    try:
        if not name or not image:
            print("DockerCreate: missing name or image")
            return -1

        cli = docker.from_env()

        # Ensure image present (or pull)
        try:
            img = cli.images.get(image)
        except NotFound:
            print(f"DockerCreate: pulling image {image}")
            img = cli.images.pull(image)

        mem_limit = _parse_memory(memory)
        nano      = None if cpus in (None, "", "None") else int(float(cpus) * 1_000_000_000)

        # >>> FIX: honor list syntax from st.py (_parse_network_arg)
        primary_net, extra_nets = _normalize_networks(network)

        # ---- single-host-port publishing ----
        ports_map = _build_port_bindings_for_single_host_port(img, port)
        if _is_kdenlive_image_name(image):
            ports_map = _force_single_host_port_binding(ports_map, "3001/tcp")

        host_kwargs = {}
        if mem_limit is not None: host_kwargs["mem_limit"] = mem_limit
        if nano is not None:      host_kwargs["nano_cpus"] = nano

        # ---- hide host block devices (mask sysfs) ----
        _mask_opts = "rw,nosuid,nodev,size=1m"
        host_kwargs["tmpfs"] = {
            "/sys/block": _mask_opts,
            "/sys/class/block": _mask_opts,
            "/sys/devices/virtual/block": _mask_opts,
        }
        host_kwargs["security_opt"] = (host_kwargs.get("security_opt") or []) + ["no-new-privileges"]

        # Optional: gVisor toggle via env/label
        try:
            if os.environ.get("USE_GVISOR_BLOCK_HIDE", "0").lower() in ("1","true","yes"):
                host_kwargs["runtime"] = "runsc"
        except Exception:
            pass

        # Persistent storage allocation → bind mount to /mnt/root
        volumes = None
        extra_mounts = []
        try:
            host_path = _allocate_persistent_path(name, disk)
            # >>> fail-fast if disk requested but allocation failed
            if (disk is not None and str(disk).strip() not in ("", "0", "0.0")) and not host_path:
                print("DockerCreate: disk requested but no valid Docker volume base -> ABORT")
                return -3
            if host_path:
                volumes = {host_path: {"bind": CONTAINER_DATA_MOUNT, "mode": "rw"}}
                fm = subprocess.run(["findmnt", "-no", "SOURCE", host_path], text=True, capture_output=True, check=False)
                src = (fm.stdout or "").strip()
                m = re.match(r"/dev/(loop\d+)", src or "")
                if m:
                    loop_dev = m.group(1)
                    sys_block_path = f"/sys/block/{loop_dev}"
                    if os.path.isdir(sys_block_path):
                        extra_mounts.append(docker.types.Mount(type="bind", source=sys_block_path, target=f"/sys/block/{loop_dev}", read_only=True))
                    try:
                        st = os.stat(f"/dev/{loop_dev}")
                        majmin = f"{os.major(st.st_rdev)}:{os.minor(st.st_rdev)}"
                        host_mm_path = f"/sys/dev/block/{majmin}"
                        if os.path.exists(host_mm_path):
                            extra_mounts.append(docker.types.Mount(type="bind", source=host_mm_path, target=f"/sys/dev/block/{majmin}", read_only=True))
                    except Exception:
                        pass
        except Exception as e:
            print(f"DockerCreate: allocator/lsblk exposure warn: {e}")

        dbg = {
            "image": image, "name": name, "ports": ports_map,
            "network": primary_net, "extra_nets": extra_nets,
            "mem_limit": mem_limit, "nano_cpus": nano,
            "volumes": volumes,
        }
        print("DockerCreate: create() debug ->", json.dumps(dbg))

        # ---- assemble create kwargs (so we can inject devices before create) ----
        create_kwargs = dict(
            image=image,
            name=name,
            ports=ports_map,
            network=primary_net or None,
            restart_policy={"Name": "unless-stopped"},
            volumes=volumes,
            mounts=extra_mounts or None,
            **host_kwargs
        )

        # Archiware: add tape devices on initial create (dynamic, no hardcoded tag)
        try:
            devs = _archiware_devices_for_create({"Config": {"Image": image}, "HostConfig": {}})
            if devs:
                create_kwargs["devices"] = (create_kwargs.get("devices") or []) + devs
                create_kwargs["privileged"] = True
                _emit(f"[DockerCreate] archiware devices added: {devs}", 20)
        except Exception as e:
            _emit(f"[DockerCreate] archiware inject warn: {e}", 20)

# Ubuntu: enable NET_ADMIN + tun device for WireGuard/VPN support
        try:
            img_lower = str(image).lower()
            if any(tok in img_lower for tok in ("ubuntu",)):
                _emit(f"[DockerCreate] ubuntu image detected: enabling NET_ADMIN + tun", 20)
                create_kwargs["privileged"] = True
                create_kwargs["cap_add"] = (create_kwargs.get("cap_add") or []) + ["NET_ADMIN", "SYS_MODULE"]
                create_kwargs["sysctls"] = {"net.ipv4.conf.all.src_valid_mark": "1"}
                if os.path.exists("/dev/net/tun"):
                    create_kwargs["devices"] = (create_kwargs.get("devices") or []) + ["/dev/net/tun:/dev/net/tun:rwm"]
                if create_kwargs.get("mounts") is None:
                    create_kwargs["mounts"] = []
                create_kwargs["mounts"].append(
                    docker.types.Mount(
                        type="bind",
                        source="/lib/modules",
                        target="/lib/modules",
                        read_only=True
                    )
                )
        except Exception as e:
            _emit(f"[DockerCreate] ubuntu inject warn: {e}", 20)

# Kdenlive: browser-based video editor — needs software GL, audio, shm
        try:
            img_lower = str(image).lower()
            if any(tok in img_lower for tok in ("kdenlive",)):
                _emit(f"[DockerCreate] kdenlive image detected: applying display/audio env", 20)
                existing_env = list(create_kwargs.get("environment") or [])
                kdenlive_env = {
                    "LIBGL_ALWAYS_SOFTWARE": "1",
                    "MLT_NO_VAAPI":          "1",
                    "GALLIUM_DRIVER":        "llvmpipe",
                    "SDL_VIDEODRIVER":       "offscreen",
                    "XDG_RUNTIME_DIR":       "/run/user/911",
                    # Selkies-based Kdenlive requires HTTPS for WebCodecs/audio.
                    "HTTPS_ONLY":            "true",
                    "LAUNCH_NOHTTPS":        "false",
                }
                existing_keys = {e.split("=", 1)[0] for e in existing_env if "=" in e}
                for k, v in kdenlive_env.items():
                    if k not in existing_keys:
                        existing_env.append(f"{k}={v}")
                create_kwargs["environment"] = existing_env
                create_kwargs["shm_size"] = create_kwargs.get("shm_size") or (1 * 1024 * 1024 * 1024)
                if os.path.exists("/dev/dri"):
                    create_kwargs["devices"] = (create_kwargs.get("devices") or []) + ["/dev/dri:/dev/dri:rwm"]
        except Exception as e:
            _emit(f"[DockerCreate] kdenlive inject warn: {e}", 20)
        # >>> IMPORTANT: pass primary_net so container is NOT on default 'bridge'
        c = cli.containers.create(**create_kwargs)

        # >>> Attach any extra networks (best-effort)
        for n in extra_nets:
            try:
                cli.networks.get(n).connect(c)
            except Exception as en:
                print(f"DockerCreate: extra network connect failed: {n}: {en}")

        print(f"DockerCreate: created container id={c.short_id}")
        try:
            _refresh_system_used()
        except Exception:
            pass
        return 0

    except APIError as e:
        expl = getattr(e, "explanation", None) or str(e)
        try:
            body = e.response.json() if getattr(e, "response", None) is not None else {}
        except Exception:
            body = {}
        print("DockerCreate APIError:", expl, "| body:", body)
        return -2
    except Exception as e:
        print("DockerCreate Exception:", repr(e))
        traceback.print_exc()
        return -3

def DockerStart(name, cmd, cmd_id):
    _emit(f"[DockerStart][{cmd_id}] begin name={name}", 20)

    try:
        cli = _client()
    except Exception as e:
        _emit(f"[DockerStart][{cmd_id}] _client() failed: {repr(e)}", 20)
        return -2

    # get container
    try:
        c = cli.containers.get(name)
    except docker.errors.NotFound:
        _emit(f"[DockerStart][{cmd_id}] get({name!r}) -> NotFound", 20)
        return -11
    except docker.errors.APIError as e:
        expl = getattr(e, "explanation", "") or str(e)
        _emit(f"[DockerStart][{cmd_id}] get APIError: {expl}", 20)
        return -1
    except Exception as e:
        _emit(f"[DockerStart][{cmd_id}] get unexpected: {repr(e)}", 20)
        return -2

    # pre snapshot
    try: c.reload()
    except Exception: pass
    pre = _snap(c)
    _emit(f"[DockerStart][{cmd_id}] pre status={pre['status']} running={pre['running']} "
          f"pid={pre['pid']} ports={pre['ports']} nets={pre['nets']}", 20)

    # already running
    if pre["running"] or pre["status"] == "running":
        _emit(f"[DockerStart][{cmd_id}] already running; no-op", 20)
        try:
            _db_set_state(name, STATE_RUNNING)
            _refresh_system_used()
        except Exception as e:
            _emit(f"[DockerStart][{cmd_id}] DB/refresh no-op: {repr(e)}", 20)
        return 0

    # prefer HostConfig.PortBindings; fallback to NetworkSettings.Ports
    def _ports_from_info(_info):
        hb = (_info.get("HostConfig") or {}).get("PortBindings") or {}
        out = {}
        try:
            # hb keys look like '8000/tcp', values are lists of {"HostIp":"", "HostPort":"5456"}
            for ckey, lst in hb.items():
                if not lst:
                    continue
                hp = lst[0].get("HostPort")
                if hp:
                    out[ckey] = int(hp) if str(hp).isdigit() else hp
            if out:
                return out
        except Exception:
            pass
        # fallback to NetworkSettings view (works even for stopped containers usually)
        return _extract_ports(_info)

    # -------- LEGACY FIX / SELF-HEAL --------
    try:
        info = c.attrs
        hostcfg = info.get("HostConfig") or {}
        mounts_list = info.get("Mounts") or []
        tmpfs_cfg = hostcfg.get("Tmpfs") or {}

        # detect bad /proc/partitions bind and missing sysfs masks
        has_bad_proc_bind = any((m.get("Destination") == "/proc/partitions"
                                 and m.get("Type") == "bind") for m in mounts_list)
        missing_sys_masks = not all(p in tmpfs_cfg for p in ("/sys/block",
                                                             "/sys/class/block",
                                                             "/sys/devices/virtual/block"))
        kdenlive_wrong_https_port = False
        try:
            image_name = (info.get("Config") or {}).get("Image") or ""
            if _is_kdenlive_image_name(image_name):
                current_port_bind = _ports_from_info(info)
                normalized = _force_single_host_port_binding(current_port_bind, "3001/tcp") or {}
                kdenlive_wrong_https_port = normalized != (current_port_bind or {})
        except Exception:
            kdenlive_wrong_https_port = False

        fix_needed = has_bad_proc_bind or missing_sys_masks or kdenlive_wrong_https_port

        if fix_needed:
            from docker.types import Mount

            _emit(f"[DockerStart][{cmd_id}] legacy config detected "
                  f"(bad_proc={has_bad_proc_bind}, missing_sys_masks={missing_sys_masks}, "
                  f"kdenlive_wrong_https_port={kdenlive_wrong_https_port}) — repairing by recreate", 20)

            # capture config to recreate
            image        = (info.get("Config") or {}).get("Image")
            env          = (info.get("Config") or {}).get("Env")
            cmd_cfg      = (info.get("Config") or {}).get("Cmd")
            entrypoint   = (info.get("Config") or {}).get("Entrypoint")
            working_dir  = (info.get("Config") or {}).get("WorkingDir")
            labels       = (info.get("Config") or {}).get("Labels") or {}
            restart_pol  = hostcfg.get("RestartPolicy") or {"Name": "unless-stopped"}
            net_mode     = hostcfg.get("NetworkMode") or None
            port_bind    = _ports_from_info(info)
            if _is_kdenlive_image_name(image):
                port_bind = _force_single_host_port_binding(port_bind, "3001/tcp")
            limits       = _host_config_limits(info)
            volumes      = _gather_existing_binds(info)  # dict {src: {bind:dst,mode:..}}

            # drop any legacy proc bind from the volumes dict
            vols_clean = {src: cfg for src, cfg in volumes.items()
                          if cfg.get("bind") != "/proc/partitions"}

            # build new tmpfs masks
            tmpfs_masks = {
                "/sys/block": "rw,nosuid,nodev,size=1m",
                "/sys/class/block": "rw,nosuid,nodev,size=1m",
                "/sys/devices/virtual/block": "rw,nosuid,nodev,size=1m",
            }

            # selective lsblk exposure: find host_path bound to CONTAINER_DATA_MOUNT
            extra_mounts = []
            try:
                host_path = None
                for src, cfg in vols_clean.items():
                    if cfg.get("bind") == CONTAINER_DATA_MOUNT:
                        host_path = src; break
                if host_path and os.path.isdir(host_path):
                    # determine loop device for that mount
                    fm = subprocess.run(["findmnt", "-no", "SOURCE", host_path],
                                        text=True, capture_output=True, check=False)
                    srcdev = (fm.stdout or "").strip()
                    m = re.match(r"/dev/(loop\d+)", srcdev or "")
                    if m:
                        loop_dev = m.group(1)
                        sys_block_path = f"/sys/block/{loop_dev}"
                        if os.path.isdir(sys_block_path):
                            extra_mounts.append(Mount(type="bind",
                                                      source=sys_block_path,
                                                      target=f"/sys/block/{loop_dev}",
                                                      read_only=True))
                        # also expose /sys/dev/block/<maj:min>
                        try:
                            st = os.stat(f"/dev/{loop_dev}")
                            maj = os.major(st.st_rdev);  minr = os.minor(st.st_rdev)
                            mm_path = f"/sys/dev/block/{maj}:{minr}"
                            if os.path.exists(mm_path):
                                extra_mounts.append(Mount(type="bind",
                                                          source=mm_path,
                                                          target=mm_path,
                                                          read_only=True))
                        except Exception as e:
                            _emit(f"[DockerStart][{cmd_id}] maj:min expose warn: {e}", 20)
            except Exception as e:
                _emit(f"[DockerStart][{cmd_id}] selective lsblk exposure warn: {e}", 20)

            # security opts; preserve existing if any
            secopts = hostcfg.get("SecurityOpt") or []
            if "no-new-privileges" not in secopts:
                secopts = list(secopts) + ["no-new-privileges"]

            # prepare args for create()
            create_kwargs = dict(
                image=image,
                name=name,
                detach=False,  # we'll start explicitly below
                environment=env,
                command=cmd_cfg,
                entrypoint=entrypoint,
                working_dir=working_dir,
                labels=labels,
                network=net_mode if net_mode and net_mode != "default" else None,
                restart_policy=restart_pol,
                ports=port_bind or None,
                volumes=vols_clean or None,
                mounts=extra_mounts or None,
                security_opt=secopts,
                **limits
            )

            # stop & remove old, recreate new with fixed mounts
            try:
                c.stop(timeout=5)
            except Exception:
                pass
            try:
                c.remove(v=True, force=True)
            except Exception:
                pass

            # inject tmpfs masks
            create_kwargs["tmpfs"] = tmpfs_masks

            _emit(f"[DockerStart][{cmd_id}] recreating container with fixed mounts...", 20)

            # --- Archiware: inject tape devices on recreate ---
            try:
                devs = _archiware_devices_for_create(info)  # list of "host:container:rwm"
                if devs:
                    create_kwargs["devices"] = (create_kwargs.get("devices") or []) + devs
                    create_kwargs["privileged"] = True
                    _emit(f"[DockerStart][{cmd_id}] archiware devices added: {devs}", 20)
            except Exception as e:
                _emit(f"[DockerStart][{cmd_id}] archiware inject warn: {e}", 20)

            # Ubuntu: preserve NET_ADMIN + tun on restart
            try:
                img_lower = str((info.get("Config") or {}).get("Image") or "").lower()
                if any(tok in img_lower for tok in ("ubuntu",)):
                    _emit(f"[DockerStart][{cmd_id}] ubuntu image: re-applying NET_ADMIN + tun", 20)
                    create_kwargs["privileged"] = True
                    create_kwargs["cap_add"] = (create_kwargs.get("cap_add") or []) + ["NET_ADMIN", "SYS_MODULE"]
                    create_kwargs["sysctls"] = {"net.ipv4.conf.all.src_valid_mark": "1"}
                    if os.path.exists("/dev/net/tun"):
                        create_kwargs["devices"] = (create_kwargs.get("devices") or []) + ["/dev/net/tun:/dev/net/tun:rwm"]
            except Exception as e:
                _emit(f"[DockerStart][{cmd_id}] ubuntu inject warn: {e}", 20)

# Kdenlive: re-apply display/audio env on restart
            try:
                img_lower = str((info.get("Config") or {}).get("Image") or "").lower()
                if any(tok in img_lower for tok in ("kdenlive",)):
                    _emit(f"[DockerStart][{cmd_id}] kdenlive image: re-applying display/audio env", 20)
                    existing_env = list(create_kwargs.get("environment") or [])
                    kdenlive_env = {
                        "LIBGL_ALWAYS_SOFTWARE": "1",
                        "MLT_NO_VAAPI":          "1",
                        "GALLIUM_DRIVER":        "llvmpipe",
                        "SDL_VIDEODRIVER":       "offscreen",
                        "XDG_RUNTIME_DIR":       "/run/user/911",
                        # Selkies-based Kdenlive requires HTTPS for WebCodecs/audio.
                        "HTTPS_ONLY":            "true",
                        "LAUNCH_NOHTTPS":        "false",
                    }
                    existing_keys = {e.split("=", 1)[0] for e in existing_env if "=" in e}
                    for k, v in kdenlive_env.items():
                        if k not in existing_keys:
                            existing_env.append(f"{k}={v}")
                    create_kwargs["environment"] = existing_env
                    create_kwargs["shm_size"] = create_kwargs.get("shm_size") or (1 * 1024 * 1024 * 1024)
                    if os.path.exists("/dev/dri"):
                        create_kwargs["devices"] = (create_kwargs.get("devices") or []) + ["/dev/dri:/dev/dri:rwm"]
            except Exception as e:
                _emit(f"[DockerStart][{cmd_id}] kdenlive inject warn: {e}", 20)
            c = cli.containers.create(**create_kwargs)

            # (re)attach to additional user networks if any
            try:
                nets = (info.get("NetworkSettings") or {}).get("Networks") or {}
                extra_nets = [n for n in nets.keys()
                              if n and n not in (None, "", "bridge", "host", "none")
                              and n != (net_mode or "")]
                for n in extra_nets:
                    try:
                        cli.networks.get(n).connect(c)
                    except Exception as en:
                        _emit(f"[DockerStart][{cmd_id}] extra network connect failed: {n}: {en}", 20)
            except Exception:
                pass
    except Exception as e:
        _emit(f"[DockerStart][{cmd_id}] self-heal check failed (continuing): {repr(e)}", 20)

    # ---- Reconcile networks to match DB exactly (adds + removes) ----
    try:
        info = c.attrs
        # What the container currently has (works for stopped)
        existing = list(((info.get("NetworkSettings") or {}).get("Networks") or {}).keys())
        existing = [n for n in existing if n]

        # What the GUI/DB says this VM should have
        desired = _desired_networks_for_vm(name)

        unmanaged = {"bridge", "host", "none"}
        existing_clean = [n for n in existing if n not in unmanaged]
        desired_clean  = [n for n in desired if n not in unmanaged]

        # Set differences
        to_connect    = [n for n in desired_clean  if n not in existing_clean]
        to_disconnect = [n for n in existing_clean if n not in desired_clean]

        _emit(f"[DockerStart][{cmd_id}] net reconcile:"
              f" existing={existing_clean} desired={desired_clean}"
              f" → connect={to_connect} disconnect={to_disconnect}", 20)

        cli = _client()

        # Disconnect removed nets first (safe while stopped)
        for n in to_disconnect:
            try:
                cli.networks.get(n).disconnect(c, force=True)
                _emit(f"[DockerStart][{cmd_id}] disconnected '{n}'", 20)
            except Exception as e:
                _emit(f"[DockerStart][{cmd_id}] disconnect '{n}' failed: {e}", 30)

        # Connect new nets
        for n in to_connect:
            try:
                cli.networks.get(n).connect(c)
                _emit(f"[DockerStart][{cmd_id}] connected '{n}'", 20)
            except Exception as e:
                _emit(f"[DockerStart][{cmd_id}] connect '{n}' failed: {e}", 30)

        # If nothing changed, say so clearly
        if not to_connect and not to_disconnect:
            _emit(f"[DockerStart][{cmd_id}] networks already up-to-date", 20)

    except Exception as e:
        _emit(f"[DockerStart][{cmd_id}] reconcile nets warn: {repr(e)}", 30)
    # try start
    try:
        c.start()
    except docker.errors.APIError as e:
        expl = (getattr(e, "explanation", "") or str(e)).strip()
        _emit(f"[DockerStart][{cmd_id}] start APIError: {expl}", 20)
        low = expl.lower()
        if "already running" in low:
            try:
                _db_set_state(name, STATE_RUNNING)
                _refresh_system_used()
            except Exception as ee:
                _emit(f"[DockerStart][{cmd_id}] DB/refresh after APIError-noop: {repr(ee)}", 20)
            return 0
        if "port is already allocated" in low:
            return -12
        if "network" in low and "not found" in low:
            return -13
        return -1
    except Exception as e:
        _emit(f"[DockerStart][{cmd_id}] start unexpected: {repr(e)}", 20)
        return -2

    # post snapshot
    try: c.reload()
    except Exception: pass
    post = _snap(c)
    _emit(f"[DockerStart][{cmd_id}] post status={post['status']} running={post['running']} "
          f"pid={post['pid']} ports={post['ports']} nets={post['nets']}", 20)

    if not (post["running"] or post["status"] == "running"):
        try:
            raw = c.logs(tail=120)
            tail = raw.decode("utf-8","ignore") if isinstance(raw,(bytes,bytearray)) else str(raw)
        except Exception as le:
            tail = f"<log-read-error: {repr(le)}>"
        _emit(f"[DockerStart][{cmd_id}] not running; exit={post.get('exit_code')} "
              f"error={post.get('error')!r}\n{tail}", 20)
        return -1

    try:
        _db_set_state(name, STATE_RUNNING)
        _refresh_system_used()
    except Exception as e:
        _emit(f"[DockerStart][{cmd_id}] DB/refresh after start: {repr(e)}", 20)

    _emit(f"[DockerStart][{cmd_id}] SUCCESS", 20)
    return 0

def DockerStop(name, cmd, cmd_id):
    try:
        c = _client().containers.get(name)
        c.stop()
        _db_set_state(name, STATE_STOPPED)
        _refresh_system_used()
        return 0
    except Exception as e:
        print(f"DockerStop error: {e}")
        return -1


def _db_delete_veth_for_vm(vm_name: str, cmd_id: str = "UI") -> int:
    """
    Delete veth_port rows for a VM/container (e.g. 'ubuntu01-eth0').

    We assume the naming convention '<vm_name>-ethX'.
    """
    vm_name = (vm_name or "").strip()
    if not vm_name:
        return 0

    try:
        conn = sqlite3.connect(DB_PATH)
        conn.text_factory = str
        c = conn.cursor()

        # Only rows like 'ubuntu01-eth0', 'ubuntu01-eth1', ...
        pattern = f"{vm_name}-eth%"
        c.execute("DELETE FROM veth_port WHERE name LIKE ?", (pattern,))
        deleted = c.rowcount or 0
        conn.commit()
        c.close()
        conn.close()

        _log_cleanup(
            f"[DockerDelete][{cmd_id}] deleted {deleted} veth_port rows for vm={vm_name}",
            20
        )
        return deleted
    except Exception as e:
        _log_cleanup(
            f"[DockerDelete][{cmd_id}] veth_port cleanup warn for vm={vm_name}: {e}",
            30
        )
        return -1

def DockerDelete(
    name: str,
    cmd: str,
    cmd_id: str,
    keep_backups: bool = False,
    keep_snapshots: bool = False,
) -> int:
    """
    Delete Docker container + its disk image.

    keep_backups:
        True  -> leave myBackups rows and backup tar.gz files alone
        False -> delete myBackups rows AND backup files (Option B)

    keep_snapshots:
        True  -> do NOT delete snapshot DB rows; preserve snapshots dir
        False -> delete snapshot DB rows + snapshot files (via vm_root removal)
    """
    try:
        cli = _client()
        try:
            c = cli.containers.get(name)
        except NotFound:
            # Container already gone -> just cleanup disk + DB
            _db_set_state(name, STATE_DELETED)
            _refresh_system_used()

            ok_disk = release_container_disk(name, keep_snapshots=keep_snapshots)
            _log_cleanup(
                f"[DockerDelete][{cmd_id}] cleanup after NotFound: disk={ok_disk}",
                20
            )
            # veth_port cleanup
            try:
                veth_deleted = _db_delete_veth_for_vm(name, cmd_id)
            except Exception as e:
                _log_cleanup(
                    f"[Delete] veth_port cleanup warn (NotFound): {e}",
                    30
                )
            # Backups
            bcount = 0
            if not keep_backups:
                try:
                    bcount = _db_delete_backups_for_vm(name, cmd_id)
                except Exception as e:
                    _log_cleanup(
                        f"[Delete] backup cleanup warn (NotFound): {e}",
                        30
                    )

            # Snapshots (DB only; files handled by release_container_disk)
            scount = 0
            if not keep_snapshots:
                try:
                    scount = _db_delete_snapshots_for_vm(name, cmd_id)
                except Exception as e:
                    _log_cleanup(
                        f"[Delete] snapshot cleanup warn (NotFound): {e}",
                        30
                    )

            _log_cleanup(
                f"[DockerDelete][{cmd_id}] DB cleanup after NotFound: "
                f"backups={bcount}, snaps={scount}",
                20
            )
            return 0

        # Normal delete path
        try:
            c.stop(timeout=5)
        except Exception as e:
            _log_cleanup(f"[DockerDelete][{cmd_id}] stop warn: {e}", 30)
        try:
            c.remove(v=True, force=True)
        except Exception as e:
            _log_cleanup(f"[DockerDelete][{cmd_id}] remove warn: {e}", 30)

        _db_set_state(name, STATE_DELETED)
        _refresh_system_used()

        ok_disk = release_container_disk(name, keep_snapshots=keep_snapshots)
        _log_cleanup(
            f"[DockerDelete][{cmd_id}] cleanup result: disk={ok_disk}",
            20
        )

        # Backups
        bcount = 0
        if not keep_backups:
            try:
                bcount = _db_delete_backups_for_vm(name, cmd_id)
            except Exception as e:
                _log_cleanup(
                    f"[Delete] backup cleanup warn: {e}",
                    30
                )

        # Snapshots (DB only)
        scount = 0
        if not keep_snapshots:
            try:
                scount = _db_delete_snapshots_for_vm(name, cmd_id)
            except Exception as e:
                _log_cleanup(
                    f"[Delete] snapshot cleanup warn: {e}",
                    30
                )

        # vm_storage cleanup always safe
        try:
            _db_clear_vm_storage_for_vm(name, cmd_id)
        except Exception as e:
            _log_cleanup(
                f"[Delete] vm_storage cleanup warn: {e}",
                30
            )

        # veth_port cleanup for this VM
        try:
            veth_deleted = _db_delete_veth_for_vm(name, cmd_id)
        except Exception as e:
            _log_cleanup(
                f"[Delete] veth_port cleanup warn: {e}",
                30
            )

        _log_cleanup(
            f"[DockerDelete][{cmd_id}] DB cleanup result: backups={bcount}, snaps={scount}",
            20
        )
        return 0

    except Exception as e:
        _log_cleanup(f"[DockerDelete][{cmd_id}] UNEXPECTED: {e}", 40)
        return -1

def DockerResize(name, cmd, image, memory, cpus, disk, network, port, cmd_id):
    """
    Resize CPU / Memory (absolute targets) and optionally grow the per-VM disk image
    to an ABSOLUTE size in GB. Refuses disk growth if the storage base lacks space.
    Return 0 on success, -1 on failure, -21 on capacity error.
    """
    import sqlite3

    # --- small local helpers -------------------------------------------------
    def _parse_disk_gb_local(v):
        try:
            if v is None:
                return None
            s = str(v).strip()
            if s == "" or s.lower() == "none":
                return None
            return float(s)
        except Exception:
            return None

    def _vm_disk_from_db(vm_name: str) -> float:
        try:
            conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
            row = cur.execute(
                "SELECT COALESCE(vm_disk_size,0.0) FROM virtualmachine WHERE TRIM(name)=?",
                (vm_name.strip(),)
            ).fetchone()
            cur.close(); conn.close()
            return float(row[0]) if row else 0.0
        except Exception:
            return 0.0

    def _update_vm_disk_in_db(vm_name: str, size_gb: float) -> None:
        try:
            conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
            cur.execute(
                "UPDATE virtualmachine SET vm_disk_size=? WHERE TRIM(name)=?",
                (float(size_gb), vm_name.strip())
            )
            conn.commit()
        except Exception as e:
            print(f"[RESIZE-WARN] DB vm_disk_size update failed: {e}")
        finally:
            try: cur.close()
            except: pass
            try: conn.close()
            except: pass

    # ------------------------------------------------------------------------
    try:
        cli = _client()
        try:
            c = cli.containers.get(name)
        except Exception:
            return -1

        c.reload()

        changed_any = False
        cpu_target_for_db = None
        mem_target_for_db = None

        # --- current limits (from docker HostConfig) ---
        try:
            info = c.attrs
            cur_nano = int((info.get("HostConfig") or {}).get("NanoCpus") or 0)
            cur_mem  = int((info.get("HostConfig") or {}).get("Memory")   or 0)
        except Exception:
            cur_nano = 0
            cur_mem  = 0

        # ========================= MEMORY =========================
        if memory is not None and str(memory).strip() != "":
            try:
                target_vm_mem_gb = max(0.0, float(memory))
                mem_target_for_db = target_vm_mem_gb
                mem_limit = int(target_vm_mem_gb * (1024 ** 3))
                if cur_mem != mem_limit:
                    c.update(mem_limit=mem_limit, memswap_limit=mem_limit)
                    c.reload()
                    print(f"[RESIZE-DBG] set memory to {target_vm_mem_gb} GB")
                    changed_any = True
                else:
                    print("[RESIZE-DBG] memory already at target; no-op")
            except Exception as e:
                print(f"[RESIZE] memory update failed: {e}")
                return -1

        # =========================== CPU ==========================
        if cpus is not None and str(cpus).strip() != "":
            try:
                target_vm_cpu = max(0.001, float(cpus))
                cpu_target_for_db = target_vm_cpu
                target_nano = int(target_vm_cpu * 1_000_000_000)
                if cur_nano != target_nano:
                    if _set_nano_cpus_cli(name, target_vm_cpu):
                        print(f"[RESIZE-DBG] set NanoCPUs={target_nano}")
                        changed_any = True
                    else:
                        if abs(target_vm_cpu - int(target_vm_cpu)) < 1e-6 and int(target_vm_cpu) >= 1:
                            cpuset = "0" if int(target_vm_cpu) == 1 else f"0-{int(target_vm_cpu)-1}"
                            c.update(cpuset_cpus=cpuset); c.reload()
                            print(f"[RESIZE-DBG] set cpuset_cpus={cpuset}")
                            changed_any = True
                        else:
                            return -1
                else:
                    print("[RESIZE-DBG] NanoCPUs already at target; no-op")
            except Exception as e:
                print(f"[RESIZE] cpu update failed: {e}")
                return -1

        # =========================== DISK =========================
        try:
            # Accept absolute target GB (None / "" / "None" → no change)
            disk_gb = _parse_disk_gb_local(disk)
            print(f"[RESIZE-DBG] incoming disk param={disk!r} -> parsed={disk_gb!r}")

            # ---- HARD GUARD: refuse shrink requests (unsafe) ----
            if disk_gb is not None:
                try:
                    cur_disk_db = _vm_disk_from_db(name)
                except Exception:
                    cur_disk_db = 0.0
                if disk_gb < float(cur_disk_db) - 1e-9:
                    print("[RESIZE-ERR] shrink requested; refusing (target "
                          f"{disk_gb:.2f} GB < current {cur_disk_db:.2f} GB)")
                    return -21

            if disk_gb is not None:
                # choose storage base
                base = None
                try:
                    base = _active_storage_base()
                except Exception:
                    pass
                if not base:
                    base = _db_get_docker_storage_base_from_volume()

                if base and os.path.isdir(base):
                    # capacity guard
                    try:
                        cur_disk_db = _vm_disk_from_db(name)
                    except Exception:
                        cur_disk_db = 0.0
                    grow_by = max(0.0, float(disk_gb) - float(cur_disk_db))

                    if grow_by > 0.0:
                        total_b, used_b, free_b = shutil.disk_usage(base)
                        free_gb = free_b / (1024 ** 3)
                        if grow_by > free_gb + 0.01:
                            print(f"[RESIZE] not enough free space on {base}: need +{grow_by:.2f} GB, free {free_gb:.2f} GB")
                            return -21

                    # (optional) run allocator to ensure path layout is sane
                    try:
                        cmdline = [
                            "python3", ALLOCATOR_BIN,
                            "--vm-name", name,
                            "--size-gb", str(disk_gb),
                            "--strategy", "loopback",
                            "--base", base,
                            "--db", DB_PATH,
                            "--owner", "0:0",
                            "--mode", "755",
                        ]
                        print(f"[RESIZE-DBG] allocator: {' '.join(cmdline)}")
                        r = subprocess.run(cmdline, text=True, capture_output=True)
                        print(f"[RESIZE-DBG] allocator rc={r.returncode}")
                        if r.stdout: print(f"[RESIZE-DBG] allocator stdout: {r.stdout.strip()}")
                        if r.stderr: print(f"[RESIZE-DBG] allocator stderr: {r.stderr.strip()}")
                        if r.returncode != 0:
                            print("[RESIZE-WARN] allocator returned non-zero; continuing to direct grow")
                    except Exception as e:
                        print(f"[RESIZE-WARN] allocator exception: {e} (continuing to direct grow)")

                    # Now do the actual grow (stop/unmount/resize/mount/restart)
                    ok = _grow_container_disk(name, float(disk_gb))
                    if not ok:
                        print("[RESIZE-ERR] _grow_container_disk failed")
                        return -1

                    # verify again by reading disk.img size
                    try:
                        vm_root = os.path.join(base, name)
                        img = os.path.join(vm_root, "disk.img")
                        if os.path.isfile(img):
                            final_bytes = os.path.getsize(img)
                            if final_bytes + 4096 < float(disk_gb) * (1024**3):
                                print("[RESIZE-ERR] final img size mismatch after grow")
                                return -1
                    except Exception:
                        pass

                    # Success → persist new absolute size
                    _update_vm_disk_in_db(name, float(disk_gb))
                    changed_any = True
                else:
                    print("[RESIZE-WARN] no storage base available; skip disk grow")

        except Exception as e:
            print(f"[RESIZE-WARN] disk grow exception: {e}")
            return -1

        # =================== persist CPU/Mem targets ==========================
        try:
            _db_update_vm_targets(
                name,
                vcpu=cpu_target_for_db if cpu_target_for_db is not None else None,
                mem_gb=mem_target_for_db if mem_target_for_db is not None else None
            )
        except Exception as e:
            print(f"[RESIZE-WARN] DB update failed: {e}")

        # Recompute system totals (used/total storage from the active base)
        try:
            _refresh_system_used()
        except Exception:
            pass

        if not changed_any and _parse_disk_gb_local(disk) is None:
            print("[RESIZE-DBG] nothing changed; exiting OK")
        return 0

    except Exception:
        return -1

def DockerPause(name, cmd, cmd_id):
    try:
        c = _client().containers.get(name)
        c.pause()
        return 0
    except Exception:
        return -1

def DockerUnPause(name, cmd, cmd_id):
    try:
        c = _client().containers.get(name)
        c.unpause()
        return 0
    except Exception:
        return -1

def DockerList(state=""):
    try:
        cli = _client()
        state = (state or "").strip().lower()
        all_flag = False if state == "running" else True
        _ = cli.containers.list(all=all_flag)
        return 0
    except Exception:
        return -1

def DockerAttachStorage(name, cmd, partition, cmd_id, container_path="/data_new"):
    try:
        if partition is None:
            return -1
        part = str(partition).strip()
        host_path = f"/mnt/p{int(part)}" if part.isdigit() else part
        if not os.path.exists(host_path):
            return -1
        cli = _client()
        c = cli.containers.get(name)
        info = c.attrs
        vols = _gather_existing_binds(info)
        vols[host_path] = {"bind": container_path, "mode": "rw"}
        image = (info.get("Config") or {}).get("Image")
        env = (info.get("Config") or {}).get("Env")
        cmd_cfg = (info.get("Config") or {}).get("Cmd")
        entrypoint = (info.get("Config") or {}).get("Entrypoint")
        working_dir = (info.get("Config") or {}).get("WorkingDir")
        labels = (info.get("Config") or {}).get("Labels") or {}
        port_bindings = _extract_ports(info)
        limits = _host_config_limits(info)
        restart_policy = (info.get("HostConfig") or {}).get("RestartPolicy") or {"Name": "unless-stopped"}
        net_mode = (info.get("HostConfig") or {}).get("NetworkMode") or None
        try: c.stop(timeout=5)
        except Exception: pass
        try: c.remove(v=True, force=True)
        except Exception: pass
        _ = cli.containers.create(
            image=image,
            name=name,
            ports=port_bindings if port_bindings else None,
            environment=env,
            command=cmd_cfg,
            entrypoint=entrypoint,
            working_dir=working_dir,
            labels=labels,
            network=net_mode if net_mode and net_mode != "default" else None,
            restart_policy=restart_policy,
            volumes=vols,
            **limits
        )
        return 0
    except Exception:
        return -1

def _cidr_overlaps_host(cidr_str):
    import ipaddress, subprocess, json
    try:
        net = ipaddress.ip_network(str(cidr_str).strip(), strict=False)
        r = subprocess.run(
            ["ip", "-j", "-4", "addr"],
            capture_output=True, text=True, check=True
        )
        data = json.loads(r.stdout)
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

def _pick_gateway_for_cidr(cidr_str: str, gw_in: Optional[str] = None) -> Optional[str]:
    """Pick a valid gateway inside cidr_str, preferring gw_in if valid."""
    try:
        net = ipaddress.ip_network(str(cidr_str).strip(), strict=False)
    except Exception:
        return None

    if gw_in:
        try:
            gw = ipaddress.ip_address(str(gw_in).strip())
            if gw in net and gw not in (net.network_address, net.broadcast_address):
                return str(gw)
        except Exception:
            pass

    try:
        for host in net.hosts():
            return str(host)
    except Exception:
        pass
    return None

def EnsureDockerNetworkFromArgs(
    name: str,
    cidr: str,
    gw_in: Optional[str] = None,
    cmd_id: str = "UI",
) -> int:
    """
    Ensure a Docker bridge network exists using the CIDR passed from GUI/CCM.

    Returns:
      0   success / idempotent
     -14  invalid CIDR
     -15  CIDR/gateway rejected by policy (overlap, etc.)
     -16  Docker API error from DockerNetworkCreate
    """
    name = (name or "").strip()
    cidr = (cidr or "").strip()
    gw_in = (gw_in or "").strip() if gw_in else None

    if not name:
        _emit("[NET][UI] EnsureDockerNetworkFromArgs: empty name", 30)
        return -21

    if not cidr:
        _emit(f"[NET][UI] EnsureDockerNetworkFromArgs: empty CIDR for '{name}'", 30)
        return -21

    ok, reason = _validate_cidr_policy(cidr)
    if not ok:
        _emit(f"[NET][UI] REFUSED '{name}': {reason}", 30)
        return -15

    gw_final = _pick_gateway_for_cidr(cidr, gw_in)
    if not gw_final:
        _emit(
            f"[NET][UI] REFUSED '{name}': cannot pick gateway for cidr={cidr}, gw={gw_in}",
            30,
        )
        return -15

    rc = DockerNetworkCreate(cidr, gw_final, name, cmd_id=cmd_id)
    if rc == 0:
        _emit(
            f"[NET][UI] ensured docker network '{name}' ({cidr}, gw={gw_final})",
            20,
        )
    else:
        _emit(
            f"[NET][UI] DockerNetworkCreate failed for '{name}' ({cidr}, gw={gw_final}): rc={rc}",
            40,
        )
    return rc

def EnsureDockerNetworkFromDB(name: str, cmd_id: str = "UI") -> int:
    """
    Ensure that the network defined in DB has a matching Docker bridge.

    Returns:
      0   success / idempotent
     -14  invalid CIDR
     -15  CIDR/gateway rejected by policy (overlap, etc.)
     -21  missing DB row / empty CIDR
     -16  Docker API error from DockerNetworkCreate
    """
    name = (name or "").strip()
    if not name:
        _emit("[NET][UI] empty network name", 30)
        return -21

    row = _db_q_one("SELECT cidr FROM network WHERE TRIM(name)=?", (name,))
    if not row:
        _emit(f"[NET][UI] network '{name}' not found in DB", 30)
        return -21

    cidr = (row[0] or "").strip()
    cidr = (cidr or "").strip()
    gw_in =  None

    if not cidr:
        _emit(f"[NET][UI] network '{name}' has empty CIDR", 30)
        return -21

    ok, reason = _validate_cidr_policy(cidr)
    if not ok:
        _emit(f"[NET][UI] REFUSED '{name}': {reason}", 30)
        return -15

    gw_final = _pick_gateway_for_cidr(cidr, gw_in)
    if not gw_final:
        _emit(f"[NET][UI] REFUSED '{name}': cannot pick gateway for cidr={cidr}, gw={gw_in}", 30)
        return -15

    rc = DockerNetworkCreate(cidr, gw_final, name, cmd_id=cmd_id)
    if rc == 0:
        _emit(f"[NET][UI] ensured docker network '{name}' ({cidr}, gw={gw_final})", 20)
    else:
        _emit(f"[NET][UI] DockerNetworkCreate failed for '{name}': rc={rc}", 40)
    return rc

def DockerNetworkDelete(name: str, cmd_id: str = "UI") -> int:
    """
    Delete a Docker network by name.

    Returns:
      0   success or already absent
     -16  Docker API / CLI error
    """
    name = (name or "").strip()
    if not name:
        _emit("[NET][UI] DockerNetworkDelete: empty name", 30)
        return -16

    try:
        # If you are using docker SDK
        import docker
        client = docker.from_env()

        try:
            net = client.networks.get(name)
        except Exception:
            # Not found – treat as success (idempotent delete)
            _emit(f"[NET][UI] docker network '{name}' already absent", 20)
            return 0

        net.remove()
        _emit(f"[NET][UI] deleted docker network '{name}' (cmd_id={cmd_id})", 20)
        return 0

    except Exception as exc:
        _emit(f"[NET][UI] DockerNetworkDelete error for '{name}': {exc}", 40)
        return -16

def DockerNetworkCreate(cidr_in: str, gw_in: str, name: str, cmd_id: str = "NET") -> int:
    """
    Create (or idempotently ensure) a user-defined bridge network.
    Returns:
        0   on success / idempotent OK
       -14 invalid CIDR
       -15 invalid gateway OR CIDR rejected by policy OR subnet mismatch
       -16 Docker API / unexpected error
    """
    import ipaddress, docker, traceback

    def _log(msg):
        try:
            logger.info(msg)
        except Exception:
            pass
        try:
            sprint_docker(msg, 0)
        except Exception:
            try:
                sprint(msg, 0)
            except Exception:
                print(msg)

    _log(f"[DockerNetworkCreate][{cmd_id}] ENTER cidr={cidr_in!r} gw={gw_in!r} name={name!r}")

    # ----- CIDR parse / normalize -----
    try:
        net_if = ipaddress.ip_interface(str(cidr_in).strip())
        subnet = net_if.network
    except Exception as e:
        _log(f"[DockerNetworkCreate][{cmd_id}] invalid CIDR: {e}")
        _log(traceback.format_exc())
        return -14

    cidr_str = subnet.with_prefixlen

    # ----- Try to find existing Docker network by name BEFORE policy -----
    cli = None
    existing = []
    try:
        cli = docker.from_env()
        existing = cli.networks.list(names=[name])
    except Exception as e:
        _log(f"[DockerNetworkCreate][{cmd_id}] list warn (cannot pre-check existing networks): {e}")
        _log(traceback.format_exc())
        # we'll continue anyway and let Docker handle creation later

    # If a network with this name already exists, inspect its subnet
    try:
        for n in existing:
            if n.name != name:
                continue

            # Extract existing subnets from IPAM config
            existing_subnets = []
            try:
                cfgs = (n.attrs or {}).get("IPAM", {}).get("Config", []) or []
                for cfg in cfgs:
                    s = cfg.get("Subnet")
                    if not s:
                        continue
                    try:
                        existing_subnets.append(ipaddress.ip_network(s, strict=False))
                    except Exception:
                        continue
            except Exception as e:
                _log(f"[DockerNetworkCreate][{cmd_id}] warn: failed to inspect IPAM for '{name}': {e}")
                _log(traceback.format_exc())
                existing_subnets = []

            if any(subnet == ex for ex in existing_subnets):
                # Same name, same subnet → idempotent OK
                _log(f"[DockerNetworkCreate][{cmd_id}] FOUND existing '{name}' with matching subnet {cidr_str} — OK")
                return 0

            if existing_subnets:
                # We have a network with this name but a different subnet → config mismatch
                _log(
                    f"[DockerNetworkCreate][{cmd_id}] WARNING: existing network '{name}' has different subnet(s) "
                    f"{existing_subnets}, wanted {cidr_str}"
                )
                return -15
            else:
                # Network exists but no usable subnet info; treat as mismatch
                _log(
                    f"[DockerNetworkCreate][{cmd_id}] WARNING: existing network '{name}' has no IPAM subnet, "
                    f"cannot reconcile with requested {cidr_str}"
                )
                return -15
    except Exception as e:
        _log(f"[DockerNetworkCreate][{cmd_id}] warn examining existing networks: {e}")
        _log(traceback.format_exc())
        # fall through to policy + create

    # ----- Policy: host + restricted overlap guard (only for new networks) -----
    ok, reason = _validate_cidr_policy(cidr_str)
    if not ok:
        _log(f"[DockerNetworkCreate][{cmd_id}] REFUSED: {reason}")
        # treat policy rejection as “bad network settings”
        return -15

    # ----- Gateway validation -----
    try:
        gw_ip = ipaddress.ip_address(str(gw_in).strip())
    except Exception as e:
        _log(f"[DockerNetworkCreate][{cmd_id}] invalid gateway: {e}")
        _log(traceback.format_exc())
        return -15

    if gw_ip == subnet.network_address:
        gw_ip = ipaddress.ip_address(int(subnet.network_address) + 1)
        _log(f"[DockerNetworkCreate][{cmd_id}] auto-fix gateway -> {gw_ip}")

    if gw_ip not in subnet or gw_ip == subnet.broadcast_address:
        _log(f"[DockerNetworkCreate][{cmd_id}] gateway {gw_ip} not in {subnet.with_prefixlen}")
        return -15

    subnet_str, gateway_str = subnet.with_prefixlen, str(gw_ip)

    # ----- Create network if we reach here -----
    try:
        # if cli failed earlier, re-create it now
        if cli is None:
            cli = docker.from_env()

        ipam_pool = docker.types.IPAMPool(subnet=subnet_str, gateway=gateway_str)
        ipam_cfg = docker.types.IPAMConfig(pool_configs=[ipam_pool])

        net = cli.networks.create(
            name=name,
            driver="bridge",
            ipam=ipam_cfg,
            check_duplicate=True,
            attachable=True,
            internal=False,
            options={"com.docker.network.bridge.enable_icc": "true"},
        )
        _log(f"[DockerNetworkCreate][{cmd_id}] CREATED (bridge) id={net.id[:12]} name={name}")
        return 0

    except docker.errors.APIError as e:
        expl = getattr(e, "explanation", None) or str(e)
        _log(f"[DockerNetworkCreate][{cmd_id}] APIError: {expl}")
        _log(traceback.format_exc())
        return -16
    except Exception as e:
        _log(f"[DockerNetworkCreate][{cmd_id}] UNEXPECTED: {repr(e)}")
        _log(traceback.format_exc())
        return -16

def DockerSnapshotCreate(vm_name: str, snapshot_name: str, mode: str = "offline") -> int:
    """
    Create a point-in-time snapshot of <vm_name>'s disk.img as <snapshots>/<name>.img.

    Validation:
      - If snapshot_name is empty => auto-generate "ss-YYYYmmddHHMMSS".
      - Allowed name: 3..63 chars, lowercase letters, digits, dashes only,
        must start/end with alphanumeric.
      - Duplicate names for the same VM are rejected.

    Returns:
      0   -> accepted (worker thread performs the copy)
      -21 -> invalid or duplicate name
      -1  -> other synchronous failure
    """
    try:
        import re

        base, vm_dir, img, mnt, snaps = _vm_base_paths(vm_name)
        if not os.path.isfile(img):
            print(f"[SNAP] disk image missing: {img}")
            return -1

        os.makedirs(snaps, exist_ok=True)

        # --- Resolve VM id for DB writes ---
        parent_VM_id = None
        try:
            conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
            row = cur.execute("SELECT id FROM virtualmachine WHERE TRIM(name)=? LIMIT 1",
                              (vm_name,)).fetchone()
            if row: parent_VM_id = int(row[0])
        finally:
            try: cur.close()
            except: pass
            try: conn.close()
            except: pass

        # --- Normalize / validate name ---
        snap_in = (snapshot_name or "").strip()
        auto_mode = (snap_in == "")
        if auto_mode:
            snap_norm = time.strftime("ss-%Y%m%d%H%M%S")
        else:
            snap_norm = snap_in.lower()

        # Name policy: 3..63, [a-z0-9-], start/end alnum
        valid = (3 <= len(snap_norm) <= 63) and \
                (re.fullmatch(r"[a-z0-9](?:[a-z0-9-]*[a-z0-9])?", snap_norm) is not None)
        if not valid:
            print(f"[SNAP] invalid name: {snap_norm!r}")
            return -21

        # --- Duplicate check: filesystem + DB (belt & suspenders) ---
        target_img = os.path.join(snaps, f"{snap_norm}.img")
        if os.path.exists(target_img):
            print(f"[SNAP] duplicate: file exists {target_img}")
            return -21
        try:
            conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
            if parent_VM_id is not None:
                dup = cur.execute("""
                    SELECT 1 FROM virtualmachine_snapshot
                     WHERE vm_id=? AND TRIM(image_name)=?
                     LIMIT 1
                """, (parent_VM_id, snap_norm)).fetchone()
                if dup:
                    print(f"[SNAP] duplicate: DB row exists for {vm_name}/{snap_norm}")
                    return -21
        finally:
            try: cur.close()
            except: pass
            try: conn.close()
            except: pass

        # --- Insert progress row in DB (best-effort) ---
        last_id = None
        try:
            conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
            cur.execute("""
                INSERT INTO virtualmachine_snapshot
                    (image_name, tag, state, cr_date, edit_date, vm_id, result)
                VALUES(?, 'docker', 0, ?, ?, ?, ?)
            """, (
                snap_norm,
                time.strftime("%Y-%m-%d %H:%M:%S"),
                time.strftime("%Y-%m-%d %H:%M:%S"),
                parent_VM_id,
                "progress..."
            ))
            conn.commit()
            last_id = cur.lastrowid
        except Exception as e:
            # Non-fatal: keep going, but log it
            print(f"[SNAP] DB insert warn: {e}")
        finally:
            try: cur.close()
            except: pass
            try: conn.close()
            except: pass

        # --- Background worker that performs the copy & updates DB ---
        def worker():
            rc = 0
            try:
                # Container control (best-effort)
                was_running = False
                try:
                    cli = _client()
                    c = cli.containers.get(vm_name)
                    c.reload()
                    was_running = (c.status == "running")
                except Exception:
                    c = None

                if mode == "offline" and was_running and c is not None:
                    print(f"[SNAP] stopping {vm_name} for snapshot")
                    try: c.stop(timeout=15)
                    except Exception: pass

                try: subprocess.run(["sync"], check=False)
                except Exception: pass

                tmp_dst = os.path.join(snaps, f"{snap_norm}.img.tmp")
                fin_dst = os.path.join(snaps, f"{snap_norm}.img")

                print(f"[SNAP] copying {img} -> {fin_dst}")
                _cp_reflink_sparse(img, tmp_dst)
                os.replace(tmp_dst, fin_dst)

                # Write metadata JSON
                meta = {
                    "vm": vm_name,
                    "snapshot": snap_norm,
                    "created": time.strftime("%Y-%m-%d %H:%M:%S"),
                    "image": os.path.basename(fin_dst),
                    "size_bytes": os.path.getsize(fin_dst),
                    "vm_meta": _snapshot_meta(vm_name),
                }
                try:
                    with open(os.path.join(snaps, f"{snap_norm}.json"), "w") as f:
                        json.dump(meta, f, indent=2)
                except Exception as me:
                    print(f"[SNAP] meta write warn: {me}")

                # Touch last_local_backup and finalize DB row
                try:
                    conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
                    cur.execute(
                        "UPDATE virtualmachine SET last_local_backup=Date() WHERE TRIM(name)=?",
                        (vm_name,)
                    )
                    if last_id is not None:
                        cur.execute(
                            "UPDATE virtualmachine_snapshot SET result=?, savedPath=?, edit_date=datetime('now') WHERE id=?",
                            ("success", fin_dst, last_id)
                        )
                    conn.commit()
                except Exception as ue:
                    print(f"[SNAP] DB finalize warn: {ue}")
                finally:
                    try: cur.close()
                    except: pass
                    try: conn.close()
                    except: pass

                if mode == "offline" and was_running and c is not None:
                    print(f"[SNAP] restarting {vm_name}")
                    try: c.start()
                    except Exception: pass

            except Exception as e:
                rc = -1
                print(f"[SNAP] worker failed: {e}")
                # best-effort DB failure mark
                try:
                    conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
                    if last_id is not None:
                        cur.execute(
                            "UPDATE virtualmachine_snapshot SET result='failed', edit_date=datetime('now') WHERE id=?",
                            (last_id,)
                        )
                        conn.commit()
                except Exception:
                    pass
                finally:
                    try: cur.close()
                    except: pass
                    try: conn.close()
                    except: pass
            return rc

        t = threading.Thread(target=worker, daemon=True)
        t.start()
        return 0

    except Exception as e:
        print(f"[SNAP] create failed: {e}")
        return -1 

def DockerSnapshotList(vm_name: str) -> List[Dict[str, Any]]:
    """
    Return a list of snapshots for a given VM with basic metadata.

    Each entry will look like:
    {
        "snapshot": "ub-t-ss1",
        "image":    "ub-t-ss1.img",
        "created":  "2025-10-03 17:38:42",   # optional, from .json or file mtime
        "vm_meta":  {...},                   # optional metadata
        "path":     "/mnt/dockervolX/<vm>/snapshots/ub-t-ss1.img"
    }
    """
    out: List[Dict[str, Any]] = []
    try:
        _, _, _, _, snaps_dir = _vm_base_paths(vm_name)
        if not os.path.isdir(snaps_dir):
            return out

        for fn in sorted(os.listdir(snaps_dir)):
            if fn.endswith(".img"):
                snap_name = fn[:-4]  # strip .img
                img_path  = os.path.join(snaps_dir, fn)
                meta_path = os.path.join(snaps_dir, f"{snap_name}.json")

                # start with minimal fields
                entry = {
                    "snapshot": snap_name,
                    "image": fn,
                    "path": img_path
                }

                # try to load extra JSON metadata if present
                try:
                    with open(meta_path) as f:
                        meta = json.load(f)
                        if isinstance(meta, dict):
                            entry.update(meta)
                except Exception:
                    pass

                # if no created date, fall back to file mtime
                if "created" not in entry:
                    try:
                        ts = os.path.getmtime(img_path)
                        entry["created"] = time.strftime(
                            "%Y-%m-%d %H:%M:%S", time.localtime(ts)
                        )
                    except Exception:
                        entry["created"] = None

                out.append(entry)

    except Exception as e:
        print(f"[SNAP] list failed: {e}")

    return out

def DockerSnapshotDelete(vm_name: str, snapshot_name: List[str]) -> int:
    """Delete a snapshot .img (+ .json if present)."""
    try:
        _, _, _, _, snaps = _vm_base_paths(vm_name)
        if isinstance(snapshot_name, str):
            snap_list = [snapshot_name]
        else:
            snap_list = snapshot_name
        
        rc = 0

        for snap in snap_list:
            try:
                snap = _safe_snap_name(snap)
                img = os.path.join(snaps, f"{snap}.img")
                jsn = os.path.join(snaps, f"{snap}.json")
                rc = 0
                if os.path.exists(img):
                    os.remove(img)
                if os.path.exists(jsn):
                    os.remove(jsn)
            except Exception as e:
                print(f"[SNAP] Failed to delete {snap}: {e}")
                rc = -1
        return rc
    except Exception as e:
        print(f"[SNAP] delete failed: {e}")
        return -1

def DockerExportLocal(vm_name: str, mode: str = "offline"):
    """
    Create <saved_path>/<vm>.tar.gz by tarring the mounted 'mnt' dir.
    Writes the archive using sudo so we can create it under root-owned mounts.
    Returns (0, path) on success; (-2, msg) on failure.
    """
    import os, subprocess, datetime, sqlite3

    try:
        # Resolve saved_path and export target <vm>.tar.gz
        conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
        row = cur.execute("""
            SELECT v.saved_path, v.name
            FROM virtualmachine v
            WHERE TRIM(v.name)=?
        """, (vm_name.strip(),)).fetchone()
        cur.close(); conn.close()
        if not row:
            return (-2, f"VM '{vm_name}' not found in DB")
        saved_path, vmname = row
        saved_path = (saved_path or "").rstrip("/")
        if not saved_path or not os.path.isdir(saved_path):
            return (-2, f"saved_path not found: {saved_path}")

        src_dir = saved_path  # typically .../<vm>/mnt
        dst = os.path.join(saved_path, f"{vmname}.tar.gz")

        # If already present, treat as success (idempotent)
        if os.path.isfile(dst):
            return (0, dst)

        # Ensure parent dir exists (with sudo, in case it’s root-owned)
        subprocess.run(["sudo", "/bin/mkdir", "-p", saved_path], check=True)

        # Offline mode: stop container if running (best-effort)
        if mode == "offline":
            try:
                cli = _client()
                c = cli.containers.get(vm_name)
                c.reload()
                if c.status == "running":
                    try: c.stop(timeout=15)
                    except Exception: pass
            except Exception:
                pass

        # Create the tar.gz directly at DEST with sudo (no temp rename needed)
        # Tar the CONTENTS of src_dir (i.e., -C src_dir .)
        cmd = ["sudo", "/bin/tar", "-C", src_dir, "-czf", dst, "."]
        r = subprocess.run(cmd, text=True, capture_output=True)
        if r.returncode != 0:
            return (-2, f"sudo tar failed rc={r.returncode}: {r.stderr.strip() or r.stdout.strip()}")

        return (0, dst)

    except Exception as e:
        return (-2, f"{e}")

def DockerBackupFull(name, backup_name=None, dest=None, cmd_id=None,
                     backupType=None, volume=None, include_disk=True,
                     extra_host_paths=None):
    """
    Full backup (dynamic destination + dynamic data mount detection).
    Returns (0, "Backup started in background") immediately; worker updates DB row to 'done' or 'Error'.

    Assumes modules (os, time, json, hashlib, shutil, tarfile, tempfile, subprocess,
    sqlite3, docker, threading) and constants (DB_PATH) are imported/defined at module top.
    """
    try:
        display_name = backup_name or ""
        vm_id = None
        last_id = None

        # Create initial 'progress...' row so UI shows activity right away
        try:
            with sqlite3.connect(DB_PATH) as conn:
                cur = conn.cursor()
                # Resolve VM ID once
                row = cur.execute(
                    "SELECT id FROM virtualmachine WHERE TRIM(name)=?",
                    (name,)
                ).fetchone()
                if row:
                    vm_id = int(row[0])

                cur.execute("""
                    INSERT INTO myBackups
                        (BackupName, uuid, cr_date, edit_date, local_path, vm_type,
                         VMId, vm_image_size, vm_group_id, state, upload_state,
                         download_path, download_state, backup_time, image_description,
                         backup_server, backup_type, volume)
                    VALUES(?, ?, datetime(), datetime(), '', 'docker',
                           ?, 0, 16, 0, 0,
                           '', 'progress...', datetime(), '',
                           '', ?, ?)
                """, (display_name, (cmd_id or ""), vm_id, (backupType or "full"), (volume or "")))
                conn.commit()
                last_id = cur.lastrowid
        except Exception as e:
            sprint(f"[BACKUP] DB insert warn: {e}", 0)
            return (-1, "DB insert failed")

        def _mark_error(msg: str):
            try:
                with sqlite3.connect(DB_PATH) as conn:
                    cur = conn.cursor()
                    cur.execute("""
                        UPDATE myBackups
                           SET download_state='Error',
                               state=-2,
                               image_description=CASE
                                   WHEN COALESCE(NULLIF(image_description,''), '') = '' THEN ?
                                   ELSE image_description
                               END,
                               edit_date=datetime()
                         WHERE id=?
                    """, (msg, last_id))
                    conn.commit()
            except Exception:
                pass

        def _mark_done(dst_final: str, final_size: int, bserver: str, btype: str, bvol: str):
            try:
                with sqlite3.connect(DB_PATH) as conn:
                    cur = conn.cursor()
                    cur.execute("""
                        UPDATE myBackups
                           SET local_path      = ?,
                               download_path   = ?,
                               download_state  = 'done',
                               backup_time     = COALESCE(backup_time, datetime('now')),
                               vm_type         = COALESCE(NULLIF(vm_type,''), 'docker'),
                               image_description = COALESCE(NULLIF(image_description,''), 'Local full backup'),
                               vm_image_size   = ?,
                               state           = 1,
                               vm_group_id     = COALESCE(vm_group_id, 16),
                               backup_server   = ?,
                               backup_type     = ?,
                               volume          = ?,
                               edit_date       = datetime('now')
                         WHERE id=?
                    """, (dst_final, dst_final, int(final_size), bserver, btype, bvol, last_id))
                    conn.commit()
            except Exception as e:
                sprint(f"[FULL-BACKUP] DB final update warn: {e}", 0)
                _mark_error(f"DB finalize failed: {e}")

        # -------- Worker that performs the real backup --------
        def worker():
            try:
                # 1) Resolve destination (don't mutate inbound 'dest')
                orig_dest = dest
                bserver = None
                dest_override = None

                vol_input = (volume or None)

                # short 'dest' (e.g. 'sanbkpsrvr') counts as volume name
                if (not vol_input) and orig_dest and not str(orig_dest).startswith("/"):
                    vol_input = orig_dest
                    orig_dest = None

                if orig_dest and os.path.isabs(str(orig_dest)):
                    dest_override = orig_dest.rstrip("/")
                    bserver = os.path.basename(dest_override)
                elif vol_input:
                    bserver = str(vol_input).strip()
                    dest_override = f"/mnt/{bserver}"
                else:
                    bserver = None
                    dest_override = None

                # 2) Optional: duplicate backup name validation for this VM
                if display_name:
                    try:
                        with sqlite3.connect(DB_PATH) as conn:
                            cur = conn.cursor()
                            cur.execute("""
                                SELECT COUNT(*) FROM myBackups
                                 WHERE BackupName = ?
                                   AND VMId = (SELECT id FROM virtualmachine WHERE TRIM(name)=?)
                            """, (display_name, name))
                            if (cur.fetchone() or [0])[0] > 1:  # >1 because we already inserted one progress row with same name
                                _mark_error(f"Backup name '{display_name}' already exists for VM '{name}'")
                                return
                    except Exception as e:
                        sprint(f"[BACKUP-VALIDATION] duplicate check warn: {e}", 0)
                        # continue, not fatal

                # 3) Compute paths (no hardcoded default volume)
                paths = _resolve_local_backup_paths(
                    name,
                    prefer_volume_name=None,
                    subdir='backups',
                    dest_override=dest_override,
                    backup_name=display_name
                )

                btype      = (backupType or "full")
                bvol       = (volume or None)
                dst_final  = paths["dst_file"]
                dst_dir    = paths["dst_dir"]
                # vm_id already resolved above
                export_src = paths["src_file"]
                export_dir = paths["src_dir"]

                # 4) Ensure export exists
                if not os.path.isfile(export_src):
                    rc, msg = DockerExportLocal(name, mode="online")
                    if rc != 0:
                        time.sleep(2)
                        rc, msg = DockerExportLocal(name, mode="offline")
                        if rc != 0:
                            _mark_error(f"Export failed: {msg}")
                            return
                    # final check with small delay to avoid races
                    time.sleep(1)
                    if not os.path.isfile(export_src):
                        _mark_error(f"Export not found after creation: {export_src}")
                        return

                # 5) Optional disk image
                disk_img = None
                if include_disk:
                    base = _active_storage_base() or _db_get_docker_storage_base_from_volume()
                    cand = os.path.join(base, name, "disk.img") if base else None
                    if cand and os.path.isfile(cand):
                        disk_img = cand

                tmp_tar = os.path.join(tempfile.gettempdir(), os.path.basename(dst_final))
                tmp_manifest = os.path.join(
                    tempfile.gettempdir(),
                    os.path.basename(dst_final).rsplit(".", 2)[0] + ".tar.manifest.json"
                )

                # 6) Normalize extra host paths
                host_paths = []
                if extra_host_paths:
                    for p in extra_host_paths:
                        p = (p or "").strip()
                        # skip blanks / "None" / non-existent
                        if not p or p.lower() == "none" or not os.path.exists(p):
                            continue
                        # skip if it's the same as the destination or would capture the backup we’re writing
                        try:
                            if 'dst_dir' in locals():
                                rp = os.path.realpath(p)
                                rd = os.path.realpath(dst_dir)
                                # if dst_dir inside p, or p inside dst_dir, skip to avoid recursion
                                if rp == rd or rp.startswith(rd + os.sep) or rd.startswith(rp + os.sep):
                                    continue
                        except Exception:
                            pass
                        host_paths.append(p)

                # 7) Docker meta + discover actual data mount target
                docker_meta = {}
                data_mount_target = None
                try:
                    cli = docker.from_env()
                    c = cli.containers.get(name); c.reload()
                    attrs = c.attrs or {}
                    cfg, hc = (attrs.get("Config") or {}), (attrs.get("HostConfig") or {})
                    docker_meta = {
                        "image_ref": cfg.get("Image"),
                        "resources": {
                            "cpus": (hc.get("NanoCpus") or 0) / 1_000_000_000.0 or None,
                            "memory_gb": (hc.get("Memory") or 0) / (1024**3) or None,
                        },
                        "ports": list((attrs.get("NetworkSettings") or {}).get("Ports") or []),
                        "networks": list(((attrs.get("NetworkSettings") or {}).get("Networks") or {}).keys()),
                        "env": {kv.split("=",1)[0]: kv.split("=",1)[1] if "=" in kv else "" for kv in (cfg.get("Env") or [])}
                    }
                    vm_base = _active_storage_base() or _db_get_docker_storage_base_from_volume()
                    if vm_base:
                        vm_mnt_host = os.path.join(vm_base, name, "mnt")
                        for m in (attrs.get("Mounts") or []):
                            if (m.get("Type") == "bind") and (m.get("Source") == vm_mnt_host):
                                data_mount_target = m.get("Destination")
                                break
                except Exception:
                    pass

                # 8) Build the archive
                with tarfile.open(tmp_tar, "w:gz") as tar:
                    # export
                    tar.add(export_src, arcname="data/export.tar.gz")

                    # disk image
                    if disk_img:
                        tmp_img = os.path.join(tempfile.gettempdir(), f"{name}-disk.img")
                        try:
                            cp_bin = shutil.which("cp") or "/bin/cp"
                            subprocess.run(
                                ["sudo", cp_bin, "--reflink=auto", "--sparse=always", disk_img, tmp_img],
                                check=True, text=True, capture_output=True
                            )
                            tar.add(tmp_img, arcname="image/disk.img")
                        finally:
                            try: os.remove(tmp_img)
                            except: pass

                    # external (attached) host paths
                    for hp in host_paths:
                        safe = hp.lstrip("/").replace("..", "_")
                        arcname = os.path.join("external", safe)
                        try:
                            tar.add(hp, arcname=arcname)
                        except Exception:
                            pass  # best-effort

                    # manifest (+ export hash)
                    def _sha256(p):
                        h = hashlib.sha256()
                        with open(p, "rb") as fh:
                            for chunk in iter(lambda: fh.read(1024*1024), b""):
                                h.update(chunk)
                        return h.hexdigest()

                    export_sz   = os.path.getsize(export_src)
                    export_hash = _sha256(export_src)

                    manifest_vols = []
                    if export_dir and data_mount_target:
                        manifest_vols.append({"type": "bind", "source": export_dir, "dest": data_mount_target})

                    manifest = {
                        "version": 1,
                        "created_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                        "vm": {"id": vm_id, "name": name, "vm_type": "docker"},
                        "source": {
                            "saved_path": export_dir,
                            "export_file": export_src,
                            "image_type": os.path.splitext(export_src)[1].lstrip(".") or "tar.gz",
                        },
                        "archive": {
                            "local_path": None,     # filled after copy
                            "size_bytes": None,     # filled after copy
                            "sha256": None,         # filled after copy
                            "backup_name": display_name or os.path.basename(dst_final),
                        },
                        "docker": docker_meta,
                        "export_digest": {"size_bytes": int(export_sz), "sha256": export_hash},
                        "volumes": manifest_vols or None,
                        "external_paths": host_paths or None,
                        "notes": "Full backup (+ optional disk.img + optional attached paths)"
                    }
                    mb = json.dumps(manifest, indent=2).encode("utf-8")
                    ti = tarfile.TarInfo("config/manifest.json"); ti.size = len(mb)
                    tar.addfile(ti, BytesIO(mb))

                # 9) Copy to final + compute from final
                subprocess.run(["sudo", "mkdir", "-p", dst_dir], check=True, text=True)
                cp_bin = shutil.which("cp") or "/bin/cp"
                subprocess.run(
                    ["sudo", cp_bin, "--reflink=auto", "--sparse=always", tmp_tar, dst_final],
                    check=True, text=True
                )

                # compute from final file
                try:
                    final_size = os.path.getsize(dst_final)
                except Exception:
                    final_size = 0
                try:
                    with open(dst_final, "rb") as fh:
                        final_hash = hashlib.sha256(fh.read()).hexdigest()
                except Exception:
                    final_hash = None

                # write manifest alongside final
                manifest["archive"]["local_path"] = dst_final
                manifest["archive"]["size_bytes"] = int(final_size)
                manifest["archive"]["sha256"]     = final_hash

                with open(tmp_manifest, "w") as mf:
                    json.dump(manifest, mf, indent=2)
                dst_manifest = os.path.join(
                    dst_dir,
                    os.path.basename(dst_final).rsplit(".", 2)[0] + ".tar.manifest.json"
                )
                subprocess.run(["sudo", cp_bin, tmp_manifest, dst_manifest], check=True, text=True)

                # cleanup temps
                try: os.remove(tmp_tar)
                except: pass
                try: os.remove(tmp_manifest)
                except: pass

                # 10) Finalize DB row
                _mark_done(dst_final, final_size, bserver, btype, bvol)

            except subprocess.CalledProcessError as e:
                _mark_error(f"sudo copy/mkdir failed: {e}")
            except Exception as e:
                _mark_error(str(e))

        # Launch async worker
        t = threading.Thread(target=worker, daemon=True)
        t.start()

        return (0, "Backup started in background")

    except subprocess.CalledProcessError as e:
        return (-2, f"sudo copy/mkdir failed: {e}")
    except Exception as e:
        return (-2, f"{e}")
# --- Custom, selectable backup ----------------------------------------------

# assumes top-level imports:
# import os, json, time, tarfile, tempfile, subprocess, hashlib, sqlite3, docker
# from io import BytesIO
def DockerBackupCustom(
    name: str,
    backup_name: str = None,
    dest: str = None,                # may be "sanbkpsrvr" or "/mnt/sanbkpsrvr"
    cmd_id: str = None,
    backupType: str = None,
    volume: str = None,              # optional label
    *,
    include_data_export: bool = True,
    include_disk_image: bool = False,
    include_container_config: bool = True,
    include_bind_mounts: bool = False,
    include_logs: bool = False,
    include_snapshots_meta: bool = False,
    bind_mount_filters: list = None,
    extra_host_paths: list = None,
    log_tail_kb: int = 256
):
    """
    Create a selectable 'custom' backup archive (no hardcoded backup destination).
    Returns: (0, msg) immediately, actual work happens in background thread.
    """

    # --- Prevent duplicate backup name for the same VM ---
    if backup_name and str(backup_name).strip():
        try:
            with sqlite3.connect(DB_PATH) as conn:
                cur = conn.cursor()
                cur.execute("""
                    SELECT COUNT(*) FROM myBackups
                     WHERE BackupName = ?
                       AND VMId = (SELECT id FROM virtualmachine WHERE TRIM(name)=?)
                """, (backup_name, name))
                if (cur.fetchone() or [0])[0] > 0:
                    return (-21, {
                        "status": "fail",
                        "message": f"Backup name '{backup_name}' already exists for VM '{name}'",
                        "code": -21
                    })
        except Exception as e:
            sprint(f"[BACKUP-VALIDATION] warning: duplicate check failed ({e})", 0)

    try:
        display_name = backup_name
        vm_id = None
        last_id = None

        # --- Insert initial "progress" row ---
        try:
            with sqlite3.connect(DB_PATH) as conn:
                cur = conn.cursor()
                row = cur.execute(
                    "SELECT id FROM virtualmachine WHERE TRIM(name)=?",
                    (name,)
                ).fetchone()
                if row:
                    vm_id = int(row[0])

                cur.execute("""
                    INSERT INTO myBackups
                        (BackupName, uuid, cr_date, edit_date, local_path, vm_type,
                         VMId, vm_image_size, vm_group_id, state, upload_state,
                         download_path, download_state, backup_time, image_description,
                         backup_server, backup_type, volume)
                    VALUES(?, ?, datetime(), datetime(), '', 'docker',
                           ?, 0, 16, 0, 0,
                           '', 'progress...', datetime(), '',
                           '', ?, ?)
                """, (display_name, (cmd_id or ""), vm_id, backupType or "custom", volume or ""))
                conn.commit()
                last_id = cur.lastrowid
        except Exception as e:
            sprint(f"[BACKUP] DB insert warn: {e}", 0)
            return (-1, "DB insert failed")

        # ----------------- BACKGROUND WORKER -----------------
        def worker():
            try:
                orig_dest = dest

                # --- Selection options ---
                selections = []
                if include_data_export:      selections.append("data_export")
                if include_disk_image:       selections.append("disk_image")
                if include_container_config: selections.append("container_config")
                if include_bind_mounts:      selections.append("bind_mounts")
                if include_logs:             selections.append("logs")
                if include_snapshots_meta:   selections.append("snapshots_meta")
                if extra_host_paths:         selections.append("extra_host_paths")
                if not selections:
                    raise RuntimeError("No backup components selected")

                # --- Resolve destination ---
                resolved_dest = None
                if orig_dest and str(orig_dest).strip():
                    d = str(orig_dest).strip()
                    resolved_dest = d if d.startswith("/") else f"/mnt/{d}"

                paths = _resolve_local_backup_paths(
                    name,
                    prefer_volume_name=None,
                    subdir='backups',
                    dest_override=resolved_dest,
                    backup_name=display_name
                )
                dst_archive = paths["dst_file"]
                vm_id_local = paths["vm_id"]
                export_src  = paths["src_file"]
                export_dir  = paths["src_dir"]
                dst_dir     = os.path.dirname(dst_archive)

                # --- Ensure export exists (try online then offline) ---
                if include_data_export and not os.path.isfile(export_src):
                    rc, msg = DockerExportLocal(name, mode="online")
                    if rc != 0:
                        time.sleep(2)
                        rc, msg = DockerExportLocal(name, mode="offline")
                        if rc != 0:
                            raise RuntimeError(f"Export failed: {msg}")
                    if not os.path.isfile(export_src):
                        time.sleep(3)
                        if not os.path.isfile(export_src):
                            raise RuntimeError(f"Export not found after creation: {export_src}")

                # --- Disk image ---
                disk_img = None
                if include_disk_image:
                    base = _active_storage_base() or _db_get_docker_storage_base_from_volume()
                    if base:
                        candidate = os.path.join(base, name, "disk.img")
                        if os.path.isfile(candidate):
                            disk_img = candidate

                # --- Ensure destination dir exists (sudo) ---
                subprocess.run(["sudo", "mkdir", "-p", dst_dir], check=True, text=True)

                # --- Inspect container mounts ---
                mounts = []
                try:
                    r = subprocess.run(
                        ["docker", "inspect", name, "--format", "{{json .Mounts}}"],
                        text=True, capture_output=True, check=True
                    )
                    mounts = json.loads((r.stdout or "").strip() or "[]")
                except Exception:
                    mounts = []

                # --- Container metadata ---
                docker_meta = {}
                try:
                    cli = docker.from_env()
                    c = cli.containers.get(name)
                    c.reload()
                    attrs = c.attrs or {}
                    cfg   = (attrs.get("Config") or {})
                    hc    = (attrs.get("HostConfig") or {})
                    docker_meta = {
                        "image_ref": cfg.get("Image"),
                        "resources": {
                            "cpus":      float((hc.get("NanoCpus") or 0) / 1_000_000_000.0) if hc.get("NanoCpus") else None,
                            "memory_gb": float((hc.get("Memory")   or 0) / (1024**3))       if hc.get("Memory")   else None,
                        },
                        "ports":     (attrs.get("NetworkSettings") or {}).get("Ports"),
                        "networks":  list(((attrs.get("NetworkSettings") or {}).get("Networks") or {}).keys()),
                        "env":       {kv.split("=",1)[0]: kv.split("=",1)[1] if "=" in kv else "" for kv in (cfg.get("Env") or [])}
                    }
                except Exception:
                    docker_meta = {}

                # --- SHA256 helper ---
                def _sha256_file(p):
                    h = hashlib.sha256()
                    with open(p, "rb") as f:
                        for chunk in iter(lambda: f.read(1024*1024), b""):
                            h.update(chunk)
                    return h.hexdigest()

                export_digest = None
                if include_data_export:
                    export_digest = {
                        "size_bytes": int(os.path.getsize(export_src)),
                        "sha256": _sha256_file(export_src)
                    }

                # --- Decide which mounts to include ---
                mounts_to_pack = []
                if include_bind_mounts and mounts:
                    vm_root_candidates = set()
                    try:
                        base = _active_storage_base() or _db_get_docker_storage_base_from_volume()
                        if base:
                            vm_root_candidates.add(os.path.join(base, name))
                    except Exception:
                        pass
                    if export_dir:
                        vm_root_candidates.add(export_dir)

                    for m in mounts:
                        if (m or {}).get("Type") != "bind":
                            continue
                        src = (m.get("Source") or "").strip()
                        if not src or not os.path.exists(src):
                            continue
                        allow = False
                        if bind_mount_filters:
                            allow = any(str(src).startswith(p) for p in bind_mount_filters)
                        else:
                            allow = any(str(src).startswith(root) for root in vm_root_candidates)
                        if allow:
                            mounts_to_pack.append({"source": src, "dest": (m.get("Destination") or "")})

                # --- Extra host paths ---
                host_paths = []
                if extra_host_paths:
                    for p in extra_host_paths:
                        p = (p or "").strip()
                        if p and os.path.exists(p):
                            host_paths.append(p)

                # --- Logs (optional) ---
                logs_blob = None
                if include_logs:
                    try:
                        kb = max(1, int(log_tail_kb))
                        out = subprocess.run(["docker", "logs", name], text=True, capture_output=True)
                        data = (out.stdout or "") + ("\n" + (out.stderr or "") if out.stderr else "")
                        if data:
                            tail_bytes = kb * 1024
                            enc = data.encode("utf-8", "ignore")
                            logs_blob = enc[-tail_bytes:]
                    except Exception:
                        logs_blob = None

                # --- Snapshots meta (optional) ---
                snaps_index = None
                if include_snapshots_meta:
                    try:
                        snaps = DockerSnapshotList(name)
                        snaps_index = snaps or []
                    except Exception:
                        snaps_index = []

                # --- Build the archive ---
                with tarfile.open(dst_archive, "w:gz") as tar:
                    if include_data_export and os.path.isfile(export_src):
                        tar.add(export_src, arcname="data/export.tar.gz")

                    disk_status = "skipped"
                    if include_disk_image:
                        if disk_img and os.path.isfile(disk_img):
                            tmp_img = os.path.join(tempfile.gettempdir(), f"{name}-disk.img")
                            try:
                                cp_bin = shutil.which("cp") or "/bin/cp"
                                subprocess.run(
                                    ["sudo", cp_bin, "--reflink=auto", "--sparse=always", disk_img, tmp_img],
                                    text=True, check=True, capture_output=True
                                )
                                tar.add(tmp_img, arcname="image/disk.img")
                                disk_status = "included"
                            except Exception as _e:
                                disk_status = f"error:{_e}"
                            finally:
                                try: os.remove(tmp_img)
                                except Exception: pass
                        else:
                            disk_status = "not_found"

                    if include_container_config and docker_meta:
                        b = json.dumps(docker_meta, indent=2).encode("utf-8")
                        ti = tarfile.TarInfo("config/container.json"); ti.size = len(b)
                        tar.addfile(ti, BytesIO(b))

                    for m in mounts_to_pack:
                        src = m["source"]
                        safe_name = src.lstrip("/").replace("..", "_")
                        arcname = os.path.join("mounts", safe_name)
                        try: tar.add(src, arcname=arcname)
                        except Exception: pass

                    for hp in host_paths:
                        safe = hp.lstrip("/").replace("..", "_")
                        arcname = os.path.join("external", safe)
                        try: tar.add(hp, arcname=arcname)
                        except Exception: pass

                    if logs_blob:
                        ti = tarfile.TarInfo("logs/container.log")
                        ti.size = len(logs_blob)
                        tar.addfile(ti, BytesIO(logs_blob))

                    if snaps_index is not None:
                        b = json.dumps(snaps_index, indent=2).encode("utf-8")
                        ti = tarfile.TarInfo("snapshots/index.json")
                        ti.size = len(b)
                        tar.addfile(ti, BytesIO(b))

                    manifest = {
                        "version": 1,
                        "created_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                        "vm": {"id": vm_id_local, "name": name, "vm_type": "docker"},
                        "archive": {"local_path": dst_archive},
                        "selected": selections,
                        "source": {
                            "saved_path": export_dir,
                            "export_file": export_src if include_data_export else None,
                        },
                        "export_digest": export_digest,
                        "disk_image": {"path": disk_img, "status": disk_status} if include_disk_image else None,
                        "docker": docker_meta if include_container_config else None,
                        "bind_mounts": mounts_to_pack if include_bind_mounts else None,
                        "extra_host_paths": host_paths or None
                    }
                    mb = json.dumps(manifest, indent=2).encode("utf-8")
                    ti = tarfile.TarInfo("config/manifest.json"); ti.size = len(mb)
                    tar.addfile(ti, BytesIO(mb))

                # --- Final DB Update ---
                try:
                    final_size = os.path.getsize(dst_archive)
                except Exception:
                    final_size = 0

                tag = "Custom backup: " + ",".join(selections)
                bserver = os.path.basename(str(resolved_dest).rstrip("/")) if resolved_dest else None
                btype   = backupType or "custom"
                bvol    = volume or None
                display = backup_name or os.path.basename(dst_archive)

                with sqlite3.connect(DB_PATH) as conn:
                    cur = conn.cursor()
                    cur.execute("""
                        UPDATE myBackups
                           SET local_path=?, download_path=?, download_state='done',
                               backup_time=COALESCE(backup_time, datetime('now')),
                               vm_type=COALESCE(NULLIF(vm_type,''),'docker'),
                               image_description=?, vm_image_size=?,
                               state=1, vm_group_id=COALESCE(vm_group_id,16),
                               backup_server=?, backup_type=?, volume=?, edit_date=datetime('now')
                         WHERE id=?
                    """, (dst_archive, dst_archive, tag, int(final_size or 0),
                          bserver, btype, bvol, last_id))
                    conn.commit()

                sprint(f"[CUSTOM-BACKUP] success: {dst_archive}", 1)

            except Exception as e:
                sprint(f"[CUSTOM-BACKUP] Exception: {e}", 0)
                try:
                    with sqlite3.connect(DB_PATH) as conn:
                        cur = conn.cursor()
                        cur.execute("""
                            UPDATE myBackups
                               SET download_state='Error', state=-2,
                                   image_description=COALESCE(NULLIF(image_description,''), ?),
                                   edit_date=datetime('now')
                             WHERE id=?
                        """, (f"Custom backup error: {e}", last_id))
                        conn.commit()
                except Exception as ee:
                    sprint(f"[CUSTOM-BACKUP] DB mark Error failed: {ee}", 0)

        t = threading.Thread(target=worker, daemon=True)
        t.start()
        return (0, "Backup started in background")

    except Exception as e:
        return (-2, f"{e}")

def DockerListContainerVolumes(name: str):
    """
    Returns ONLY volumes explicitly attached via DockerAttachVolume:

      - Host paths under /mnt/<volume_name>
      - Where that volume is linked to this VM in vm_storage

    We EXCLUDE:
      - The root-storage bind (.../<vm>/mnt -> /mnt)
      - System binds (/sys, /proc, /dev)
      - Any other random binds not registered in vm_storage
    """
    try:
        cli = _client()
        c = cli.containers.get(name)
        c.reload()
        attrs  = c.attrs or {}
        mounts = (attrs.get("Mounts") or [])
        state  = "Running" if ((attrs.get("State") or {}).get("Running") is True) else "Stopped"

        # --- Detect VM root dir so we can HIDE root-storage bind ---
        base = None
        try:
            base = _active_storage_base() or _db_get_docker_storage_base_from_volume()
        except Exception:
            base = None

        vm_root = os.path.join(base, name) if base else None
        vm_mnt  = os.path.join(vm_root, "mnt") if vm_root else None

        # --- Build allowlist of host paths from vm_storage <-> volume for THIS VM ---
        allowed_hosts = set()      # e.g. "/mnt/attachbkvol"
        host_to_label = {}         # map host path -> volume name

        try:
            conn = sqlite3.connect(DB_PATH)
            cur  = conn.cursor()
            cur.execute("""
                SELECT v.name
                  FROM vm_storage s
                  JOIN virtualmachine vm ON vm.id = s.vm_id
                  JOIN volume v         ON v.id  = s.volume_id
                 WHERE TRIM(vm.name) = ?
            """, (name,))
            for (vname,) in cur.fetchall():
                host_path = f"/mnt/{vname}"
                allowed_hosts.add(host_path)
                host_to_label[host_path] = vname
            cur.close()
            conn.close()
        except Exception:
            # If DB lookup fails, we simply won't list any attached volumes.
            allowed_hosts = set()
            host_to_label = {}

        items = []
        for m in mounts:
            if (m or {}).get("Type") != "bind":
                continue

            src = (m.get("Source")      or "").strip()
            dst = (m.get("Destination") or "").strip()
            if not src or not dst:
                continue

            # Ignore system binds completely
            if src.startswith(("/sys", "/proc", "/dev")):
                continue

            # Explicitly HIDE root-storage bind (.../<vm>/mnt -> /mnt)
            if vm_mnt and src == vm_mnt:
                continue

            # Only show volumes that were attached via DockerAttachVolume
            # and therefore registered in vm_storage → /mnt/<volume_name>
            if src not in allowed_hosts:
                continue

            label = host_to_label.get(src)
            if not label:
                # Fallback: leaf of host path (after /mnt/)
                if src.startswith("/mnt/") and len(src.split("/")) >= 3:
                    label = src.split("/")[2]
                else:
                    label = os.path.basename(src) or src

            items.append({
                "name":   label,   # e.g. "attachbkvol"
                "host":   src,     # e.g. "/mnt/attachbkvol"
                "target": dst,     # e.g. "/mnt/archiware/vol1"
                "type":   "bind",
                "state":  state,
            })

        return (0, items)

    except Exception as e:
        return (-2, {"status": "fail", "message": f"Exception: {e}"})

# --- Backup delete -----------------------------------------------------------

def _safe_rm_file(p: str) -> Tuple[bool, str]:
    try:
        if not p:
            return (False, "empty path")
        if os.path.isdir(p):
            return (False, "is a directory")
        if not os.path.exists(p):
            return (True, "already missing")

        sudo = shutil.which("sudo")
        if sudo:
            r = subprocess.run([sudo, "rm", "-f", p], text=True, capture_output=True)
            if r.returncode != 0:
                return (False, (r.stderr or r.stdout or "rm failed").strip())
        else:
            os.remove(p)
        return (True, "deleted")
    except Exception as e:
        return (False, str(e))

def _db_vm_id_by_name(vm_name: str) -> Optional[int]:
    try:
        conn = sqlite3.connect(DB_PATH); cur = conn.cursor()
        row = cur.execute("SELECT id FROM virtualmachine WHERE TRIM(name)=?", (vm_name.strip(),)).fetchone()
        cur.close(); conn.close()
        return int(row[0]) if row else None
    except Exception:
        try:
            cur.close(); conn.close()
        except Exception:
            pass
        return None


def DockerBackupDelete(name=None, backup_ids=None, backup_name=None):
    """
    Delete backups by IDs (preferred) or by name (optionally scoped by VM name).
    - name may be None when deleting by IDs.
    Returns: (0, [{"id":..,"name":..,"path":..,"status":"deleted","detail":".."}, ...])
             (-21, {"status":"fail","message":"No matching backups found"})
             (-2,  {"status":"fail","message":"Exception: ..."})
    """
    try:
        deleted = []

        # normalize inputs
        ids = []
        if backup_ids:
            if isinstance(backup_ids, (list, tuple)):
                ids = [int(x) for x in backup_ids if str(x).strip().isdigit()]
            elif isinstance(backup_ids, str):
                s = backup_ids.strip()
                if s.startswith("[") and s.endswith("]"):
                    s = s[1:-1]
                for tok in s.replace(" ", "").split(","):
                    if tok.isdigit():
                        ids.append(int(tok))

        # resolve rows to delete
        rows = []
        conn = sqlite3.connect(DB_PATH); cur = conn.cursor()

        if ids:
            qmarks = ",".join("?" for _ in ids)
            cur.execute(f"SELECT id, VMId, BackupName, local_path FROM myBackups WHERE id IN ({qmarks})", ids)
            rows = cur.fetchall()

        elif backup_name and str(backup_name).strip():
            bname = str(backup_name).strip()
            if name and str(name).strip():
                # scope by VM name if provided
                cur.execute("SELECT id FROM virtualmachine WHERE TRIM(name)=?", (str(name).strip(),))
                vmrow = cur.fetchone()
                if vmrow:
                    vmid = int(vmrow[0])
                    cur.execute(
                        "SELECT id, VMId, BackupName, local_path FROM myBackups WHERE VMId=? AND BackupName=?",
                        (vmid, bname)
                    )
                else:
                    rows = []
            else:
                # global match by name (could delete multiple VMs’ backups with same name)
                cur.execute(
                    "SELECT id, VMId, BackupName, local_path FROM myBackups WHERE BackupName=?",
                    (bname,)
                )
            if not rows:
                rows = cur.fetchall()
        else:
            try:
                cur.close(); conn.close()
            except Exception:
                pass
            return (-21, {"status": "fail", "message": "backup_ids or backup_name is required", "code": -21})

        if not rows:
            try:
                cur.close(); conn.close()
            except Exception:
                pass
            return (-21, {"status": "fail", "message": "No matching backups found", "code": -21})

        # ---------- OPTIONAL SAFEGUARD: enforce VM scope when name is provided ----------
        if name and str(name).strip():
            try:
                cur.execute("SELECT id FROM virtualmachine WHERE TRIM(name)=?", (str(name).strip(),))
                vmrow = cur.fetchone()
                if vmrow:
                    vmid = int(vmrow[0])
                    # keep only backups that belong to this VM
                    rows = [r for r in rows if int(r[1]) == vmid]  # r[1] is VMId
            except Exception:
                pass
            if not rows:
                try:
                    cur.close(); conn.close()
                except Exception:
                    pass
                return (-21, {"status": "fail", "message": "No matching backups found for this VM", "code": -21})
        # -------------------------------------------------------------------------------

        # delete files + rows
        for (bid, _vmid, bname, path) in rows:
            status = "deleted"; detail = "deleted"
            # delete archive + companion manifest best-effort
            try:
                if path and os.path.exists(path):
                    # delete main archive
                    try:
                        os.remove(path)
                    except Exception:
                        try:
                            subprocess.run(["sudo", "rm", "-f", "--", path], check=True, text=True)
                        except Exception as e_rm:
                            status = "partial"; detail = f"db-only (file delete failed: {e_rm})"

                    # delete companion .tar.manifest.json if present
                    try:
                        base = os.path.basename(path)
                        d = os.path.dirname(path)

                        if base.lower().endswith(".tar.gz"):
                            stem = base[:-7]
                        elif base.lower().endswith(".tar"):
                            stem = base[:-4]
                        else:
                            stem = os.path.splitext(base)[0]

                        manifest = os.path.join(d, f"{stem}.tar.manifest.json")
                        if os.path.exists(manifest):
                            try:
                                os.remove(manifest)
                            except Exception:
                                subprocess.run(["sudo", "rm", "-f", "--", manifest], check=False, text=True)
                    except Exception:
                        pass
                else:
                    detail = "db-only (path missing)"
            except Exception as e_del:
                status = "partial"; detail = f"db-only (error: {e_del})"

            # remove DB row
            try:
                cur.execute("DELETE FROM myBackups WHERE id=?", (int(bid),))
                conn.commit()
            except Exception as e_db:
                status = "fail"; detail = f"db delete failed: {e_db}"

            deleted.append({
                "id": int(bid),
                "name": bname,
                "path": path,
                "status": status,
                "detail": detail
            })

        try:
            cur.close(); conn.close()
        except Exception:
            pass

        # success if at least one row was processed
        return (0, deleted)

    except Exception as e:
        return (-2, {"status": "fail", "message": f"Exception: {e}"})
# --- NEW: helpers to faithfully reconstruct docker.create() ------------------

def _merge_secopts(existing, extra):
    out = list(existing or [])
    for s in (extra or []):
        if s and s not in out:
            out.append(s)
    return out

def _convert_port_bindings_for_sdk(info: dict):
    """
    Build docker-py 'ports' mapping that preserves exact host port/IP.
    Returns dict like {'8080/tcp': ('0.0.0.0', 7743)} or {'53/udp': 5353}
    """
    ports_arg = {}
    hostcfg = (info or {}).get("HostConfig") or {}
    hb = hostcfg.get("PortBindings") or {}
    if hb:
        for ckey, lst in hb.items():
            # ckey is like "8080/tcp"
            if isinstance(lst, list) and lst:
                # docker SDK accepts ('ip', port) or int port
                ip = (lst[0] or {}).get("HostIp") or ""
                hp = (lst[0] or {}).get("HostPort") or ""
                if str(ip).strip():
                    try:
                        ports_arg[ckey] = (ip, int(hp)) if str(hp).isdigit() else (ip, str(hp))
                    except Exception:
                        ports_arg[ckey] = (ip, str(hp))
                else:
                    ports_arg[ckey] = int(hp) if str(hp).isdigit() else str(hp)
            else:
                # no host binding; just expose the container port
                ports_arg[ckey] = None
        return ports_arg

    # Fallback: NetworkSettings.Ports (may lose HostIp specificity)
    ns = (info or {}).get("NetworkSettings") or {}
    pmap = ns.get("Ports") or {}
    for ckey, lst in (pmap or {}).items():
        if isinstance(lst, list) and lst:
            hp = (lst[0] or {}).get("HostPort") or ""
            ports_arg[ckey] = int(hp) if str(hp).isdigit() else str(hp)
        else:
            ports_arg[ckey] = None
    return ports_arg

def _mounts_from_inspect(info: dict):
    """
    Return a list[docker.types.Mount] representing BOTH bind and named-volume mounts
    from docker inspect. Keeps read-only flags.
    """
    from docker.types import Mount
    mts = []
    for m in ((info or {}).get("Mounts") or []):
        typ = (m.get("Type") or "").lower()
        dst = m.get("Destination")
        ro  = bool(m.get("RW") is False)  # RW is False => read-only
        if typ == "bind":
            src = m.get("Source")
            if src and dst:
                mts.append(Mount(type="bind", source=src, target=dst, read_only=ro))
        elif typ == "volume":
            name = m.get("Name")
            if name and dst:
                # Keep volume options if present
                opts = {}
                labels = m.get("Labels") or {}
                if labels: opts["labels"] = labels
                mts.append(Mount(type="volume", source=name, target=dst, read_only=ro, **opts))
    return mts

def _create_kwargs_from_inspect(info: dict,
                                *,
                                override_mounts=None,
                                add_mounts=None,
                                extra_devices=None,
                                ensure_secopt=None,
                                tmpfs_masks=None,
                                ports_override=None,
                                name=None):
    """
    Build docker.create(**kwargs) compatible dict from inspect info.
    You can override mounts completely or append to them; pass devices, security opts, etc.
    """
    from docker.types import Ulimit, LogConfig

    cfg     = (info.get("Config") or {})
    hostcfg = (info.get("HostConfig") or {})

    # Base kwargs from Config
    kwargs = dict(
        image        = cfg.get("Image"),
        name         = name or None,
        environment  = cfg.get("Env"),
        command      = cfg.get("Cmd"),
        entrypoint   = cfg.get("Entrypoint"),
        working_dir  = cfg.get("WorkingDir"),
        labels       = (cfg.get("Labels") or {}),
        hostname     = cfg.get("Hostname"),
        user         = cfg.get("User"),
    )

    # Ports: preserve exact bindings
    kwargs["ports"] = ports_override if (ports_override is not None) else _convert_port_bindings_for_sdk(info)

    # HostConfig-ish fields
    # Network
    net_mode = hostcfg.get("NetworkMode") or None
    if net_mode and net_mode != "default":
        kwargs["network"] = net_mode

    # Restart policy
    rp = hostcfg.get("RestartPolicy") or {}
    if rp:
        kwargs["restart_policy"] = rp

    # Resources
    mem = hostcfg.get("Memory") or None
    if mem:
        kwargs["mem_limit"] = int(mem)
    nano = hostcfg.get("NanoCpus") or hostcfg.get("NanoCPUs") or None
    if nano:
        kwargs["nano_cpus"] = int(nano)

    # Log config
    logcfg = hostcfg.get("LogConfig") or {}
    if logcfg and (logcfg.get("Type") or ""):
        try:
            kwargs["log_config"] = LogConfig(type=logcfg.get("Type"), config=(logcfg.get("Config") or {}))
        except Exception:
            kwargs["log_config"] = logcfg  # best effort

    # Ulimits
    if hostcfg.get("Ulimits"):
        ul = []
        for u in hostcfg.get("Ulimits") or []:
            try:
                ul.append(Ulimit(name=u.get("Name"), soft=u.get("Soft"), hard=u.get("Hard")))
            except Exception:
                pass
        if ul: kwargs["ulimits"] = ul

    # Capabilities
    if hostcfg.get("CapAdd"):
        kwargs["cap_add"] = hostcfg.get("CapAdd")
    if hostcfg.get("CapDrop"):
        kwargs["cap_drop"] = hostcfg.get("CapDrop")

    # DNS / hosts / sysctls
    if hostcfg.get("Dns"):        kwargs["dns"] = hostcfg.get("Dns")
    if hostcfg.get("DnsSearch"):  kwargs["dns_search"] = hostcfg.get("DnsSearch")
    if hostcfg.get("ExtraHosts"): kwargs["extra_hosts"] = hostcfg.get("ExtraHosts")
    if hostcfg.get("Sysctls"):    kwargs["sysctls"] = hostcfg.get("Sysctls")

    # IPC / PID / Runtime / ShmSize / Privileged
    if hostcfg.get("IpcMode"):    kwargs["ipc_mode"]  = hostcfg.get("IpcMode")
    if hostcfg.get("PidMode"):    kwargs["pid_mode"]  = hostcfg.get("PidMode")
    if hostcfg.get("Runtime"):    kwargs["runtime"]   = hostcfg.get("Runtime")
    if hostcfg.get("ShmSize"):    kwargs["shm_size"]  = hostcfg.get("ShmSize")
    if hostcfg.get("Privileged"): kwargs["privileged"]= bool(hostcfg.get("Privileged"))

    # Security opts (merge)
    sec = hostcfg.get("SecurityOpt") or []
    if ensure_secopt:
        sec = _merge_secopts(sec, ensure_secopt)
    if sec:
        kwargs["security_opt"] = sec

    # Tmpfs mounts
    tmpfs = hostcfg.get("Tmpfs") or {}
    if tmpfs_masks:
        tmpfs = dict(tmpfs) if tmpfs else {}
        tmpfs.update(tmpfs_masks)
    if tmpfs:
        kwargs["tmpfs"] = tmpfs

    # Devices (merge pass-through)
    devs = hostcfg.get("Devices") or []
    # docker SDK wants list[dict] or list["host:ctr:perm"]; we pass dicts if present
    if extra_devices:
        # Add extra device specs (strings "host:ctr:rwm")
        devs = list(devs) + list(extra_devices)
    if devs:
        kwargs["devices"] = devs

    # Mounts (prefer Mount objects)
    if override_mounts is not None:
        mnts = list(override_mounts)
    else:
        mnts = _mounts_from_inspect(info)
    if add_mounts:
        mnts = list(mnts) + list(add_mounts)
    if mnts:
        kwargs["mounts"] = mnts

    return kwargs

# --- UPDATED: DockerAttachVolume using full-fidelity recreate ----------------

def DockerAttachVolume(name, cmd, cmd_id, vol_id=None, vol_name=None, target=None, mode="rw", mkdir="0"):
    global os, json, sqlite3, time, re
    from docker.types import Mount
    try:
        cli = _client()
        old = cli.containers.get(name)
        info = old.attrs
        hostcfg = info.get("HostConfig") or {}

        # --- Resolve volume path from DB ---
        db = sqlite3.connect(DB_PATH); cur = db.cursor()
        if vol_name:
            cur.execute("SELECT id, name FROM volume WHERE name=?", [vol_name])
        else:
            cur.execute("SELECT id, name FROM volume WHERE id=?", [vol_id])
        row = cur.fetchone(); cur.close(); db.close()
        if not row:
            return (-21, {"status":"fail","message":"Volume not found in DB"})
        vid, vname = row
        host_path = f"/mnt/{vname}"

        if not os.path.exists(host_path):
            if str(mkdir).lower() in ("1","true","yes"):
                os.makedirs(host_path, exist_ok=True)
            else:
                return (-21, {"status":"fail","message":f"Host path {host_path} missing"})

        ro = (str(mode).lower() in ("ro","read-only"))

        # --- Build current mounts from _gather_existing_binds(info) (robust) ---
        #     and compute used targets + idempotency check.
        binds = _gather_existing_binds(info) or {}  # {host: {"bind": dest, "mode": "rw|ro"}}
        used_targets = set()
        existing_mounts = []

        for hp, cfg in binds.items():
            dest = (cfg or {}).get("bind") or ""
            m = (cfg or {}).get("mode") or "rw"
            if not dest:
                continue
            used_targets.add(dest)
            # Drop problematic /sys/dev/block/<maj:min> (colon in path breaks docker create)
            if str(hp).startswith("/sys/dev/block/"):
                continue
            existing_mounts.append(
                Mount(type="bind", source=hp, target=dest, read_only=(m == "ro"))
            )

        # Validation: prevent re-attaching the same host path
        if host_path in binds:
            already = (binds.get(host_path) or {}).get("bind") or f"/mnt/{name}/vol1"
            existing_mode = (binds.get(host_path) or {}).get("mode") or "rw"
            return (-21, {"status":"fail",
                          "message":f"Volume already attached at {already} (mode={existing_mode}). Detach it first or choose another volume.",
                          "code":-21})

        # --- Choose/adjust target (auto-increment if busy) ---
        # Desired scheme:
        #   default      -> /mnt/<name>/vol1
        #   short input  -> "vol3" => /mnt/<name>/vol3
        #   absolute ok  -> "/mnt/ANY/PATH" (used as-is, but still de-duped with suffix)
        if target and str(target).strip():
            t = str(target).strip()
            if not t.startswith("/"):
                # short form like "vol2"
                base = f"/mnt/{name}/{t}"
            else:
                base = os.path.normpath(t)
        else:
            base = f"/mnt/{name}/vol1"

        def _next_free_target(base_path: str, used: set):
            # if free, use it
            if base_path not in used:
                return base_path
            # bump only the numeric suffix or append 2, 3, ...
            m = re.match(r"^(.*?)(\d+)$", base_path)
            if m:
                stem, num = m.group(1), int(m.group(2))
                n = num + 1
                cand = f"{stem}{n}"
                while cand in used:
                    n += 1
                    cand = f"{stem}{n}"
                return cand
            # no numeric suffix → append 2, 3, ...
            n = 2
            cand = f"{base_path}{n}"
            while cand in used:
                n += 1
                cand = f"{base_path}{n}"
            return cand

        final_target = _next_free_target(base, used_targets)

        new_mount = Mount(type="bind", source=host_path, target=final_target, read_only=ro)
        final_mounts = existing_mounts + [new_mount]

        # Preserve exact published ports
        ports_map = _convert_port_bindings_for_sdk(info)
        print(f"[AttachVolume][{cmd_id}] {name}: attaching {host_path} -> {final_target} mode={'ro' if ro else 'rw'}")
        if ports_map:
            print(f"[AttachVolume][{cmd_id}] preserving ports: {ports_map}")

        # Security: ensure no-new-privileges remains (merge)
        ensure_sec = ["no-new-privileges"]

        # Archiware devices (best-effort)
        extra_devs = []
        try:
            extra_devs = _archiware_devices_for_create(info) or []
        except Exception:
            pass

        # Build create kwargs from inspect + overrides
        tmpfs_masks = {
            "/sys/block": "rw,nosuid,nodev,size=1m",
            "/sys/class/block": "rw,nosuid,nodev,size=1m",
            "/sys/devices/virtual/block": "rw,nosuid,nodev,size=1m",
        }
        create_kwargs = _create_kwargs_from_inspect(
            info,
            override_mounts=final_mounts,
            extra_devices=extra_devs,
            ensure_secopt=ensure_sec,
            tmpfs_masks=tmpfs_masks,
            ports_override=ports_map,
            name=f"{name}-attach-{int(time.time())}",
        )
        if extra_devs:
            create_kwargs["privileged"] = True

        # Create new first (safe swap)
        try:
            newc = cli.containers.create(**create_kwargs)
        except Exception as ce:
            return (-2, {"status":"fail","message":f"create failed: {ce}"})

        # Reconnect additional user networks (beyond primary)
        try:
            nets = (info.get("NetworkSettings") or {}).get("Networks") or {}
            primary = hostcfg.get("NetworkMode") or None
            extra_nets = [n for n in nets.keys()
                          if n and n not in ("bridge","host","none") and n != (primary or "")]
            for n in extra_nets:
                try: cli.networks.get(n).connect(newc)
                except Exception: pass
        except Exception:
            pass

        # Swap
        try:
            try: old.stop(timeout=5)
            except Exception: pass
            try: old.remove(v=True, force=True)
            except Exception: pass

            try: newc.rename(name)
            except Exception as re:
                print(f"[AttachVolume][{cmd_id}] rename warn: {re}")

            # newc.start()
        except Exception as se:
            return (-2, {"status":"fail","message":f"start failed: {se}"})

        # DB link
        try:
            db = sqlite3.connect(DB_PATH); cur = db.cursor()
            cur.execute(
                "INSERT OR REPLACE INTO vm_storage(name,state,volume_id,vm_id,cr_date) "
                "SELECT ?,1,id,(SELECT id FROM virtualmachine WHERE TRIM(name)=?),datetime() FROM volume WHERE id=?",
                [vname, name, vid]
            )
            db.commit(); cur.close(); db.close()
        except Exception as e:
            sprint(f"[AttachVolume][{cmd_id}] DB update warn: {e}", 0)

        print(f"[AttachVolume][{cmd_id}] SUCCESS")
        return (0, {"status":"success","message":"Volume attached",
                    "mount":{"host":host_path,"container":final_target,"mode":("ro" if ro else "rw")}})

    except Exception as e:
        return (-2, {"status":"fail","message":f"Exception: {e}"})
# --- UPDATED: DockerDetachVolume with full fidelity too ----------------------

def DockerDetachVolume(name, cmd=None, cmd_id=None, vol_id=None, vol_name=None, target=None):
    import os, json, sqlite3, time
    from docker.types import Mount
    try:
        cli = _client()
        old = cli.containers.get(name)
        info = old.attrs
        hostcfg = (info.get("HostConfig") or {})

        # --- Gather existing binds -> {host_path: {"bind": dest, "mode": "..."}}
        existing_binds = _gather_existing_binds(info) or {}

        # Normalize keys (host paths) with realpath to be tolerant
        norm_binds = {}
        for hp, cfg in existing_binds.items():
            try:
                norm_binds[os.path.realpath(hp)] = cfg
            except Exception:
                norm_binds[hp] = cfg
        existing_binds = norm_binds

        to_remove = None
        vname_for_db = None

        # Prefer an explicit target match (most reliable)
        if target:
            for hp, cfg in existing_binds.items():
                if (cfg or {}).get("bind") == target:
                    to_remove = hp
                    break

        # vol_name fallback
        if not to_remove and vol_name:
            vname_for_db = vol_name.strip()
            want = f"/mnt/{vname_for_db}"
            want_r = os.path.realpath(want)
            if want_r in existing_binds:
                to_remove = want_r
            else:
                # suffix/basename fallback
                for hp in existing_binds.keys():
                    if os.path.basename(hp) == vname_for_db or hp.endswith("/" + vname_for_db):
                        to_remove = hp
                        break

        # vol_id fallback
        if not to_remove and vol_id:
            try:
                db = sqlite3.connect(DB_PATH); cur = db.cursor()
                cur.execute("SELECT name FROM volume WHERE id=?", [int(vol_id)])
                r = cur.fetchone(); cur.close(); db.close()
                if r:
                    vname_for_db = r[0]
                    want = f"/mnt/{vname_for_db}"
                    want_r = os.path.realpath(want)
                    if want_r in existing_binds:
                        to_remove = want_r
                    else:
                        for hp in existing_binds.keys():
                            if os.path.basename(hp) == vname_for_db or hp.endswith("/" + vname_for_db):
                                to_remove = hp
                                break
            except Exception:
                pass

        if not to_remove:
            return (-21, {"status": "fail", "message": "Volume not attached or invalid reference"})

        # Build the new mounts list: keep everything except 'to_remove'
        mounts_list = []
        for hp, cfg in existing_binds.items():
            if hp == to_remove:
                continue
            dest = (cfg or {}).get("bind")
            mode = (cfg or {}).get("mode") or "rw"
            # drop /sys/dev/block/<maj:min> (colon path issue) — container will be fine without it
            if str(hp).startswith("/sys/dev/block/"):
                continue
            ro = (str(mode).lower() in ("ro", "read-only"))
            mounts_list.append(Mount(type="bind", source=hp, target=dest, read_only=ro))

        # Preserve networking
        net_mode = hostcfg.get("NetworkMode") or None
        extra_nets = []
        try:
            nets = (info.get("NetworkSettings") or {}).get("Networks") or {}
            extra_nets = [n for n in nets.keys()
                          if n and n not in ("bridge", "host", "none")
                          and n != (net_mode or "")]
        except Exception:
            extra_nets = []

        # Preserve exact ports (Host IP/Port)
        try:
            ports_arg, port_bindings_arg = _port_bindings_from_info(info)
        except Exception:
            ports_arg, port_bindings_arg = [], {}

        # Other preserved settings
        image       = (info.get("Config") or {}).get("Image")
        env         = (info.get("Config") or {}).get("Env")
        command     = (info.get("Config") or {}).get("Cmd")
        entrypoint  = (info.get("Config") or {}).get("Entrypoint")
        working_dir = (info.get("Config") or {}).get("WorkingDir")
        labels      = (info.get("Config") or {}).get("Labels") or {}
        restart_pol = hostcfg.get("RestartPolicy") or {"Name": "unless-stopped"}
        limits      = _host_config_limits(info)
        tmpfs_masks = {
            "/sys/block": "rw,nosuid,nodev,size=1m",
            "/sys/class/block": "rw,nosuid,nodev,size=1m",
            "/sys/devices/virtual/block": "rw,nosuid,nodev,size=1m",
        }

        # Create the new container first (safe swap)
        temp_name = f"{name}-detach-{int(time.time())}"
        create_kwargs = dict(
            image=image,
            name=temp_name,
            environment=env,
            command=command,
            entrypoint=entrypoint,
            working_dir=working_dir,
            labels=labels,
            network=net_mode if net_mode and net_mode != "default" else None,
            restart_policy=restart_pol,
            mounts=mounts_list,
            tmpfs=tmpfs_masks,
            security_opt=["no-new-privileges"],
            **limits
        )
        # Only set ‘ports’ when we have bindings to preserve (or SDK can error)
        if port_bindings_arg:
            create_kwargs["ports"] = port_bindings_arg

        # Re-inject Archiware devices (if applicable)
        try:
            extra_devs = _archiware_devices_for_create(info)
            if extra_devs:
                create_kwargs["devices"] = extra_devs
                create_kwargs["privileged"] = True
        except Exception:
            pass

        newc = cli.containers.create(**create_kwargs)
        # Reconnect extra networks
        for n in extra_nets:
            try:
                cli.networks.get(n).connect(newc)
            except Exception:
                pass

        # Swap in
        try:
            try: old.stop(timeout=5)
            except Exception: pass
            try: old.remove(v=True, force=True)
            except Exception: pass

            try: newc.rename(name)
            except Exception as e:
                try: newc.remove(v=True, force=True)
                except Exception: pass
                return (-2, {"status": "fail", "message": f"rename failed: {e}"})

            # try: newc.start()
            # except Exception as e:
            #     return (-2, {"status": "fail", "message": f"start failed: {e}"})
        finally:
            pass

        # DB mark detached (best-effort)
        try:
            if vol_name or vol_id:
                db = sqlite3.connect(DB_PATH); cur = db.cursor()
                if vol_name:
                    # cur.execute("""
                    #     UPDATE vm_storage
                    #        SET state=0, edit_date=datetime()
                    #      WHERE volume_id IN (SELECT id FROM volume WHERE TRIM(name)=?)
                    # """, [vol_name.strip()])
                    cur.execute("""
                        DELETE FROM vm_storage
                         WHERE volume_id IN (SELECT id FROM volume WHERE TRIM(name)=?)
                    """, [vol_name.strip()])
                elif vol_id:
                    # cur.execute("""
                    #     UPDATE vm_storage
                    #        SET state=0, edit_date=datetime()
                    #      WHERE volume_id=?
                    # """, [int(vol_id)])
                    cur.execute("""
                        DELETE FROM vm_storage
                         WHERE volume_id=?
                    """, [int(vol_id)])
                db.commit(); cur.close(); db.close()
        except Exception as e:
            sprint(f"[DetachVolume][{cmd_id}] DB update warn: {e}", 0)

        return (0, {"status": "success",
                    "message": "Volume detached",
                    "removed": [{"host": to_remove}]})

    except Exception as e:
        return (-2, {"status": "fail", "message": f"Exception: {e}"})
