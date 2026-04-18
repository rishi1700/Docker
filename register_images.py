#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import argparse
import sqlite3
from pathlib import Path
import subprocess
import os
import sys
from typing import Optional, Tuple, List, Set
import string
import logging
import time
import shutil
import re

DEFAULT_DB = "/mnt/data/quantumDB.db"

# ---------------- logging ----------------
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
log = logging.getLogger("register-images")

# ---------------- friendly name mapping ----------------
def strip_pack_suffix(basename: str) -> str:
    stem = basename
    for suf in (".tar.gz", ".tgz", ".tar", ".tar.zst", ".tar.xz"):
        if stem.endswith(suf):
            stem = stem[: -len(suf)]
            break
    return stem

# map legacy/old repos to canonical names
_DISPLAY_NAME_OVERRIDES = {
    "sanuyi-archiver": "archiware",   # e.g., sanuyi-archiver -> archiware
}

def _apply_overrides_to_ref(ref: str) -> str:
    """
    Apply repo overrides to a docker ref and force lowercase.
    Handles optional registry prefix (e.g. 'myreg:5000/ns/repo:tag').
    """
    if not ref:
        return ref
    if "/" in ref:
        prefix, last = ref.rsplit("/", 1)
    else:
        prefix, last = "", ref
    parts = last.split(":", 1)
    repo = parts[0]
    tag = parts[1] if len(parts) > 1 else "latest"
    repo = _DISPLAY_NAME_OVERRIDES.get(repo, repo)
    out = f"{repo}:{tag}"
    return (f"{prefix}/{out}" if prefix else out).lower()

def friendly_name_from_file(basename: str) -> str:
    """
    Produce canonical docker-style image name (repo:tag), lowercase, no spaces,
    with repo overrides applied.
    """
    stem = strip_pack_suffix(basename)
    ref = ref_from_file_name(stem)
    if not ref:
        return (stem.replace("_", "-") + ":latest").lower()
    return _apply_overrides_to_ref(ref)

# ---------------- docker ref helpers ----------------
_ALLOWED_REPO = set(string.ascii_lowercase + string.digits + "._-/")
_ALLOWED_TAG  = set(string.ascii_lowercase + string.digits + "._-")

def norm_repo(s: str) -> str:
    s = (s or "").lower()
    return "".join(ch if ch in _ALLOWED_REPO else "-" for ch in s).strip("-")

def norm_tag(s: Optional[str]) -> str:
    t = (s or "latest").lower()
    t = "".join(ch if ch in _ALLOWED_TAG else "-" for ch in t).strip("-")
    return t or "latest"

def make_ref(repo: str, tag: Optional[str], repo_prefix: str = "") -> str:
    repo = norm_repo(repo)
    tag  = norm_tag(tag)
    ref = f"{repo}:{tag}"
    if repo_prefix:
        rp = repo_prefix.rstrip("/")
        ref = f"{rp}/{ref}"
    return ref

def ref_from_file_name(file_name: str, repo_prefix: str = "") -> Optional[str]:
    """
    e.g. 'sanuyi_archiver_1.0.3' -> 'sanuyi-archiver:1.0.3'
         'mysql_8.0'             -> 'mysql:8.0'
         'nginx_stable'          -> 'nginx-stable:latest'
    """
    if not file_name:
        return None
    stem = file_name.strip()
    toks = stem.split("_")
    if len(toks) >= 2:
        tag = toks[-1]
        repo = "-".join(toks[:-1])
        return make_ref(repo, tag, repo_prefix)
    else:
        return make_ref(stem, "latest", repo_prefix)


def alias_refs(image_name: str, file_name: str, repo_prefix: str = "") -> List[str]:
    """
    Return exactly one canonical ref derived from file_name, with overrides applied,
    all lowercase, suitable for tagging/pulling.
    """
    can_ref = ref_from_file_name(file_name, repo_prefix=repo_prefix)
    can_ref = _apply_overrides_to_ref(can_ref) if can_ref else None
    return [can_ref] if can_ref else []

# ---------------- locate images dir ----------------
def find_images_dir(root: Path) -> Path:
    root = root.resolve()
    if root.is_file():
        raise FileNotFoundError(f"{root} is a file, expected a directory.")

    candidates: List[Path] = []

    if list(root.glob("*.tar.gz")) or list(root.glob("*.tgz")) or list(root.glob("*.tar")) or \
       list(root.glob("*.tar.zst")) or list(root.glob("*.tar.xz")):
        candidates.append(root)

    images = root / "images"
    if images.is_dir() and (list(images.glob("*.tar.gz")) or list(images.glob("*.tgz")) or list(images.glob("*.tar")) or
                            list(images.glob("*.tar.zst")) or list(images.glob("*.tar.xz"))):
        candidates.append(images)

    for d in root.iterdir():
        if not d.is_dir():
            continue
        maybe = d / "images"
        if maybe.is_dir() and (list(maybe.glob("*.tar.gz")) or list(maybe.glob("*.tgz")) or list(maybe.glob("*.tar")) or
                               list(maybe.glob("*.tar.zst")) or list(maybe.glob("*.tar.xz"))):
            candidates.append(maybe)

    if len(candidates) > 1:
        raise RuntimeError(f"Ambiguous images dirs found (multiple candidates): {', '.join(str(c) for c in candidates)}. Specify a more precise path.")
    if not candidates:
        raise FileNotFoundError(f"Could not find an images/ folder with .tar.gz/.tgz/.tar under: {root}")

    return candidates[0]

# ---------------- DB helpers ----------------
def get_group_id(conn: sqlite3.Connection, group_id: Optional[int], group_name: Optional[str]) -> int:
    """
    Resolve group id. Priority:
      1) explicit --group-id
      2) lookup by --group-name
      3) fallback to Docker group name
    """
    if group_id is not None:
        return int(group_id)
    name = (group_name or "SanuyiRepo").strip()
    cur = conn.execute("SELECT id FROM vm_group WHERE lower(group_name)=lower(?) LIMIT 1", (name,))
    row = cur.fetchone()
    if row:
        return int(row[0])
    # Final fallback: docker
    cur = conn.execute("SELECT id FROM vm_group WHERE lower(group_name)='docker' LIMIT 1")
    row = cur.fetchone()
    if not row:
        raise RuntimeError(f"vm_group not found for '{name}' or 'docker'")
    return int(row[0])

def already_registered(conn: sqlite3.Connection, group_id: int, file_name: str) -> bool:
    cur = conn.execute(
        """
        SELECT 1 FROM vm_image
        WHERE vm_group_id = ? AND lower(file_name) = lower(?)
        LIMIT 1
        """,
        (group_id, file_name),
    )
    return cur.fetchone() is not None

def update_image_row(conn: sqlite3.Connection,
                     group_id: int,
                     image_name: str,
                     file_name: str,
                     size_bytes: int,
                     saved_dir: str,
                     image_type: str) -> None:
    conn.execute(
        """
        UPDATE vm_image
           SET image_name       = ?,
               path_app_saved   = ?,
               vm_image_size    = ?,
               image_type       = ?,
               edit_date        = CURRENT_TIMESTAMP
         WHERE vm_group_id      = ?
           AND lower(file_name) = lower(?)
        """,
        (image_name, saved_dir, size_bytes, image_type, group_id, file_name),
    )

def register_image(conn: sqlite3.Connection,
                   group_id: int,
                   image_name: str,
                   file_name: str,
                   size_bytes: int,
                   saved_dir: str,
                   image_type: str = "tar.gz") -> None:
    image_cost = "free"
    support_cost = 10000
    image_paths = {
        "archiware:7.4.5" : {
            "image_path" : "/images/sanuyiP5.png",
            "description" : "Archiware's P5 Software Platform is ideal for businesses in the Media and Entertainment industry. Four modules in the Archiware P5 Suite secure data using the A-B-C of data management: Archive, Backup and Cloning."
        },
        "mysql:8.0" : {
            "image_path" : "/images/mysqlImage.png",
            "description" : "MySQL is a widely used open-source relational database management system (RDBMS). It utilizes Structured Query Language (SQL) for managing and manipulating data, which is organized into tables with defined relationships. Known for its reliability."
        },
        "opensis:1.0.1" : {
            "image_path" : "/images/OpenSiS.jpg",
            "description" : "OpenSIS is an open-source student information and school management system for K-12, trade schools, and higher education"
        },
        "ubuntu-gotty:1.0" : {
            "image_path" : "/images/ubuntu3.jpg",
            "description" : "Ubuntu is a popular, free, and open-source operating system based on the Linux kernel, known for its user-friendliness, stability, and strong community support."
        }
    }
    description = image_paths[image_name]["description"] if image_name in image_paths else ""
    path_image_icon = image_paths[image_name]["image_path"] if image_name in image_paths else ""
    conn.execute(
        """
        INSERT INTO vm_image (
            image_name, state, cr_date, edit_date, del_date,
            path_app_saved, vm_image_size, vm_group_id, downloded,
            image_cost, support_cost, image_description, path_image_icon,
            app_download_server, image_type, file_name, download_percentage,
            uuid, profile_id
        )
        SELECT
            ?, 1, CURRENT_TIMESTAMP, CURRENT_TIMESTAMP, NULL,
            ?, ?, ?, 'yes',
            ?, ?, ?, ?,
            NULL, ?, ?, 100,
            NULL, NULL
        WHERE NOT EXISTS (
            SELECT 1 FROM vm_image
            WHERE vm_group_id = ? AND lower(file_name) = lower(?)
        )
        """,
        (
            image_name,
            saved_dir,
            size_bytes,
            group_id,
            image_cost,
            support_cost,
            description,
            path_image_icon,
            image_type,
            file_name,
            group_id,
            file_name,
        ),
    )

# ---------------- docker helpers ----------------
def docker_available() -> bool:
    return shutil.which("docker") is not None

def docker_image_exists(ref: str) -> bool:
    if not ref:
        return False
    try:
        out = subprocess.run(
            ["docker", "image", "inspect", ref],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False
        )
        return out.returncode == 0
    except Exception:
        return False

def docker_load_archive(archive_path: str) -> Tuple[bool, Optional[str], Optional[str], str]:
    """
    Returns (ok, loaded_ref, loaded_id, raw_output)
    loaded_ref: from "Loaded image: <ref>" (preferred, if tagged)
    loaded_id: from "Loaded image ID: <id>" (fallback for untagged)
    """
    try:
        proc = subprocess.run(
            ["docker", "load", "-i", archive_path],
            capture_output=True, text=True, check=True
        )
        out = (proc.stdout or "") + (proc.stderr or "")
    except subprocess.CalledProcessError as e:
        return (False, None, None, (e.stdout or "") + (e.stderr or ""))

    loaded_ref = None
    loaded_id = None
    for line in out.splitlines():
        l = line.strip().lower()
        if l.startswith("loaded image:"):
            loaded_ref = line.split(":", 1)[1].strip()
        elif l.startswith("loaded image id:"):
            loaded_id = line.split(":", 1)[1].strip()

    return (True, loaded_ref, loaded_id, out)

def docker_tag(src: str, dst: str) -> bool:
    try:
        subprocess.run(["docker", "tag", src, dst], check=True)
        return docker_image_exists(dst)
    except subprocess.CalledProcessError:
        return False

# ---------------- scoped reset helpers ----------------
SUPPORTED_TAR_EXTS = (".tar", ".tar.gz", ".tgz", ".tar.zst", ".tar.xz")

def list_target_basenames(images_dir: str) -> Set[str]:
    targets: Set[str] = set()
    p = Path(images_dir)
    if not p.is_dir():
        return targets
    for name in os.listdir(images_dir):
        for ext in SUPPORTED_TAR_EXTS:
            if name.endswith(ext):
                targets.add(name[: -len(ext)])
                break
    return targets


def _fk_from_child_to_vm(conn: sqlite3.Connection, table: str) -> Optional[str]:
    cur = conn.execute(f"PRAGMA foreign_key_list({table});")
    for row in cur.fetchall():
        if str(row[2]).lower() == "virtualmachine":
            return str(row[3])
    return None


def reset_scoped_db(db_path: str, group_id: int, targets: Set[str], dry_run: bool, skip_vacuum: bool) -> None:
    if not targets:
        log.info("[reset] No matching tarballs found in images dir; skip DB reset.")
        return
    if not (os.path.isfile(db_path) and os.access(db_path, os.R_OK | os.W_OK)):
        raise FileNotFoundError(f"DB file missing or not writable: {db_path}")

    t0 = time.time()
    with sqlite3.connect(db_path, timeout=10) as conn:
        conn.execute("PRAGMA foreign_keys=ON;")
        conn.execute("PRAGMA busy_timeout=3000;")
        cur = conn.cursor()

        file_names = sorted(targets)
        cur.execute(
            f"""
            SELECT id, image_name, file_name
            FROM vm_image
            WHERE vm_group_id=? AND file_name IN ({_placeholders(len(file_names))})
            """,
            (group_id, *file_names),
        )
        img_rows = cur.fetchall()
        img_ids = [r[0] for r in img_rows]

        log.info(f"[reset] group_id={group_id} targets={file_names}")
        if not img_rows:
            log.info("[reset] No vm_image matches for those file_names; nothing to delete.")
            return

        for _id, _iname, _fname in img_rows:
            log.info(f"[reset] will delete vm_image.id={_id} image_name={_iname!r} file_name={_fname!r}")

        if dry_run:
            log.info("[reset] DRY-RUN: no DB changes made.")
            return

        # find referencing VMs
        cur.execute(
            f"SELECT id FROM virtualmachine WHERE vm_image_id IN ({_placeholders(len(img_ids))})",
            (*img_ids,),
        )
        vm_ids = [r[0] for r in cur.fetchall()]

        # child tables (if exist & FK to VM)
        for t in ("vm_network", "vm_storage"):
            if _table_exists(conn, t):
                fk_col = _fk_from_child_to_vm(conn, t)
                if fk_col and vm_ids:
                    cur.execute(f"DELETE FROM {t} WHERE {fk_col} IN ({_placeholders(len(vm_ids))})", (*vm_ids,))
                    log.info(f"[reset] deleted {cur.rowcount} rows from {t}")

        # delete VMs
        if vm_ids:
            cur.execute(f"DELETE FROM virtualmachine WHERE id IN ({_placeholders(len(vm_ids))})", (*vm_ids,))
            log.info(f"[reset] deleted {cur.rowcount} rows from virtualmachine")

        # delete vm_image
        cur.execute(f"DELETE FROM vm_image WHERE id IN ({_placeholders(len(img_ids))})", (*img_ids,))
        log.info(f"[reset] deleted {cur.rowcount} rows from vm_image")

        conn.commit()

    if not skip_vacuum:
        with sqlite3.connect(db_path, timeout=10) as conn_v:
            conn_v.isolation_level = None
            conn_v.execute("PRAGMA busy_timeout=3000;")
            conn_v.execute("VACUUM;")
        log.info(f"[reset] VACUUM done in {time.time()-t0:.2f}s")
    else:
        log.info("[reset] VACUUM skipped")

def remove_daemon_images_by_patterns(patterns: List[str]) -> None:
    if not patterns:
        return
    if not docker_available():
        log.warning("[daemon] docker not available; skip removal")
        return
    try:
        out = subprocess.check_output(
            ["docker", "images", "--format", "{{.Repository}}:{{.Tag}} {{.ID}}"],
            text=True,
            stderr=subprocess.STDOUT,
        ).strip()
    except subprocess.CalledProcessError as e:
        log.error(f"[daemon] list failed: {e.output}")
        return
    to_rm: List[str] = []
    for ln in out.splitlines():
        if not ln.strip():
            continue
        try:
            ref, img_id = ln.split()
        except ValueError:
            continue
        if any(pat in ref for pat in patterns):
            to_rm.append(img_id)
    ids = sorted(set(to_rm))
    if not ids:
        log.info("[daemon] no matching images to remove")
        return
    try:
        subprocess.run(["docker", "rmi", "-f"] + ids, check=True, text=True, stderr=subprocess.STDOUT)
        log.info(f"[daemon] removed {len(ids)} images")
    except subprocess.CalledProcessError as e:
        log.error(f"[daemon] rmi failed: {e.output}")


def full_wipe_db_and_daemon(db_path: str, group_id: int, remove_daemon: bool = True) -> None:
    if not (os.path.isfile(db_path) and os.access(db_path, os.R_OK | os.W_OK)):
        raise FileNotFoundError(f"DB file missing or not writable: {db_path}")

    with sqlite3.connect(db_path, timeout=10) as conn:
        conn.execute("PRAGMA foreign_keys=ON;")
        conn.execute("PRAGMA busy_timeout=3000;")
        cur = conn.cursor()

        cur.execute("SELECT 1 FROM vm_group WHERE id=?", (group_id,))
        if not cur.fetchone():
            print(f"[warn] vm_group id={group_id} not found; nothing to wipe.")
            return

        cur.execute("SELECT id, image_name, file_name FROM vm_image WHERE vm_group_id=?", (group_id,))
        img_rows = cur.fetchall()
        if not img_rows:
            print(f"[info] No vm_image rows in group {group_id}; DB wipe skipped.")
            return

        img_ids = [r[0] for r in img_rows]
        image_refs = []
        for _id, iname, _fname in img_rows:
            if isinstance(iname, str) and ":" in iname and re.match(r"^[\w][\w.\-\/]*:[\w.\-]+$", iname.strip()):
                image_refs.append(iname.strip().lower())

        ph_img = _placeholders(len(img_ids))
        cur.execute(f"SELECT id FROM virtualmachine WHERE vm_image_id IN ({ph_img})", (*img_ids,))
        vm_ids = [r[0] for r in cur.fetchall()]

        def table_exists(t: str) -> bool:
            r = cur.execute(
                "SELECT 1 FROM sqlite_master WHERE type='table' AND lower(name)=lower(?) LIMIT 1",
                (t,)
            ).fetchone()
            return r is not None

        child_specs = []
        for t in ("vm_network", "vm_storage"):
            if table_exists(t):
                for row in cur.execute(f"PRAGMA foreign_key_list({t});").fetchall():
                    if str(row[2]).lower() == "virtualmachine":
                        child_specs.append((t, str(row[3])))
                        break

        if vm_ids:
            ph_vm = _placeholders(len(vm_ids))
            for (t, fk) in child_specs:
                cur.execute(f"DELETE FROM {t} WHERE {fk} IN ({ph_vm})", (*vm_ids,))
            cur.execute(f"DELETE FROM virtualmachine WHERE id IN ({ph_vm})", (*vm_ids,))

        cur.execute(f"DELETE FROM vm_image WHERE id IN ({ph_img})", (*img_ids,))
        conn.commit()

    with sqlite3.connect(db_path, timeout=10) as conn_v:
        conn_v.isolation_level = None
        conn_v.execute("PRAGMA busy_timeout=3000;")
        conn_v.execute("VACUUM;")

    print(f"[done] DB wiped for group={group_id} (images={len(img_rows)}, vms={len(vm_ids)})")

    if remove_daemon and image_refs:
        if shutil.which("docker") is None:
            print("[warn] Docker CLI not found; skipping docker rmi.")
            return

        def _exists(ref: str) -> bool:
            try:
                return subprocess.run(
                    ["docker", "image", "inspect", ref],
                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False
                ).returncode == 0
            except Exception:
                return False

        to_remove = [r for r in image_refs if _exists(r)]
        if not to_remove:
            print("[info] No matching local docker images to remove.")
            return

        CHUNK = 20
        removed = 0
        for i in range(0, len(to_remove), CHUNK):
            chunk = to_remove[i:i+CHUNK]
            try:
                subprocess.run(["docker", "rmi", "-f"] + chunk, check=True)
                removed += len(chunk)
            except subprocess.CalledProcessError as e:
                print(f"[warn] docker rmi failed for {chunk}: {e}")
        print(f"[done] docker images removed: {removed}/{len(to_remove)}")

def _placeholders(n: int) -> str:
    return ",".join(["?"] * n)

def _table_exists(conn: sqlite3.Connection, name: str) -> bool:
    cur = conn.execute(
        "SELECT 1 FROM sqlite_master WHERE type='table' AND lower(name)=lower(?) LIMIT 1",
        (name,),
    )
    return cur.fetchone() is not None


def _docker_rmi_refs(refs: List[str]) -> None:
    if not refs:
        return
    if shutil.which("docker") is None:
        print("[warn] Docker CLI not found; skipping daemon removals", file=sys.stderr)
        return
    # Only remove existing refs
    to_remove = []
    for r in refs:
        try:
            rc = subprocess.run(
                ["docker", "image", "inspect", r],
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False
            ).returncode
            if rc == 0:
                to_remove.append(r)
        except Exception:
            pass
    if not to_remove:
        print("  [ok  ] no matching docker tags present locally")
        return
    try:
        subprocess.run(["docker", "rmi", "-f"] + to_remove, check=True)
        print(f"  [rmi ] removed: {', '.join(to_remove)}")
    except subprocess.CalledProcessError as e:
        print(f"  [warn] docker rmi failed: {e}", file=sys.stderr)


def _is_repo_tag(s: str) -> bool:
    return s and (":" in s) and ("/" not in s.split(":")[1])  # crude but fine: repo:tag

def _remove_one_image(conn: sqlite3.Connection, group_id: int, ident: str) -> bool:
    """
    ident can be 'repo:tag' or 'file_name' (tar basename).
    Returns True if something was removed from DB (even if Docker removal later fails).
    """
    cur = conn.cursor()

    # Resolve vm_image row in this group
    if _is_repo_tag(ident):
        cur.execute(
            """
            SELECT id, image_name, file_name FROM vm_image
            WHERE vm_group_id=? AND lower(image_name)=lower(?)
            """,
            (group_id, ident),
        )
    else:
        cur.execute(
            """
            SELECT id, image_name, file_name FROM vm_image
            WHERE vm_group_id=? AND lower(file_name)=lower(?)
            """,
            (group_id, ident),
        )
    row = cur.fetchone()
    if not row:
        print(f"[warn] --remove-image '{ident}': no matching vm_image row in group_id={group_id}")
        return False

    img_id, image_name, file_name = row
    print(f"[info] removing image: id={img_id} image_name={image_name!r} file_name={file_name!r}")


    # Collect VM ids that reference this image
    vm_ids = [r[0] for r in conn.execute(
        "SELECT id FROM virtualmachine WHERE vm_image_id=?", (img_id,)
    ).fetchall()]

    if vm_ids:
        ph = ",".join(["?"] * len(vm_ids))
        for t in ("vm_network", "vm_storage"):
            if _table_exists(t):
                fk = _fk_child_to_vm(t)
                if fk:
                    conn.execute(f"DELETE FROM {t} WHERE {fk} IN ({ph})", (*vm_ids,))

        conn.execute(f"DELETE FROM virtualmachine WHERE id IN ({ph})", (*vm_ids,))

    # Delete vm_image row
    conn.execute("DELETE FROM vm_image WHERE id=?", (img_id,))
    return True

def _docker_rmi_if_present(ref: str) -> None:
    try:
        out = subprocess.run(
            ["docker", "image", "inspect", ref],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False
        )
        if out.returncode == 0:
            subprocess.run(["docker", "rmi", "-f", ref], check=True)
            print(f"[daemon] removed {ref}")
        else:
            print(f"[daemon] {ref} not present; skip")
    except Exception as e:
        print(f"[warn] docker rmi {ref} failed: {e}")

# ---------------- argparse ----------------
def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description="Register prebuilt Docker image tarballs into quantumDB.db for a specific vm_group. Optionally reset scoped rows and docker images, then load/tag."
    )
    ap.add_argument("path", help="Path to the images directory OR the pack root directory")
    ap.add_argument("--db", default=DEFAULT_DB, help=f"SQLite DB path (default: {DEFAULT_DB})")

    # group selection
    ap.add_argument("--group-id", type=int, default=19, help="vm_group.id to use (default: 19 for SanuyiRepo)")

    # registration behavior
    ap.add_argument("--dry-run", action="store_true", help="Show what would be inserted/updated without changing the DB")
    ap.add_argument("--refresh", action="store_true",
                    help="If a row exists, UPDATE its metadata (path/size/type/name) instead of skipping.")
    ap.add_argument("--overwrite", action="store_true",
                    help="Alias for --refresh (safe UPDATE instead of DELETE+INSERT to avoid FK errors).")
    ap.add_argument("--force-delete", action="store_true",
                    help="DANGEROUS: DELETE existing rows before insert. Will fail if other tables reference vm_image.")
    ap.add_argument("--load", action="store_true", help="After registering, docker load each archive and tag it")
    ap.add_argument("--repo-prefix", default="", help="Optional repo/registry prefix, e.g. 'myregistry:5000'")
    ap.add_argument("--force-tag", action="store_true", help="Retag even if target ref already exists locally")


    # integrated scoped reset
    ap.add_argument("--scoped-reset", action="store_true",
                    help="Before registering, delete only vm_image/VM rows whose file_name matches tarballs in the images dir (for the chosen group).")
    ap.add_argument("--daemon-pattern", action="append", default=[],
                    help="After DB reset, also remove docker images whose repo:tag contains this substring (repeatable).")
    ap.add_argument("--skip-vacuum", action="store_true", help="Skip VACUUM after DB reset")

    ap.add_argument("--full-wipe", action="store_true",
                    help="Delete ALL images & referencing VMs for --group-id from DB, then remove those docker images.")
    ap.add_argument("--group-name", help="Name of vm_group (alternative to --group-id)")

    ap.add_argument(
        "--remove",
        nargs="+",
        metavar="BASENAME",
        help="Remove specific images by vm_image.file_name (tar basename, e.g. 'archiware_7.4.5'). "
             "Removes from DB and Docker daemon."
    )

    ap.add_argument(
        "--remove-image", action="append", default=[],
        help="Remove a specific image (repeatable). Accepts repo:tag (e.g. archiware:7.4.5) "
             "or tarball file_name without extension (e.g. archiware_7.4.5). "
             "Removes from DB (in the chosen group) and from Docker daemon."
    )
    ap.add_argument(
        "--register-image", action="append", default=[],
        help="Register only the specified image(s). Accepts tarball basenames "
             "(e.g. archiware_7.4.5) or repo:tag (e.g. archiware:7.4.5). "
             "Skips all other tarballs in the images dir."
)

    return ap.parse_args()

# ---------------- main ----------------
def main():
    args = parse_args()
    do_refresh = args.refresh or (args.overwrite and not args.force_delete)

    if args.full_wipe:
        if getattr(args, "group_id", None) is None and getattr(args, "group_name", None) is None:
            print("[ERR ] --full-wipe requires --group-id", file=sys.stderr)
            sys.exit(2)
        # safety banner
        print(f"[confirm] FULL WIPE of group_id={args.group_id}: DB rows (vm_image + VMs) and docker images (by repo:tag).")
        # If you want a prompt, uncomment next two lines:
        # ans = input("Type 'YES' to proceed: ").strip().upper()
        # if ans != "YES": sys.exit(0)
        full_wipe_db_and_daemon(args.db, int(args.group_id), remove_daemon=True)
        return

    images_root = find_images_dir(Path(args.path))
    tars = sorted(list(images_root.glob("*.tar.gz"))
                  + list(images_root.glob("*.tgz"))
                  + list(images_root.glob("*.tar"))
                  + list(images_root.glob("*.tar.zst"))
                  + list(images_root.glob("*.tar.xz")))
    if not tars:
        print(f"No .tar.gz/.tgz/.tar(.zst/.xz) images found in {images_root}")
        return

    # --- Targeted register (optional) ---
    if getattr(args, "register_image", None):
        requested = {x.strip().lower() for x in args.register_image if x and x.strip()}
        if requested:
            filtered = []
            for gz in tars:
                # basename without compression suffix
                base = strip_pack_suffix(gz.name).lower()          # e.g. "archiware_7.4.5"
                # canonical repo:tag we will register as
                ref  = friendly_name_from_file(gz.name).lower()    # e.g. "archiware:7.4.5"
                if base in requested or ref in requested:
                    filtered.append(gz)

            if not filtered:
                print(f"[warn] --register-image specified but no matches found in {images_root}")
                return

            tars = filtered
            print(f"[info] Targeted register: {len(tars)} match(es) -> {[gz.name for gz in tars]}")

    if args.load and not docker_available():
        print("[warn] --load requested but Docker is not available on PATH. Continuing without loading.", file=sys.stderr)
        args.load = False

    conn = sqlite3.connect(args.db)
    try:
        conn.execute("PRAGMA foreign_keys=ON")
        group_id = get_group_id(conn,
                        getattr(args, "group_id", None),
                        getattr(args, "group_name", None))

        # --- Targeted removal (optional) ---
        remove_idents: List[str] = []
        if getattr(args, "remove_image", None):
            remove_idents += [x.strip() for x in args.remove_image if x and x.strip()]
        if getattr(args, "remove", None):
            # --remove is file_name (tar basename). We accept those too.
            remove_idents += [x.strip() for x in args.remove if x and x.strip()]

        if remove_idents:
            print(f"[info] Removing specific images from group {group_id}: {remove_idents}")
            removed_any = False
            for ident in remove_idents:
                ident_norm = ident.lower()
                try:
                    # DB remove by repo:tag or by file_name
                    if _remove_one_image(conn, group_id, ident_norm):
                        removed_any = True

                    # Docker: if repo:tag, remove as-is; if file_name, derive canonical repo:tag(s)
                    if _is_repo_tag(ident_norm):
                        _docker_rmi_if_present(ident_norm)
                    else:
                        # e.g., archiware_7.4.5 -> archiware:7.4.5
                        for ref in alias_refs(None, ident_norm, repo_prefix=args.repo_prefix or ""):
                            if ref:
                                _docker_rmi_if_present(ref)
                except Exception as e:
                    print(f"[ERR ] remove-image '{ident}': {e}", file=sys.stderr)

            if removed_any:
                conn.commit()

            # Summary after removals
            print("\n[summary after removals]")
            cur = conn.execute(
                """
                SELECT id, image_name, file_name, vm_image_size
                FROM vm_image
                WHERE vm_group_id = ?
                ORDER BY id
                """,
                (group_id,),
            )
            rows = cur.fetchall()
            if rows:
                print(f"{'id':<5}  {'image_name':<30}  {'file_name':<28}  {'size_bytes':>12}")
                print("-" * 83)
                for rid, iname, fname, sz in rows:
                    iname = iname or "-"
                    fname = fname or "-"
                    sz_s  = "-" if sz is None else str(sz)
                    print(f"{rid:<5}  {iname[:30]:<30}  {fname[:28]:<28}  {sz_s:>12}")
            else:
                print("(none)")
            return

        inserted, skipped, updated = 0, 0, 0
        loaded, tagged, existed = 0, 0, 0

        print(f"[info] Using DB: {args.db}")
        print(f"[info] Images dir: {images_root}")
        print(f"[info] Group id={group_id} (name={args.group_name or 'n/a'})")
        if args.repo_prefix:
            print(f"[info] Repo prefix: {args.repo_prefix}")
        if args.load:
            print(f"[info] Will load images into Docker and tag them")
        if args.force_delete:
            print(f"[warn] Using --force-delete (DELETE+INSERT). This may fail on FK or break references!", file=sys.stderr)
        if args.scoped_reset:
            print(f"[info] Scoped reset enabled (DB + optional daemon).")
        print()

        # --- Scoped reset (optional) ---
        if args.scoped_reset:
            if getattr(args, "register_image", None):
                targets = {strip_pack_suffix(gz.name) for gz in tars}
            else:
                targets = list_target_basenames(str(images_root))
            reset_scoped_db(args.db, group_id, targets, args.dry_run, args.skip_vacuum)
            if args.daemon_pattern:
                remove_daemon_images_by_patterns(args.daemon_pattern)

        # --- Register / update rows ---
        for gz in tars:
            base = gz.name
            file_name = strip_pack_suffix(base)
            size_bytes = gz.stat().st_size
            image_name = friendly_name_from_file(base)  # canonical repo:tag, lowercased
            path_saved = str(images_root)
            if base.endswith(".tar.gz"):
                img_type = "tar.gz"
            elif base.endswith(".tgz"):
                img_type = "tgz"
            elif base.endswith(".tar.zst"):
                img_type = "tar.zst"
            elif base.endswith(".tar.xz"):
                img_type = "tar.xz"
            else:
                img_type = "tar"

            exists = already_registered(conn, group_id, file_name)

            if exists and args.force_delete and not args.dry_run:
                conn.execute(
                    "DELETE FROM vm_image WHERE vm_group_id = ? AND lower(file_name) = lower(?)",
                    (group_id, file_name),
                )
                exists = False

            if exists:
                if do_refresh and not args.dry_run:
                    update_image_row(conn, group_id, image_name, file_name, size_bytes, path_saved, img_type)
                    print(f"[update] {file_name} → {image_name}")
                    updated += 1
                else:
                    print(f"[skip] {file_name} → {image_name}")
                    skipped += 1
            else:
                print(f"[add ] {image_name} (file_name={file_name}, size={size_bytes} bytes)")
                if not args.dry_run:
                    register_image(
                        conn,
                        group_id,
                        image_name=image_name,
                        file_name=file_name,
                        size_bytes=size_bytes,
                        saved_dir=path_saved,
                        image_type=img_type,
                    )
                    inserted += 1

            # --- Docker load/tag (optional) ---
            if args.load:
                desired_tags = alias_refs(image_name, file_name, repo_prefix=args.repo_prefix)
                ordered = [t for t in desired_tags if t]  # Only canonical tag

                present = [t for t in ordered if docker_image_exists(t)]
                if present:
                    print(f"  [ok  ] local present: {', '.join(present)}")
                    existed += 1
                    continue

                abs_path = str(gz.resolve())
                print(f"  [load] {base} -> docker…")
                ok, loaded_ref, loaded_id, raw = docker_load_archive(abs_path)
                if not ok:
                    print(f"  [ERR ] docker load failed for {base}")
                    tail = "\n".join(raw.splitlines()[-5:])
                    if tail:
                        print("        " + tail.replace("\n", "\n        "))
                    continue
                loaded += 1

                present = [t for t in ordered if docker_image_exists(t)]
                if present:
                    print(f"  [ok  ] target present: {', '.join(present)}")
                    tagged += 1
                    continue

                src_ref = None
                if loaded_ref and docker_image_exists(loaded_ref):
                    src_ref = loaded_ref
                elif loaded_id and docker_image_exists(loaded_id):
                    src_ref = loaded_id
                else:
                    for t in ordered:
                        if docker_image_exists(t):
                            src_ref = t
                            break

                if src_ref:
                    for dst in ordered:
                        if docker_image_exists(dst) and not args.force_tag:
                            continue
                        if docker_tag(src_ref, dst):
                            print(f"  [tag ] {src_ref} -> {dst}")
                            tagged += 1
                        else:
                            print(f"  [warn] failed to tag {src_ref} -> {dst}")
                    if loaded_ref and loaded_ref != ordered[0] and docker_image_exists(loaded_ref):
                        try:
                            subprocess.run(["docker", "rmi", loaded_ref], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                            print(f"  [rm  ] removed unwanted tag: {loaded_ref}")
                        except subprocess.CalledProcessError:
                            print(f"  [warn] failed to remove unwanted tag: {loaded_ref}")
                else:
                    if ordered and docker_image_exists(ordered[0]):
                        print(f"  [ok  ] target now present: {ordered[0]}")
                        tagged += 1
                    else:
                        print(f"  [warn] image loaded but could not tag to: {', '.join(ordered)}")

        if not args.dry_run:
            conn.commit()

        print(f"\n[done] inserted={inserted}, updated={updated}, skipped={skipped}")
        if args.load:
            print(f"[done] docker: existed={existed}, loaded={loaded}, tagged={tagged}")

        # --- Summary for the chosen group ---
        print(f"\n[summary of images for vm_group_id={group_id}]")
        cur = conn.execute(
            """
            SELECT id, image_name, file_name, vm_image_size
            FROM vm_image
            WHERE vm_group_id = ?
            ORDER BY id
            """,
            (group_id,),
        )
        rows = cur.fetchall()
        if rows:
            print(f"{'id':<5}  {'image_name':<30}  {'file_name':<28}  {'size_bytes':>12}")
            print("-" * 83)
            for rid, iname, fname, sz in rows:
                iname = iname or "-"
                fname = fname or "-"
                sz_s  = "-" if sz is None else str(sz)
                print(f"{rid:<5}  {iname[:30]:<30}  {fname[:28]:<28}  {sz_s:>12}")
        else:
            print("(none)")
    except sqlite3.Error as e:
        conn.rollback()
        print(f"[ERR ] Database error: {e}", file=sys.stderr)
        sys.exit(1)
    finally:
        conn.close()

if __name__ == "__main__":
    main()
