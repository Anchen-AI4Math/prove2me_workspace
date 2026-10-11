"""Install the official, same-version Lean runtime inside this task only."""
import hashlib
import json
from pathlib import Path, PurePosixPath
import posixpath
import shutil
import subprocess
import sys
import tarfile
import urllib.request
from compression import zstd

sys.stdout.reconfigure(encoding="utf-8")
TASK = Path(__file__).resolve().parents[1]
DEST = TASK / "runtime"
DEST.mkdir(exist_ok=True)
NAME = "lean-4.33.1-linux"
URL = f"https://github.com/leanprover/lean4/releases/download/v4.33.1/{NAME}.tar.zst"
SHA256 = "890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235"
archive = DEST / f"{NAME}.tar.zst"
if not archive.exists():
    opener = urllib.request.build_opener(urllib.request.ProxyHandler(
        {"https": "http://127.0.0.1:65532", "http": "http://127.0.0.1:65532"}))
    request = urllib.request.Request(URL, headers={"User-Agent": "Codex-PiExponent"})
    partial = archive.with_suffix(archive.suffix + ".partial")
    downloaded = 0
    with opener.open(request, timeout=60) as response, partial.open("wb") as out:
        while block := response.read(4 * 1024 * 1024):
            out.write(block)
            downloaded += len(block)
            if downloaded % (64 * 1024 * 1024) == 0:
                print("Downloaded MiB:", downloaded // (1024 * 1024), flush=True)
    partial.rename(archive)
digest = hashlib.file_digest(archive.open("rb"), "sha256").hexdigest()
if digest != SHA256:
    raise SystemExit("Official release SHA-256 mismatch; no runtime extracted")
print("Official release SHA-256 verified", flush=True)
tar_path = DEST / f"{NAME}.tar"
if not tar_path.exists():
    with zstd.open(archive, "rb") as source, tar_path.open("wb") as out:
        shutil.copyfileobj(source, out, 4 * 1024 * 1024)
with tarfile.open(tar_path, "r:") as package:
    members = package.getmembers()
    for member in members:
        path = PurePosixPath(member.name)
        if path.is_absolute() or ".." in path.parts or path.parts[0] != NAME:
            raise SystemExit("Archive member escapes task runtime directory")
        if not (member.isfile() or member.isdir() or member.issym() or member.islnk()):
            raise SystemExit("Unexpected special file in runtime archive")
        if member.issym() or member.islnk():
            link = member.linkname if member.islnk() else posixpath.join(
                posixpath.dirname(member.name), member.linkname)
            normalized = PurePosixPath(posixpath.normpath(link))
            if normalized.is_absolute() or normalized.parts[0] != NAME:
                raise SystemExit("Runtime symlink escapes archive root")
print("Archive paths validated:", len(members), flush=True)
linux_dest = "/mnt/d/users/self_projects/prove2me_workspace/missions/pi-irrationality-measure/runtime"
result = subprocess.run(["wsl.exe", "-d", "Ubuntu", "--", "tar", "--no-same-owner",
                         "-xf", f"{linux_dest}/{NAME}.tar", "-C", linux_dest])
if result.returncode:
    raise SystemExit(result.returncode)
manifest = {"version": "4.33.1", "source": URL, "sha256": digest,
            "official_release": "https://github.com/leanprover/lean4/releases/tag/v4.33.1",
            "runtime": str(DEST / NAME), "shared_toolchain_changed": False}
(DEST / "manifest.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")
print(json.dumps(manifest), flush=True)
