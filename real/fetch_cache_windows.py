"""Replay Mathlib's generated download manifest using Python's system trust store.

The standard Mathlib cache command generates curl.cfg. This fallback is useful
when a Windows toolchain curl cannot use the host's certificate store. TLS
verification stays enabled. Run the standard `lake exe cache unpack` afterwards.
Only official Mathlib cache URLs and filenames beneath the selected cache
directory are accepted. This script does not generate or alter cache keys.
"""
from concurrent.futures import ThreadPoolExecutor, as_completed
import argparse
import http.client
import json
from pathlib import Path
import random
import re
import ssl
import time
import urllib.request
import urllib.error
from urllib.parse import urlparse

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("cache_dir", type=Path)
parser.add_argument("--workers", type=int, choices=range(1, 9), default=4)
parser.add_argument("--attempts", type=int, choices=range(1, 9), default=5)
parser.add_argument("--timeout", type=float, default=45)
args = parser.parse_args()
if args.timeout <= 0:
    parser.error("--timeout must be positive")
cache = args.cache_dir.resolve()
lines = (cache / "curl.cfg").read_text(encoding="utf-8").splitlines()
jobs = []
seen = set()
if len(lines) % 2:
    raise ValueError("The generated curl manifest has an incomplete entry")
for i in range(0, len(lines), 2):
    if not (lines[i].startswith("url = ") and lines[i + 1].startswith("-o ")):
        raise ValueError(f"Unexpected manifest syntax at line {i + 1}")
    url = lines[i][6:]
    parts = urlparse(url)
    if not (
        parts.scheme == "https"
        and parts.netloc == "lakecache.blob.core.windows.net"
        and not parts.query
        and not parts.fragment
        and re.fullmatch(r"/(mathlib4-master|mathlib4)/f/[0-9a-f]{16}\.ltar", parts.path)
    ):
        raise ValueError(f"Unexpected official-cache URL at line {i + 1}")
    name = Path(parts.path).name
    declared = Path(json.loads(lines[i + 1][3:])).resolve()
    if declared.parent != cache or declared.name != name + ".part":
        raise ValueError(f"Manifest output escapes the cache at line {i + 2}")
    if name not in seen:
        jobs.append(cache / name)
        seen.add(name)

# Load public system roots once. Verification and hostname checking stay enabled.
tls_context = ssl.create_default_context()
retry_statuses = {408, 429, 500, 502, 503, 504}


def download(candidate, partial):
    with urllib.request.urlopen(candidate, timeout=args.timeout, context=tls_context) as response:
        expected = response.headers.get("Content-Length")
        size = 0
        with partial.open("wb") as output:
            while chunk := response.read(1024 * 1024):
                output.write(chunk)
                size += len(chunk)
        if expected is not None and size != int(expected):
            raise http.client.IncompleteRead(b"", int(expected) - size)
        if size == 0:
            raise OSError("The official cache returned an empty archive")
        return size


def fetch(path):
    if path.exists() and path.stat().st_size > 0:
        return 0
    partial = path.with_suffix(".ltar.part")
    for container in ("mathlib4-master", "mathlib4"):
        candidate = f"https://lakecache.blob.core.windows.net/{container}/f/{path.name}"
        for attempt in range(args.attempts):
            try:
                size = download(candidate, partial)
                partial.replace(path)
                return size
            except urllib.error.HTTPError as error:
                partial.unlink(missing_ok=True)
                if error.code == 404:
                    break
                if error.code not in retry_statuses:
                    raise
                last_error = error
            except urllib.error.URLError as error:
                partial.unlink(missing_ok=True)
                if isinstance(error.reason, ssl.SSLCertVerificationError):
                    raise
                last_error = error
            except ssl.SSLCertVerificationError:
                partial.unlink(missing_ok=True)
                raise
            except (OSError, http.client.IncompleteRead) as error:
                partial.unlink(missing_ok=True)
                last_error = error
            if attempt + 1 == args.attempts:
                raise RuntimeError(
                    f"{path.name}: {args.attempts} bounded attempts failed: {last_error}"
                ) from last_error
            time.sleep(min(8, 0.75 * 2**attempt) + random.uniform(0, 0.5))
    raise RuntimeError(f"No official cache entry for {path.name}")

total = 0
failures = []
existing = sum(path.exists() and path.stat().st_size > 0 for path in jobs)
print(f"Manifest: {len(jobs)} entries; {existing} complete; {len(jobs) - existing} missing", flush=True)
last_report = time.monotonic()
with ThreadPoolExecutor(max_workers=args.workers) as pool:
    pending = {pool.submit(fetch, path): path for path in jobs}
    for count, result in enumerate(as_completed(pending), 1):
        try:
            total += result.result()
        except Exception as error:
            failures.append({"file": pending[result].name, "error": str(error)})
            print(f"Failed: {pending[result].name}: {error}", flush=True)
        if count % 100 == 0 or time.monotonic() - last_report >= 20:
            print(f"Completed {count}/{len(jobs)} entries; failures={len(failures)}", flush=True)
            last_report = time.monotonic()
print(json.dumps({"files": len(jobs), "downloaded_bytes": total, "failures": failures}))
raise SystemExit(bool(failures))
