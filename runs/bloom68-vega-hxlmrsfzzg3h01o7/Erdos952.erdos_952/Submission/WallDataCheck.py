#!/usr/bin/env python3
"""Compile only WallData Lean files, recording kernel-check resource usage.

Reproduce the complete certificate:
    python3 Submission/WallDataGenerate.py full
    python3 Submission/WallDataCheck.py --full --jobs 6

This driver is untrusted. Every certificate theorem uses `decide +kernel`.
Lean's kernel checks the proof terms; this program only invokes Lean, runs the
separate provenance audit, and logs resource costs. Mathlib must already be built.
"""
from __future__ import annotations
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / '.lake/build/lib/lean/Submission'


def compile_one(source: str, threads: int = 1) -> dict:
    src = Path(source)
    if not src.is_absolute():
        src = ROOT / src
    src = src.resolve()
    if src.parent != ROOT / 'Submission' or not src.name.startswith('WallData') or src.suffix != '.lean':
        raise ValueError(f'Not a WallData Lean source: {src}')
    before = src.read_bytes()
    OUT.mkdir(parents=True, exist_ok=True)
    log = src.with_suffix('.log')
    artifact = OUT / src.with_suffix('.olean').name
    command = ['lake', 'env', 'lean', f'-j{threads}', '-o', str(artifact), str(src)]
    started = time.time()
    t = time.monotonic()
    with log.open('w') as f:
        proc = subprocess.Popen(command, cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        _, status, usage = os.wait4(proc.pid, 0)
        proc.returncode = os.waitstatus_to_exitcode(status)
    unchanged = src.read_bytes() == before
    result = {
        'source': str(src.relative_to(ROOT)),
        'source_sha256': hashlib.sha256(before).hexdigest(),
        'source_unchanged_during_compile': unchanged,
        'command': command,
        'exit_code': proc.returncode,
        'started_unix': started,
        'finished_unix': time.time(),
        'wall_seconds': round(time.monotonic() - t, 3),
        'user_seconds': round(usage.ru_utime, 3),
        'system_seconds': round(usage.ru_stime, 3),
        'max_rss_kib': usage.ru_maxrss,
        'source_bytes': len(before),
        'source_lines': len(before.decode().splitlines()),
        'olean_bytes': artifact.stat().st_size if proc.returncode == 0 else None,
        'log': str(log.relative_to(ROOT)),
    }
    src.with_suffix('.timing.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def run_many(sources, jobs, threads):
    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = {pool.submit(compile_one, src, threads): src for src in sources}
        for future in concurrent.futures.as_completed(futures):
            result = future.result()
            print(json.dumps(result), flush=True)
            results.append(result)
    return results


def succeeded(results):
    return all(r['exit_code'] == 0 and r['source_unchanged_during_compile'] for r in results)


def full_build(jobs, threads):
    t = time.monotonic()
    subprocess.run([sys.executable, 'Submission/WallDataAudit.py'], cwd=ROOT, check=True)
    manifest = json.loads((ROOT / 'Submission/WallDataManifest.json').read_text())
    results = []
    phases = [(['Submission/WallDataChecker.lean'], 1),
              (['Submission/WallDataListChecker.lean'], 1),
              (['Submission/WallDataPackedChecker.lean'], 1),
              ([p['source'] for p in manifest['parts']], jobs),
              (['Submission/WallData.lean'], 1),
              (['Submission/WallDataVerify.lean', 'Submission/WallDataPackedTests.lean',
                'Submission/WallDataCheckerTests.lean'], jobs)]
    for sources, concurrency in phases:
        stage = run_many(sources, concurrency, threads)
        results.extend(stage)
        if not succeeded(stage):
            break
    summary = {
        'status': 'PASS' if succeeded(results) else 'FAIL',
        'wall_seconds': round(time.monotonic() - t, 3),
        'cpu_seconds': round(sum(r['user_seconds'] + r['system_seconds'] for r in results), 3),
        'max_single_compilation_rss_kib': max(r['max_rss_kib'] for r in results),
        'source_lines': sum(r['source_lines'] for r in results),
        'source_bytes': sum(r['source_bytes'] for r in results),
        'olean_bytes': sum(r['olean_bytes'] or 0 for r in results),
        'jobs': jobs, 'lean_threads_per_job': threads, 'compilations': results,
    }
    (ROOT / 'Submission/WallDataBuildSummary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k:v for k,v in summary.items() if k != 'compilations'}), flush=True)
    return succeeded(results)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('sources', nargs='*')
    p.add_argument('--jobs', type=int, default=1)
    p.add_argument('--threads', type=int, default=1)
    p.add_argument('--full', action='store_true')
    args = p.parse_args()
    if args.jobs <= 0 or args.threads <= 0:
        p.error('jobs and threads must be positive')
    if args.full:
        if args.sources:
            p.error('do not combine --full with explicit source names')
        ok = full_build(args.jobs, args.threads)
    else:
        if not args.sources:
            p.error('provide WallData source names or --full')
        ok = succeeded(run_many(args.sources, args.jobs, args.threads))
    raise SystemExit(0 if ok else 1)

if __name__ == '__main__':
    main()
