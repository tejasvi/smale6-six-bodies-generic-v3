#!/usr/bin/env python3
"""Compiles Lean modules of a package in parallel under a memory budget, each with `lean` directly (one thread), and
records per module the wall time, CPU time and peak memory.
Usage: kf1_build.py LOG BUDGET_GB MAXJOBS MODULE:EST_GB ...  (run from the package root; LEAN_PATH must be set;
extra arguments of lean in KF_LEAN_ARGS)
A module is a path such as L6CheckK/F1/Shards/S0.lean; its .olean and .ilean go to .lake/build/lib/lean (or KF_OUT).
Jobs start in the given order while the sum of the estimates of the running jobs stays within the budget."""
import os, subprocess, sys, time

log_path, budget, maxjobs = sys.argv[1], float(sys.argv[2]), int(sys.argv[3])
jobs = []
for a in sys.argv[4:]:
    m, est = a.rsplit(':', 1)
    jobs.append((m, float(est)))
out = os.environ.get('KF_OUT', '.lake/build/lib/lean')   # where the .olean/.ilean files go
extra = os.environ.get('KF_LEAN_ARGS', '').split()   # e.g. --load-dynlib=... for precompiled elaborator code
running = {}
fails = 0
t0 = time.time()
with open(log_path, 'a') as log:
    log.write(f'# start {time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())} jobs {len(jobs)} budget_gb {budget} maxjobs {maxjobs}\n')
    log.flush()
    while jobs or running:
        while jobs and len(running) < maxjobs and (not running or sum(e for _, e, _ in running.values()) + jobs[0][1] <= budget):
            m, est = jobs.pop(0)
            base = m[:-len('.lean')]
            os.makedirs(os.path.dirname(os.path.join(out, base)), exist_ok=True)
            tf = f'/tmp/kf1_time_{os.getpid()}_{len(running)}_{time.time_ns()}'
            cmd = ['nice', '-n', '10', '/usr/bin/time', '-f', '%e %U %S %M', '-o', tf, 'lean', *extra, '-j1', '-DElab.async=false', '-R', '.',
                   '-o', os.path.join(out, base + '.olean'), '-i', os.path.join(out, base + '.ilean'), m]
            of = open(tf + '.out', 'w')
            p = subprocess.Popen(cmd, stdout=of, stderr=subprocess.STDOUT)
            of.close()
            running[p.pid] = (m, est, (p, tf))
        time.sleep(1)
        for pid in list(running):
            m, est, (p, tf) = running[pid]
            if p.poll() is None:
                continue
            msg = open(tf + '.out').read()
            os.remove(tf + '.out')
            try:
                wall, user, sys_, rss = open(tf).read().split()[-4:]
                os.remove(tf)
            except Exception:
                wall = user = sys_ = rss = '?'
            log.write(f'{m} exit {p.returncode} wall_s {wall} user_s {user} sys_s {sys_} maxrss_kb {rss} est_gb {est}\n')
            if p.returncode != 0:
                fails += 1
                log.write('  ' + msg.replace('\n', '\n  ')[:4000] + '\n')
            log.flush()
            del running[pid]
    log.write(f'# end {time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())} wall_s {time.time() - t0:.1f} failures {fails}\n')
print('failures', fails)
sys.exit(1 if fails else 0)
