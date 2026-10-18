#!/usr/bin/env python3
"""Builds the modules of the kernel run of F2-F4 in dependency order, in parallel under a memory budget, each with
`lean` directly (one thread, nice 10), from ROOT (LEAN_PATH must include ROOT/out); logs time and peak memory per
module. Dependencies: the deps.txt files written by kf34k_gen.py (`module: dependencies`).
Usage: kf34k_build.py ROOT LOG BUDGET_GB MAXJOBS DEPS.txt...
Estimated memory (GB), from KF34K_EST="NG_BASE,NG_PER,NG_MIN,VG,OTHER" (default "2,0.006,0,7,7"): for a group of kernel
checks (NG) max(NG_MIN, NG_BASE + NG_PER * the weight of its largest unit, from groups.txt beside deps.txt), for a covering
module (VG) VG, OTHER otherwise. A module whose .olean is newer than its source counts as built (an earlier run); the
modules that an earlier scheduler of the same tree is still compiling (it was ended to change its parameters) are
followed to their end, with their records from their time files ("adopted")."""
import os, re, subprocess, sys, time

root, log_path, budget, maxjobs = sys.argv[1], sys.argv[2], float(sys.argv[3]), int(sys.argv[4])
deps = {}
for f in sys.argv[5:]:
    for line in open(f):
        m, _, ds = line.partition(':')
        deps[m.strip()] = ds.split()
mods = list(deps)
done, failed, running = set(), set(), {}


def path_of(m):
    return m.replace('.', '/') + '.lean'


# a module whose .olean is newer than its source was built by an earlier run
for m in mods:
    src = os.path.join(root, path_of(m))
    ol = os.path.join(root, 'out', path_of(m)[:-5] + '.olean')
    if os.path.exists(ol) and os.path.exists(src) and os.path.getmtime(ol) >= os.path.getmtime(src):
        done.add(m)
pending = set(mods) - done
est_s = os.environ.get('KF34K_EST', '2,0.006,0,7,7')
ng_base, ng_per, ng_min, vg_est, other_est = map(float, est_s.split(','))

maxw = {}
for f in sys.argv[5:]:
    gf = os.path.join(os.path.dirname(f), 'groups.txt')
    if os.path.exists(gf):
        cls = os.path.basename(os.path.dirname(f))
        for line in open(gf):
            t = line.split()
            if 'maxw' in t:
                maxw[f'L6CheckF.{cls}.{t[0]}'] = int(t[t.index('maxw') + 1])


def est(m):
    kind = m.rsplit('.', 1)[1]
    if kind.startswith('NG'):
        return max(ng_min, ng_base + ng_per * maxw.get(m, 1000))
    if kind.startswith('VG'):
        return vg_est
    return other_est


def cmdline(pid):
    try:
        return [a for a in open(f'/proc/{pid}/cmdline').read().split('\0') if a]
    except OSError:
        return []


# the jobs of an earlier scheduler: /usr/bin/time -f FMT -o TF lean -DElab.async=false -o OLEAN SRC, with OLEAN of a
# module still pending here
adopted = {}
for d in os.listdir('/proc'):
    a = cmdline(d) if d.isdigit() else []
    if len(a) > 6 and a[0].endswith('/time') and 'lean' in a:
        m = a[-1][:-5].replace('/', '.')
        if m in pending and a[a.index('lean') + 1:][-2] == os.path.join(root, 'out', path_of(m)[:-5] + '.olean'):
            pending.discard(m)
            adopted[int(d)] = a
            running[int(d)] = (m, est(m), None, a[a.index('-o') + 1])

t0 = time.time()
with open(log_path, 'a') as log:
    log.write(f'# start {time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())} modules {len(mods)} already {len(done)} '
              f'budget_gb {budget} maxjobs {maxjobs} est {est_s} adopted {len(adopted)}\n')
    log.flush()
    while pending or running:
        ready = [m for m in pending if all(d in done for d in deps[m] if d in deps)]
        ready.sort()
        for m in ready:
            if len(running) >= maxjobs:
                break
            e = est(m)
            if running and sum(x[1] for x in running.values()) + e > budget:
                break
            if any(d in failed for d in deps[m]):
                pending.discard(m)
                failed.add(m)
                log.write(f'{m} skipped (dependency failed)\n')
                continue
            pending.discard(m)
            p = path_of(m)
            olean = os.path.join(root, 'out', p[:-5] + '.olean')
            os.makedirs(os.path.dirname(olean), exist_ok=True)
            tf = f'/tmp/kf34k_time_{os.getpid()}_{time.time_ns()}'
            of = open(tf + '.out', 'w')
            proc = subprocess.Popen(['nice', '-n', '10', '/usr/bin/time', '-f', '%e %U %S %M', '-o', tf, 'lean',
                                     '-DElab.async=false', '-o', olean, p], cwd=root, stdout=of,
                                    stderr=subprocess.STDOUT)
            of.close()
            running[proc.pid] = (m, e, proc, tf)
        time.sleep(1)
        for pid in list(running):
            m, e, proc, tf = running[pid]
            if proc is not None and proc.poll() is None or proc is None and cmdline(pid) == adopted[pid]:
                continue
            try:
                msg = open(tf + '.out').read()
                os.remove(tf + '.out')
            except OSError:
                msg = ''
            try:
                txt = open(tf).read()
                wall, user, sys_, rss = txt.split()[-4:]
                os.remove(tf)
            except Exception:
                txt, wall, user, sys_, rss = '', '?', '?', '?', '?'
            if proc is not None:
                rc = proc.returncode
            else:
                # an adopted job: its status from its time file and its .olean
                a, b = re.search(r'non-zero status (\d+)', txt), re.search(r'terminated by signal (\d+)', txt)
                rc = int(a.group(1)) if a else -int(b.group(1)) if b else 0 if txt else 1
                ol = os.path.join(root, 'out', path_of(m)[:-5] + '.olean')
                if rc == 0 and not (os.path.exists(ol) and os.path.getmtime(ol) >= os.path.getmtime(os.path.join(root, path_of(m)))):
                    rc = 1
            log.write(f'{m} exit {rc} wall_s {wall} user_s {user} maxrss_kb {rss}' + (' adopted' if proc is None else '') +
                      '\n')
            if rc == 0:
                done.add(m)
            else:
                failed.add(m)
                log.write('  ' + msg.replace('\n', '\n  ')[:3000] + '\n')
            log.flush()
            del running[pid]
    log.write(f'# end {time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())} wall_s {time.time() - t0:.1f} '
              f'built {len(done)} failed {len(failed)}\n')
print('built', len(done), 'failed', len(failed))
sys.exit(1 if failed else 0)
