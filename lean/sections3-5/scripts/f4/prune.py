#!/usr/bin/env python3
"""Keep in data/f4/certs/ exactly one file per certificate referenced by data/f4/links/ (the smaller one if both
<certid>.txt and <certid>.txt.gz exist); move every other file to RUN_DIR/extra_certs/ (not part of the data), and
move back from there the files of referenced certificates that are missing.
Usage: prune.py RUN_DIR"""
import glob
import os
import shutil
import sys


def main():
    run = sys.argv[1]
    certs = os.path.join(run, 'data', 'f4', 'certs')
    extra = os.path.join(run, 'extra_certs')
    os.makedirs(extra, exist_ok=True)
    ref = set()
    for f in glob.glob(os.path.join(run, 'data', 'f4', 'links', 'c*.txt')):
        for ln in open(f):
            if ln.strip():
                ref.add(ln.split()[2])
    files = {}
    for f in os.listdir(certs):
        files.setdefault(f.split('.')[0], []).append(f)
    moved = 0
    for cid, fs in files.items():
        if cid not in ref:
            keep = []
        else:
            keep = [min(fs, key=lambda f: os.path.getsize(os.path.join(certs, f)))]
        for f in fs:
            if f not in keep:
                shutil.move(os.path.join(certs, f), os.path.join(extra, f))
                moved += 1
    # referenced certificates whose file was moved earlier: move the smallest copy back
    restored = 0
    for cid in sorted(ref - set(files)):
        cand = [f for f in os.listdir(extra) if f.split('.')[0] == cid]
        if cand:
            f = min(cand, key=lambda f: os.path.getsize(os.path.join(extra, f)))
            shutil.move(os.path.join(extra, f), os.path.join(certs, f))
            files[cid] = [f]
            restored += 1
    print(f'{restored} referenced files restored from extra_certs')
    missing = sorted(ref - set(files))
    print(f'{len(ref)} referenced, {moved} files moved to extra_certs, {len(missing)} referenced without a file')
    for cid in missing:
        print('missing', cid)


if __name__ == '__main__':
    main()
