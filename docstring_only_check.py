#!/usr/bin/env python3
"""Check that two versions of a Lean 4 source file differ only in comments and docstrings.

  docstring_only_check.py ORIGINAL EDITED [ORIGINAL EDITED ...]

For each pair, removes every comment from both files: line comments (`--` to the end of the line) and block comments
(`/- ... -/`, nested to any depth, which includes the docstrings `/-- ... -/` and `/-! ... -/`), but not text inside
string literals (`"..."` with escapes, raw strings `r"..."`, `r#"..."#`) or character literals (`'a'`, `'\\n'`). Each
comment becomes one space; the remaining text is split at whitespace into tokens. The pair passes when the two token
sequences are equal. Prints, per pair: the SHA-256 of each file, the SHA-256 of each token sequence (tokens joined by
single spaces), and PASS or FAIL; exits 1 if any pair fails."""
import hashlib, re, sys

IDENT = re.compile(r"[A-Za-z0-9_'.!?À-\U0010FFFF]")


def strip_comments(src):
    out, i, n = [], 0, len(src)
    while i < n:
        c = src[i]
        prev = src[i - 1] if i > 0 else ' '
        if src.startswith('--', i):                       # line comment
            j = src.find('\n', i)
            i = n if j < 0 else j
            out.append(' ')
        elif src.startswith('/-', i):                     # block comment, nested
            depth, i = 1, i + 2
            while i < n and depth:
                if src.startswith('/-', i):
                    depth, i = depth + 1, i + 2
                elif src.startswith('-/', i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise ValueError('unterminated block comment')
            out.append(' ')
        elif c == 'r' and not IDENT.match(prev) and re.match(r'r#*"', src[i:]):    # raw string
            m = re.match(r'r(#*)"', src[i:])
            close = '"' + m.group(1)
            j = src.find(close, i + len(m.group(0)))
            if j < 0:
                raise ValueError('unterminated raw string')
            out.append(src[i:j + len(close)])
            i = j + len(close)
        elif c == '"':                                    # string literal with escapes
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            if j >= n:
                raise ValueError('unterminated string')
            out.append(src[i:j + 1])
            i = j + 1
        elif c == "'" and not IDENT.match(prev):          # character literal (not a prime of an identifier)
            m = re.match(r"'(\\.[^']*|[^\\'])'", src[i:])
            if m:
                out.append(m.group(0))
                i += len(m.group(0))
            else:
                out.append(c)
                i += 1
        else:
            out.append(c)
            i += 1
    return ''.join(out)


def tokens(path):
    return strip_comments(open(path, encoding='utf-8').read()).split()


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    args = sys.argv[1:]
    if not args or len(args) % 2:
        sys.exit(__doc__)
    bad = 0
    for a, b in zip(args[::2], args[1::2]):
        ta, tb = tokens(a), tokens(b)
        ok = ta == tb
        bad += not ok
        print(f'{"PASS" if ok else "FAIL"}  {b}\n  file sha256   {sha(open(a, "rb").read())}  {sha(open(b, "rb").read())}'
              f'\n  tokens sha256 {sha(" ".join(ta).encode())}  {sha(" ".join(tb).encode())}  ({len(ta)}, {len(tb)} tokens)')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
