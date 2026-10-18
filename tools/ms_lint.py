"""Lint msolve input files against the grammar that msolve 0.9.4 is known to parse correctly.

msolve 0.9.4 silently misparses many inputs (wrong solutions or [-1], no error); the test inputs are not included. Known bad forms:
  * parentheses:                 "(x-1)*(x-2)", "L - (x + 3*y)";
  * "**" powers:                 "x**2-1";
  * a variable repeated in a term (last exponent wins): "x*x", "x^2*x", "y*x*y";
  * a numeric factor after a variable, incl. division (the factor is dropped or misread):
                                 "x/2", "3*x/2", "x^2/4", "x^2*1/4", "x*2", "2*x*3";
  * floats "1.5*x"; Singular short format "x2"; a trailing ";"; unknown variables (silently dropped);
  * like terms not collected: "x^2+x^2-8", "y+x+x-2", "y-2-2", "y+x*y-y*x-2" (wrong or nonsense output);
  * a leading "+" (segfault).
Known good: an optional coefficient FIRST (integer or a/b), then distinct variables with optional ^integer, e.g.
"-3/4*x^2*y + 2*y - 1/5". The linter accepts exactly
  poly := term (('+'|'-') term)*   with an optional leading '-'
  term := coef | [coef '*'] var ['^' INT] ('*' var ['^' INT])*      (each var at most once)
  with pairwise distinct monomials in each polynomial
  coef := INT | INT '/' INT
Usage: python ms_lint.py FILE.ms [...]   (exit status 1 if any file is flagged)
       or `from ms_lint import lint_text` (returns a list of problems; empty means accepted).
"""
import re, sys

_COEF = re.compile(r'[0-9]+(/[0-9]+)?$')
_VARF = re.compile(r'([A-Za-z_][A-Za-z_0-9]*)(\^([0-9]+))?$')

def lint_polys(vars_line, polys):
    probs = []
    names = [v.strip() for v in vars_line.split(',') if v.strip()]
    nameset = set(names)
    if len(nameset) != len(names):
        probs.append('repeated variable name in the first line')
    body = polys.strip()
    for ch, what in (('(', 'parenthesis'), (')', 'parenthesis'), ('**', '"**" power'), (';', '";"'), ('.', 'float or "."')):
        if ch in body:
            probs.append(what)
    for k, p in enumerate(body.replace('\n', ' ').split(',')):
        p = p.replace(' ', '').replace('\t', '')
        if not p:
            probs.append('empty polynomial %d' % k)
            continue
        if p.startswith('+'):
            probs.append('leading "+" in polynomial %d' % k)
        q = p[1:] if p[0] in '+-' else p
        monos = set()
        for t in re.split(r'[+-]', q):
            if not t:
                probs.append('empty term (doubled sign) in polynomial %d' % k)
                continue
            fs = t.split('*')
            seen = set()
            mono = []
            for i, f in enumerate(fs):
                if _COEF.match(f):
                    if i != 0:
                        probs.append('numeric factor %r not first in a term of polynomial %d: %s' % (f, k, t[:60]))
                    continue
                m = _VARF.match(f)
                if not m:
                    probs.append('bad factor %r in polynomial %d: %s' % (f[:30], k, t[:60]))
                    continue
                v = m.group(1)
                if v not in nameset:
                    probs.append('unknown variable %r in polynomial %d (msolve drops it silently)' % (v, k))
                if v in seen:
                    probs.append('variable %s repeated in a term of polynomial %d: %s' % (v, k, t[:60]))
                seen.add(v)
                mono.append((v, int(m.group(3) or 1)))
            key = tuple(sorted(mono))
            if key in monos:
                probs.append('monomial repeated in polynomial %d (msolve does not collect like terms): %s' % (k, t[:60]))
            monos.add(key)
    return probs

def lint_text(text):
    lines = text.split('\n')
    if len(lines) < 3:
        return ['fewer than three lines']
    if not re.fullmatch(r'\s*[0-9]+\s*', lines[1]):
        return ['second line is not a characteristic: %r' % lines[1][:40]]
    return lint_polys(lines[0], '\n'.join(lines[2:]))

if __name__ == '__main__':
    bad = 0
    for fn in sys.argv[1:]:
        try:
            pr = lint_text(open(fn, encoding='utf-8', errors='replace').read())
        except Exception as e:
            pr = ['unreadable: %s' % e]
        if pr:
            bad += 1
            print(fn + ': ' + '; '.join(sorted(set(pr)))[:400])
    sys.exit(1 if bad else 0)
