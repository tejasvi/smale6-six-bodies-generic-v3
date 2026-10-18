import sys, json, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
import n4_trop, tropcheck


def main():
    kind, m, wd = sys.argv[1], [int(x) for x in sys.argv[2:6]], sys.argv[6]
    polys, gens = (n4_trop.n4_system if kind == 'n4' else n4_trop.kc_system)(m, 'all')
    res = tropcheck.run(polys, gens, 65521, wd, kind)
    print(json.dumps({k: v for k, v in res.items() if k != 'failures'}))
    for f in res['failures'][:10]:
        print('FAIL', f['cone'], f['point'])


if __name__ == '__main__':
    main()
