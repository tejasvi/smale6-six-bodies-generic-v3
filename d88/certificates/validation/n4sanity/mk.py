import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
import n4_diagrams as N
tests = [('A z12 w34 at (1,1,2,2)', N.sing_class_A([1,1,2,2], 0, 1, 2, 3)),
         ('D z{13,24} w{23,14} at (1,6,2,3)', N.sing_class_D([1,6,2,3], 0, 1, 2, 3)),
         ('B tri123 at (1,4,4,7)', N.sing_class_B([1,4,4,7], 0, 1, 2)),
         ('C tri123 stroke 3-4 at (4,4,1,7)', N.sing_class_C([4,4,1,7], 0, 1, 2, 3)),
         ('C tri123 stroke 3-4 at (4,4,2,7) (control)', N.sing_class_C([4,4,2,7], 0, 1, 2, 3))]
out = []
for name, (ring, body) in tests:
    out += [ring.replace('CHAR', '0'), body, 'ideal G = std(I);', 'print("%s | unit: " + string(G[1]==1) + " | dim " + string(dim(G)));' % name, 'kill r;']
out.append('quit;')
open('sanity.sing', 'w').write('\n'.join(out) + '\n')
