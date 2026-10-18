import sys, time
sys.path.insert(0, '.')
import zwenum as Z
import labelled_io
t=time.time()
pairs, pos, edges, diags, (te, tc) = Z.enumerate_diagrams(6)
print(f'n=6: {len(edges)} edge vectors pass E2/E3/E6 ({te:.1f} s); {len(diags)} labelled diagrams ({tc:.1f} s)', flush=True)
labelled_io.save('n6_labelled.txt', pairs, diags)
