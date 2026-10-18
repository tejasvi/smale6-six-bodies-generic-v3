# Numerical sanity check of the E4 -> (E1),(E2) reduction (not part of the proof).
# Converse direction: build (q, beta, m) satisfying (E1),(E2) (complex masses), build the planar configuration with
# squared distances d_kl = p_kl^-2, p_kl = eps_kl q_k q_l, and check that it solves E4 with these masses.
import mpmath as mp, random
mp.mp.dps = 50
w = mp.exp(2j*mp.pi/3)
pairs = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
random.seed(1)
def run(eps):
    E = lambda k,l: w**eps[(min(k,l),max(k,l))]
    q = [mp.mpc(random.uniform(.5,2),random.uniform(-1,1)) for _ in range(3)]
    def mat(q4):
        qq = q+[q4]
        A = mp.matrix(5,5)
        for k in range(4):
            for l in range(4):
                if l!=k: A[k,l] = E(k,l)*qq[l]
            A[k,4] = qq[k]**2
        for l in range(4): A[4,l] = qq[l]**3
        return A
    N=16
    pts=[mp.exp(2j*mp.pi*i/N) for i in range(N)]
    vals=[mp.det(mat(t)) for t in pts]
    coef=[sum(vals[i]*pts[i]**(-j) for i in range(N))/N for j in range(N)]
    deg=max(j for j in range(N) if abs(coef[j])>1e-30)
    low=min(j for j in range(N) if abs(coef[j])>1e-30)
    roots=mp.polyroots([coef[j] for j in range(deg,low-1,-1)],maxsteps=200,extraprec=200)
    q4=max(roots,key=lambda r: -abs(abs(r)-1))
    q4=mp.findroot(lambda t: mp.det(mat(t)), q4)
    q.append(q4)
    A = mat(q4)
    # m4 = 1: solve rows 0..3 for (m1,m2,m3,beta), check row 4
    B = mp.matrix(4,4); rhs = mp.matrix(4,1)
    for k in range(4):
        for j,col in enumerate([0,1,2,4]): B[k,j] = A[k,col]
        rhs[k] = -A[k,3]
    sol = mp.lu_solve(B, rhs)
    m = [sol[0], sol[1], sol[2], mp.mpf(1)]; beta = sol[3]
    chk = sum(A[4,l]*m[l] for l in range(4))
    p = {pr: E(*pr)*q[pr[0]]*q[pr[1]] for pr in pairs}
    d = {pr: p[pr]**-2 for pr in pairs}
    best=None
    for s2 in (1,-1):
        for s3 in (1,-1):
            X=[mp.mpc(0),mp.mpc(1),0,0]; Y=[mp.mpc(0),d[(0,1)],0,0]
            for k,s in ((2,s2),(3,s3)):
                a,b,c = -d[(0,1)], d[(0,k)]+d[(0,1)]-d[(1,k)], -d[(0,k)]
                r = (-b+s*mp.sqrt(b*b-4*a*c))/(2*a)
                if r == 0: print("dbg", q, m, a, b, c)
                X[k]=r; Y[k]=d[(0,k)]/r
            err = abs((X[2]-X[3])*(Y[2]-Y[3])-d[(2,3)])/abs(d[(2,3)])
            if best is None or err<best[0]: best=(err,X,Y)
    err,X,Y = best
    def F(Z,k): return sum(m[l]*p[(min(k,l),max(k,l))]**3*(Z[k]-Z[l]) for l in range(4) if l!=k)
    res = max(abs(F(X,k)) for k in range(4)) + max(abs(F(Y,k)) for k in range(4))
    scale = max(abs(m[l]*p[pr]**3*(X[pr[0]]-X[pr[1]])) for pr in pairs for l in range(4))
    U = sum(m[k]*m[l]*p[(k,l)] for (k,l) in pairs)
    return abs(chk), err, res/scale, abs(U)
for b in range(3):
    for c in range(3):
        eps = {(0,1):0,(0,2):(-b)%3,(0,3):0,(1,2):(-c)%3,(1,3):0,(2,3):0}
        print((b,c), [mp.nstr(x,3) for x in run(eps)])
