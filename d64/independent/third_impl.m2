-- Referee: third implementation (Macaulay2, my own builders from the formulas of d64/DERIVATION.md 4.1 and 5.1).
-- (1) Lemma E at mu0 = (3,5,7,11), EXACT over Q(w), w^2+w+1 = 0: for all 729 patterns e the seven cubics
--     q_j^2 A_k - q_k^2 A_j, sum mu_k q_k^3 (A_k = sum_{l != k} w^{e_kl} mu_l q_l) have no zero in P^3, and for all 64 sign
--     patterns s the quartics G_k = sum_{l != k} s_kl mu_l prod_{j != k,l} (xi_k - xi_j)^2 (xi_1 = 0) have no zero in P^2.
--     Test: the homogeneous ideal has Krull dimension 0.
-- (2) Lemma C at mu0, modulo the prime PR (default 1000003): the 14 chart ideals of the compact model are the unit ideal.
mu = {3,5,7,11};
K = toField(QQ[w]/(w^2+w+1));
S = K[q_1..q_4];
prs = {{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}};
pidx = (k,l) -> position(prs, pp -> pp == {min(k,l), max(k,l)});
nfail = 0; npass = 0;
t0 = cpuTime();
for ex in toList((set{0,1,2})^**6) do (
    e := toList deepSplice ex;
    A := apply(4, k -> sum(select(4, l -> l != k), l -> (sub(w, S))^(e#(pidx(k,l))) * mu#l * q_(l+1)));
    gg := flatten apply(4, j -> apply(toList(j+1..3), k -> q_(j+1)^2 * A#k - q_(k+1)^2 * A#j));
    gg = append(gg, sum(4, k -> mu#k * q_(k+1)^3));
    I := ideal gg;
    if dim I == 0 then npass = npass + 1 else (nfail = nfail + 1; print("FAIL noncollinear " | toString e));
);
print("noncollinear (729 patterns, exact over Q(w)): pass " | toString npass | " fail " | toString nfail | " cpu " | toString(cpuTime() - t0));
nfail1 = nfail;
T = QQ[d_2..d_4];
xi = {0_T, d_2, d_3, d_4};
nfail = 0; npass = 0;
for bits in toList((set{1,-1})^**6) do (
    b := toList deepSplice bits;
    sg := (k,l) -> if k < l then b#(pidx(k,l)) else -(b#(pidx(l,k)));
    G := apply(4, k -> sum(select(4, l -> l != k), l -> sg(k,l) * mu#l * product(select(4, j -> j != k and j != l), j -> (xi#k - xi#j)^2)));
    I := ideal G;
    if dim I == 0 then npass = npass + 1 else (nfail = nfail + 1; print("FAIL collinear " | toString b));
);
print("collinear (64 patterns, exact over Q): pass " | toString npass | " fail " | toString nfail);
-- (2) compact model of C_4 modulo PR
PR = 1000003;
F = ZZ/PR;
R = F[s,t,p_(1,2),p_(1,3),p_(1,4),p_(2,3),p_(2,4),p_(3,4),c];
P = (k,l) -> p_(min(k,l)+1, max(k,l)+1);
x = {mu#2 * s, mu#2 * t, -(mu#0 * s + mu#1 * t), 0_R};
eqI = apply(4, k -> sum(select(4, l -> l != k), l -> mu#l * (P(k,l))^3 * (x#k - x#l)));
eqII = apply(3, k -> sum(select(4, l -> l != k), l -> mu#l * P(k,l) * product(select(4, j -> j != k and j != l), j -> x#k - x#j)) - c * product(select(4, l -> l != k), l -> x#k - x#l));
a = (k,l) -> (P(k,l))^2 * (x#k - x#l);
eqIII = apply({{0,1,2},{0,1,3},{0,2,3},{1,2,3}}, tr -> (k := tr#0; l := tr#1; n := tr#2; a(l,n)*a(n,k) + a(k,l)*a(n,k) + a(k,l)*a(l,n)));
eqs = eqI | eqII | eqIII;
-- bidegree check: deg s = deg t = (1,0), deg p = (0,1), deg c = (-1,1)
bideg = m -> (ee := (exponents m)#0; {ee#0 + ee#1 - ee#8, sum(toList(ee_{2..7})) + ee#8});
for f in eqs do ( ds := unique apply(terms f, bideg); if #ds != 1 then print("NOT BIHOMOGENEOUS"); );
print("bidegrees: " | toString apply(eqs, f -> bideg((terms f)#0)));
nfail = 0;
for xv in {s,t} do for pv in {p_(1,2),p_(1,3),p_(1,4),p_(2,3),p_(2,4),p_(3,4),c} do (
    J := ideal apply(eqs, f -> sub(f, {xv => 1, pv => 1}));
    u := (1_R % J == 0);
    print("chart " | toString xv | "=1, " | toString pv | "=1: unit ideal " | toString u);
    if not u then nfail = nfail + 1;
);
print("C4 charts mod " | toString PR | ": failures " | toString nfail);
if nfail1 == 0 and nfail == 0 then print "THIRD IMPLEMENTATION: PASS" else print "THIRD IMPLEMENTATION: FAIL";
exit 0
