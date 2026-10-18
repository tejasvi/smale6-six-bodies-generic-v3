R = ZZ/65521[X2,X3,U1,U2,U3,p12,p13,p14,p23,p24,p34, MonomialOrder => GRevLex];
I = ideal(2*X2*p12^3+3*X3*p13^3-2*p12^3-3*p13^3-30*p14^3+1, -1*X2*p12^3-3*X2*p23^3-30*X2*p24^3+1*X2+3*X3*p23^3+1*p12^3, 2*X2*p23^3-1*X3*p13^3-2*X3*p23^3-30*X3*p34^3+1*X3+1*p13^3, 2*X2*p24^3+3*X3*p34^3+1*p14^3, 3*U1*p12^3+3*U1*p13^3+30*U1*p14^3-1*U1-3*U2*p12^3-3*U2*p23^3-30*U2*p24^3+1*U2-3*U3*p13^3+3*U3*p23^3, 2*U1*p12^3+4*U1*p13^3+30*U1*p14^3-1*U1-2*U2*p12^3+2*U2*p23^3-4*U3*p13^3-2*U3*p23^3-30*U3*p34^3+1*U3, -1*X2*U1*p12^2+1*X2*U2*p12^2+1*U1*p12^2-1*U2*p12^2-1, -1*X3*U1*p13^2+1*X3*U3*p13^2+1*U1*p13^2-1*U3*p13^2-1, 1*U1*p14^2-1, 1*X2*U2*p23^2-1*X2*U3*p23^2-1*X3*U2*p23^2+1*X3*U3*p23^2-1, 1*X2*U2*p24^2-1, 1*X3*U3*p34^2-1);
t0 = cpuTime();
G = groebnerBasis(I, Strategy => "F4");
L = monomialIdeal leadTerm G;
print("dim " | toString(dim L) | " degree " | toString(degree L) | " cpu " | toString(cpuTime() - t0));
exit 0;
