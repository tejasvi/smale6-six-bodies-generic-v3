import sympy as sp
x, y, z = sp.symbols('x y z')
w = sp.Rational(-1, 2) + sp.sqrt(3)*sp.I/2
prod = 1
for i in range(3):
    for j in range(3):
        prod *= (x + w**i*y + w**j*z)
prod = sp.expand(prod)
target = sp.expand((x**3 + y**3 + z**3)**3 - 27*x**3*y**3*z**3)
print('prod_{i,j}(x + w^i y + w^j z) == (x^3+y^3+z^3)^3 - 27 x^3y^3z^3:', sp.simplify(prod - target) == 0)
