"""Exact algebra for the original frozen Kummer homogeneous ODE.
This checks identities only, not a Lean compilation or a PDE existence proof.
Run with Python and SymPy; all assertions are exact symbolic equalities.
"""
import sympy as S

r = S.symbols('r', positive=True)
br, bi, ur, ui, vr, vi = S.symbols('br bi ur ui vr vi', real=True)
b = br + S.I * bi
a = 2 * S.I * b
u = ur + S.I * ui
up = vr + S.I * vi
w = r * up - a * u
upp = -(2 / r + S.I * r / 2) * up - b * u
wp = r * upp + (1 - a) * up
expected_wp = -(1 + a) * w / r - a * (1 + a) * u / r - S.I * r * w / 2
assert S.simplify(wp - expected_wp) == 0

# P(r)=exp(i*r^2/4), v=P*w. Its oscillatory derivative cancels exactly.
P = S.symbols('P', nonzero=True)
vp = P * (wp + S.I * r * w / 2)
assert S.simplify(vp - (-(1 + a) * P * w - a * (1 + a) * P * u) / r) == 0

wr, wi, ar, ai = S.symbols('wr wi ar ai', real=True)
w = wr + S.I * wi
aa = ar + S.I * ai
uprime = (aa * u + w) / r
wprime = -(1 + aa) * w / r - aa * (1 + aa) * u / r - S.I * r * w / 2
Eprime = S.expand_complex(2 * S.re(uprime * S.conjugate(u) + wprime * S.conjugate(w)))
rhs = 2 / r * (
    S.re(aa) * (ur**2 + ui**2)
    - S.re(1 + aa) * (wr**2 + wi**2)
    + S.re(w * S.conjugate(u) - aa * (1 + aa) * u * S.conjugate(w))
)
assert S.simplify(Eprime - rhs) == 0
print('PASS: exact shearing w=r*uprime-2*i*b*u')
print('PASS: exp(i*r^2/4) removes the large purely imaginary radial drift')
print('PASS: exact energy identity; no O(r) contribution remains')
