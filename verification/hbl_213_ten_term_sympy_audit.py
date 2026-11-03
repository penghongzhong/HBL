"""Exact symbolic check: ten original quartic Hartree interaction monomials
reduce to three weighted scale/radius envelopes. Algebra audit, NOT Lean/PDE
verification of source membership or boundary matching."""
import sympy as S
ell,d,q=S.symbols('ell d q', positive=True)
D,E,Cm,Cc,Cz=S.symbols('D E Cm Cc Cz', nonnegative=True)
v=D/d; z=E*S.sqrt(ell)/q
pm,pc,pz=Cm*S.sqrt(ell)/d,Cc/d,Cz*ell/q
w=d**S.Rational(7,4)
A1=S.sqrt(ell)*d**(-S.Rational(5,4))/q
A2=ell*d**(-S.Rational(1,4))/q**2
A3=ell**S.Rational(3,2)*d**S.Rational(3,4)/q**3
terms=[
 ('PmV3',pm*v**3,Cm*D**3,A1,q/d),
 ('PmV2Z',4*pm*v**2*z,4*Cm*D**2*E,A1,S.sqrt(ell)),
 ('PmVZ2',4*pm*v*z**2,4*Cm*D*E**2,A2,S.sqrt(ell)),
 ('PmZ3',pm*z**3,Cm*E**3,A3,S.sqrt(ell)),
 ('PzV3',pz*v**3,Cz*D**3,A1,S.sqrt(ell)),
 ('PzV2Z',4*pz*v**2*z,4*Cz*D**2*E,A2,S.sqrt(ell)),
 ('PzVZ2',4*pz*v*z**2,4*Cz*D*E**2,A3,S.sqrt(ell)),
 ('PcV2Z',4*pc*v**2*z,4*Cc*D**2*E,A1,S.Integer(1)),
 ('PcVZ2',4*pc*v*z**2,4*Cc*D*E**2,A2,S.Integer(1)),
 ('PcZ3',pc*z**3,Cc*E**3,A3,S.Integer(1)),
]
assert len(terms)==10
for name,term,coeff,env,ratio in terms:
    assert S.simplify(w*term/(coeff*env)-ratio)==0,name
    assert ratio in (S.Integer(1),S.sqrt(ell),q/d),name
    print(f'{name}: remainder = {ratio} <= 1 (0<ell<=1, 1<=q<=d)')
K1=Cm*D**3+4*Cm*D**2*E+Cz*D**3+4*Cc*D**2*E
K2=4*Cm*D*E**2+4*Cz*D**2*E+4*Cc*D*E**2
K3=Cm*E**3+4*Cz*D*E**2+Cc*E**3
for env,K in ((A1,K1),(A2,K2),(A3,K3)):
    assert S.simplify(sum(c for _,_,c,a,_ in terms if a==env)-K)==0
print('EXACT ALGEBRA PASS: all ten source monomials and their coefficients.')
print('Lean source and PDE/analytic closure require separate strict audits.')
