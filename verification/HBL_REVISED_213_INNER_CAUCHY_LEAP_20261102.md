# HBL revised 2.13 — honest LEAP inner Cauchy bridge (2026-11-02)

This is a **candidate supporting lemma**, not acceptance of revised 2.13 or of the dynamical Type-II blowup main theorem.

## Strict numerical boundary

- Revised manuscript: **11/13 (84.62%)**, unchanged.
- Unmodified 2026-11-01 13-label original: **9/13 (69.23%)**, unchanged.
- Historic original 21-environment ledger: **9/21**, unchanged.
- Revised 2.12 was strictly accepted at workflow run **41465373137**.
- Existing independently integrated sources succeeded at runs **41469389648** and **41469389088**.
- New supporting Lean module: `HBL/TypeIIDynamicSelection/ActualHartreePhysicalInnerKummerBridge.lean` with an independent strict full type and axiom audit.
- Strict CI workflow: `.github/workflows/hbl-213-physical-inner-cauchy.yml`. Do not mark this candidate proved before that job concludes success.

## Exact mathematical boundary

Let `k=sqrt(q)>0`, `x_-=center-d`, `x_+=center+d`.
The single whole-radiation Hartree residual is `Fphys=Res(V+Z)-Res(V)`, where
`Z(s,R)=exp(-i gamma(s))*sqrt(ell(s))*z(time(s),ell(s)*R)`.
The fixed-annulus Kummer source is `F(x)=Fphys(k*clamp(x,x_-,x_+))`.
Under the **visible extra full complex weighted-L2 and global continuity hypotheses** for `Fphys`, the already certified H+/H- classical affine theorem constructs
`u_+` and `u_-` solving their original two physical channel equations.

Their ACTUAL Kummer-coordinate inner Cauchy data are

```
U_-=u_+(k*x_-)+i*u_-(k*x_-)
D_-=k*(d u_+/dR(k*x_-)+i*d u_-/dR(k*x_-))
```

The candidate Lean theorem computes this `k` by differentiating the constructed classical functions; it does not insert an arbitrary derivative.

Let `G_F` denote the original two-Wronskian normalized inhomogeneous Green solution, `(phi,psi)` the original physical homogeneous Kummer pair, `W_- != 0`, and `V_-=U_- -G_F(x_-)`, `E_-=D_- -G_F'(x_-)`.
The unique Cauchy coefficients are

```
a=(V_-*psi'(-d)-E_-*psi(-d))/W_-
c=(phi(-d)*E_--phi'(-d)*V_-)/W_-
```

The **remaining outer compatibility pair** is precisely

```
Uout = G_F(x_+) + a*phi(d) + c*psi(d)
DUout= G_F'(x_+)+ a*phi'(d)+ c*psi'(d).
```

This equivalence is already strictly verified by `ActualKummerTwoInterfaceObstruction.lean`. The **genuinely normalized** Green inverse is unchanged only when `a=c=0` by `ActualKummerNormalizedNoHomogeneousFreedom.lean`. Hence obtaining a local inhomogeneous IVP solution is NOT proof of global normalized Kummer matching. No additional homogeneous freedom is allowed.

## Minimal remaining dependency chain

```
[accepted revised 2.12: actual local Hartree physical source + normalized Green]
        +
[existing actual classical H+/H- inner solutions
   | explicit continuous global source and weighted L2 hypotheses]
        |
[new k=sqrt(q) inner C1 jet bridge: candidate, strict CI pending]
        |
[unproved: PDE/source conjugacy to actual Kummer equation
 and actual physical far-field classical C1 jet]
        |
[unproved: true inner/outer transfer compatibility while keeping original
 normalized Green boundary conditions; no new coefficients]
        |
[unproved: weighted nonlocal Riesz mixed-source positive-order gain
 and all moving-cutoff/parameter/Frobenius residual gains]
        |
[unproved: finite nonlinear profile recursion and energy/topology matching]
        |
[REVISED 2.13, OPEN] -> [dynamically selected Type-II rate from PDE, OPEN]
```

**Important:** The candidate module does not derive the global source continuity, weighted-L2 bound, far-field C1 jet, or physical Hartree-flow PDE from scratch. Their presence as hypotheses must not be reported as discharged. A field-defined Hartree residual is not by itself a certified global Hartree solution. The main theorem must derive, never assume, the Type-II rate.
