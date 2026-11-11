# HBL §2.13 — a Fredholm-compatible phase source with no third spatial jet

10 November 2026 (Pacific time). This is a **decisive regularity obstruction for the proposed C³ Hermite repair as currently justified**, not a counterexample to the physical Hartree blow-up theorem. The existing actual source producers generally establish weighted L² membership, sometimes continuity, but have **not** established the C¹ source regularity required to define and bound the *same source's* third-derivative trace at the selected moving interfaces. Original environments remain **11/13**.

## An explicit source in the phase Fredholm range

Fix an interior radial interface \(R>0\) and \(0<\delta<R/2\). Let \(\chi\in C_c^\infty((R-\delta,R+\delta))\) equal 1 near \(R\). Define
\[
W(r)=(1+r^2)^{-1/2},\qquad
L_-=-\partial_r^2-\frac2r\partial_r-3W(r)^4,
\]
\[
q(r)=\frac4{15}\chi(r)|r-R|^{5/2},\qquad F(r)=L_-q(r).
\]
Near the interface (\(r\ne R\)),
\[
q''(r)=|r-R|^{1/2},\qquad
q'''(r)=\tfrac12\operatorname{sgn}(r-R)|r-R|^{-1/2}.
\]
In particular
\[
q\in C_c^2((0,\infty)),\quad q'''\notin L^2_{\rm loc}(R-\delta,R+\delta),\quad
\boxed{F\in C_c^0((0,\infty))\cap L^2_{\rm weighted}\text{ for EVERY locally bounded positive weight},\qquad F\notin H^1_{\rm loc}.}\tag{RG1}
\]
The last nonmembership follows because the smooth-coefficient lower-order terms \(-2q'/r-3W^4q\) have an \(L^2\) derivative, whereas the derivative of the leading \(-q''\) has magnitude \(\tfrac12|r-R|^{-1/2}\) and its square is nonintegrable.

Crucially this is not excluded by the phase Fredholm compatibility condition. Direct differentiation gives
\[
L_-W=0.
\]
Since \(q\) is compactly supported away from 0 and infinity, twice integrating by parts against \(W\) yields
\[
\boxed{\int_0^\infty r^2W(r)F(r)\,dr
=\int_0^\infty r^2(L_-W)(r)q(r)\,dr=0.}\tag{RG2}
\]
Thus \(F\) is continuous, belongs to the weighted source Hilbert space (and so does \(rF\), the common conjugated input on a compact positive-radius annulus), and satisfies the exact phase Fredholm zero-mode cancellation; nevertheless its origin-regular solution can lack the very third derivative used by the proposed repair.

Any other classical solution \(v\) of \(L_-v=F\) near \(R\) differs from \(q\) by a solution of a *homogeneous smooth-coefficient* second-order ODE. That difference is smooth near \(R\), so it cannot cancel the failure of \(q'''(R)\) or the nonintegrability of \(q'''\). Therefore changing the normalized Green representative by a homogeneous solution cannot resolve (RG1). This shows that even pointwise continuity **plus** Fredholm compatibility **do not imply** the existence of the actual third-jet discrepancy \(d_3\).

## Exact implication for the 4-region original-Hartree route

The accepted theorem `actual_Hartree_true_inner_spectral_C2_jump_native_shell_budget` uses weighted L² input together with *continuity* of the two inner sources. The compatible C³ repair lemma `actual_Hartree_physical_C3_repair_endpoint_jets`, strict CI 42944437228, proves a correct polynomial statement **provided** its independent jet arguments \(d_2,d_3\) are already actual numbers from the same field. The preceding example demonstrates that the former hypotheses cannot produce the latter inputs. The existing proof cannot silently instantiate a \(d_3\) or upgrade its strong source norm from the polynomial identities.

One sufficient route is to derive physical source \(F_p,F_m\in C^1\) in a full moving neighborhood of each interface, prove the corresponding normalized Fredholm and Kummer fields are \(C^3\) up to the interface, and obtain real estimates for \(\partial_r F_p,\partial_r F_m\), the two actual third jets, and their parameter/time differences. Weighted L² and mere continuity are insufficient. An alternative is to replace the differentiated Hessian--Morawetz topology by a dispersive error topology that does not require these traces, but then its full original-Hartree evolution and modulation estimates must be separately proved.

This does **not** assert that the specifically constructed physical Hartree radiation \(z\) is rough: a smooth actual trajectory could satisfy the missing regularity. The point is that current original-PDE source hypotheses, with \(z\) only measurable and bounded in the retained static producer, **cannot guarantee** it. The companion global feedback bound `HBL_213_TRUE_HARTREE_C3_NONLOCAL_FEEDBACK_20261110.md` controls \(\dot H^{-1}\), not the demanded differentiated source norm, and therefore does not bypass this gate.

**Evidence:** historical strict original-Hartree C²-source module CI 42854633900 and new strictly successful C³ *polynomial only* CI 42944437228 (Lean 4.35.0-rc3, Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, --trust=0, warningAsError, only `propext`, `Classical.choice`, `Quot.sound`). This counterexample and the stated regularity gap are **paper proofs, not new Lean-certified declarations**. Neither §2.13 nor the final PDE-derived Type-II theorem is closed; unchanged **11/13**.
