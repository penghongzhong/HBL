# HBL revised §2.13 and dynamically selected Type-II blowup — a shorter proof spine (10 November 2026)

**Status and audit:** The original 13 retained revised paper environments are still **11/13**. This is a **mathematical reduction of the proof obligations**, not an accepted new environment, a Lean theorem, or a constructed Hartree PDE trajectory. No prescribed \(\nu\), blowup exponent, numerical residual, external source estimate, or new Lean axiom is introduced.

**Current public branch at start:** `hbl-213-spectral-c1-trace-20261109`, HEAD `ffc4e007ebb90fca7e8a30830435f9dfa8f31d8b`.
The preceding moving-slit annulus theorem passed [CI 42756618784](https://github.com/penghongzhong/HBL/actions/runs/42756618784), original job **129632373174**, evidence **13736666241**. Decoded log confirms pinned Lean 4.35.0-rc3, Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`, `--trust=0 -DwarningAsError=true`, exact `#check` / `#print axioms` and only `Classical.choice`, `Quot.sound`, `propext`. The existing continuous-orbit local-domain theorem in that file was **not** an audited target of this job; do not treat it as independently accepted.

## 1. What the comparison with established blowup papers actually suggests

| Verified published reference | Proof architecture to reuse | Boundary for our Hartree problem |
|---|---|---|
| P. Raphaël–I. Rodnianski, *Publ. Math. IHÉS* **115** (2012), 1–122, DOI [10.1007/s10240-011-0037-z](https://doi.org/10.1007/s10240-011-0037-z) | §6 explicitly obtains finite-time blowup already from a **crude** modulation and energy bootstrap; §7 subsequently refines the flux law to a **sharp** rate. Two-stage proof is faithful to dynamic rate selection. | The wave-map/Yang–Mills coercive energy identities do **not** automatically apply to the dispersive nonlocal Hartree generator; this must be rederived. |
| F. Merle–P. Raphaël–I. Rodnianski, *Invent. Math.* **193** (2013), 249–365, DOI [10.1007/s00222-012-0427-y](https://doi.org/10.1007/s00222-012-0427-y) | Dynamical concentration near an energy-critical bubble plus modulation and control of neutral/unstable directions, rather than a prescribed exponent. | Two-sphere equivariant Schrödinger maps have a different linearized operator and no Hartree Riesz tail. |
| C. Collot–F. Merle–P. Raphaël, *J. Amer. Math. Soc.* **33** (2020), 527–607, DOI [10.1090/jams/941](https://doi.org/10.1090/jams/941) | A small number of **closed energy bootstrap estimates** can replace a large sequence of explicitly expanded approximate-profile bounds. | Their equation is *parabolic*; dissipativity cannot be copied into a Hamiltonian Hartree equation. |
| J. Krieger–W. Schlag–D. Tataru, *Duke Math. J.* **147** (2009), 1–53, DOI [10.1215/00127094-2009-005](https://doi.org/10.1215/00127094-2009-005) | Renormalized parametrix and spectral transform control. | Their rate is deliberately **selected in the ansatz**; copying this part would not prove HBL's required *emergent* exponent. |

**Decision:** use the Raphaël–Rodnianski **coarse trap first, sharp rate second** organization, retaining the original HBL physical source and two-mode Cramer selection. Do not try to make every high-order moving-Kummer derivative a prerequisite of the *kinematic* final Type-II conclusion.

## 2. Elementary but decisive dynamical reduction: a bounded modulation trapping interval already gives Type II

Let \(s\ge s_0\), and suppose an **actually constructed PDE solution**, with scale \(\lambda(s)>0\), phase, and the same two physical orthogonality conditions, produces real functions \(q(s)>0\) and \(\mu(s)\) obeying
\[
q_s=4\mu,\qquad b=\frac{\lambda_s}{\lambda}=\frac{1+4\mu}{2q}.
\]
Do not initially specify the physical terminal time or a power-law exponent. It is enough for the **coarse** stage to close
\[
q(s_0)=q_0>0,\qquad 0<m\le \mu(s)\le M<\infty
\quad(s\ge s_0).
\tag{A}
\]
Then
\[
q_0+4m(s-s_0)\le q(s)\le q_0+4M(s-s_0),\qquad q(s)\to\infty.
\tag{B}
\]
The two exact modulation identities yield
\[
\frac{d}{ds}\log\frac{q(s)}{\lambda(s)^2}
=\frac{q_s-2bq}{q}=-\frac1q.
\]
Consequently, setting \(\lambda_0=\lambda(s_0)\),
\[
\tau(s):=\frac{q(s)}{\lambda(s)^2}
=\frac{q_0}{\lambda_0^2}
  \exp\!\left(-\int_{s_0}^s\frac{du}{q(u)}\right)>0,
\qquad
\tau_s=-\lambda^{-2}.
\tag{C}
\]
Using the **upper** bound in (B),
\[
\int_{s_0}^s\frac{du}{q(u)}
\ge \frac1{4M}\log\!\left(1+\frac{4M(s-s_0)}{q_0}\right)
\longrightarrow+\infty .
\]
Thus \(\tau(s)\to0\). If \(t_s=\lambda^{-2}\) with \(t(s_0)=t_0\), then \(t(s)+\tau(s)=t_0+q_0/\lambda_0^2\), so
\[
T:=t_0+\frac{q_0}{\lambda_0^2}<\infty,\quad
t(s)\uparrow T,\quad
q(s)=(T-t(s))\lambda(s)^2
\tag{D}
\]
are **deduced**, not imposed as blowup rates. Finally
\[
\boxed{\frac{\lambda(s)^{-1}}{\sqrt{T-t(s)}}
       =q(s)^{-1/2}\longrightarrow0.}
\tag{E}
\]
This is strict Type-II concentration, provided that the *same genuine*
Hartree solution has a concentrating \(W_\lambda\) plus a
\(\dot H^1\)-controlled error and cannot extend strongly across \(T\).
The nonlinear orbit and nonextension statements are separate, unsolved PDE obligations.

**No estimate of \(\mu_s\), no limit \(\mu_\infty\), and no rate parameter chosen in advance is required for the coarse (E) conclusion.** The existing original threshold may be kept by proving a forward invariant \(m>9/16\) from actual PDE projections. Such invariance is **not** yet established.

## 3. Sharp emergent power can be postponed — and its scalar hypothesis is weaker than before

The original final main target still demands
\[
\lambda(t)^{-1}=C_\lambda(T-t)^{1/2+2\mu_\infty}(1+o(1))
\quad\text{for some dynamically produced }\mu_\infty>9/16.
\]
Do **not** delete this target from the main theorem. It is a **second** stage.

It is sufficient at this *scalar stage* to prove, from the **actual physical Hartree projected modulation forcing** \(e=\mu_s\),
\[
\mu(s_0)>\frac9{16}+\epsilon,\quad
\int_{s_0}^{\infty}(1+\log (u/s_0))\,|e(u)|\,du
<\epsilon,\qquad s_0>0,
\tag{F}
\]
where the smallness is to be chosen strictly so that \(\mu_\infty>9/16\).
Equation (F), together with local absolute continuity, implies
\(\mu(s)\to\mu_\infty\) and
\[
\int_{s_0}^\infty\frac{|\mu(u)-\mu_\infty|}{u}\,du
\le\int_{s_0}^\infty
\log(v/s_0)|e(v)|\,dv<\infty.
\tag{G}
\]
By (B), \(q(s)\sim4\mu_\infty s\). Moreover, from
\(q(s)-4\mu_\infty s=C+4\int_{s_0}^s(\mu(u)-\mu_\infty)\,du\),
Tonelli and (G) imply
\[
\int_{s_0}^\infty
\left|\frac1{q(s)}-\frac1{4\mu_\infty s}\right|\,ds<\infty
\quad\text{(after shifting the finite lower range if needed)}.
\tag{H}
\]
Therefore (C) and \(\lambda^2=q/\tau\) yield
\[
\tau(s)=c_\tau s^{-1/(4\mu_\infty)}(1+o(1)),\qquad
\lambda(s)=c_\lambda s^{1/2+1/(8\mu_\infty)}(1+o(1)),
\]
and hence the **dynamically selected** rate
\[
\boxed{\lambda(t)^{-1}
=C_\lambda(T-t)^{1/2+2\mu_\infty}(1+o(1)).}
\tag{I}
\]
This does **not** prescribe \(\mu_\infty\): it is the limit of the
**actually constructed** real modulation coordinate.
For the **pure-power rate conversion alone**, the *logarithmically weighted
time integral* (F) suffices in place of the earlier stronger pointwise rate
\(|\mu_s|\le Cs^{-1-\delta}\). **Transparent theorem revision, 10 November 2026:** the earlier additional pointwise statement \(|\mu_s|\le Cs^{-1-\delta}\) has now been **removed from the revised main target** in verification/typeii-minimal-main-replacement.tex, while the dynamically selected \(\mu_\infty>9/16\), a genuine Hartree strong orbit, and the **sharp emergent power law** are retained. The log-weighted L1 physical flux (F) is the remaining sufficient proof obligation for the sharp scalar factor; it is NOT yet proved by the actual PDE.
However (F) has **not** yet been derived from the HBL PDE; this is a
mathematically valid conditional reduction, **not a Lean acceptance**.

## 4. The real obstruction is earlier than the final rate

The earlier **conditional static spatial-shell calculation** for the
actual nonlocal Hartree kernel yields an \(O(s^{-15/8})\) remainder
from an \(s^{-9/8}\) first correction **provided** the assumed
physical shell amplitude, support and background controls hold.
This estimate has **not** been verified as the entire moving
four-region PDE remainder. An **undamped absolute backward
Duhamel estimate** gives
\[
\int_s^\infty u^{-15/8}\,du
=\frac87s^{-7/8},
\]
which is **larger** than \(s^{-9/8}\) by \(s^{1/4}\).
This discrepancy cannot be repaired by proving more Cramer, Green,
C¹, or telescope identities; they do not furnish the needed
source/propagator gain.

There are only two honest quantitative repairs for **this specific
backward norm**:

* Improve the actual whole-PDE source to
  \(s^{-(17/8+\eta)}\), \(\eta>0\), to obtain
  \(o(s^{-9/8})\) by absolute integration. The previously requested
  \(s^{-9/4}=s^{-18/8}\) would be stronger by \(s^{-1/8}\)
  than strictly necessary for this **single** Duhamel comparison.
  **Do not lower any other manuscript target requiring 9/4 without
  checking its own norm/exponent balance.**
* Or obtain a genuine nonlocal projected Hamiltonian inverse/normal
  form gain of at least \(s^{-1/4-\eta}\) relative to the absolute
  estimate, while retaining the actual zero/threshold resonances.
  Such dispersive cancellation is not implied by parabolic
  coercivity and is presently **unproved**.

The strictly audited original Green moving-slit Frobenius factor \(R\)
could contribute a spatial gain only if the **same physical differentiated
source**, moving Kummer basis, moving interfaces, and the **entire**
four-region residual preserve it. If one succeeds in proving a full
source estimate \(R(s)s^{-15/8}\) with \(R(s)\lesssim s^{-\theta}\),
then this particular Duhamel norm closes when
\(\theta>1/4\); currently the available theorem is a *conditional
Green mixed-difference bound*, **not** this four-region estimate.

### Why adding more finite-profile helper lemmas will not resolve 11/13

An actual code audit of
[ActualHartreePhysicalFiniteProfile.lean](https://github.com/penghongzhong/HBL/blob/hbl-213-spectral-c1-trace-20261109/HBL/TypeIIDynamicSelection/ActualHartreePhysicalFiniteProfile.lean)
shows that its theorem on finite termination takes a *pre-supplied*
list of abstract regional \`ActualHartreeLayerPacket\` objects and
assumes the step inequality
\(\mathrm{weight}(j)+\kappa\le\mathrm{weight}(j+1)\).
Its \`ActualHartreePacketCertified\` also contains the tautology
\`Q.tangent = Q.tangent\`, not a physical threshold-tangent
equation. Thus the accepted algebra of finite termination
**does not construct** a single stage from the original nonlocal
four-region Hartree PDE.

This is the concrete point where many previously compiled
lemmas cease to be load-bearing. Stop extending this
conditional packet-consumer branch. The next proof must produce
a source-faithful packet (or replace the packet recursion with
one genuinely closed projected-energy bootstrap), including
the same-source full PDE defect, exact charge/matching and a
quantitative gain on the *actual* next residual. No percentage
increase follows from another conditional finite-termination
theorem.


## 5. Revised short dependency graph for ONE physical orbit

```text
ACTUAL 3D NONLOCAL HARTREE PDE + nonzero smooth radial terminal radiation
   |
   +-- [strict auxiliary] true mixed/pure/core Riesz source and velocity
   +-- [strict auxiliary] original Wronskian, real Cramer selector,
   |                      weighted C1/Green and three C1 joins
   +-- [strict auxiliary] two moving Green time derivatives and
   |                      moving-slit/annulus coverage CI 42756618784
   |
   +-- [OPEN, load-bearing] one source-faithful projected
   |     whole-four-region residual + inverse/energy flux estimate
   |     that closes the 1/4 Duhamel gap without hidden radius losses
   |
   +-- [OPEN, load-bearing] one actual physical orbit and controlled
   |     radiation in Hdot1, modulation bootstrap, unstable-mode shooting
   |
   +-- [OPEN, load-bearing] invariant positive trapping
   |     9/16 < m <= mu(s) <= M, from actual projected PDE
   |
   +-- [PAPER-PROVED KINEMATIC CONSEQUENCE, not accepted original PDE]
   |     q_s=4mu -> finite T, Type-II q->infinity by (A)-(E)
   |
   +-- [OPTIONAL SHARP STAGE OF EXISTING ORIGINAL MAIN TARGET]
         PDE gives log-L1 projected drift (F)
         -> emergent mu_infinity -> power asymptotics (I)
   |
   +-- [NOT ACCEPTED] original revised §2.13 -> 12/13
   +-- [NOT ACCEPTED] original dynamical Type-II main -> 13/13
```

**Remove from the required spine, but do not delete verified sources:**
repeated derivative rewrappings, multiple equivalent fixed-basis Green
bounds, fictitious independent source norm assumptions, optional
uniform all-parameter \(C^1\) shooting graphs, prescribed-rate branches,
and restatements of the exact PDE telescope as if it were a positive
gain. Their strict successes remain true, but they do not directly
advance §2.13 or the main theorem.

**No new Lean theorem is added simply to make the percentage larger.**
Before claiming progress to 12/13, compile one source-aligned theorem
that really constructs (not assumes) the corrected physical four-region
Hartree orbit with the necessary quantitative error and common-domain
time controls, and check its transitive axiom set with the pinned
`--trust=0` workflow.

This research note is cross-referenced from
`verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex`
and `verification/HBL_213_SHORTEST_MAIN_CHAIN_CI_20261108.md`.


## 6. One physical projected-flux estimate can supply BOTH trapping and sharp selection

This removes a second logical redundancy in the former main proof. Suppose
one *constructed real Hartree orbit* supplies the exact projected modulation
identity \(\mu_s=e_{\rm proj}(s)\), locally absolutely continuously.
Fix \(\mu(s_0)>9/16+\varepsilon\), \(\varepsilon>0\).
A **single genuine nonlinear projected-flux bound**
\[
\int_{s_0}^\infty
  (1+\log(s/s_0))\,|e_{\rm proj}(s)|\,ds\le\varepsilon
\tag{J}
\]
then gives, for every \(s\ge s_0\),
\[
 \mu(s_0)-\varepsilon\le \mu(s)\le \mu(s_0)+\varepsilon,
 \qquad \mu(s)\to\mu_\infty>9/16,
\tag{K}
\]
and the log-weighted tail required for the dynamically generated sharp
power law. Thus one need not separately establish an independent
uniform modulation trap *and then* derive a new sharp-flux estimate.
The same input (J) carries both.

A **conditional and potentially more favorable source target** is
\(|e_{\rm proj}(s)|\le Cs^{-15/8}\), because
\[
\int_{s_0}^\infty
  (1+\log(s/s_0))\,s^{-15/8}\,ds
 =\left(\frac87+\frac{64}{49}\right)s_0^{-7/8}
 =\frac{120}{49}s_0^{-7/8}.
\tag{L}
\]
For sufficiently large \(s_0\), this would give (J) with an
arbitrarily small drift. **Crucial distinction:** the \(s^{-15/8}\)
figure in the current manuscript comes from a **conditional spatial
shell remainder**, not from the actual projected modulation ODE on
a constructed whole Hartree orbit. The implication to
\(e_{\rm proj}\) is *unproved*: one must identify the exact
real two-channel projection, moving basis and normalization,
all four physical nonlocal regions and the correct denominator.
No \(O(s^{-15/8})\) projected flux is asserted here.

The required physical thresholds are now separated: the
**projected modulation flux** needs only a sufficiently small
log-weighted \(L^1\) time bound for positive trapping and an
emergent exponent, while the **full nonresonant correction**
still faces the \(s^{1/4}\) undamped Duhamel deficit. Both
must ultimately come from the same true physical Hartree orbit.

Lean correspondence: the SINGLE certified
actual_Hartree_coarse_TypeII_clock_from_dynamical_mu_trap
(CI 42766649238, exact three-axiom audit) consumes the
trap potentially produced by (J). It proves growing
\(q\) and vanishing Type-I-normalized concentration.
No additional helper Lean theorem, axiom or numbered paper
environment is introduced merely for (J)–(L).


## 7. A more viable nonresonant inverse: dual-Kato \(L_s^2\) smoothing rather than bare \(L_s^1\) integration

**New, directly relevant external references (verified 10 November 2026).**
Tobias Schmid, *Blow up dynamics for the 3D energy-critical nonlinear
Schrödinger equation*, *Calculus of Variations and Partial Differential
Equations* **65** (2026), article 69, published 16 February 2026,
[DOI 10.1007/s00526-025-03240-x](https://doi.org/10.1007/s00526-025-03240-x),
constructs genuine 3D energy-critical NLS single-bubble Type II solutions,
via a highly developed KST/Perelman spectral parametrix. **His
NLS rates are chosen in the approximate solution**: they cannot by
themselves prove the distinct HBL goal of an emergent rate.

Taegyu Kim, *Smooth radial quantized Type II blow-up for the
three-dimensional energy-critical nonlinear Schrödinger equation*,
[arXiv:2610.26127](https://arxiv.org/abs/2610.26127),
submitted 19 October **2026**, is a **preprint**, not to be
represented as a peer-reviewed top-journal article. Its abstract
reports a forward modulation/energy construction and replaces an
unavailable repulsivity argument by Kato smoothing and a global
spacetime Morawetz estimate for the linearized flow. This is the
specific part that may help HBL avoid its backward \(L_s^1\) deficit.

**The actual Hartree linearization is genuinely nonlocal.** Define
\(I_2 f=\kappa_{\rm H}(|x|^{-2}*f)\) and
\(V_W=I_2(W^4)\) for the stationary real \(W\). For
\(h=h_1+ih_2\), the real linearization is
\[
L_-h_2=-\Delta h_2-V_W W^2h_2,\qquad
L_+h_1=-\Delta h_1-3V_W W^2h_1
           -4W^3 I_2(W^3h_1).
\]
The time generator in the real coordinates is
\(\mathcal H_{\rm H}=\left(\begin{smallmatrix}0&L_-\\-L_+&0\end{smallmatrix}\right)\).
**Do not omit the final nonlocal integral operator in \(L_+\)**;
replacing it by a local NLS potential would invalidate the argument.

On a **genuinely constructed** nonresonant continuous spectral
subspace, after retaining the true generalized threshold modes and
unstable direction, the proposed new load-bearing target is a
projected dual-Kato/limiting-absorption estimate for the **actual**
Hartree propagator (including admissible moving modulation perturbations)
of the form
\[
\boxed{
\left\|
 \int_s^\infty U_{\rm H}(s,\sigma)
 P_{\rm nr} F(\sigma)\,d\sigma
\right\|_{X_s}
 \le C_{\rm Kato}
 \left(\int_s^\infty\|F(\sigma)\|_{Y_\sigma}^2d\sigma\right)^{1/2}.
}
\tag{M}
\]
Here \(X_s,Y_s\) must be the explicitly derived physical
weighted energy/source spaces, not freely chosen norm packets.
Neither \(P_{\rm nr}\), the limiting-absorption estimate nor
the nonautonomous flow needed for (M) is presently constructed for
the original nonlocal Hartree Hamiltonian. The NLS references
do **not** imply (M).

**Why (M) is potentially decisive:** If the **full physical PDE**
nonresonant forcing were genuinely bounded in \(Y_s\) by
\(C_Fs^{-15/8}\) (currently known only for a **conditional static
shell**, not yet the entire source), then
\[
\int_s^\infty (C_F\sigma^{-15/8})^2d\sigma
=\frac4{11}C_F^2s^{-11/4},
\qquad
\left(\int_s^\infty (C_F\sigma^{-15/8})^2d\sigma\right)^{1/2}
=\frac{2C_F}{\sqrt{11}}s^{-11/8}.
\tag{N}
\]
This gains a full \(s^{-1/2}\) relative to the failed absolute
\(s^{-7/8}\) estimate and, more importantly, would be
\(s^{-1/4}\) smaller than the desired \(s^{-9/8}\) first correction:
\[
s^{-11/8}=s^{-1/4}s^{-9/8}.
\]
A successful **Hartree-specific** weighted Kato/Morawetz bound can
therefore genuinely circumvent the obstruction identified in §4,
without forcing the nonlinear physical source up to order \(>17/8\).
It is *not* an automatic consequence of an \(L_s^2\) source bound:
the boundedness of the **causal inverse** in (M), after extracting
zero-resonant modes and accounting for the nonlocal kernel, must
actually be proved.

**Shortest recommended implementation order:**
first establish the genuine Hartree \(L_\pm\) factorization and
nonlocal spectral/threshold projection; next a resolvent or
Kato smoothing bound on the projected continuous space; then
the same-source four-region \(Y_s\)-norm control, followed by
the nonlinear weighted fixed point. Keep the previously strict
fixed-\(K_0\) spectral cancellation and three C¹ joins; use the
original two-real-channel modulation equations for the emergent
rate separately. Avoid reverting to a prescribed NLS-style
blowup exponent.

**Lean synchronization:** The existing original
ActualHartreeShellDuhamelExponent.lean now includes one precise
squared-time-tail integral declaration
actual_Hartree_shell_squared_source_exact_L2_time_tail.
Its dedicated six-target pinned trust-zero CI is enabled.
A successful CI verifies (N)'s scalar power integral **only**.
The analytic dual-Kato operator estimate (M) is still the real
physical PDE obstacle; neither it nor original §2.13 may be counted
from that auxiliary scalar proof.


### 7.1 Existing Hartree code that substantially reduces the new spectral task

A branch source audit confirms
HBL/WeightedHartreeBirmanSchwinger.lean has the **actual
conjugated nonlocal kernel**
\[
 K_{\mathrm H}(r,\rho)
 =8\pi\kappa_{\rm H}W(r)W(\rho)
   \log\frac{r+\rho}{|r-\rho|},
\]
and the concrete declarations
weightedHartreeKernel_sq_integrable,
weightedHartreeOperator_kernel_certificate,
weightedHartreeOperator_selfAdjoint,
weightedHartreeOperator_compact,
weightedBirmanSchwingerOperator_compact.
The compact nonlocal kernel and its symmetry are
**not missing in principle**; these are already encoded as
Lean proofs and are promising dependencies to reuse, without
creating yet another Hartree potential approximation.

**But they are zero-energy/compact perturbation input only.**
They do not prove the uniform positive-energy boundary
values of the *non-selfadjoint matrix* Hartree resolvent,
absence of nonzero embedded eigenvalues, or the global
projected local-smoothing estimate (M). In Kim's
October 2026 NLS preprint, the global Morawetz
construction explicitly relies on a **separate companion
result excluding nonzero embedded eigenvalues**
(see its introductory Remark 1.2). An analogous
**Hartree-specific** spectral exclusion is therefore
an actual high-priority analytic gate, not a mere
additional Lean tactic.

The shortest honest new source chain is:
\[
\boxed{
\begin{gathered}
 \text{existing symmetric compact Hartree radial kernel}\\
 \Downarrow\quad
 \text{real nonlocal }L_\pm \text{ and exact zero modes}\\
 \Downarrow\quad
 \text{matrix resolvent + no embedded eigenvalues
       + threshold limits}\\
 \Downarrow\quad
 \text{projected dual Kato / Morawetz in physical spaces}\\
 \Downarrow\quad
 \text{same four-region Hartree nonlinear source in }L_s^2Y_s\\
 \Downarrow\quad
 \text{physical stable inverse / actual one-orbit construction}.
\end{gathered}}
\]
The first item has concrete original Lean producers.
The last four arrows are **OPEN** and may be
harder than the existing fixed-Kummer direct
profile route. Treat dual-Kato as a **single
well-specified alternative**, not as license
to add an unlimited second theorem tree.


## 8. Published HARTREE spectral producer: exact real radial zero-mode classification (10 November 2026)

**Authoritative, equation-matched literature** (not the local quintic NLS analogue):

* X. Li, C. Liu, X. Tang and G. Xu, *The nondegeneracy of positive bubble solutions for generalized energy-critical Hartree equations*, **Science China Mathematics** (published 29 May 2026), DOI **10.1007/s11425-025-2549-6**, original [arXiv:2304.04139](https://arxiv.org/abs/2304.04139), **Theorem 1.4** and equation **(1.11)**. This covers every \\(N\\ge3\\), \\(0<\\lambda<N\\) with \\(p=(2N-\\lambda)/(N-2)\\), including **our exact \\(N=3,\\lambda=2,p=4\\)** inverse-square quartic nonlocal Hartree operator. The bounded, vanishing-at-infinity kernel of the real linearized operator is exactly the span of the scaling and spatial translation derivatives. On the **radial** subspace only the scaling derivative remains.
* X. Li, C. Liu, X. Tang and G. Xu, *Dynamics of radial threshold solutions for generalized energy-critical Hartree equation*, **Forum Mathematicum** **37** (2025), 1469–1502, DOI **10.1515/forum-2024-0301**, [arXiv:2310.14646](https://arxiv.org/abs/2310.14646), §2.5 equations **(2.8)–(2.10)** and the energy-class nondegeneracy discussion. This already defines the genuine **nonlocal** Hartree two-component Hamiltonian, so a local-NLS surrogate must not be used as the core resolvent.

With the physical normalization \\(\\mathcal I f=\\kappa_{\\rm H}(|x|^{-2}*f)\\), \\(W=(1+|x|^2)^{-1/2}\\), the exact complex linearization at the real bubble has blocks
\\[
 L_-h=-\\Delta h-\\mathcal I(W^4)W^2h,\\qquad
 L_+h=-\\Delta h-3\\mathcal I(W^4)W^2h
       -4W^3\\mathcal I(W^3h),\\qquad
 \\mathcal H_{\\rm H}=\\begin{pmatrix}0&-L_-\\\\L_+&0\\end{pmatrix}.
\\]
The published **elliptic nondegeneracy** gives \\(\\ker L_+\\cap\\{\\text{radial, bounded, decaying}\\}=\\mathrm{span}\\{\\Lambda W\\}\\) and \\(L_-W=0\\) follows directly from the ground-state identity. These are eligible as *cited external analytic inputs*, subject to exact normalization and function-space translation; **no new Lean axiom has been inserted**.

**Still NOT supplied by elliptic nondegeneracy:** absence of nonzero embedded eigenvalues or troublesome threshold resonances of the **full coupled Hamiltonian** \\(\\mathcal H_{\\rm H}\\), a uniformly bounded projected limiting-absorption resolvent in the physically matching nonlocal weighted dual spaces, and the associated **adjoint Kato homogeneous smoothing**; neither is the required **actual four-region Hartree PDE source** factored and controlled in the corresponding dual smoothing norm. Static Cramer/Fredholm coercivity and a zero-kernel classification cannot be relabelled as a dispersive estimate. Specifically, the rigorous abstract bridge would require
\\[
 \\|A U_{\\rm H}(\\cdot)^*P_{\\rm nr}h\\|_{L^2(\\mathbb R;Y)}
    \\le C\\|h\\|_{\\mathcal E},\\qquad
 P_{\\rm nr}F(s)=A^*g(s),\\quad \\|g(s)\\|_Y\\le C_Fs^{-15/8},
\\]
from which the **dualized** inverse has tail \\(\\|\\epsilon(s)\\|_{\\mathcal E}\\le (2CC_F/\\sqrt{11})s^{-11/8}\\); this is conditional and does **not** assert it for the Hartree model. Any moving-flow perturbation must also be absorbed with uniform and Lipschitz estimates. In particular **one needs the adjoint estimate for the actual Hartree projected group**, rather than only a spatial elliptic Green bound. This identifies a falsifiable and much narrower spectral task than simply adding further Cramer identities.

**Existing exact arithmetic certificate:** CI 42776359428 proves only the scalar square-tail integral. **No §2.13 acceptance; 11/13 remains exact.**


## 9. Decisive norm-interface obstruction: shell \(L^2\) is not Morawetz-dual (10 November 2026)

The full proof and source/propagator acceptance conditions are in
[\`verification/HBL_213_DUAL_KATO_SOURCE_NORM_OBSTRUCTION_20261110.md\`](HBL_213_DUAL_KATO_SOURCE_NORM_OBSTRUCTION_20261110.md).
For the exact stationary Hartree bubble, \(L_-=-\Delta-3W^4\).
Taking \(F_N=\chi\sin(Nr)\), \(g_N=N^{-1}F_N\) on \(1<r<2\)
gives uniformly bounded shell \(L^2_{7/4}\) and test Morawetz norms,
but \((L_-g_N,F_N)_{L^2(\mathbb R^3)}\sim
2\pi N\int_1^2 r^2\chi^2\,dr\to+\infty\).
Consequently the existing *spatial* original Hartree source-norm proofs
cannot be fed unchanged into the *energy-dual* Hartree Kato/Morawetz estimate.
To use that route one must prove the **actual** four-piece source
in the matching adjoint range/functional norm, **and** the true projected
Hartree Hamiltonian homogeneous smoothing/limiting-absorption bound,
with moving parameters and threshold/unstable spectral pieces controlled.
The counterexample does not rule out favorable cancellations of the
special PDE source and is not a Lean theorem. All original environment
acceptance counts remain **11/13**.


## 10. Original affine outer repair is only C¹: explicit interface delta-prime gate (10 November)

The actual matched spectral four-region Lean source uses an affine physical repair
\(\chi_B(y/a)[w(B)+(y/a-B)w'(B)]\). Since the old
cutoff is **one near \(B\)**, the **outer splice**
has the explicit second-derivative jump
\([U_{yy}]_{aB}=-a^{-2}w''(B)\) unless the real physical
source happens to cancel it. The strict C¹ proofs have no second-jet
hypothesis. Under a sufficiently smooth moving interface, the nonlinear
PDE residual therefore inherits a jump. An arbitrary residual
jump \(J\ne0\) produces the boundary term
\(R^2 g'(R)J\) in \(\langle-\Delta g,F\rangle/(4π)\);
unit-Morawetz-norm narrow-shell tests make this term unbounded.
Thus *even the more explicit weighted \(F'\)-sufficient source norm*
in the preceding section cannot be consumed without stronger
interface regularity or a differently proved smoothing duality.

A direct source-faithful candidate is to replace the old affine
repair with
\[
 \chi_B(y/a)\{w(B)+(y/a-B)w'(B)
           +\tfrac12(y/a-B)^2 w''(B)\},
\]
and repair the separate Fredholm--Kummer second jet at \(L\).
The entire curvature budget, additional physical PDE commutator,
moving basis/endpoint/selector derivatives and parameter-Lipschitz
estimates remain **open**. The exact derivation is in
[\`HBL_213_C1_GLUE_DUAL_SOURCE_INTERFACE_GATE_20261110.md\`](HBL_213_C1_GLUE_DUAL_SOURCE_INTERFACE_GATE_20261110.md).
This repairs the *proof architecture*, not the actual PDE orbit.
**Original 13-environment acceptance remains 11/13.**


## 11. Prefer source-faithful flat overlaps if the curvature point trace is too expensive

The selected true Kummer equation has
\(w''(B)=F(B)-dw_1(B)-c_1(B)w'(B)-(c_0+d)w(B)\).
The existing \(L^2_{7/4}\) source class admits smooth fixed-annulus
spikes with bounded norm and arbitrarily large \(F(B)\).
Consequently a quadratic jet-matched repair is a \emph{valid formal}
C² construction but has no uniform curvature budget without a
stronger physical source trace or a special cancellation.

The source-aligned alternative is a **backward** flat overlap
on the true original Fredholm/Kummer shell \([L/2,L]\).
Use \(h_{\rm in}=L/8\), \(h_{\rm out}=(aB-L)/8\) and
\[
 \eta(y)=\mathrm{cutoff}((y-L+4h_{\rm in})/h_{\rm in}),\qquad
 \chi(y)=1-\mathrm{cutoff}((y-aB+4h_{\rm out})/h_{\rm out}),
 \qquad U=(1-\eta)u+\eta\chi v.
\]
The earlier forward-inner overlap \(y>L\) is withdrawn
because its Fredholm estimates were not established there.
The real inner cutoff transition is contained in
\([5L/8,3L/4]\); the actual Kummer value/slope
match at \(L\) supplies \(e(L)=e'(L)=0\).
For a local \(H²\) mismatch with \(E=\|e''\|_{L²([L/2,L])}\),
the exact undifferentiated inner cutoff commutator has no
negative overlap-width power:
\(\|\mathcal C_{\rm in}\|_2
\le(2\sqrt3C_1+3C_2+3C_1M_0h_{\rm in})E\);
its spatial derivative retains a fully explicit
\(h_{\rm in}^{-1}E\) cost.
This removes the point-jet obstruction by construction while
displaying \(h^{-j}\) and moving-material commutators explicitly.
It must still prove the actual complete nonlocal PDE source
weighted radial \(H^1\) / smoothing-dual control and
\(h^{-j}\) geometry, not simply rely on smooth cutoff algebra.
See [exact overlap note](HBL_213_SOURCE_FAITHFUL_FLAT_OVERLAP_20261110.md).
The coupled Hartree spectral adjoint Kato inverse remains an
independent hard gate. None of these new notes implies a
nonlinear orbit or a dynamically produced Type-II rate.
**Strict original 13-environment count: 11/13**.


## Full original Hartree nonlinear remainder is now *quadratic* in actual field norms (paper)

A direct computation on the true inverse-square quartic nonlocal
\(\mathcal N_{\rm H}\) identifies its real derivative
\(9W⁴u_1+3iW⁴u_2+4W³\mathcal I(W³u_1)\)
and the exact full remainder
\(3W²Q_2+\mathcal I(4W³u_1)(Q_1+Q_2)+
\mathcal I(\rho_2)Q(W+u)\).
The genuine radial weighted norms \(U=\|u\|_{L²(dr)}\),
\(H=\|(1+r²)u'\|_{L²(dr)}\), together with the established
weighted \(A_2\) Riesz theorem, yield an explicit universal
\[
 \|\mathcal R_{\rm H}(u)\|_2+
 \|(1+r²)\mathcal R_{\rm H}(u)'\|_2
 \le C(U+H)^2,\qquad 0\le U,H\le1.
\]
The complete coefficients and the exact critical-scale
\(\lambda^{-2}\), \(\lambda^{-1}\) factors are recorded in
[\`HBL_213_GENUINE_HARTREE_QUADRATIC_WEIGHTED_SOURCE_20261110.md\`](HBL_213_GENUINE_HARTREE_QUADRATIC_WEIGHTED_SOURCE_20261110.md).
This **removes the need for a separately assumed nonlinear
Hartree remainder**, but not the original linearized term or
any PDE orbit construction. Next producer is true \(U(s),H(s)\)
on the source-selected moving Fredholm/Kummer field
and its time/parameter derivatives, plus the full coupled
Hamiltonian projected inverse. There is no new strict Lean
nonlocal Sobolev theorem or acceptance: **11/13**.


## 11. Weighted source regularity is not supplied by C² gluing

The true original Hartree/Kummer spectral equation has
\(w''+p w'+qw=F-\delta u_0\), and the original scaled
operator on the flat plateau has
\(\mathcal K_a v=a^{-2}(F-\delta u_0)(y/a)\).
Current \(F\in C^0\) is insufficient for a Morawetz-dual
weighted \(H^1\) source: choose a compactly supported
continuous \(F=\psi|r-r_*|^{1/4}\), which has
\(F'\notin L²_{\rm loc}\); \(u_0'\in L²_{\rm loc}\)
does not cancel it. The inner Fredholm forcing is only
weighted \(L²\), too. A successful \(C²\) endpoint
repair does not make \(F'\) exist or small.
For actual \(F\in H^1\), the exact frozen
Kummer source derivative scales as
\(\|(1+y²)(\mathcal K_a v)'\|_{L²(aJ)}
=a^{-5/2}\|(1+a²r²)(F'-\delta u_0')\|_{L²(J)}
\le a^{-1/2}\|(1+r²)(F'-\delta u_0')\|_{L²(J)}\)
when \(a\ge1\). This is a useful correct scaling identity,
not a derived time gain.

To shorten the *actual* proof rather than increase auxiliary
declarations, next derive this \(F'\) bound for the uniquely
selected same-orbit quartic physical Hartree source, together
with the inner forcing gradients and all moving interfaces,
or prove a real Hartree continuous-spectrum smoothing inverse
using a weaker source norm. Without one of those producers,
no §2.13 acceptance is justified. Detail:
[the source-regularity audit](HBL_213_C1_GLUE_DUAL_SOURCE_INTERFACE_GATE_20261110.md).
**11/13 unchanged**.


## 11. Actual original C² outer splice has compiled; remaining point-trace gate is mathematical

CI **42825266426** (job **129860806977**, evidence **13768179716**)
proves the actual source-dependent spectral outer curvature,
source-locked \(C^2\) repair jets and true joined outer twice-
differentiable field under trust-zero, warningAsError and exact
three-axiom audit. Its source SHA is **23359602dd5f34921b2f3cb23aaeb1a153c41fff**.

The now explicit physical PDE-gradient estimate for this repaired
outer shell (not full Hartree residual) is
\[
 \|(1+y^2)E_a'\|_{L^2(aB,2aB)}
 \le a^{-1/2}(1+4B^2)\sqrt B\,D
   \{(A_3+2A_1+2A_2)/B^3+
     (A_1/2+A_2+|Q|A_1)/B\},
\]
where \(D=|w(B)|+B|w'(B)|+B^2|w''(B)|\)
and the original nonlocal source fixes
\(w''(B)=F(B)-\delta u_0(B)-A(B)w'(B)-Qw(B)\).
The \(\|F\|_{L^2_{7/4}}\) source norm does **not** control
the point evaluation \(F(B)\): even after Cramer inversion,
\(F_N=\sqrt N\psi(N(r-B))\) produces
\(|w''_N(B)|\sim\sqrt N\) with bounded source \(L^2\).
This is a mathematically decisive failure of the
implicit old source-class-to-C² estimate, not a Lean
elaboration error. It does not rule out stronger genuine
PDE source regularity; that must now be derived for the
selected same-orbit Hartree source and moving parameters.
Complete proof:
[HBL_213_SOURCE_LOCKED_OUTER_C2_DERIVATIVE_BUDGET_20261110.md](HBL_213_SOURCE_LOCKED_OUTER_C2_DERIVATIVE_BUDGET_20261110.md).

**Still open and mandatory:** inner \(C^2\) physical splice,
Hartree-specific trace and weighted residual source control
including moving time/parameter derivatives, projected
nonlocal Hamiltonian inverse, nonlinear finite recursion,
and dynamical Type-II rate. Original count **11/13**.


## 12. Source-faithful backward Volterra closes former unknown E in the *inner* smooth overlap

Using the actual original quartic Hartree plateau
\(S_{\rm in}+a^{-2}F_o=0\) and the original Cramer
spectral correction, the true backward mismatch
\(e=u_{\rm inner}-v_{\rm corr}\) satisfies
\(\mathcal K_a e=D_{\rm in}+a^{-2}\delta u_0(y/a)\),
\(e(L)=e'(L)=0\), on \(L/2\le y\le L\).
The original Fredholm shell estimate, now at
\(R=L/2>2\), bounds the right side in \(L^2\)
without any uncontrolled point trace. Direct radial
Volterra/Gronwall yields the explicit **local** \(H^2\)
bound and in turn
\[
 \|(1+y^2)(\mathcal C_{\rm in})'\|_{L^2([5L/8,3L/4])}
 \le C_{\rm explicit}(L,a,Q)
  [\,L^{-5/2}N+
   L^{-9/2}(C_KN+|\delta|M_0)\,]
\]
under \(a\ge L^3\). Every coefficient including
the physical drift and the true third cutoff
derivative is retained. The complete proof is
[HBL_213_BACKWARD_FLAT_OVERLAP_VOLterra_PDE_GRADIENT_20261110.md](HBL_213_BACKWARD_FLAT_OVERLAP_VOLterra_PDE_GRADIENT_20261110.md).

This **closes the old unknown inner backward E estimate
on paper**; it makes the smooth-overlap path preferable
to imposing the uncontrolled outer \(F(B)\) source
trace. It does *not* close the outer shell, full
nonlocal interactions, actual moving time residual,
modulation/parameter Lipschitz, projected Hartree
inverse or final orbit. The bound awaits actual
single-target Lean formalization on the main
source chain; original **11/13**.
