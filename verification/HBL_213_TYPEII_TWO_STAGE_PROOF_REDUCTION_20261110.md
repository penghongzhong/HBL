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
\(|\mu_s|\le Cs^{-1-\delta}\). **Important:** the current original main theorem additionally states the quantitative bound \(|\mu_s|\le Cs^{-1-\delta}\) as its own conclusion; that assertion is **not implied** by (F). It must still be proved if the theorem statement is unchanged, or explicitly moved into a separate sharpened theorem with a genuine manuscript revision.
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
