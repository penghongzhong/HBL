# HBL 2.13 — complete actual obstruction and the original-data correction bound

## Acceptance anchor

The four new public declarations in the two new source files passed strict Lean replay and complete statement/axiom audit.

- Exact code commit: `520fc62810cd6bf63c93e54223c307aac6f0a069`.
- Successful workflow: [41924227732](https://github.com/penghongzhong/HBL/actions/runs/41924227732), job `126904285401`; all steps completed successfully.
- Evidence artifact: `13368108160`, `hbl-213-complete-obstruction-audit`.
- Downloaded ZIP SHA-256: `bfc34fcaa7bc621ec219963d9b550b97336b93d04ce97e4b08d9d8db32c5f7ff`.
- Fixed Lean `4.35.0-rc3`, compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`; Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`.

The downloaded artifact was independently inspected. Both target-source `--trust=0 -DwarningAsError=true` logs are empty. All four complete type reports are present without truncation; all four transitive axiom lists are exactly `propext`, `Classical.choice`, `Quot.sound`. The two archived source hashes and Git blob identifiers agree with the immutable code commit. The audit log has 262971 bytes. This is a targeted replay of the two new sources, **not** a claim that all earlier 110 statements were replayed in this workflow. Historical dependencies retain their existing warnings.

The revised manuscript ledger remains **11/13 (84.62%)**. No manuscript environment is added by this intermediate acceptance.

## The gap closed in this round

The previous source bridge still had an unestimated complete compatibility obstruction on its right-hand side. That obstruction is now bounded using the SAME full physical outer source and SAME fixed normalized Fredholm baseline jet.

Write

\[
L=\ell^{-1/16},\qquad r_0=L/a,\qquad
N_0=\|F_{+,0}\|_{L^{2,7/4}}+\|F_{-,0}\|_{L^{2,7/4}},
\]

where the two sources are exactly `actualHartreeTransmissionPlusSource` and `actualHartreeTransmissionMinusSource`. Let

\[
F_0(r)=-a^2S_{\rm Hartree}(\ell,c,z;ar),\qquad
J_0=\operatorname{CanonicalInnerJet}(F_{+,0},F_{-,0};a,r_0),
\]

and

\[
Z=T_{r_0}(J_0)-\operatorname{GreenCoeffA}(K,B,F_0;r_0).
\]

The affine charges in J0 remain the charges forced by the two original resonance pairings. There is no additional tunable monopole amplitude, arbitrary trace column or interface-repair forcing.

For the actual origin-normalized Kummer pair, set

\[
C_K=1+(D+1)GB^2,\qquad
C_T=2(D+1)G C_{\rm val}+C_K C_{\rm der},\qquad
Q_z=\operatorname{actualHartreePhysicalWeightedSourceConstant}(B_0,A_0).
\]

The constants D,G bound the actual basis and its coefficients on its positive construction interval. For fixed basis data, these constants are independent of L, a, ell, c and the particular source.

### 1. Full outer coefficient, with no small-left-endpoint loss

`actual_Hartree_full_interval_Green_coefficient_bound` proves integrability of the actual Green density and

\[
\boxed{\quad
\|\operatorname{GreenCoeffA}(K,B,F_0;r_0)\|
\le C_K B Q_z\ell^{1/8}.
\quad}
\]

The pointwise physical source estimate is applied at the integration point r, not replaced by a supremum at r0. The exact Wronskian gives norm of its inverse equal to r^2; the physical forcing gives norm at most Q_z ell^(1/8)/r^2. Their product is uniformly bounded before integration over the entire [r0,B]. Thus the estimate contains no artificial r0^(-2) loss and drops no part of the outer forcing.

### 2. The actual baseline Fredholm trace

`actual_Hartree_canonical_baseline_outgoing_trace_bound` reuses the existing normalized-output value and derivative bounds for arbitrary continuous sources in the original weighted space. It proves, under L>2 and a>=L^3,

\[
\boxed{\quad \|T_{L/a}(J_0)\|\le (C_T/a)N_0.\quad}
\]

The functions under `deriv` are explicitly identified with the actual normalized q/r outputs. No independently selected existential inner solution is substituted. In particular the factor a in the physical-to-Kummer slope is retained.

### 3. Complete obstruction

`actual_Hartree_moment_locked_full_obstruction_bound` constructs weighted membership for the actual physical channels and combines both producers:

\[
\boxed{\quad \|Z\|\le (C_T/a)N_0+C_K B Q_z\ell^{1/8}.\quad}
\]

This is a bound for the original core/radiation source at a frozen time, not a theorem for the residual of every later profile iterate.

### 4. Same-source compatible correction with no unestimated Z

`actual_Hartree_same_source_compatible_correction_region` combines the full matrix's already proved unique cancellation, its quantitative inverse, the actual speed-source L^(5/2) estimate and the new obstruction bound.

It chooses a common cutoff threshold L0 and 0<epsilon<=1 for the SAME basis and source. From

\[
L\ge L_0,\qquad a\ge L^3,\qquad a|c|\le\varepsilon
\]

it derives |c|<=1, L|c|<=1 and L/a<=B. It then constructs the unique real pair (delta b,delta omega) solving the actual full compatibility equation and proves

\[
\boxed{\quad
N_{\rm adj}\le N_0+
\frac{1024C_{\rm src}}{B^2}L^{-1/2}
\left[\frac{C_T}{a}N_0+C_K B Q_z\ell^{1/8}\right].
\quad}
\]

Here the adjusted sources are exactly

\[
F_+=F_{+,0}+\delta\omega G_\omega,\qquad
F_-=F_{-,0}+\delta b G_b.
\]

Neither an assumed inverse bound nor an assumed estimate for Z is an input to this synthesis theorem. The outer source, normalized baseline jet, compatibility columns and inverse estimate all use the same K,B,L,a,c and physical radiation slice.

## Exact scope and remaining manuscript obligation

The regional synthesis still explicitly takes the actual Kummer pair, its D/G estimates and the small-B condition. Earlier origin-basis construction supplies such data; this round does not add a second theorem quantifying over a newly constructed basis. The physical hypotheses remain 0<ell<=1, measurable radiation with its actual sup and Strauss bounds, and continuity of the two physical inner sources.

This round closes the previously isolated **complete Z estimate and its insertion into the actual adjusted-source bound**. It does not establish that a physical time trajectory remains in the parameter region.

The already accepted backward-shell estimate can now consume the displayed original-data bound, with the SAME unique speed increment after verifying the shared basis and regularity hypotheses. Inserting it gives a paper-level shell estimate with no unestimated Z. The additional product L^(-3/4)L^(-1/2)ell^(1/8) equals a fixed constant times ell^(13/64). This algebraic consequence is not separately counted as a new Lean theorem in this run.

To accept the original finite-profile theorem, the SAME complete PDE correction must still control its nonlocal feedback, actual time derivative, varying parameters/Hessian, nonlinear Taylor remainder and remote radiation matching in the manuscript norm. A bound for this particular base physical source cannot be automatically re-used as an arbitrary-iterate relative residual gain. The finite recurrence must receive a genuinely proved PDE step, not a redefined order label or an assumed `hstep`.

The final type-II concentration rate must still be derived from the Hartree dynamics, not supplied as an assumption. The formal manuscript acceptance therefore remains **11/13**.

## Debug history

Runs `41922113188`, `41922721284` and `41923628160` failed during Lean implementation. They are not acceptance evidence. The repairs aligned the unfolded Wronskian identity, explicit real-to-complex derivative casts, and exact function substitution under deriv; they did not weaken mathematical assumptions or add axioms. The successful run is exclusively `41924227732` at the immutable code commit above.
