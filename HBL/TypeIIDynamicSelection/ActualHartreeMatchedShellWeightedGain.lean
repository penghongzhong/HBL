import HBL.TypeIIDynamicSelection.ActualHartreeTwoChannelMatchedShell
import HBL.TypeIIDynamicSelection.ActualHartreeShellWeightedNorm
import Mathlib.Tactic

/-!
# The actual matched Kummer shell error in the fixed Fredholm source norm

This is the full cutoff commutator of the original scaled Kummer
operator. Its zero-order term cancels algebraically, leaving only
actual first and second derivatives and smooth coefficients. Therefore
the commutator is measurable even when the exterior field has only
local regularity on the shell.

The two normalized Fredholm responses, the actual matched Cauchy jet
and the same-source exterior equation produce the pointwise estimate.
The final bound includes both the radial conjugation and the shell
volume in L^{2,7/4}(dr). No measurability or size of an abstract error
is supplied as an additional hypothesis.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.Profile.Kummer

/-- The complete scaled Kummer cutoff commutator of the actual mismatch. -/
def actualMatchedKummerShellError
    (mu theta a R : ℝ) (d : ℝ → ℂ) (r : ℝ) : ℂ :=
  actualMatchedScaledKummerApply mu theta a
      (fun x => actualOneLayerInnerOverlapCutoff R x * d x) r -
    actualOneLayerInnerOverlapCutoff R r *
      actualMatchedScaledKummerApply mu theta a d r

/-- Zero-order cancellation gives global measurability from actual
derivatives. The mismatch itself need not be globally measurable. -/
theorem actual_matched_Kummer_shell_error_measurable
    (mu theta a R : ℝ) (d : ℝ → ℂ) :
    Measurable (actualMatchedKummerShellError mu theta a R d) := by
  let chi := actualOneLayerInnerOverlapCutoff R
  have hchi : Measurable chi :=
    (show Continuous chi from continuous_iff_continuousAt.2
      (fun r => (actual_one_layer_overlap_cutoff_hasDerivAt R r).continuousAt)).measurable
  have heq : actualMatchedKummerShellError mu theta a R d =
      fun r =>
        deriv (deriv (fun x => chi x * d x)) r - chi r * deriv (deriv d) r +
          (2 / (r : ℂ) + (((a ^ 2)⁻¹ : ℝ) : ℂ) * (Complex.I * (r : ℂ) / 2)) *
            (deriv (fun x => chi x * d x) r - chi r * deriv d r) := by
    funext r
    unfold actualMatchedKummerShellError actualMatchedScaledKummerApply
      complexRadialLaplacian
    simp only [chi, Complex.real_smul]
    ring
  rw [heq]
  have hcoeff : Measurable (fun r : ℝ =>
      2 / (r : ℂ) + (((a ^ 2)⁻¹ : ℝ) : ℂ) * (Complex.I * (r : ℂ) / 2)) := by
    fun_prop
  exact ((measurable_deriv (deriv (fun x => chi x * d x))).sub
    (hchi.mul (measurable_deriv (deriv d)))).add
      (hcoeff.mul ((measurable_deriv (fun x => chi x * d x)).sub
        (hchi.mul (measurable_deriv d))))

/-- Actual matched two-channel corrections have a quantitative shell
error in the same weighted source space used by the fixed inverse.
Both displayed bounds retain the complete Kummer transport term. -/
theorem actual_Hartree_two_channel_matched_shell_weighted_gain :
    ∃ C : ℝ, 0 < C ∧
      ∀ (mu theta a R r0 : ℝ) (Fp Fm : ℝ → ℝ)
        (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
        (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
        (U : Set ℝ) (v : ℝ → ℂ),
        Continuous Fp → Continuous Fm →
        IsOpen U → Icc R (2 * R) ⊆ U →
        0 < a → 2 < R →
        16 * R ^ 2 * ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) ≤ 1 →
        r0 ∈ Icc R (2 * R) →
        (∀ x ∈ U, DifferentiableAt ℝ v x) →
        (∀ x ∈ Icc R (2 * R), DifferentiableAt ℝ (deriv v) x) →
        actualHartreeTwoChannelInner Fp Fm hp hm r0 = v r0 →
        deriv (actualHartreeTwoChannelInner Fp Fm hp hm) r0 = deriv v r0 →
        (∀ x ∈ Icc R (2 * R),
          actualMatchedScaledKummerApply mu theta a v x =
            -actualHartreeTwoChannelPhysicalSource Fp Fm x) →
        let d := fun x => actualHartreeTwoChannelInner Fp Fm hp hm x - v x
        let E := actualMatchedKummerShellError mu theta a R d
        InWeightedL2 (7 / 4 : ℝ) (actualConjugatedShellMagnitude R E) ∧
        innerWeightedNorm (7 / 4 : ℝ) (actualConjugatedShellMagnitude R E) ≤
          20 * C * R ^ (13 / 4 : ℝ) *
            (actualInnerShellEquationConstant / R ^ 4 +
              actualInnerShellKummerConstant mu theta / a ^ 2) *
            (innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm) ∧
        innerWeightedNorm (7 / 4 : ℝ) (actualConjugatedShellMagnitude R E) ≤
          20 * C *
            (actualInnerShellEquationConstant * R ^ (-(3 / 4 : ℝ)) +
              actualInnerShellKummerConstant mu theta * R ^ (13 / 4 : ℝ) / a ^ 2) *
            (innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm) := by
  obtain ⟨C, hC, hShell⟩ := actual_Hartree_two_channel_matched_shell_gain
  refine ⟨C, hC, ?_⟩
  intro mu theta a R r0 Fp Fm hp hm U v hcp hcm hU hSub ha hR hsmall hr0
    hv hv2 hleft hdleft heq
  dsimp only
  let d : ℝ → ℂ := fun x => actualHartreeTwoChannelInner Fp Fm hp hm x - v x
  let E := actualMatchedKummerShellError mu theta a R d
  have hRpos : 0 < R := by linarith
  have hRone : 1 ≤ R := by linarith
  have hg := hShell mu theta a R r0 Fp Fm hp hm U v
    hcp hcm hU hSub ha hR hsmall hr0 hv hv2 hleft hdleft heq
  have hE : Measurable E := actual_matched_Kummer_shell_error_measurable mu theta a R d
  have hbound : ∀ r ∈ Icc R (2 * R),
      ‖E r‖ ≤ C * actualHartreeTwoChannelShellBudget mu theta a R Fp Fm := by
    intro r hr
    exact (hg r hr).2.2.2.2
  have hstart : R ∈ Icc R (2 * R) := ⟨le_rfl, by linarith⟩
  have hA : 0 ≤ C * actualHartreeTwoChannelShellBudget mu theta a R Fp Fm :=
    (norm_nonneg (E R)).trans (hbound R hstart)
  have hw := actual_conjugated_shell_weighted_power_bound R
    (C * actualHartreeTwoChannelShellBudget mu theta a R Fp Fm)
      hRone hA E hE hbound
  have hraw :
      innerWeightedNorm (7 / 4 : ℝ) (actualConjugatedShellMagnitude R E) ≤
        20 * C * R ^ (13 / 4 : ℝ) *
          (actualInnerShellEquationConstant / R ^ 4 +
            actualInnerShellKummerConstant mu theta / a ^ 2) *
          (innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm) := by
    apply hw.2.trans_eq
    unfold actualHartreeTwoChannelShellBudget
    ring
  refine ⟨hw.1, hraw, hraw.trans_eq ?_⟩
  have hpower : R ^ (13 / 4 : ℝ) / R ^ 4 = R ^ (-(3 / 4 : ℝ)) := by
    rw [← Real.rpow_natCast R 4, ← Real.rpow_sub hRpos]
    norm_num
  calc
    _ = 20 * C *
        (actualInnerShellEquationConstant * (R ^ (13 / 4 : ℝ) / R ^ 4) +
          actualInnerShellKummerConstant mu theta * R ^ (13 / 4 : ℝ) / a ^ 2) *
        (innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm) := by ring
    _ = _ := by rw [hpower]

end HBL.TypeIIDynamicSelection
