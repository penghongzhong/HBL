import HBL.TypeIIDynamicSelection.ActualHartreeInnerShellEquation
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedKummerShellGain
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedCoupledCompatibility
import HBL.MonopoleComplexResidual
import Mathlib.Tactic

/-!
The same normalized real and imaginary inner responses, a genuine
same-source exterior equation, and their matched shell commutator.

The source may already contain the uniquely determined modulation
increments. No independent size hypothesis on the mismatch, its
derivative, or the forced affine tail is used. The exterior field is
required to solve the full scaled Kummer equation and to have the
same value and first derivative at the actual interface.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.Profile.Kummer

/-- The physical field of the same two normalized fixed-inverse outputs. -/
def actualHartreeTwoChannelInner
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm) (r : ℝ) : ℂ :=
  (actualMomentLockedPhysicalPlus Fp hp r : ℂ) +
    Complex.I * (actualMomentLockedPhysicalMinus Fm hm r : ℂ)

/-- Both physical source channels, before the minus sign in the equation. -/
def actualHartreeTwoChannelPhysicalSource (Fp Fm : ℝ → ℝ) (r : ℝ) : ℂ :=
  ((Fp r : ℂ) + Complex.I * (Fm r : ℂ)) / (r : ℂ)

/-- The actual shell equation budget, measured in the original source norm. -/
def actualHartreeTwoChannelShellBudget
    (mu theta a R : ℝ) (Fp Fm : ℝ → ℝ) : ℝ :=
  (actualInnerShellEquationConstant / R ^ 4 +
      actualInnerShellKummerConstant mu theta / a ^ 2) *
    (innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm)

private theorem actual_two_channel_shell_budget_nonneg
    (mu theta a R : ℝ) (Fp Fm : ℝ → ℝ) :
    0 ≤ actualHartreeTwoChannelShellBudget mu theta a R Fp Fm := by
  have hv : 0 ≤ actualInnerShellValueConstant := by
    unfold actualInnerShellValueConstant
    positivity
  have hd : 0 ≤ actualInnerShellDerivativeConstant := by
    unfold actualInnerShellDerivativeConstant
    positivity
  have he : 0 ≤ actualInnerShellEquationConstant := by
    unfold actualInnerShellEquationConstant
    positivity
  have hk : 0 ≤ actualInnerShellKummerConstant mu theta := by
    unfold actualInnerShellKummerConstant
    positivity
  have hp := innerWeightedNorm_nonneg (7 / 4 : ℝ) Fp
  have hm := innerWeightedNorm_nonneg (7 / 4 : ℝ) Fm
  unfold actualHartreeTwoChannelShellBudget
  positivity

private theorem actual_two_channel_real_classical
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (hcp : Continuous Fp) (hcm : Continuous Fm) :
    ∀ r : ℝ, 0 < r →
      DifferentiableAt ℝ (actualMomentLockedPhysicalPlus Fp hp) r ∧
      DifferentiableAt ℝ (deriv (actualMomentLockedPhysicalPlus Fp hp)) r ∧
      DifferentiableAt ℝ (actualMomentLockedPhysicalMinus Fm hm) r ∧
      DifferentiableAt ℝ (deriv (actualMomentLockedPhysicalMinus Fm hm)) r := by
  let qp := normalizedPlusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) Fp hp
  let qm := normalizedMinusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) Fm hm
  have hqp := normalizedPlusOutput_classical
    (7 / 4 : ℝ) (by norm_num) (by norm_num) Fp hp hcp
  have hqm := normalizedMinusOutput_classical
    (7 / 4 : ℝ) (by norm_num) (by norm_num) Fm hm hcm
  intro r hr
  exact ⟨(div_radius_hasDerivAt qp hr (hqp r hr).1).differentiableAt,
    (div_radius_second_hasDerivAt qp (fun x hx => (hqp x hx).1) hr
      (hqp r hr).2.1).differentiableAt,
    (div_radius_hasDerivAt qm hr (hqm r hr).1).differentiableAt,
    (div_radius_second_hasDerivAt qm (fun x hx => (hqm x hx).1) hr
      (hqm r hr).2.1).differentiableAt⟩

private theorem actual_two_channel_classical_identity
    (mu theta a : ℝ) (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (hcp : Continuous Fp) (hcm : Continuous Fm) (r : ℝ) (hr : 0 < r) :
    let u := actualHartreeTwoChannelInner Fp Fm hp hm
    let qp := normalizedPlusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) Fp hp
    let qm := normalizedMinusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) Fm hm
    DifferentiableAt ℝ u r ∧ DifferentiableAt ℝ (deriv u) r ∧
      actualMatchedScaledKummerApply mu theta a u r +
        actualHartreeTwoChannelPhysicalSource Fp Fm r =
      actualInnerScaledKummerDefect mu theta a Fp qp r +
        Complex.I * actualInnerScaledKummerDefect mu theta a Fm qm r := by
  let up := actualMomentLockedPhysicalPlus Fp hp
  let um := actualMomentLockedPhysicalMinus Fm hm
  let u := actualHartreeTwoChannelInner Fp Fm hp hm
  have hc := actual_two_channel_real_classical Fp Fm hp hm hcp hcm
  have hfirst (x : ℝ) (hx : 0 < x) :
      HasDerivAt u
        (((deriv up x : ℝ) : ℂ) + Complex.I * ((deriv um x : ℝ) : ℂ)) x := by
    exact ((hc x hx).1.hasDerivAt.ofReal_comp).add
      ((hc x hx).2.2.1.hasDerivAt.ofReal_comp.const_mul Complex.I)
  have hnear : deriv u =ᶠ[𝓝 r]
      (fun x => ((deriv up x : ℝ) : ℂ) + Complex.I * ((deriv um x : ℝ) : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact (hfirst x hx).deriv
  have hsecond : HasDerivAt (deriv u)
      (((deriv (deriv up) r : ℝ) : ℂ) +
        Complex.I * ((deriv (deriv um) r : ℝ) : ℂ)) r := by
    exact (((hc r hr).2.1.hasDerivAt.ofReal_comp).add
      ((hc r hr).2.2.2.hasDerivAt.ofReal_comp.const_mul Complex.I)).congr_of_eventuallyEq hnear
  refine ⟨(hfirst r hr).differentiableAt, hsecond.differentiableAt, ?_⟩
  change actualMatchedScaledKummerApply mu theta a u r +
    actualHartreeTwoChannelPhysicalSource Fp Fm r = _
  unfold actualMatchedScaledKummerApply complexRadialLaplacian
  rw [hsecond.deriv, (hfirst r hr).deriv]
  change _ =
    (((radialLaplacian up r + Fp r / r : ℝ) : ℂ) +
      ((a ^ 2)⁻¹ : ℝ) • (Complex.I * (r : ℂ) / 2 * ((deriv up r : ℝ) : ℂ) +
        frozenZeroCoeff mu theta * (up r : ℂ))) +
    Complex.I * (((radialLaplacian um r + Fm r / r : ℝ) : ℂ) +
      ((a ^ 2)⁻¹ : ℝ) • (Complex.I * (r : ℂ) / 2 * ((deriv um r : ℝ) : ℂ) +
        frozenZeroCoeff mu theta * (um r : ℂ)))
  have hu : u r = (up r : ℂ) + Complex.I * (um r : ℂ) := rfl
  rw [hu]
  simp only [radialLaplacian, actualHartreeTwoChannelPhysicalSource,
    Complex.real_smul, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- The actual complex two-channel inner field has a source-norm
Kummer defect bound, including both actual radial derivatives. -/
theorem actual_Hartree_two_channel_inner_Kummer_defect_bound
    (mu theta a : ℝ) (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (hcp : Continuous Fp) (hcm : Continuous Fm)
    (R r : ℝ) (hR : 2 < R) (hr : R ≤ r) :
    ‖actualMatchedScaledKummerApply mu theta a
        (actualHartreeTwoChannelInner Fp Fm hp hm) r +
      actualHartreeTwoChannelPhysicalSource Fp Fm r‖ ≤
      actualHartreeTwoChannelShellBudget mu theta a R Fp Fm := by
  have hr0 : 0 < r := by linarith
  have he := (actual_two_channel_classical_identity
    mu theta a Fp Fm hp hm hcp hcm r hr0).2.2
  have hbp := (actual_Hartree_normalized_inner_scaled_Kummer_bound
    mu theta a Fp hp hcp R r hR hr).1
  have hbm := (actual_Hartree_normalized_inner_scaled_Kummer_bound
    mu theta a Fm hm hcm R r hR hr).2
  rw [he]
  calc
    _ ≤ ‖actualInnerScaledKummerDefect mu theta a Fp
          (normalizedPlusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) Fp hp) r‖ +
        ‖Complex.I * actualInnerScaledKummerDefect mu theta a Fm
          (normalizedMinusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) Fm hm) r‖ :=
      norm_add_le _ _
    _ ≤ (actualInnerShellEquationConstant * innerWeightedNorm (7 / 4 : ℝ) Fp / R ^ 4 +
          actualInnerShellKummerConstant mu theta * innerWeightedNorm (7 / 4 : ℝ) Fp / a ^ 2) +
        (actualInnerShellEquationConstant * innerWeightedNorm (7 / 4 : ℝ) Fm / R ^ 4 +
          actualInnerShellKummerConstant mu theta * innerWeightedNorm (7 / 4 : ℝ) Fm / a ^ 2) := by
      rw [norm_mul, Complex.norm_I, one_mul]
      exact add_le_add hbp hbm
    _ = _ := by unfold actualHartreeTwoChannelShellBudget; ring

private theorem actual_scaled_Kummer_sub_on_open
    (mu theta a : ℝ) (u v : ℝ → ℂ) (U : Set ℝ) (hU : IsOpen U)
    (hu : ∀ x ∈ U, DifferentiableAt ℝ u x)
    (hv : ∀ x ∈ U, DifferentiableAt ℝ v x)
    (r : ℝ) (hr : r ∈ U)
    (hu2 : DifferentiableAt ℝ (deriv u) r)
    (hv2 : DifferentiableAt ℝ (deriv v) r) :
    DifferentiableAt ℝ (deriv (fun x => u x - v x)) r ∧
      actualMatchedScaledKummerApply mu theta a (fun x => u x - v x) r =
        actualMatchedScaledKummerApply mu theta a u r -
          actualMatchedScaledKummerApply mu theta a v r := by
  have hfirst (x : ℝ) (hx : x ∈ U) :
      HasDerivAt (fun y => u y - v y) (deriv u x - deriv v x) x :=
    (hu x hx).hasDerivAt.sub (hv x hx).hasDerivAt
  have hnear : deriv (fun x => u x - v x) =ᶠ[𝓝 r]
      (fun x => deriv u x - deriv v x) := by
    filter_upwards [hU.mem_nhds hr] with x hx
    exact (hfirst x hx).deriv
  have hsecond := (hu2.hasDerivAt.sub hv2.hasDerivAt).congr_of_eventuallyEq hnear
  refine ⟨hsecond.differentiableAt, ?_⟩
  unfold actualMatchedScaledKummerApply complexRadialLaplacian
  rw [hsecond.deriv, (hfirst r hr).deriv]
  simp only [Complex.real_smul]
  ring

/-- A genuine same-source exterior solution and the actual normalized
two-channel field produce a small matched shell commutator. The exterior
regularity is local to an open neighborhood of the shell, and no bound
on the mismatch is an assumption. -/
theorem actual_Hartree_two_channel_matched_shell_gain :
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
        let A := actualHartreeTwoChannelShellBudget mu theta a R Fp Fm
        ∀ r ∈ Icc R (2 * R),
          ‖complexRadialLaplacian d r‖ ≤ 2 * A ∧
          ‖d r‖ ≤ 8 * R ^ 2 * A ∧
          ‖deriv d r‖ ≤ 8 * R * A ∧
          ‖complexRadialLaplacian
                (fun x => actualOneLayerInnerOverlapCutoff R x * d x) r -
              actualOneLayerInnerOverlapCutoff R r * complexRadialLaplacian d r‖ ≤ C * A ∧
          ‖actualMatchedScaledKummerApply mu theta a
                (fun x => actualOneLayerInnerOverlapCutoff R x * d x) r -
              actualOneLayerInnerOverlapCutoff R r *
                actualMatchedScaledKummerApply mu theta a d r‖ ≤ C * A := by
  obtain ⟨C, hC, hgain⟩ := actual_Hartree_matched_scaled_Kummer_shell_gain
  obtain ⟨Cfull, hCfull, hfull⟩ := actual_Hartree_matched_full_Kummer_shell_gain
  refine ⟨C + Cfull, add_pos hC hCfull, ?_⟩
  intro mu theta a R r0 Fp Fm hp hm U v hcp hcm hU hSub ha hR hsmall hr0 hv hv2 hleft hdleft heq
  let u := actualHartreeTwoChannelInner Fp Fm hp hm
  let d : ℝ → ℂ := fun x => u x - v x
  let V : Set ℝ := U ∩ Ioi (0 : ℝ)
  have hR0 : 0 < R := by linarith
  have hV : IsOpen V := hU.inter isOpen_Ioi
  have hSubV : Icc R (2 * R) ⊆ V := by
    intro x hx
    exact ⟨hSub hx, hR0.trans_le hx.1⟩
  have hclass (x : ℝ) (hx : 0 < x) :=
    actual_two_channel_classical_identity mu theta a Fp Fm hp hm hcp hcm x hx
  have hu : ∀ x ∈ V, DifferentiableAt ℝ u x :=
    fun x hx => (hclass x hx.2).1
  have hvV : ∀ x ∈ V, DifferentiableAt ℝ v x := fun x hx => hv x hx.1
  have hd : ∀ x ∈ V, DifferentiableAt ℝ d x := fun x hx => (hu x hx).sub (hvV x hx)
  have hsub (x : ℝ) (hx : x ∈ Icc R (2 * R)) :=
    actual_scaled_Kummer_sub_on_open mu theta a u v V hV hu hvV x (hSubV hx)
      (hclass x (hR0.trans_le hx.1)).2.1 (hv2 x hx)
  have hdd : ∀ x ∈ Icc R (2 * R), DifferentiableAt ℝ (deriv d) x :=
    fun x hx => (hsub x hx).1
  have hd0 : d r0 = 0 := sub_eq_zero.mpr hleft
  have hdd0 : deriv d r0 = 0 := by
    rw [show deriv d r0 = deriv u r0 - deriv v r0 from
      ((hu r0 (hSubV hr0)).hasDerivAt.sub (hvV r0 (hSubV hr0)).hasDerivAt).deriv]
    exact sub_eq_zero.mpr hdleft
  have hdefect : ∀ x ∈ Icc R (2 * R),
      ‖actualMatchedScaledKummerApply mu theta a d x‖ ≤
        actualHartreeTwoChannelShellBudget mu theta a R Fp Fm := by
    intro x hx
    rw [(hsub x hx).2, heq x hx, sub_neg_eq_add]
    exact actual_Hartree_two_channel_inner_Kummer_defect_bound
      mu theta a Fp Fm hp hm hcp hcm R x hR hx.1
  have hA := actual_two_channel_shell_budget_nonneg mu theta a R Fp Fm
  have hg := hgain mu theta a d V R (actualHartreeTwoChannelShellBudget mu theta a R Fp Fm) r0
    hV hSubV ha hR0 hA hsmall hr0 hd hdd hd0 hdd0 hdefect
  have hf := hfull mu theta a d V R (actualHartreeTwoChannelShellBudget mu theta a R Fp Fm) r0
    hV hSubV ha hR0 hA hsmall hr0 hd hdd hd0 hdd0 hdefect
  dsimp only
  intro r hr
  refine ⟨(hg r hr).1, (hg r hr).2.1, (hg r hr).2.2.1, ?_, ?_⟩
  · exact (hg r hr).2.2.2.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCfull.le) hA)
  · exact (hf r hr).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC.le) hA)

end HBL.TypeIIDynamicSelection
