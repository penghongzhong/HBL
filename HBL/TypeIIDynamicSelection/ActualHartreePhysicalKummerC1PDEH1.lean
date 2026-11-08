import HBL.TypeIIDynamicSelection.ActualHartreePhysicalKummerC1Splice
import HBL.TypeIIDynamicSelection.ActualKummerRepairPhysicalH1TimeGain
import Mathlib.Tactic

/-!
# One actual Kummer source: exact equation, physical C1 gluing and H1 gain

This single certificate reuses the SAME origin-normalized forced Green
solution and its genuinely selected right value/slope jet.
The physical pullback solves its exact forced scaled Kummer equation,
the Kummer / repair / zero continuation is differentiable with the
correct two physical interface derivatives, and the compact replacement
has a strictly positive three-dimensional radial Hdot1 shell gain.

The upper jet's source decay remains an explicit premise to be supplied
by the actual coupled Hartree compatibility producer. Neither a free
homogeneous amplitude nor a prescribed Type-II rate is introduced.
This is one physical Kummer component, not the full three-region profile.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_physical_matched_Kummer_C1_PDE_and_H1_certificate
    {mu theta scale r0 B : ℝ} (K : OriginKummerPair mu theta scale)
    (a s beta rho CX CD : ℝ)
    (ha : 0 < a) (hr0 : 0 < r0) (horder : r0 ≤ B)
    (hB : B < scale) (hs : 1 ≤ s)
    (hbeta : 1 / 2 < beta)
    (hrho : (1 / 2 + actualKummerRepairCenterTimeGain beta) / 2 ≤ rho)
    (hCX : 0 ≤ CX) (hCD : 0 ≤ CD)
    (hX : a * B ≤ CX * s ^ (1 / 2 : ℝ))
    (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo 0 scale, ContinuousAt F r)
    (U DU : ℂ)
    (hJet :
      ‖actualOriginMatchedKummerValue K r0 B F U DU B‖ +
        B * ‖actualOriginMatchedKummerSlope K r0 B F U DU B‖ ≤
      CD * s ^ (-rho)) :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      let w := actualOriginMatchedKummerValue K r0 B F U DU
      let v := actualOriginMatchedKummerPullback K a r0 B F U DU
      let UB := w B
      let DUB := actualOriginMatchedKummerSlope K r0 B F U DU B
      let rep := actualKummerPhysicalInterfaceRepair a B UB DUB
      let glued := actualPhysicalMatchedKummerC1Splice a B v rep
      (∀ y ∈ Ioo 0 (a * scale),
        actualMatchedScaledKummerApply mu theta a v y =
          ((a ^ 2)⁻¹ : ℝ) • F (y / a)) ∧
      HasDerivAt glued ((1 / a : ℝ) • DUB) (a * B) ∧
      HasDerivAt glued 0 (2 * a * B) ∧
      (∫ y in Icc (a * B) (2 * a * B),
        y ^ 2 * ‖deriv rep y‖ ^ 2) ≤
        (4 * (3 * C1 + 1) ^ 2 * CX * CD ^ 2) *
          s ^ (-actualKummerRepairCenterTimeGain beta) := by
  obtain ⟨C1,C2,hC1,hC2,hEnergy⟩ :=
    actual_Kummer_physical_repair_shell_H1_positive_time_gain
  refine ⟨C1,C2,hC1,hC2,?_⟩
  dsimp only
  let w := actualOriginMatchedKummerValue K r0 B F U DU
  let v := actualOriginMatchedKummerPullback K a r0 B F U DU
  let UB := w B
  let DUB := actualOriginMatchedKummerSlope K r0 B F U DU B
  let rep := actualKummerPhysicalInterfaceRepair a B UB DUB
  let glued := actualPhysicalMatchedKummerC1Splice a B v rep
  have hEquation (y : ℝ) (hy : y ∈ Ioo 0 (a * scale)) :
      actualMatchedScaledKummerApply mu theta a v y =
        ((a ^ 2)⁻¹ : ℝ) • F (y / a) := by
    exact (actual_Hartree_matched_Kummer_pullback_classical
      K a ha hr0 horder hB F hF U DU y hy).2.2
  have hJoins :=
    actual_Hartree_matched_Kummer_repair_is_C1_at_both_physical_joins
      K a ha hr0 horder hB F hF U DU
  have hBpos : 0 < B := hr0.trans_le horder
  have hEnergyBound :=
    hEnergy a B s beta rho CX CD ha hBpos hs hbeta
      hrho hCX hCD hX UB DUB (by
        simpa only [w, UB, DUB] using hJet)
  dsimp only at hJoins hEnergyBound
  refine ⟨hEquation, ?_, ?_, ?_⟩
  · simpa only [glued, v, rep, w, UB, DUB] using hJoins.1
  · simpa only [glued, v, rep, w, UB, DUB] using hJoins.2
  · simpa only [rep, w, UB, DUB] using hEnergyBound.2


/-- The frozen physical Kummer operator is local: two spatial profiles
equal on a neighborhood have exactly the same full second-order operator.
Both radial derivatives and the drift/zero-order terms are retained. -/
private theorem actual_matched_scaled_Kummer_apply_of_eventuallyEq
    (mu theta a y : ℝ) (f g : ℝ → ℂ)
    (heq : f =ᶠ[𝓝 y] g) :
    actualMatchedScaledKummerApply mu theta a f y =
      actualMatchedScaledKummerApply mu theta a g y := by
  have hVal : f y = g y := heq.eq_of_nhds
  have hDer : deriv f y = deriv g y := heq.deriv_eq
  have hSecond : deriv (deriv f) y = deriv (deriv g) y :=
    heq.deriv.deriv_eq
  unfold actualMatchedScaledKummerApply complexRadialLaplacian
  rw [hVal, hDer, hSecond]

/-- The actual three-piece C1 physical Kummer splice, not merely its
unspliced Green branch, obeys the genuine forced equation throughout the
interior, the physical repair equation on the open replacement annulus,
and the homogeneous zero equation beyond its outer cutoff. In particular
there is no hidden singular source at either C1 junction. -/
theorem actual_Hartree_physical_Kummer_C1Splice_three_source_regions
    {mu theta scale r0 B : ℝ} (K : OriginKummerPair mu theta scale)
    (a : ℝ) (ha : 0 < a)
    (hr0 : 0 < r0) (horder : r0 ≤ B) (hB : B < scale)
    (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo 0 scale, ContinuousAt F r)
    (U DU : ℂ) :
    let w := actualOriginMatchedKummerValue K r0 B F U DU
    let v := actualOriginMatchedKummerPullback K a r0 B F U DU
    let UB := w B
    let DUB := actualOriginMatchedKummerSlope K r0 B F U DU B
    let rep := actualKummerPhysicalInterfaceRepair a B UB DUB
    let glued := actualPhysicalMatchedKummerC1Splice a B v rep
    (∀ y ∈ Ioo 0 (a * B),
      actualMatchedScaledKummerApply mu theta a glued y =
        ((a ^ 2)⁻¹ : ℝ) • F (y / a)) ∧
    (∀ y ∈ Ioo (a * B) (2 * a * B),
      actualMatchedScaledKummerApply mu theta a glued y =
        actualMatchedScaledKummerApply mu theta a rep y) ∧
    (∀ y : ℝ, 2 * a * B < y →
      actualMatchedScaledKummerApply mu theta a glued y = 0) := by
  dsimp only
  let w := actualOriginMatchedKummerValue K r0 B F U DU
  let v := actualOriginMatchedKummerPullback K a r0 B F U DU
  let UB := w B
  let DUB := actualOriginMatchedKummerSlope K r0 B F U DU B
  let rep := actualKummerPhysicalInterfaceRepair a B UB DUB
  let glued := actualPhysicalMatchedKummerC1Splice a B v rep
  have hBpos : 0 < B := hr0.trans_le horder
  have hAB : a * B < 2 * a * B := by
    have hpos := mul_pos ha hBpos
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    have hNear : glued =ᶠ[𝓝 y] v := by
      filter_upwards [Iio_mem_nhds hy.2] with t ht
      change (if t ≤ a * B then v t
        else if t ≤ 2 * a * B then rep t else 0) = v t
      change t < a * B at ht
      simp [le_of_lt ht]
    have hOp :=
      actual_matched_scaled_Kummer_apply_of_eventuallyEq
        mu theta a y glued v hNear
    have hyClass : y ∈ Ioo 0 (a * scale) :=
      ⟨hy.1, hy.2.trans (mul_lt_mul_of_pos_left hB ha)⟩
    rw [hOp]
    exact (actual_Hartree_matched_Kummer_pullback_classical
      K a ha hr0 horder hB F hF U DU y hyClass).2.2
  · intro y hy
    have hNear : glued =ᶠ[𝓝 y] rep := by
      filter_upwards [Ioi_mem_nhds hy.1, Iio_mem_nhds hy.2]
        with t htlo hthi
      change (if t ≤ a * B then v t
        else if t ≤ 2 * a * B then rep t else 0) = rep t
      change a * B < t at htlo
      change t < 2 * a * B at hthi
      simp [not_le.mpr htlo, hthi.le]
    exact actual_matched_scaled_Kummer_apply_of_eventuallyEq
      mu theta a y glued rep hNear
  · intro y hy
    have hNear : glued =ᶠ[𝓝 y] (fun _ => (0 : ℂ)) := by
      filter_upwards [Ioi_mem_nhds hy] with t ht
      change 2 * a * B < t at ht
      have htlo : a * B < t := hAB.trans ht
      change (if t ≤ a * B then v t
        else if t ≤ 2 * a * B then rep t else 0) = 0
      simp [not_le.mpr htlo, not_le.mpr ht]
    have hOp :=
      actual_matched_scaled_Kummer_apply_of_eventuallyEq
        mu theta a y glued (fun _ => (0 : ℂ)) hNear
    rw [hOp]
    simp [actualMatchedScaledKummerApply, complexRadialLaplacian]


end HBL.TypeIIDynamicSelection
