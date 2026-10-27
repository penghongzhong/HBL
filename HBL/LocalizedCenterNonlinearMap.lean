import HBL.WeightedCenterNonlinearMap
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-!
# Small-ball localization of the centre Duhamel fixed point

No global Lipschitz assumption is imposed on the original nonlinearity.
An explicit radial retraction gives a globally Lipschitz extension, with
constant at most twice the small-ball constant. A forcing bound puts the
fixed point in the unmodified region and removes the retraction.

This repairs the local/global interface only. The constrained propagator,
the mapping of the physical Hartree remainder into its source space, and
the local Lipschitz estimate remain explicit inputs, not constructed here.
No original manuscript environment is newly accepted by this module.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology

namespace HBL.MainBackward.Localized

/-- Radial retraction onto the closed ball of positive radius R. -/
def radialClip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (x : E) : E := (R / max R ‖x‖) • x

theorem radialClip_eq_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) :
    radialClip R x = x := by
  rw [radialClip, max_eq_left hx, div_self hR.ne', one_smul]

theorem radialClip_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (x : E) : ‖radialClip R x‖ ≤ R := by
  have hm : 0 < max R ‖x‖ := hR.trans_le (le_max_left _ _)
  have hc : 0 ≤ R / max R ‖x‖ := div_nonneg hR.le hm.le
  rw [radialClip, norm_smul, Real.norm_of_nonneg hc]
  calc
    _ ≤ (R / max R ‖x‖) * max R ‖x‖ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hc
    _ = R := div_mul_cancel₀ _ hm.ne'

private theorem radialClip_difference_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (x y : E) (hxy : ‖x‖ ≤ ‖y‖) :
    ‖radialClip R x - radialClip R y‖ ≤ 2 * ‖x - y‖ := by
  let a : ℝ := max R ‖x‖
  let b : ℝ := max R ‖y‖
  have hRa : R ≤ a := le_max_left _ _
  have hxa : ‖x‖ ≤ a := le_max_right _ _
  have hyb : ‖y‖ ≤ b := le_max_right _ _
  have ha : 0 < a := hR.trans_le hRa
  have hb : 0 < b := hR.trans_le (le_max_left _ _)
  have hab : a ≤ b := max_le_max_left R hxy
  have hc : 0 ≤ R / a := div_nonneg hR.le ha.le
  have hc1 : R / a ≤ 1 := (div_le_one ha).2 hRa
  have hcd : 0 ≤ R / a - R / b := by
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ hb ha).2
    nlinarith
  have hba : b - a ≤ ‖x - y‖ := by
    have hn := norm_sub_norm_le y x
    rw [norm_sub_rev] at hn
    have hbd : b ≤ a + ‖x - y‖ :=
      max_le (by linarith [norm_nonneg (x - y)]) (by linarith)
    linarith
  have hid : radialClip R x - radialClip R y =
      (R / a) • (x - y) + (R / a - R / b) • y := by
    change (R / a) • x - (R / b) • y = _
    rw [smul_sub, sub_smul]
    abel
  have halg : (R / a - R / b) * b = (R / a) * (b - a) := by
    rw [sub_mul, mul_sub, div_mul_cancel₀ _ hb.ne', div_mul_cancel₀ _ ha.ne']
  rw [hid]
  calc
    _ ≤ ‖(R / a) • (x - y)‖ + ‖(R / a - R / b) • y‖ := norm_add_le _ _
    _ = (R / a) * ‖x - y‖ + (R / a - R / b) * ‖y‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hc, Real.norm_of_nonneg hcd]
    _ ≤ (R / a) * ‖x - y‖ + (R / a - R / b) * b := by
      exact _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left hyb hcd)
    _ = (R / a) * ‖x - y‖ + (R / a) * (b - a) := by rw [halg]
    _ ≤ (R / a) * ‖x - y‖ + (R / a) * ‖x - y‖ := by
      exact _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left hba hc)
    _ ≤ 2 * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]

theorem radialClip_difference_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (x y : E) :
    ‖radialClip R x - radialClip R y‖ ≤ 2 * ‖x - y‖ := by
  rcases le_total ‖x‖ ‖y‖ with h | h
  · exact radialClip_difference_of_norm_le hR x y h
  · simpa only [norm_sub_rev] using radialClip_difference_of_norm_le hR y x h

theorem radialClip_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : ℝ → ℝ) (hρ : Continuous ρ) (hpos : ∀ t, 0 < ρ t) :
    Continuous (fun z : ℝ × E => radialClip (ρ z.1) z.2) := by
  have hc : Continuous (fun z : ℝ × E => ρ z.1 / max (ρ z.1) ‖z.2‖) :=
    (hρ.comp continuous_fst).div
      ((hρ.comp continuous_fst).max continuous_snd.norm)
      (fun z => ne_of_gt ((hpos z.1).trans_le (le_max_left _ _)))
  exact hc.smul continuous_snd

/-- A positive radius on the entire clamped time line. -/
def lateRadius (s0 p R t : ℝ) : ℝ := R * (max s0 t) ^ (-p)

theorem lateRadius_pos {s0 p R : ℝ} (hs0 : 0 < s0) (hR : 0 < R) (t : ℝ) :
    0 < lateRadius s0 p R t := by
  exact mul_pos hR (Real.rpow_pos_of_pos (hs0.trans_le (le_max_left _ _)) _)

theorem lateRadius_continuous {s0 p R : ℝ} (hs0 : 0 < s0) :
    Continuous (lateRadius s0 p R) := by
  apply continuous_iff_continuousAt.2
  intro t
  have hm : 0 < max s0 t := hs0.trans_le (le_max_left _ _)
  have hp : ContinuousAt (fun x : ℝ => (max s0 x) ^ (-p)) t :=
    (Real.continuousAt_rpow_const (max s0 t) (-p) (Or.inl hm.ne')).comp
      (continuous_const.max continuous_id).continuousAt
  exact continuousAt_const.mul hp

/-- The original nonlinearity is left unchanged on the shrinking ball. -/
def localizedCenterNonlinearity (s0 p R : ℝ)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (t : ℝ) (z : ConstrainedCenterSpace) : ConstrainedCenterSpace :=
  G t (radialClip (lateRadius s0 p R t) z)

/-- Only points in the shrinking ball are quantified over. -/
def LocalCenterLipschitz (s0 p delta Cnl R : ℝ)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace) : Prop :=
  ∀ t, s0 ≤ t → ∀ z w,
    ‖z‖ ≤ R * t ^ (-p) → ‖w‖ ≤ R * t ^ (-p) →
    ‖G t z - G t w‖ ≤ Cnl * t ^ (-1 - delta) * ‖z - w‖

theorem localizedCenter_continuous {s0 p R : ℝ}
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hR : 0 < R)
    (hG : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2)) :
    Continuous (fun z : ℝ × ConstrainedCenterSpace =>
      localizedCenterNonlinearity s0 p R G z.1 z.2) := by
  exact hG.comp (continuous_fst.prodMk
    (radialClip_continuous (lateRadius s0 p R)
      (lateRadius_continuous hs0) (lateRadius_pos hs0 hR)))

theorem localizedCenter_zero {s0 p R : ℝ}
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hG : ∀ t, s0 ≤ t → G t 0 = 0) :
    ∀ t, s0 ≤ t → localizedCenterNonlinearity s0 p R G t 0 = 0 := by
  intro t ht
  simpa only [localizedCenterNonlinearity, radialClip, smul_zero] using hG t ht

theorem localizedCenter_global_bound {s0 p delta Cnl R : ℝ}
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hR : 0 < R) (hC : 0 ≤ Cnl)
    (hG : LocalCenterLipschitz s0 p delta Cnl R G) :
    ∀ t, s0 ≤ t → ∀ z w,
      ‖localizedCenterNonlinearity s0 p R G t z -
        localizedCenterNonlinearity s0 p R G t w‖ ≤
      (2 * Cnl) * t ^ (-1 - delta) * ‖z - w‖ := by
  intro t ht z w
  have hρ := lateRadius_pos (p := p) hs0 hR t
  have hz := radialClip_norm_le hρ z
  have hw := radialClip_norm_le hρ w
  have hr : lateRadius s0 p R t = R * t ^ (-p) := by
    simp only [lateRadius, max_eq_right ht]
  rw [hr] at hz hw
  have hg := hG t ht _ _ hz hw
  have hc : 0 ≤ Cnl * t ^ (-1 - delta) :=
    mul_nonneg hC (Real.rpow_nonneg (hs0.trans_le ht).le _)
  calc
    _ ≤ Cnl * t ^ (-1 - delta) *
      ‖radialClip (lateRadius s0 p R t) z - radialClip (lateRadius s0 p R t) w‖ := by
        simpa only [localizedCenterNonlinearity, hr] using hg
    _ ≤ Cnl * t ^ (-1 - delta) * (2 * ‖z - w‖) :=
      mul_le_mul_of_nonneg_left (radialClip_difference_le hρ z w) hc
    _ = _ := by ring

theorem localizedCenter_agrees_on_path {s0 p R : ℝ}
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hR : 0 < R)
    (q : CenterWeightedPath s0 p) (hq : ‖q‖ ≤ R)
    {t : ℝ} (ht : s0 ≤ t) :
    localizedCenterNonlinearity s0 p R G t (unweightPathGlobal p s0 q t) =
      G t (unweightPathGlobal p s0 q t) := by
  have hb : ‖unweightPathGlobal p s0 q t‖ ≤ lateRadius s0 p R t := by
    rw [lateRadius, max_eq_right ht]
    exact (unweightPathGlobal_norm_bound p s0 hs0 q ht).trans
      (mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg (hs0.trans_le ht).le _))
  unfold localizedCenterNonlinearity
  rw [radialClip_eq_of_norm_le (lateRadius_pos hs0 hR t) hb]

theorem localizedCenter_tail_eq {s0 p R : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hR : 0 < R)
    (q : CenterWeightedPath s0 p) (hq : ‖q‖ ≤ R)
    {s : ℝ} (hs : s0 ≤ s) :
    weightedCenterNonlinearTail CE (localizedCenterNonlinearity s0 p R G) p q s =
      weightedCenterNonlinearTail CE G p q s := by
  unfold weightedCenterNonlinearTail weightedCenterNonlinearSource
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [localizedCenter_agrees_on_path G hs0 hR q hq (hs.trans ht.le)]

/-- Reuse the existing global Duhamel map only after proving the extension bounds. -/
def localizedCenterMap {s0 p delta Cnl R : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hdelta : 0 < delta)
    (hC : 0 ≤ Cnl) (hR : 0 < R)
    (hcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hloc : LocalCenterLipschitz s0 p delta Cnl R G) :
    CenterWeightedPath s0 p → CenterWeightedPath s0 p :=
  weightedCenterNonlinearMap CE (localizedCenterNonlinearity s0 p R G)
    hs0 hp hdelta (mul_nonneg (by norm_num) hC)
    (localizedCenter_continuous G hs0 hR hcont)
    (localizedCenter_zero G hzero)
    (localizedCenter_global_bound G hs0 hR hC hloc)

section Map
variable {s0 p delta Cnl R : ℝ}
variable (CE : StandardConstrainedCenterPropagator s0)
variable (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
variable (hs0 : 0 < s0) (hp : 1 < p) (hdelta : 0 < delta)
variable (hC : 0 ≤ Cnl) (hR : 0 < R)
variable (hcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
variable (hzero : ∀ t, s0 ≤ t → G t 0 = 0)
variable (hloc : LocalCenterLipschitz s0 p delta Cnl R G)

theorem localizedCenterMap_norm_le (q : CenterWeightedPath s0 p) :
    ‖localizedCenterMap CE G hs0 hp hdelta hC hR hcont hzero hloc q‖ ≤
      centerNonlinearLipschitzConstant CE p delta (2 * Cnl) * ‖q‖ := by
  have h2C : 0 ≤ 2 * Cnl := mul_nonneg (by norm_num) hC
  have hk := centerNonlinearLipschitzConstant_nonneg CE hs0 hp hdelta h2C
  rw [BoundedContinuousFunction.norm_le (mul_nonneg hk (norm_nonneg q))]
  intro s
  exact weightedCenterNonlinearValue_bound CE
    (localizedCenterNonlinearity s0 p R G) hs0 hp hdelta h2C
    (localizedCenter_continuous G hs0 hR hcont)
    (localizedCenter_zero G hzero)
    (localizedCenter_global_bound G hs0 hR hC hloc) q s

theorem localizedCenterMap_difference_norm (q r : CenterWeightedPath s0 p) :
    ‖localizedCenterMap CE G hs0 hp hdelta hC hR hcont hzero hloc q -
      localizedCenterMap CE G hs0 hp hdelta hC hR hcont hzero hloc r‖ ≤
      centerNonlinearLipschitzConstant CE p delta (2 * Cnl) * ‖q - r‖ := by
  exact weightedCenterNonlinearMap_difference_norm CE
    (localizedCenterNonlinearity s0 p R G) hs0 hp hdelta
    (mul_nonneg (by norm_num) hC)
    (localizedCenter_continuous G hs0 hR hcont)
    (localizedCenter_zero G hzero)
    (localizedCenter_global_bound G hs0 hR hC hloc) q r

theorem localizedCenterMap_apply (q : CenterWeightedPath s0 p)
    (hq : ‖q‖ ≤ R) (s : LateTime s0) :
    localizedCenterMap CE G hs0 hp hdelta hC hR hcont hzero hloc q s =
      weightedCenterNonlinearValue CE G p q s := by
  change (s : ℝ) ^ p • weightedCenterNonlinearTail CE
    (localizedCenterNonlinearity s0 p R G) p q s =
    (s : ℝ) ^ p • weightedCenterNonlinearTail CE G p q s
  rw [localizedCenter_tail_eq CE G hs0 hR q hq s.2]
end Map

/-- A quantitative ball bound in the given metric, not an assumed fixed point. -/
theorem affine_fixedPoint_ball
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (F : X → X) (o : X) {k R : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hdiff : ∀ x y, dist (F x) (F y) ≤ k * dist x y)
    (hforcing : dist (F o) o ≤ (1 - k) * R) :
    ∃! q, F q = q ∧ dist q o ≤ R := by
  letI : Nonempty X := ⟨o⟩
  let K : NNReal := ⟨k, hk⟩
  have hL : LipschitzWith K F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (F x) (F y) ≤ k * dist x y
    exact hdiff x y
  have hcontract : ContractingWith K F := ⟨hk1, hL⟩
  let q := ContractingWith.fixedPoint F hcontract
  have hq : F q = q := hcontract.fixedPoint_isFixedPt
  have hb : dist q o ≤ k * dist q o + dist (F o) o := by
    calc
      dist q o = dist (F q) o := by rw [hq]
      _ ≤ dist (F q) (F o) + dist (F o) o := dist_triangle _ _ _
      _ ≤ k * dist q o + dist (F o) o := _root_.add_le_add (hdiff q o) le_rfl
  have hqr : dist q o ≤ R := by
    by_contra hqR
    have hprod := mul_pos (sub_pos.mpr hk1) (sub_pos.mpr (lt_of_not_ge hqR))
    nlinarith only [hb, hforcing, hprod]
  refine ⟨q, ⟨hq, hqr⟩, ?_⟩
  intro y hy
  exact hcontract.fixedPoint_unique hy.1

/-- Unique small-ball solution of the ORIGINAL nonlinear Duhamel equation.
The propagator and local source-space bounds remain explicit assumptions. -/
theorem localizedCenter_solution {s0 p delta Cnl R : ℝ}
    (CE : StandardConstrainedCenterPropagator s0)
    (G : ℝ → ConstrainedCenterSpace → ConstrainedCenterSpace)
    (hs0 : 0 < s0) (hp : 1 < p) (hdelta : 0 < delta)
    (hC : 0 ≤ Cnl) (hR : 0 < R)
    (hcont : Continuous (fun z : ℝ × ConstrainedCenterSpace => G z.1 z.2))
    (hzero : ∀ t, s0 ≤ t → G t 0 = 0)
    (hloc : LocalCenterLipschitz s0 p delta Cnl R G)
    (b : CenterWeightedPath s0 p)
    (hsmall : centerNonlinearLipschitzConstant CE p delta (2 * Cnl) < 1)
    (hforcing : ‖b‖ ≤
      (1 - centerNonlinearLipschitzConstant CE p delta (2 * Cnl)) * R) :
    ∃! q : CenterWeightedPath s0 p, ‖q‖ ≤ R ∧
      ∀ s : LateTime s0, q s = b s + weightedCenterNonlinearValue CE G p q s := by
  let M := localizedCenterMap CE G hs0 hp hdelta hC hR hcont hzero hloc
  let k := centerNonlinearLipschitzConstant CE p delta (2 * Cnl)
  have hk : 0 ≤ k := centerNonlinearLipschitzConstant_nonneg CE hs0 hp hdelta
    (mul_nonneg (by norm_num) hC)
  have hMzero : M 0 = 0 := by
    apply BoundedContinuousFunction.ext
    intro s
    change (s : ℝ) ^ p • (-(∫ t in Ioi (s : ℝ), CE.U s t
      (localizedCenterNonlinearity s0 p R G t
        (unweightPathGlobal p s0 (0 : CenterWeightedPath s0 p) t)))) =
      (0 : ConstrainedCenterSpace)
    have hI : (∫ t in Ioi (s : ℝ), CE.U s t
        (localizedCenterNonlinearity s0 p R G t
          (unweightPathGlobal p s0 (0 : CenterWeightedPath s0 p) t))) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hz : unweightPathGlobal p s0 (0 : CenterWeightedPath s0 p) t = 0 := by
        change (max s0 t) ^ (-p) • (0 : ConstrainedCenterSpace) = 0
        exact smul_zero _
      rw [hz, localizedCenter_zero G hzero t (s.2.trans ht.le), map_zero]
    rw [hI, neg_zero, smul_zero]
  let F : CenterWeightedPath s0 p → CenterWeightedPath s0 p := fun q => b + M q
  have hdiff : ∀ q r, ‖F q - F r‖ ≤ k * ‖q - r‖ := by
    intro q r
    have hid : F q - F r = M q - M r := by
      dsimp [F]
      abel
    rw [hid]
    exact localizedCenterMap_difference_norm CE G hs0 hp hdelta hC hR hcont hzero hloc q r
  have hf0 : F 0 = b := by
    apply BoundedContinuousFunction.ext
    intro s
    change b s + M 0 s = b s
    have hz := congrArg (fun v : CenterWeightedPath s0 p => v s) hMzero
    change M 0 s = (0 : ConstrainedCenterSpace) at hz
    rw [hz, add_zero]
  have hdist0 (v : CenterWeightedPath s0 p) : dist v 0 = ‖v‖ := by
    have hz : v - (0 : CenterWeightedPath s0 p) = v := by
      apply BoundedContinuousFunction.ext
      intro s
      change v s - (0 : ConstrainedCenterSpace) = v s
      exact sub_zero _
    rw [centerWeightedPath_dist_eq_norm_sub s0 p v 0, hz]
  have hmetric : ∀ q r, dist (F q) (F r) ≤ k * dist q r := by
    intro q r
    rw [centerWeightedPath_dist_eq_norm_sub s0 p (F q) (F r),
      centerWeightedPath_dist_eq_norm_sub s0 p q r]
    exact hdiff q r
  have hf : dist (F 0) 0 ≤ (1 - k) * R := by
    rw [hf0, hdist0 b]
    exact hforcing
  obtain ⟨q, hq, huniq⟩ := affine_fixedPoint_ball F 0 hk hsmall hmetric hf
  have hqr : ‖q‖ ≤ R := by simpa only [hdist0 q] using hq.2
  refine ⟨q, ⟨hqr, ?_⟩, ?_⟩
  · intro s
    have heq := congrArg (fun v : CenterWeightedPath s0 p => v s) hq.1.symm
    change q s = b s + localizedCenterMap CE G hs0 hp hdelta hC hR hcont hzero hloc q s at heq
    rw [localizedCenterMap_apply CE G hs0 hp hdelta hC hR hcont hzero hloc q hqr s] at heq
    exact heq
  · intro y hy
    apply huniq y
    refine ⟨?_, ?_⟩
    · apply BoundedContinuousFunction.ext
      intro s
      change b s + localizedCenterMap CE G hs0 hp hdelta hC hR hcont hzero hloc y s = y s
      rw [localizedCenterMap_apply CE G hs0 hp hdelta hC hR hcont hzero hloc y hy.1 s]
      exact (hy.2 s).symm
    · rw [hdist0 y]
      exact hy.1

end HBL.MainBackward.Localized
