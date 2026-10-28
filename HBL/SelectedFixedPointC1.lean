import HBL.ParametricFixedPointC1
import HBL.MainRateSelection
import HBL.LocalizedCenterNonlinearMap

/-!
# Reuse the fixed-point, implicit-function and physical-rate proofs

Identify a selected local fixed point with the existing implicit C1 graph.
The I-D partial derivative and derivative-norm bound are derived, not inputs.
A final construction reuses affine_fixedPoint_ball to produce the selected
family itself, with strict interior control from a forcing margin. Only the
untruncated map is required to be C1; its Lipschitz extension is never
assumed differentiable.

These are assembly conclusions with explicit map and source assumptions.
The actual Hartree evolution, joint-map C1 bounds and invertibility of its
physical initial-data chart are not constructed here. No original manuscript
environment or complete blow-up theorem is newly accepted by this file.
-/

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace HBL.MainBackward

private theorem local_fixed_point_unique
    {X : Type*} [NormedAddCommGroup X]
    (T : X → X) (U : Set X) (k : NNReal) (hk : (k : ℝ) < 1)
    (hT : LipschitzOnWith k T U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hfx : T x = x) (hfy : T y = y) : x = y := by
  have hb := hT.dist_le_mul x hx y hy
  rw [hfx, hfy] at hb
  by_contra hxy
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hlt := mul_lt_mul_of_pos_right hk hd
  rw [one_mul] at hlt
  exact (not_lt_of_ge hb) hlt

/-- The existing selected fixed point is C1. Neither its regularity, the
partial-derivative formula, nor a derivative-norm bound is assumed. -/
theorem selected_local_fixedPoint_contDiffAt
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T : P × X → X) (q : P → X)
    (V : Set P) (U : Set X) (hV : IsOpen V) (hU : IsOpen U)
    (k : NNReal) (hk : (k : ℝ) < 1)
    (hq : ∀ y ∈ V, q y ∈ U)
    (hfixed : ∀ y ∈ V, T (y, q y) = q y)
    (hlip : ∀ y ∈ V, LipschitzOnWith k (fun x => T (y, x)) U)
    {p : P} (hp : p ∈ V)
    (hT : ContDiffAt ℝ 1 T (p, q p)) :
    ContDiffAt ℝ 1 q p := by
  let D : X →L[ℝ] X :=
    fderiv ℝ T (p, q p) ∘L ContinuousLinearMap.inr ℝ P X
  have hTd := (hT.differentiableAt (by norm_num)).hasFDerivAt
  have hin : HasFDerivAt (fun x : X => (p, x))
      (ContinuousLinearMap.inr ℝ P X) (q p) := by
    have he : (0 : X →L[ℝ] P).prod (ContinuousLinearMap.id ℝ X) =
        ContinuousLinearMap.inr ℝ P X := by
      apply ContinuousLinearMap.ext
      intro x
      rfl
    have hh : HasFDerivAt (fun x : X => (p, x))
        ((0 : X →L[ℝ] P).prod (ContinuousLinearMap.id ℝ X)) (q p) :=
      (hasFDerivAt_const p (q p)).prodMk (hasFDerivAt_id (q p))
    rw [he] at hh
    exact hh
  have hDx : fderiv ℝ (fun x => T (p, x)) (q p) = D :=
    (hTd.comp (q p) hin).fderiv
  have hDb : ‖D‖ ≤ (k : ℝ) := by
    rw [← hDx]
    exact norm_fderiv_le_of_lipschitzOn ℝ (hU.mem_nhds (hq p hp)) (hlip p hp)
  let F : P × X → X := fun z => z.2 - T z
  have hF : ContDiffAt ℝ 1 F (p, q p) := contDiffAt_snd.sub hT
  have hFd : HasFDerivAt F
      (ContinuousLinearMap.snd ℝ P X - fderiv ℝ T (p, q p)) (p, q p) :=
    (ContinuousLinearMap.snd ℝ P X).hasFDerivAt.sub hTd
  have hpartial : fderiv ℝ F (p, q p) ∘L ContinuousLinearMap.inr ℝ P X =
      ContinuousLinearMap.id ℝ X - D := by
    rw [hFd.fderiv]
    ext x
    simp [D, ContinuousLinearMap.comp_apply]
  obtain ⟨ψ, hψ, hψC, hlevel⟩ := contracting_fixed_point_has_C1_local_graph
    F p (q p) D hF hpartial (hDb.trans_lt hk)
  have hFzero : F (p, q p) = 0 := by
    dsimp only [F]
    rw [hfixed p hp, sub_self]
  have hψmem : ∀ᶠ y in 𝓝 p, ψ y ∈ U := by
    apply hψC.continuousAt.eventually
    apply hU.mem_nhds
    rw [hψ]
    exact hq p hp
  have heq : q =ᶠ[𝓝 p] ψ := by
    filter_upwards [hV.mem_nhds hp, hlevel, hψmem] with y hy hFy hψy
    have hψfixed : T (y, ψ y) = ψ y := by
      have hz : ψ y - T (y, ψ y) = 0 := hFy.trans hFzero
      exact (sub_eq_zero.mp hz).symm
    exact local_fixed_point_unique (fun x => T (y, x)) U k hk (hlip y hy)
      (hq y hy) hψy (hfixed y hy) hψfixed
  exact hψC.congr_of_eventuallyEq heq

/-- Shooting, reconstructed data and rate refer to the SAME selected point.
Physical chart regularity is explicitly required, not inferred from symbols. -/
theorem selected_fixedPoint_shooting_data_rate_C1
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : P × X → X) (q : P → X)
    (V : Set P) (U : Set X) (hV : IsOpen V) (hU : IsOpen U)
    (k : NNReal) (hk : (k : ℝ) < 1)
    (hq : ∀ y ∈ V, q y ∈ U)
    (hfixed : ∀ y ∈ V, T (y, q y) = q y)
    (hlip : ∀ y ∈ V, LipschitzOnWith k (fun x => T (y, x)) U)
    {p : P} (hp : p ∈ V)
    (hT : ContDiffAt ℝ 1 T (p, q p))
    (shoot : P × X → ℝ) (reconstruct : P × X → Y) (mu : Y → ℝ)
    (hshoot : ContDiffAt ℝ 1 shoot (p, q p))
    (hreconstruct : ContDiffAt ℝ 1 reconstruct (p, q p))
    (hmu : ContDiffAt ℝ 1 mu (reconstruct (p, q p))) :
    ContDiffAt ℝ 1 q p ∧
    ContDiffAt ℝ 1 (fun y => shoot (y, q y)) p ∧
    ContDiffAt ℝ 1 (fun y => reconstruct (y, q y)) p ∧
    ContDiffAt ℝ 1 (fun y => selectedPhysicalRate (mu (reconstruct (y, q y)))) p ∧
    (selectedPhysicalRate (mu (reconstruct (p, q p))) = 2 ↔
      mu (reconstruct (p, q p)) = 3 / 4) ∧
    ∀ a : ℝ,
      (∃ x ∈ U, T (p, x) = x ∧ shoot (p, x) = a) ↔ shoot (p, q p) = a := by
  have hqC := selected_local_fixedPoint_contDiffAt T q V U hV hU k hk
    hq hfixed hlip hp hT
  have hpair : ContDiffAt ℝ 1 (fun y => (y, q y)) p := contDiffAt_id.prodMk hqC
  have hs := hshoot.comp p hpair
  have hr := hreconstruct.comp p hpair
  have hm := hmu.comp p hr
  refine ⟨hqC, hs, hr, selectedPhysicalRate_contDiff.contDiffAt.comp p hm,
    selectedPhysicalRate_eq_two_iff _, ?_⟩
  intro a
  constructor
  · rintro ⟨x, hx, hxfixed, hxa⟩
    have heq : x = q p := local_fixed_point_unique (fun x => T (p, x))
      U k hk (hlip p hp) hx (hq p hp) hxfixed (hfixed p hp)
    simpa only [heq] using hxa
  · intro ha
    exact ⟨q p, hq p hp, hfixed p hp, ha⟩

/-- Reuse the existing Banach ball solver to CONSTRUCT the C1 selected family.
The extension A need only be Lipschitz. The original map T agrees with it on
the closed ball and is C1 only in the interior. Strict forcing puts the unique
solution in that interior, so no regularity of the clipping operation or
pre-existing selected solution family is assumed. -/
theorem construct_local_fixedPoint_C1_family
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T A : P × X → X) (V : Set P) (hV : IsOpen V)
    (R : ℝ) (_hR : 0 < R) (k : NNReal) (hk : (k : ℝ) < 1)
    (hA : ∀ p ∈ V, LipschitzWith k (fun x => A (p, x)))
    (hforcing : ∀ p ∈ V, ‖A (p, 0)‖ < (1 - (k : ℝ)) * R)
    (hagrees : ∀ p ∈ V, ∀ x : X, ‖x‖ ≤ R → A (p, x) = T (p, x))
    (hT : ∀ p ∈ V, ∀ x : X, ‖x‖ < R → ContDiffAt ℝ 1 T (p, x)) :
    ∃ q : P → X,
      (∀ p ∈ V, ‖q p‖ < R ∧ T (p, q p) = q p ∧ ContDiffAt ℝ 1 q p) ∧
      ∀ p ∈ V, ∀ x : X, ‖x‖ ≤ R → T (p, x) = x → x = q p := by
  classical
  have hex : ∀ p : P, ∃ x : X, p ∈ V → ‖x‖ < R ∧ T (p, x) = x := by
    intro p
    by_cases hp : p ∈ V
    · have hforce : dist (A (p, 0)) (0 : X) ≤ (1 - (k : ℝ)) * R := by
        simpa only [dist_zero_right] using (hforcing p hp).le
      obtain ⟨x, hx, _⟩ := Localized.affine_fixedPoint_ball (fun x => A (p, x))
        (0 : X) k.coe_nonneg hk (fun x y => (hA p hp).dist_le_mul x y) hforce
      have hxfixed : A (p, x) = x := hx.1
      have hxr : ‖x‖ ≤ R := by simpa only [dist_zero_right] using hx.2
      have hb : ‖x‖ ≤ (k : ℝ) * ‖x‖ + ‖A (p, 0)‖ := by
        have htri := dist_triangle (A (p, x)) (A (p, 0)) (0 : X)
        have hdist := (hA p hp).dist_le_mul x 0
        have hh := htri.trans (add_le_add hdist le_rfl)
        simpa only [hxfixed, dist_zero_right] using hh
      have hxlt : ‖x‖ < R := by
        by_contra hh
        have heq : ‖x‖ = R := le_antisymm hxr (le_of_not_gt hh)
        rw [heq] at hb
        nlinarith [hforcing p hp]
      refine ⟨x, fun _ => ⟨hxlt, ?_⟩⟩
      rw [← hagrees p hp x hxr]
      exact hxfixed
    · exact ⟨0, fun hm => (hp hm).elim⟩
  choose q hq using hex
  have hqmem : ∀ p ∈ V, q p ∈ Metric.ball (0 : X) R := by
    intro p hp
    simpa only [mem_ball_zero_iff] using (hq p hp).1
  have hqfixed : ∀ p ∈ V, T (p, q p) = q p := fun p hp => (hq p hp).2
  have hlocal : ∀ p ∈ V,
      LipschitzOnWith k (fun x => T (p, x)) (Metric.ball (0 : X) R) := by
    intro p hp
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [← hagrees p hp x (mem_ball_zero_iff.mp hx).le,
      ← hagrees p hp y (mem_ball_zero_iff.mp hy).le]
    exact (hA p hp).dist_le_mul x y
  refine ⟨q, ?_, ?_⟩
  · intro p hp
    exact ⟨(hq p hp).1, (hq p hp).2,
      selected_local_fixedPoint_contDiffAt T q V (Metric.ball (0 : X) R)
        hV Metric.isOpen_ball k hk hqmem hqfixed hlocal hp (hT p hp (q p) (hq p hp).1)⟩
  · intro p hp x hx hxfixed
    apply local_fixed_point_unique (fun x => A (p, x)) Set.univ k hk
      (hA p hp).lipschitzOnWith (Set.mem_univ _) (Set.mem_univ _)
    · rw [hagrees p hp x hx]
      exact hxfixed
    · rw [hagrees p hp (q p) (hq p hp).1.le]
      exact (hq p hp).2

#print axioms selected_local_fixedPoint_contDiffAt
#print axioms selected_fixedPoint_shooting_data_rate_C1
#print axioms construct_local_fixedPoint_C1_family

end HBL.MainBackward
