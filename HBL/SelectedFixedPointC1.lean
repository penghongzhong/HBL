import HBL.ParametricFixedPointC1
import HBL.MainRateSelection

/-!
# Identify the selected fixed point with the existing implicit C1 graph

Reuse the HBL implicit-function proof, not a second fixed-point construction.
Local contraction on an OPEN state neighborhood supplies the derivative norm
bound and uniqueness. The residual's partial derivative is proved to be I-D.
Uniqueness then identifies the already selected solution with the implicit
function; no continuity or differentiability of that selected solution is an
input. Only the original untruncated map needs to be C1: no differentiability
of a radial clipping map is required.

The second terminal transfers this identification to shooting, reconstructed
initial data and the selected physical rate using the existing rate theorem.
These are calculus/assembly conclusions conditional on the displayed actual
map, fixed-point family and reconstruction hypotheses. This file does not
construct the Hartree propagator, prove C1 of the physical nonlinear solver,
prove invertibility of the physical initial-data chart, or close thm:main.
-/

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace HBL.MainBackward

private theorem local_fixed_point_unique
    {X : Type*} [NormedAddCommGroup X]
    (T : X → X) (U : Set X) (k : ℝ≥0) (hk : (k : ℝ) < 1)
    (hT : LipschitzOnWith k T U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hfx : T x = x) (hfy : T y = y) : x = y := by
  have hb := hT.dist_le_mul hx hy
  rw [hfx, hfy] at hb
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg x y]

/-- The existing selected fixed point is C1. Neither its regularity, the
partial-derivative formula, nor a derivative-norm bound is assumed. Local
Lipschitz control suffices; no global Lipschitz extension is differentiated. -/
theorem selected_local_fixedPoint_contDiffAt
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T : P × X → X) (q : P → X)
    (V : Set P) (U : Set X) (hV : IsOpen V) (hU : IsOpen U)
    (k : ℝ≥0) (hk : (k : ℝ) < 1)
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
    simpa using (hasFDerivAt_const p (q p)).prodMk (hasFDerivAt_id (q p))
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

/-- Shooting, reconstructed data and physical rate all refer to the SAME
selected fixed point. The last equivalence gives uniqueness of the shooting
value among local fixed points. A physical coordinate chart is not fabricated:
its reconstruction and inverse-coordinate regularity are explicit inputs. -/
theorem selected_fixedPoint_shooting_data_rate_C1
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : P × X → X) (q : P → X)
    (V : Set P) (U : Set X) (hV : IsOpen V) (hU : IsOpen U)
    (k : ℝ≥0) (hk : (k : ℝ) < 1)
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

#print axioms selected_local_fixedPoint_contDiffAt
#print axioms selected_fixedPoint_shooting_data_rate_C1

end HBL.MainBackward
