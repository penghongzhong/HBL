import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
The Fredholm compatibility condition for a compact, not necessarily
self-adjoint, operator on a real Hilbert space.

The key point is that the range of `I - K` is closed.  We prove this
directly by restricting to the perpendicular complement of its kernel and
using compactness to obtain a lower bound there.  This avoids inserting a
self-adjointness hypothesis that is not available for the weighted Hartree
Birman--Schwinger operator.
-/

noncomputable section

open Module End Filter Topology

namespace HBL.Fredholm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Restriction of a continuous linear map to the perpendicular complement
of its kernel. -/
def kernelComplementRestriction (A : E →L[ℝ] E) :
    A.kerᗮ →L[ℝ] E :=
  A.comp A.kerᗮ.subtypeL

/-- A compact perturbation of the identity is bounded below after removing
its kernel. -/
theorem one_sub_antilipschitz_on_kernelComplement
    {K : E →L[ℝ] E} (hKcompact : IsCompactOperator K) :
    ∃ C, AntilipschitzWith C
      (kernelComplementRestriction (1 - K)) := by
  let A : E →L[ℝ] E := 1 - K
  let M : Submodule ℝ E := A.kerᗮ
  let S : M →L[ℝ] E := A.comp M.subtypeL
  letI : CompleteSpace M :=
    A.ker.isClosed_orthogonal.completeSpace_coe
  change ∃ C, AntilipschitzWith C S
  rw [antilipschitzWith_iff_exists_mul_le_norm]
  by_contra hbound
  push_neg at hbound
  let hsmall := hbound
  have hchoose (n : ℕ) :
      ∃ x : M, ‖x‖ ≤ 1 ∧ (1 / 2 : ℝ) ≤ ‖x‖ ∧
        ‖S x‖ < (n + 1 : ℝ)⁻¹ := by
    obtain ⟨x, hx⟩ := hsmall ((n + 1 : ℝ)⁻¹)
      (by positivity)
    have hxne : x ≠ 0 := by
      intro hx0
      subst x
      simpa using hx
    obtain ⟨c, hc, hc_upper, hc_lower, -⟩ :=
      rescale_to_shell (x := x) (show 1 < ‖(2 : ℝ)‖ by norm_num)
        (show 0 < (1 : ℝ) by norm_num) hxne
    refine ⟨c • x, hc_upper.le, ?_, ?_⟩
    · simpa using hc_lower
    · have hmap := hx
      rw [map_smul, norm_smul]
      calc
        ‖c‖ * ‖S x‖ < ‖c‖ * ((n + 1 : ℝ)⁻¹ * ‖x‖) := by
          exact mul_lt_mul_of_pos_left hmap (norm_pos_iff.mpr hc)
        _ = (n + 1 : ℝ)⁻¹ * ‖c • x‖ := by
          rw [norm_smul]
          ring
        _ ≤ (n + 1 : ℝ)⁻¹ := by
          exact mul_le_of_le_one_right (by positivity) hc_upper.le
  choose x hx_upper hx_lower hx_small using hchoose
  have hSx : Tendsto (fun n ↦ S (x n)) atTop (nhds 0) := by
    apply squeeze_zero_norm (fun n ↦ (hx_small n).le)
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨C, hCcompact, hCmem⟩ :=
    hKcompact.image_closedBall_subset_compact 1
  obtain ⟨y, hyC, ψ, hψ, hKxy⟩ :=
    hCcompact.tendsto_subseq
      (x := fun n ↦ K (x n : E))
      (fun n ↦ hCmem ⟨(x n : E), by simpa using hx_upper n, rfl⟩)
  have hxlim : Tendsto (fun n ↦ (x (ψ n) : E)) atTop (nhds y) := by
    have hSsub : Tendsto (fun n ↦ S (x (ψ n))) atTop (nhds 0) :=
      hSx.comp hψ.tendsto_atTop
    have hadd : Tendsto
        (fun n ↦ S (x (ψ n)) + K (x (ψ n) : E))
        atTop (nhds (0 + y)) := hSsub.add hKxy
    simpa [S, A, sub_apply] using hadd
  have hyM : y ∈ M := by
    exact A.ker.isClosed_orthogonal.mem_of_tendsto hxlim
      (Filter.Eventually.of_forall fun n ↦ (x (ψ n)).property)
  have hAy : A y = 0 := by
    apply tendsto_nhds_unique
      (A.continuous.continuousAt.tendsto.comp hxlim)
    have hzero := hSx.comp hψ.tendsto_atTop
    change Tendsto (fun n ↦ A (x (ψ n) : E)) atTop (nhds 0) at hzero
    exact hzero
  have hy_ne : y ≠ 0 := by
    intro hy0
    subst y
    rw [NormedAddGroup.tendsto_nhds_zero] at hxlim
    have hevent := hxlim (1 / 2 : ℝ) (by norm_num)
    suffices ∀ᶠ n in atTop, False by
      have hex : ∃ n : ℕ, False := Filter.Eventually.exists this
      exact hex.elim (fun _ hfalse ↦ hfalse)
    filter_upwards [hevent] with n hn
    exact (not_lt_of_ge (hx_lower (ψ n))) (by simpa using hn)
  have hyker : y ∈ A.ker := by
    simpa [LinearMap.mem_ker] using hAy
  exact hy_ne
    (Submodule.disjoint_def.1 A.ker.orthogonal_disjoint y hyker hyM)

/-- Removing the kernel does not change the range. -/
theorem range_kernelComplementRestriction (A : E →L[ℝ] E) :
    (kernelComplementRestriction A).range = A.range := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨(x : E), rfl⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨A.kerᗮ.orthogonalProjectionOnto x, ?_⟩
    change A (A.kerᗮ.starProjection x) = A x
    rw [A.ker.starProjection_orthogonal_val]
    have hproj : A (A.ker.starProjection x) = 0 := by
      exact (A.ker.orthogonalProjectionOnto x).property
    rw [map_sub, hproj, sub_zero]

set_option maxHeartbeats 800000 in
/-- The range of a compact perturbation of the identity is closed. -/
theorem one_sub_isClosed_range
    {K : E →L[ℝ] E} (hKcompact : IsCompactOperator K) :
    IsClosed ((1 - K).range : Set E) := by
  obtain ⟨C, hC⟩ :=
    one_sub_antilipschitz_on_kernelComplement (E := E) hKcompact
  rw [← range_kernelComplementRestriction (E := E)]
  exact hC.isClosed_range
    (kernelComplementRestriction (1 - K)).uniformContinuous

/-- For `I-K`, the range is exactly the perpendicular complement of the
adjoint kernel. -/
theorem one_sub_range_eq_adjointKernel_orthogonal
    {K : E →L[ℝ] E} (hKcompact : IsCompactOperator K) :
    (1 - K).range =
      (ContinuousLinearMap.adjoint (1 - K)).kerᗮ := by
  have hclosed := one_sub_isClosed_range hKcompact
  have hadj := ContinuousLinearMap.orthogonal_ker
    (ContinuousLinearMap.adjoint (1 - K))
  rw [ContinuousLinearMap.adjoint_adjoint] at hadj
  rw [hadj, hclosed.submodule_topologicalClosure_eq]

/-- Fredholm compatibility and the unique normalization perpendicular to
the kernel, with no symmetry assumption on the compact operator. -/
theorem existsUnique_one_sub_apply_eq_of_mem_adjointKernel_orthogonal
    {K : E →L[ℝ] E} (hKcompact : IsCompactOperator K)
    {f : E} (hf : f ∈
      (ContinuousLinearMap.adjoint (1 - K)).kerᗮ) :
    ∃! x : (1 - K).kerᗮ, (1 - K) (x : E) = f := by
  have hfrange : f ∈ (1 - K).range := by
    rw [one_sub_range_eq_adjointKernel_orthogonal hKcompact]
    exact hf
  have hfres : f ∈ (kernelComplementRestriction (1 - K)).range := by
    rwa [range_kernelComplementRestriction]
  obtain ⟨x, hx⟩ := hfres
  obtain ⟨C, hC⟩ :=
    one_sub_antilipschitz_on_kernelComplement hKcompact
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hC.injective (hy.trans hx.symm)

end HBL.Fredholm
