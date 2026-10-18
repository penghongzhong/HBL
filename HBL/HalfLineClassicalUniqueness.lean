import HBL.WeightedFreeGreenODE
import Mathlib.Analysis.Calculus.MeanValue

/-! Classical uniqueness on the half-line from the differential equation,
the endpoint value, and sublinear growth. No integral equation is assumed. -/

noncomputable section

open Set Filter
open scoped Topology

namespace HBL.Modulation.Monopole

theorem halfLine_affine_of_secondDeriv_zero
    {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Ioi 0))
    (hf' : DifferentiableOn ℝ (deriv f) (Ioi 0))
    (hf'' : ∀ r > 0, deriv (deriv f) r = 0) :
    ∃ c d : ℝ, ∀ r > 0, f r = c * r + d := by
  obtain ⟨c, hc⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero
    isPreconnected_Ioi hf' (fun r hr => hf'' r hr)
  have hlin : DifferentiableOn ℝ (fun r : ℝ => c * r) (Ioi 0) :=
    fun r _ => ((hasDerivAt_id r).const_mul c).differentiableAt.differentiableWithinAt
  obtain ⟨d, hd⟩ := isOpen_Ioi.exists_eq_add_of_deriv_eq
    isPreconnected_Ioi hf hlin (by
      intro r hr
      rw [hc r hr]
      simp)
  exact ⟨c, d, fun r hr => hd hr⟩

theorem halfLine_zero_of_secondDeriv_zero_sublinear
    {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Ici 0))
    (hf : DifferentiableOn ℝ f (Ioi 0))
    (hf' : DifferentiableOn ℝ (deriv f) (Ioi 0))
    (hf'' : ∀ r > 0, deriv (deriv f) r = 0)
    (hzero : f 0 = 0)
    (hsub : Tendsto (fun r => f r / r) atTop (𝓝 0)) :
    ∀ r ≥ 0, f r = 0 := by
  obtain ⟨c, d, hform⟩ := halfLine_affine_of_secondDeriv_zero hf hf' hf''
  have hlim : Tendsto (fun r : ℝ => c + d * r⁻¹) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)))
  have hlimf : Tendsto (fun r => f r / r) atTop (𝓝 c) := by
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    rw [hform r hr]
    field_simp
  have hc : c = 0 := tendsto_nhds_unique hlimf hsub
  have heq : EqOn f (fun _ => d) (Ioi (0 : ℝ)) := by
    intro r hr
    simpa [hc] using hform r hr
  have heq0 : f 0 = d := by
    have hext := heq.of_subset_closure hcont continuousOn_const
      (by simp : Ioi (0 : ℝ) ⊆ Ici 0) (by simp : Ici (0 : ℝ) ⊆ closure (Ioi 0))
    exact hext (by simp)
  have hd : d = 0 := heq0.symm.trans hzero
  intro r hr
  rcases hr.eq_or_lt with hr | hr
  · simpa [← hr] using hzero
  · simpa [hd] using heq hr

theorem halfLine_classical_unique_of_sublinear_difference
    {f g : ℝ → ℝ}
    (hfc : ContinuousOn f (Ici 0)) (hgc : ContinuousOn g (Ici 0))
    (hf : DifferentiableOn ℝ f (Ioi 0))
    (hg : DifferentiableOn ℝ g (Ioi 0))
    (hf' : DifferentiableOn ℝ (deriv f) (Ioi 0))
    (hg' : DifferentiableOn ℝ (deriv g) (Ioi 0))
    (hsecond : ∀ r > 0, deriv (deriv f) r = deriv (deriv g) r)
    (hzero : f 0 = g 0)
    (hsub : Tendsto (fun r => (f r - g r) / r) atTop (𝓝 0)) :
    ∀ r ≥ 0, f r = g r := by
  have hd (r : ℝ) (hr : 0 < r) :
      HasDerivAt (fun x => f x - g x) (deriv f r - deriv g r) r :=
    (hf.differentiableAt (isOpen_Ioi.mem_nhds hr)).hasDerivAt.sub
      (hg.differentiableAt (isOpen_Ioi.mem_nhds hr)).hasDerivAt
  have hd2 (r : ℝ) (hr : 0 < r) :
      HasDerivAt (deriv (fun x => f x - g x))
        (deriv (deriv f) r - deriv (deriv g) r) r := by
    have h := (hf'.differentiableAt (isOpen_Ioi.mem_nhds hr)).hasDerivAt.sub
      (hg'.differentiableAt (isOpen_Ioi.mem_nhds hr)).hasDerivAt
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact (hd x hx).deriv
  have hvan := halfLine_zero_of_secondDeriv_zero_sublinear
    (hfc.sub hgc) (hf.sub hg)
    (fun r hr => (hd2 r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => by
      change deriv (deriv (fun x => f x - g x)) r = 0
      rw [(hd2 r hr).deriv, hsecond r hr, sub_self])
    (sub_eq_zero.mpr hzero) hsub
  exact fun r hr => sub_eq_zero.mp (hvan r hr)

end HBL.Modulation.Monopole
