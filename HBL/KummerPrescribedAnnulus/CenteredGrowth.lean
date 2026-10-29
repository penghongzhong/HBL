import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace HBL.Profile.Kummer

/-- Two-sided Grönwall bound about the prescribed normalization point. -/
theorem centered_ode_norm_le_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (eps D : ℝ) (hD : 0 ≤ D) (f g : ℝ → E)
    (hf : ∀ t ∈ Icc (-eps) eps, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Icc (-eps) eps, ‖g t‖ ≤ D * ‖f t‖)
    (h₀ : ‖f 0‖ ≤ 1) :
    ∀ t ∈ Icc (-eps) eps, ‖f t‖ ≤ Real.exp (D * eps) := by
  have forward (u v : ℝ → E)
      (hu : ∀ t ∈ Icc 0 eps, HasDerivAt u (v t) t)
      (hv : ∀ t ∈ Icc 0 eps, ‖v t‖ ≤ D * ‖u t‖)
      (hzero : ‖u 0‖ ≤ 1) (t : ℝ) (ht : t ∈ Icc 0 eps) :
      ‖u t‖ ≤ Real.exp (D * eps) := by
    have hb := norm_le_gronwallBound_of_norm_deriv_right_le (K := D) (ε := 0)
      (fun s hs => (hu s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hu s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
      hzero (fun s hs => by simpa using hv s ⟨hs.1, hs.2.le⟩) t ht
    simp only [gronwallBound_ε0, sub_zero, one_mul] at hb
    exact hb.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hD))
  intro t ht
  by_cases hsign : 0 ≤ t
  · exact forward f g (fun s hs => hf s ⟨by linarith [hs.1, hs.2], hs.2⟩)
      (fun s hs => hg s ⟨by linarith [hs.1, hs.2], hs.2⟩) h₀ t ⟨hsign, ht.2⟩
  · have hn : -t ∈ Icc 0 eps := ⟨by linarith, by linarith [ht.1]⟩
    have hrev := forward (fun s => f (-s)) (fun s => -g (-s))
      (fun s hs => by
        have h := (hf (-s) ⟨by linarith [hs.2], by linarith [hs.1, hs.2]⟩).scomp s
          (hasDerivAt_neg s)
        simpa only [Function.comp_def, neg_one_smul] using! h)
      (fun s hs => by
        simpa only [norm_neg] using hg (-s)
          ⟨by linarith [hs.2], by linarith [hs.1, hs.2]⟩)
      (by simpa using h₀) (-t) hn
    simpa only [neg_neg] using hrev
end HBL.Profile.Kummer
