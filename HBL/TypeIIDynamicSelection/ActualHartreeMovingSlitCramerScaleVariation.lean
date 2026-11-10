import HBL.TypeIIDynamicSelection.ActualHartreeTrueMovingGreenOneRadiusGain
import Mathlib.Tactic

/-!
# Moving-slit geometry from the true Hartree scale variation

The previously certified real-Cramer source-time budget is valid only for
1/a(τ) ≤ r ≤ B. The actual singular Green time MVT runs at every
intermediate τ and every radius between L(ell(s))/a(s) and
L(ell(t))/a(t), L(e) = e^(-1/16).

This theorem does NOT assume that inclusion. Instead it proves it from
the true physical scale's variation V along the time segment, and the
explicit slow-cutoff slack at the two endpoint scales. In particular it
pinpoints the exact missing modulation budget:
V * L(ell(endpoint)) ≤ a(endpoint) * (L(ell(endpoint)) - 1).
There is no prescribed Type-II rate, source envelope, or PDE residual
gain in this geometric statement.
-/

noncomputable section
set_option autoImplicit false
open Set
namespace HBL.TypeIIDynamicSelection

/-- A finite variation bound for the genuine time-varying scale converts
the two slow-inner endpoint margins into an original physical Cramer shell
on the ENTIRE moving slit and at EVERY intermediate time. -/
theorem actual_Hartree_original_Cramer_shell_covers_moving_slow_slit
    (a ell : ℝ → ℝ) (s t B V : ℝ)
    (has : 0 < a s) (hat : 0 < a t)
    (hes : 0 < ell s) (het : 0 < ell t)
    (haSegment : ∀ τ ∈ Icc (min s t) (max s t), 0 < a τ)
    (hVariationS : ∀ τ ∈ Icc (min s t) (max s t),
      |a τ - a s| ≤ V)
    (hVariationT : ∀ τ ∈ Icc (min s t) (max s t),
      |a τ - a t| ≤ V)
    (hMarginS : V * actualHartreeSlowInnerRadius (ell s) ≤
      a s * (actualHartreeSlowInnerRadius (ell s) - 1))
    (hMarginT : V * actualHartreeSlowInnerRadius (ell t) ≤
      a t * (actualHartreeSlowInnerRadius (ell t) - 1))
    (hUpper : ∀ x ∈ uIoc
      (actualHartreeSlowInnerRadius (ell t) / a t)
      (actualHartreeSlowInnerRadius (ell s) / a s), x ≤ B) :
    ∀ τ ∈ Icc (min s t) (max s t),
      ∀ x ∈ uIoc
        (actualHartreeSlowInnerRadius (ell t) / a t)
        (actualHartreeSlowInnerRadius (ell s) / a s),
          x ∈ Icc (1 / a τ) B := by
  let Ls := actualHartreeSlowInnerRadius (ell s)
  let Lt := actualHartreeSlowInnerRadius (ell t)
  have hLs : 0 < Ls := Real.rpow_pos_of_pos hes _
  have hLt : 0 < Lt := Real.rpow_pos_of_pos het _
  intro τ hτ x hx
  have haτ := haSegment τ hτ
  have hlowS : a s - V ≤ a τ := by
    have h := (abs_le.mp (hVariationS τ hτ)).1
    linarith
  have hlowT : a t - V ≤ a τ := by
    have h := (abs_le.mp (hVariationT τ hτ)).1
    linarith
  have hscaleS : a s ≤ Ls * a τ := by
    have hn : 0 ≤ (a τ - (a s - V)) * Ls :=
      mul_nonneg (by linarith) hLs.le
    change V * Ls ≤ a s * (Ls - 1) at hMarginS
    nlinarith [hn, hMarginS]
  have hscaleT : a t ≤ Lt * a τ := by
    have hn : 0 ≤ (a τ - (a t - V)) * Lt :=
      mul_nonneg (by linarith) hLt.le
    change V * Lt ≤ a t * (Lt - 1) at hMarginT
    nlinarith [hn, hMarginT]
  have hsourceS : (1 : ℝ) / a τ ≤ Ls / a s :=
    (div_le_div_iff₀ haτ has).2 (by nlinarith [hscaleS])
  have hsourceT : (1 : ℝ) / a τ ≤ Lt / a t :=
    (div_le_div_iff₀ haτ hat).2 (by nlinarith [hscaleT])
  have hmin : min (Ls / a s) (Lt / a t) ≤ x := by
    change x ∈ Ioc (min (Lt / a t) (Ls / a s))
      (max (Lt / a t) (Ls / a s)) at hx
    simpa only [min_comm] using hx.1.le
  refine ⟨(le_min hsourceS hsourceT).trans hmin, ?_⟩
  exact hUpper x hx

end HBL.TypeIIDynamicSelection
