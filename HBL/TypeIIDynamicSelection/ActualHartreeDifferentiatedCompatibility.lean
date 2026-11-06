import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedCoupledInverseBound
import Mathlib.Tactic

/-!
# Differentiated two-column compatibility uses the same strict inverse

Suppose a real two-speed correction p(t) satisfies the SAME complex
compatibility identity locally,
  Z(t)+p_1(t)b(t)+p_2(t)w(t)=0.
Differentiating gives
  Y+p_1'(s)b(s)+p_2'(s)w(s)=0,
where
  Y=Z'(s)+p_1(s)b'(s)+p_2(s)w'(s).

The accepted quantitative inverse for the frozen columns therefore controls
the speed derivative with exactly the same 1024/(a B^2) constant.  No Cramer
quotient estimate or new determinant argument is used here.
-/

noncomputable section
set_option autoImplicit false

open Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection

theorem actual_complex_columns_differentiated_cancellation_bound
    (a B s : ℝ) (ha : 0 < a) (hB : 0 < B)
    (b w Z : ℝ → ℂ) (p1 p2 : ℝ → ℝ)
    (bdot wdot Zdot : ℂ) (p1dot p2dot : ℝ)
    (hb : HasDerivAt b bdot s)
    (hw : HasDerivAt w wdot s)
    (hZ : HasDerivAt Z Zdot s)
    (hp1 : HasDerivAt p1 p1dot s)
    (hp2 : HasDerivAt p2 p2dot s)
    (hlocal : ∀ᶠ t in 𝓝 s,
      Z t + (p1 t : ℂ) * b t + (p2 t : ℂ) * w t = 0)
    (hbNorm : ‖b s‖ ≤ a * B ^ 2)
    (hwNorm : ‖w s‖ ≤ a * B ^ 2)
    (hdet : a ^ 2 * B ^ 4 / 256 ≤
      (b s).re * (w s).im - (w s).re * (b s).im) :
    |p1dot| + |p2dot| ≤
      1024 / (a * B ^ 2) *
        ‖Zdot + (p1 s : ℂ) * bdot + (p2 s : ℂ) * wdot‖ := by
  have hp1c :
      HasDerivAt (fun t => (p1 t : ℂ)) (p1dot : ℂ) s :=
    hp1.ofReal_comp
  have hp2c :
      HasDerivAt (fun t => (p2 t : ℂ)) (p2dot : ℂ) s :=
    hp2.ofReal_comp
  have hterm1 := hp1c.mul hb
  have hterm2 := hp2c.mul hw
  have hsum := (hZ.add hterm1).add hterm2
  have hzero :
      HasDerivAt
        (fun t => Z t + (p1 t : ℂ) * b t + (p2 t : ℂ) * w t)
        0 s := by
    have hc : HasDerivAt (fun _ : ℝ => (0 : ℂ)) 0 s :=
      hasDerivAt_const s 0
    have hsymm : ∀ᶠ t in 𝓝 s,
        (0 : ℂ) = Z t + (p1 t : ℂ) * b t + (p2 t : ℂ) * w t :=
      hlocal.mono (fun _ ht => ht.symm)
    exact hc.congr_of_eventuallyEq hsymm
  have hder :
      Zdot +
          ((p1dot : ℂ) * b s + (p1 s : ℂ) * bdot) +
          ((p2dot : ℂ) * w s + (p2 s : ℂ) * wdot) = 0 := by
    have heq := hsum.unique hzero
    exact heq
  let Y : ℂ :=
    Zdot + (p1 s : ℂ) * bdot + (p2 s : ℂ) * wdot
  have hcancel :
      Y + (p1dot : ℂ) * b s + (p2dot : ℂ) * w s = 0 := by
    dsimp [Y]
    linear_combination hder
  have hinv :=
    actual_complex_columns_real_cancellation_bound
      a B ha hB (b s) (w s) Y (p1dot,p2dot)
      hbNorm hwNorm hdet hcancel
  simpa only [Y, Prod.fst, Prod.snd] using hinv

/-- Alias retaining the explicit `clean` name used by downstream files. -/
theorem actual_complex_columns_differentiated_cancellation_bound_clean
    (a B s : ℝ) (ha : 0 < a) (hB : 0 < B)
    (b w Z : ℝ → ℂ) (p1 p2 : ℝ → ℝ)
    (bdot wdot Zdot : ℂ) (p1dot p2dot : ℝ)
    (hb : HasDerivAt b bdot s)
    (hw : HasDerivAt w wdot s)
    (hZ : HasDerivAt Z Zdot s)
    (hp1 : HasDerivAt p1 p1dot s)
    (hp2 : HasDerivAt p2 p2dot s)
    (hlocal : ∀ᶠ t in 𝓝 s,
      Z t + (p1 t : ℂ) * b t + (p2 t : ℂ) * w t = 0)
    (hbNorm : ‖b s‖ ≤ a * B ^ 2)
    (hwNorm : ‖w s‖ ≤ a * B ^ 2)
    (hdet : a ^ 2 * B ^ 4 / 256 ≤
      (b s).re * (w s).im - (w s).re * (b s).im) :
    |p1dot| + |p2dot| ≤
      1024 / (a * B ^ 2) *
        ‖Zdot + (p1 s : ℂ) * bdot + (p2 s : ℂ) * wdot‖ :=
  actual_complex_columns_differentiated_cancellation_bound
    a B s ha hB b w Z p1 p2 bdot wdot Zdot p1dot p2dot
    hb hw hZ hp1 hp2 hlocal hbNorm hwNorm hdet

end HBL.TypeIIDynamicSelection
