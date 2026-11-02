import HBL.TypeIIDynamicSelection.ActualHartreeFullCutoffSupport
import HBL.AffineTailLemmaClosed
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic

/-!
# The true nonlocal Hartree cutoff source belongs to the original Fredholm weighted L2

This derives L^(2,sigma)(0,infinity) MEMBERSHIP of the complete
inverse-square quartic Hartree Riesz cutoff commutator from its
strictly proved sharp physical gain AND proved exact observation
support r<=2R.

Only measurability of this specific physical source is supplied as a
visible analytic input; the bound and compact support are proved,
not new assumptions. The actual single-orbit local Hartree PDE
should eventually supply source measurability by dominated
differentiation and the real weighted norm needed to close 2.12.

This is not the full one-layer stage 2.12 acceptance.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.Modulation

/-- For every manuscript Fredholm weight sigma in (3/2,2), the
actual full nonlocal Riesz cutoff commutator is weighted L2,
not merely a formal pointwise source.
No regional-solver or GeneratedTerm assumption occurs. -/
theorem actual_Hartree_nonlocal_cutoff_source_mem_manuscript_weightedL2
    (ell R B D sigma : ℝ)
    (hell : 0 < ell) (hR : 0 < R)
    (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hSigmaLo : 3 / 2 < sigma) (_hSigmaHi : sigma < 2)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hzAmp : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hzQuartic : ∀ u : ℝ, 0 < u →
      ‖z u‖ ^ 4 ≤ D * bubble u ^ 2)
    (hSourceMeas : Measurable (actualHartreeNonlocalCutoffError R ell z)) :
    MemLp
      (fun r : ℝ => affineJapaneseWeight sigma r *
        ‖actualHartreeNonlocalCutoffError R ell z r‖)
      2 halfLineMeasure := by
  let K : ℝ :=
    (2 * radialHartreeRowBoundConstant * D * B ^ 3) *
      ell ^ 2 * Real.sqrt ell
  let A : ℝ := affineJapaneseWeight sigma (2 * R) * K
  let F : ℝ → ℝ :=
    fun r => affineJapaneseWeight sigma r *
      ‖actualHartreeNonlocalCutoffError R ell z r‖
  have hK : 0 ≤ K := by
    dsimp [K]
    have := radialHartreeRowBoundConstant_pos
    positivity
  have hA : 0 ≤ A := by
    dsimp [A, affineJapaneseWeight]
    positivity
  have hWeightCont : Continuous (affineJapaneseWeight sigma) := by
    unfold affineJapaneseWeight
    have hb : Continuous (fun r : ℝ => 1 + r ^ 2) := by fun_prop
    exact hb.rpow_const (fun r => Or.inl (by positivity))
  have hFmeas : Measurable F :=
    hWeightCont.measurable.mul hSourceMeas.norm
  have hFnonneg (r : ℝ) : 0 ≤ F r := by
    dsimp [F, affineJapaneseWeight]
    positivity
  have hUpper (r : ℝ) (hr : 0 ≤ r) (hrR : r ≤ 2 * R) :
      affineJapaneseWeight sigma r ≤ affineJapaneseWeight sigma (2 * R) := by
    have h2R : 0 ≤ 2 * R := by positivity
    have hPow : r ^ 2 ≤ (2 * R) ^ 2 :=
      pow_le_pow_left₀ hr hrR 2
    unfold affineJapaneseWeight
    apply Real.rpow_le_rpow (by positivity)
      (by linarith [hPow])
    linarith
  have hPoint := actual_Hartree_nonlocal_cutoff_sharp_and_compact_support
    ell R B D hell hR hD hB z hz hzAmp hzQuartic
  have hBound (r : ℝ) (hr : 0 < r) (hrR : r ≤ 2 * R) :
      F r ≤ A := by
    have hW : 0 ≤ affineJapaneseWeight sigma r := by
      unfold affineJapaneseWeight
      positivity
    calc
      F r = affineJapaneseWeight sigma r *
          ‖actualHartreeNonlocalCutoffError R ell z r‖ := rfl
      _ ≤ affineJapaneseWeight sigma r * K :=
        mul_le_mul_of_nonneg_left (hPoint r hr).1 hW
      _ ≤ affineJapaneseWeight sigma (2 * R) * K :=
        mul_le_mul_of_nonneg_right (hUpper r hr.le hrR) hK
      _ = A := rfl
  have hDom : ∀ r : ℝ,
      ‖(Ioi (0 : ℝ)).indicator F r‖ ≤
        ‖(Ioc (0 : ℝ) (2 * R)).indicator
          (fun _ : ℝ => A) r‖ := by
    intro r
    by_cases hpos : 0 < r
    · have hposmem : r ∈ Ioi (0 : ℝ) := hpos
      by_cases hcap : r ≤ 2 * R
      · have hinside : r ∈ Ioc (0 : ℝ) (2 * R) :=
          ⟨hpos, hcap⟩
        rw [indicator_of_mem hposmem, indicator_of_mem hinside,
          Real.norm_eq_abs, abs_of_nonneg (hFnonneg r),
          Real.norm_eq_abs, abs_of_nonneg hA]
        exact hBound r hpos hcap
      · have hfar : 2 * R ≤ r := le_of_not_ge hcap
        have hzero : actualHartreeNonlocalCutoffError R ell z r = 0 :=
          (hPoint r hpos).2 hfar
        have hFzero : F r = 0 := by
          dsimp [F]
          rw [hzero]
          simp
        have hout : r ∉ Ioc (0 : ℝ) (2 * R) := by
          intro hmem
          exact hcap hmem.2
        rw [indicator_of_mem hposmem, indicator_of_notMem hout, hFzero]
        simp
    · have hnotpos : r ∉ Ioi (0 : ℝ) := hpos
      have hout : r ∉ Ioc (0 : ℝ) (2 * R) := by
        intro hmem
        exact hpos hmem.1
      rw [indicator_of_notMem hnotpos, indicator_of_notMem hout]
  have hMajor :
      MemLp ((Ioc (0 : ℝ) (2 * R)).indicator
          (fun _ : ℝ => A)) 2 (volume : Measure ℝ) :=
    memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet A
      (.inr measure_Ioc_lt_top.ne)
  have hIndicator :
      MemLp ((Ioi (0 : ℝ)).indicator F) 2
        (volume : Measure ℝ) :=
    hMajor.mono'
      ((hFmeas.indicator measurableSet_Ioi).aestronglyMeasurable)
      (Filter.Eventually.of_forall hDom)
  change MemLp F 2 ((volume : Measure ℝ).restrict (Ioi (0 : ℝ)))
  exact (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mp
    hIndicator

end HBL.TypeIIDynamicSelection
