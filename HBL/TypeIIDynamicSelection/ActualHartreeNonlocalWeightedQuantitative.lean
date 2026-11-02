import HBL.TypeIIDynamicSelection.ActualHartreeRieszMeasurability
import HBL.TypeIIDynamicSelection.ActualHartreeNonlocalWeightedSource
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic

/-!
# Quantitative L2 bound for one genuine nonlocal Hartree physical cutoff source

The previous module proves MemLp for the original Fredholm space.
Here the local majorant is converted to a NUMERIC L2 estimate:
  eLpNorm(F) <= weighted_radius * (2 C_H D B^3) ell^(5/2) sqrt(2R).

This explicitly retains the correct square-root spatial-volume factor.
When R=4/(kappa_H ell m) and m is uniformly positive, its final
physical power is ell^(2-sigma) for 3/2<sigma<2. The physical rate
and uniform actual radiation estimates are separate PDE obligations.

Not a proof of original 2.12: no generated-weight cancellation or
actual Kummer/remote inverse is claimed here.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Quantitative half-line L² estimate using the ACTUAL observation
support and a pointwise bound; the factor sqrt(2R) is not discarded. -/
theorem actual_supported_halfLine_L2_norm_le
    (R A : ℝ) (hR : 0 < R) (hA : 0 ≤ A)
    (F : ℝ → ℝ) (hF : Measurable F)
    (hFnonneg : ∀ r, 0 ≤ F r)
    (hFbound : ∀ r, 0 < r → r ≤ 2*R → F r ≤ A)
    (hFzero : ∀ r, 2*R ≤ r → F r = 0) :
    (eLpNorm F 2 halfLineMeasure).toReal ≤ A * Real.sqrt (2*R) := by
  let E : ℝ → ℝ := (Ioi (0 : ℝ)).indicator F
  let G : ℝ → ℝ := (Ioc (0 : ℝ) (2*R)).indicator (fun _ : ℝ => A)
  have hDom : ∀ r : ℝ, ‖E r‖ ≤ ‖G r‖ := by
    intro r
    by_cases hpos : 0 < r
    · have hp : r ∈ Ioi (0 : ℝ) := hpos
      by_cases hcap : r ≤ 2*R
      · have hc : r ∈ Ioc (0 : ℝ) (2*R) := ⟨hpos,hcap⟩
        change ‖(Ioi (0 : ℝ)).indicator F r‖ ≤
          ‖(Ioc (0 : ℝ) (2*R)).indicator (fun _ : ℝ => A) r‖
        rw [indicator_of_mem hp, indicator_of_mem hc,
          Real.norm_eq_abs, abs_of_nonneg (hFnonneg r),
          Real.norm_eq_abs, abs_of_nonneg hA]
        exact hFbound r hpos hcap
      · have hz : F r = 0 := hFzero r (le_of_not_ge hcap)
        have hnot : r ∉ Ioc (0 : ℝ) (2*R) :=
          fun hc => hcap hc.2
        change ‖(Ioi (0 : ℝ)).indicator F r‖ ≤
          ‖(Ioc (0 : ℝ) (2*R)).indicator (fun _ : ℝ => A) r‖
        simp [hp, hnot, hz]
    · have hp : r ∉ Ioi (0 : ℝ) := hpos
      have hnot : r ∉ Ioc (0 : ℝ) (2*R) :=
        fun hc => hpos hc.1
      change ‖(Ioi (0 : ℝ)).indicator F r‖ ≤
        ‖(Ioc (0 : ℝ) (2*R)).indicator (fun _ : ℝ => A) r‖
      simp [hp,hnot]
  have hGmem : MemLp G 2 (volume : Measure ℝ) :=
    memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet A
      (.inr measure_Ioc_lt_top.ne)
  have hLp :
      eLpNorm E 2 (volume : Measure ℝ) ≤
      eLpNorm G 2 (volume : Measure ℝ) :=
    eLpNorm_mono_ae
      ((hF.indicator measurableSet_Ioi).aestronglyMeasurable)
      (Filter.Eventually.of_forall hDom)
  have hNorm :
      (eLpNorm E 2 (volume : Measure ℝ)).toReal ≤
        (eLpNorm G 2 (volume : Measure ℝ)).toReal :=
    ENNReal.toReal_mono hGmem.eLpNorm_lt_top.ne hLp
  have hEqLeft :
      (eLpNorm E 2 (volume : Measure ℝ)).toReal =
      (eLpNorm F 2 halfLineMeasure).toReal := by
    change (eLpNorm ((Ioi (0 : ℝ)).indicator F) 2
        (volume : Measure ℝ)).toReal =
      (eLpNorm F 2
        ((volume : Measure ℝ).restrict (Ioi (0 : ℝ)))).toReal
    rw [eLpNorm_indicator_eq_eLpNorm_restrict
      measurableSet_Ioi.nullMeasurableSet]
  have hEqRight :
      (eLpNorm G 2 (volume : Measure ℝ)).toReal =
        A * Real.sqrt (2*R) := by
    change (eLpNorm ((Ioc (0 : ℝ) (2*R)).indicator
      (fun _ : ℝ => A)) 2 (volume : Measure ℝ)).toReal = _
    rw [eLpNorm_indicator_const measurableSet_Ioc.nullMeasurableSet
      (by norm_num) (by norm_num)]
    rw [ENNReal.toReal_mul, toReal_enorm,
      Real.volume_Ioc, sub_zero, ← ENNReal.toReal_rpow]
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*R)]
    simp only [Real.norm_eq_abs, abs_of_nonneg hA]
    norm_num [Real.sqrt_eq_rpow]
  rw [hEqLeft,hEqRight] at hNorm
  exact hNorm

/-- Numerical weighted L² bound for the true inverse-square Hartree
nonlocal cutoff source, not an abstract GeneratedTerm weight. -/
theorem actual_Hartree_nonlocal_physical_weighted_L2_quantitative
    (ell R B D sigma : ℝ)
    (hell : 0 < ell) (hR : 0 < R)
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hSigmaLo : 3/2 < sigma) (_hSigmaHi : sigma < 2)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hzAmp : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hzQuartic : ∀ u : ℝ, 0 < u →
      ‖z u‖^4 ≤ D * bubble u^2) :
    (eLpNorm
        (fun r : ℝ => affineJapaneseWeight sigma r *
          ‖actualHartreeNonlocalCutoffError R ell z r‖)
        2 halfLineMeasure).toReal ≤
      (affineJapaneseWeight sigma (2*R) *
        ((2 * radialHartreeRowBoundConstant * D * B^3) *
          ell^2 * Real.sqrt ell)) * Real.sqrt (2*R) := by
  let K : ℝ :=
    (2 * radialHartreeRowBoundConstant * D * B^3) *
      ell^2 * Real.sqrt ell
  let A : ℝ := affineJapaneseWeight sigma (2*R) * K
  let F : ℝ → ℝ := fun r =>
    affineJapaneseWeight sigma r *
      ‖actualHartreeNonlocalCutoffError R ell z r‖
  have hK : 0 ≤ K := by
    dsimp [K]
    have hk := radialHartreeRowBoundConstant_pos
    positivity
  have hA : 0 ≤ A := by
    have hk := radialHartreeRowBoundConstant_pos
    dsimp [A, K, affineJapaneseWeight]
    positivity
  have hWNonneg (r : ℝ) :
      0 ≤ affineJapaneseWeight sigma r := by
    dsimp [affineJapaneseWeight]
    positivity
  have hFNonneg (r : ℝ) : 0 ≤ F r :=
    mul_nonneg (hWNonneg r) (norm_nonneg _)
  have hFMeas : Measurable F := by
    have hw : Continuous (affineJapaneseWeight sigma) := by
      unfold affineJapaneseWeight
      have hb : Continuous (fun r : ℝ => 1 + r ^ 2) := by fun_prop
      exact hb.rpow_const (fun r => Or.inl (by positivity))
    exact hw.measurable.mul
      (actual_Hartree_nonlocal_cutoff_error_measurable R ell z hz).norm
  have hPoint := actual_Hartree_nonlocal_cutoff_sharp_and_compact_support
    ell R B D hell hR hD hB z hz hzAmp hzQuartic
  have hWeightLe (r : ℝ) (hr : 0 ≤ r) (hrR : r ≤ 2*R) :
      affineJapaneseWeight sigma r ≤ affineJapaneseWeight sigma (2*R) := by
    have hPow : r^2 ≤ (2*R)^2 := pow_le_pow_left₀ hr hrR 2
    unfold affineJapaneseWeight
    apply Real.rpow_le_rpow (by positivity)
      (by linarith [hPow])
    linarith
  have hBound (r : ℝ) (hr : 0 < r) (hrR : r ≤ 2*R) :
      F r ≤ A := by
    change affineJapaneseWeight sigma r *
      ‖actualHartreeNonlocalCutoffError R ell z r‖ ≤ A
    calc
      _ ≤ affineJapaneseWeight sigma r * K :=
        mul_le_mul_of_nonneg_left (hPoint r hr).1 (hWNonneg r)
      _ ≤ affineJapaneseWeight sigma (2*R) * K :=
        mul_le_mul_of_nonneg_right (hWeightLe r hr.le hrR) hK
      _ = A := rfl
  have hFar (r : ℝ) (hr : 2*R ≤ r) : F r = 0 := by
    dsimp [F]
    have hpr : 0 < r := lt_of_lt_of_le (by positivity : 0 < 2*R) hr
    rw [(hPoint r hpr).2 hr]
    simp
  have hNorm := actual_supported_halfLine_L2_norm_le
    R A hR hA F hFMeas hFNonneg hBound hFar
  change (eLpNorm F 2 halfLineMeasure).toReal ≤
    A * Real.sqrt (2*R) at hNorm
  exact hNorm

end HBL.TypeIIDynamicSelection
