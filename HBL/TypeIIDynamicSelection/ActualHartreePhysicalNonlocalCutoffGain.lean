import HBL.TypeIIDynamicSelection.ActualHartreePhysicalSpatialCutoffSourceGain
import HBL.TypeIIDynamicSelection.ActualHartreeCriticalNonlinearityScaling
import HBL.RadialHartreeDomination
import Mathlib.Tactic

/-!
# Original HBL 2.12: actual nonlocal cutoff commutator, physical-length gain

This is the TRUE nonlocal inverse-square Hartree nonlinearity, not a
surrogate cubic. The same physical radiation z is multiplied by the
actual one-layer smooth cutoff, then scaled with
  f_ell(r) = sqrt(ell) * z(ell*r).

A uniform physical amplitude bound and an explicit quartic radial
Riesz envelope are stated as analytic inputs about the chosen
physical trajectory. Neither a blowup rate nor a generated source
order is assumed. The Riesz envelope is passed through the proved
actual bubble domination and exact critical Hartree scaling, and the
nonlinear commutator gains O(ell^2), uniformly in the moving cutoff
radius R and observation point r>0.

This source-level result does NOT prove original 2.12: the weighted
Fredholm norm, derivation of these bounds from the selected Hartree
flow, Kummer/remote compatibility, parameter variations, and the
positive-minimum-weight cluster remain open.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- A single actual Hartree nonlinear term is controlled by its
NONLOCAL Riesz potential, local square density and local amplitude. -/
private theorem radial_Hartree_nonlinearity_norm_from_real_potential
    (v : ℝ → ℂ) (r P Q B : ℝ)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hPot : |radialHartreePotential (fun rho => ‖v rho‖ ^ 4) r| ≤ P)
    (hSq : ‖v r‖ ^ 2 ≤ Q)
    (hAmp : ‖v r‖ ≤ B) :
    ‖complexRadialHartreeNonlinearity v r‖ ≤ P * Q * B := by
  have hEq :
      ‖complexRadialHartreeNonlinearity v r‖ =
        |radialHartreePotential (fun rho => ‖v rho‖ ^ 4) r| *
          ‖v r‖ ^ 2 * ‖v r‖ := by
    unfold complexRadialHartreeNonlinearity
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
  calc
    _ = _ := hEq
    _ ≤ (P * Q) * B := by
      exact mul_le_mul
        (mul_le_mul hPot hSq (sq_nonneg _) hP)
        hAmp (norm_nonneg _) (mul_nonneg hP hQ)

/-- Unlike a local-cubic approximation, this keeps BOTH full Riesz
potentials: that of the globally truncated radiation and that of
the actual whole radiation. -/
private theorem radial_Hartree_nonlinear_cutoff_commutator_le
    (chi f : ℝ → ℂ) (r P Q B : ℝ)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hChi : ‖chi r‖ ≤ 1)
    (hPotWhole :
      |radialHartreePotential (fun rho => ‖f rho‖ ^ 4) r| ≤ P)
    (hPotCut :
      |radialHartreePotential
        (fun rho => ‖chi rho * f rho‖ ^ 4) r| ≤ P)
    (hSq : ‖f r‖ ^ 2 ≤ Q)
    (hAmp : ‖f r‖ ≤ B) :
    ‖complexRadialHartreeNonlinearity
        (fun x => chi x * f x) r -
      chi r * complexRadialHartreeNonlinearity f r‖ ≤
      2 * P * Q * B := by
  have hChiAmp : ‖chi r * f r‖ ≤ ‖f r‖ := by
    calc
      _ = ‖chi r‖ * ‖f r‖ := norm_mul _ _
      _ ≤ 1 * ‖f r‖ :=
        mul_le_mul_of_nonneg_right hChi (norm_nonneg _)
      _ = ‖f r‖ := one_mul _
  have hChiSq : ‖chi r * f r‖ ^ 2 ≤ Q :=
    (pow_le_pow_left₀ (norm_nonneg _) hChiAmp 2).trans hSq
  have hCut :
      ‖complexRadialHartreeNonlinearity
          (fun x => chi x * f x) r‖ ≤ P * Q * B :=
    radial_Hartree_nonlinearity_norm_from_real_potential
      (fun x => chi x * f x) r P Q B
      hP hQ hPotCut hChiSq (hChiAmp.trans hAmp)
  have hWhole :
      ‖complexRadialHartreeNonlinearity f r‖ ≤ P * Q * B :=
    radial_Hartree_nonlinearity_norm_from_real_potential
      f r P Q B hP hQ hPotWhole hSq hAmp
  have hSecond :
      ‖chi r * complexRadialHartreeNonlinearity f r‖ ≤ P * Q * B := by
    calc
      _ = ‖chi r‖ * ‖complexRadialHartreeNonlinearity f r‖ :=
        norm_mul _ _
      _ ≤ 1 * ‖complexRadialHartreeNonlinearity f r‖ :=
        mul_le_mul_of_nonneg_right hChi (norm_nonneg _)
      _ = ‖complexRadialHartreeNonlinearity f r‖ := one_mul _
      _ ≤ P * Q * B := hWhole
  calc
    _ ≤ ‖complexRadialHartreeNonlinearity
            (fun x => chi x * f x) r‖ +
          ‖chi r * complexRadialHartreeNonlinearity f r‖ :=
      norm_sub_le _ _
    _ ≤ 2 * P * Q * B := by
      linarith

/-- The actual manuscript overlap cutoff stays in the complex unit
disk, uniformly at EVERY radius and every moving value R. -/
theorem actual_Hartree_one_layer_overlap_cutoff_norm_le_one
    (R r : ℝ) :
    ‖actualOneLayerInnerOverlapCutoff R r‖ ≤ 1 := by
  have hLo : 0 ≤ cutoff (r / R) := Real.smoothTransition.nonneg _
  have hHi : cutoff (r / R) ≤ 1 := Real.smoothTransition.le_one _
  change ‖((1 - cutoff (r / R) : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hHi)]
  linarith

/-- For the actual energy-critical rescaling, the complete nonlinear
Hartree moving-cutoff PDE commutator is O(ell^2) on the whole
positive half-line, with no independent time-order assumption.

The physical regular-radiation analytic inputs are explicit:
a uniform bound B and a quartic bubble-weighted Riesz envelope D.
These must ultimately be obtained for the selected PDE orbit. -/
theorem actual_Hartree_physical_nonlocal_cutoff_commutator_length_squared
    (ell R r B D : ℝ)
    (hell : 0 < ell) (hellSmall : ell ≤ 1) (hr : 0 < r)
    (hD : 0 ≤ D) (hB : 0 ≤ B)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hzAmp : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hzQuartic : ∀ u : ℝ, 0 < u →
      ‖z u‖ ^ 4 ≤ D * bubble u ^ 2) :
    ‖complexRadialHartreeNonlinearity
        (fun x => actualOneLayerInnerOverlapCutoff R x *
          rescalePhysicalRadiation ell z x) r -
      actualOneLayerInnerOverlapCutoff R r *
        complexRadialHartreeNonlinearity
          (rescalePhysicalRadiation ell z) r‖ ≤
      2 * radialHartreeRowBoundConstant * D * B ^ 3 * ell ^ 2 := by
  let chi : ℝ → ℂ := actualOneLayerInnerOverlapCutoff R
  let g : ℝ → ℂ := fun u => chi (u / ell) * z u
  have hChi (u : ℝ) : ‖chi u‖ ≤ 1 :=
    actual_Hartree_one_layer_overlap_cutoff_norm_le_one R u
  have hChiMeas : Measurable chi := by
    have hc : Continuous (fun x : ℝ => 1 - cutoff (x / R)) :=
      continuous_const.sub
        (cutoff_contDiff_infty.continuous.comp
          (continuous_id.div_const R))
    change Measurable (fun x : ℝ => ((1 - cutoff (x / R) : ℝ) : ℂ))
    simpa only [Function.comp_def] using
      (Complex.measurable_ofReal.comp hc.measurable)
  have hgMeas : Measurable g := by
    dsimp [g]
    exact (hChiMeas.comp (measurable_id.div_const ell)).mul hz
  have hgNorm (u : ℝ) : ‖g u‖ ≤ ‖z u‖ := by
    dsimp [g]
    calc
      _ = ‖chi (u / ell)‖ * ‖z u‖ := norm_mul _ _
      _ ≤ 1 * ‖z u‖ :=
        mul_le_mul_of_nonneg_right (hChi _) (norm_nonneg _)
      _ = ‖z u‖ := one_mul _
  have hgAmp (u : ℝ) (hu : 0 < u) : ‖g u‖ ≤ B :=
    (hgNorm u).trans (hzAmp u hu)
  have hgQuartic (u : ℝ) (hu : 0 < u) :
      ‖g u‖ ^ 4 ≤ D * bubble u ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (hgNorm u) 4).trans
      (hzQuartic u hu)
  have hScaledPos : 0 < ell * r := mul_pos hell hr
  have hZPotential :
      |radialHartreePotential (fun u => ‖z u‖ ^ 4) (ell * r)| ≤
        radialHartreeRowBoundConstant * D := by
    have hb : ∀ u : ℝ, 0 < u →
        |‖z u‖ ^ 4| ≤ D * bubble u ^ 2 := by
      intro u hu
      rw [abs_of_nonneg (by positivity)]
      exact hzQuartic u hu
    exact (radialHartreePotential_bubble_sq_domination
      (fun u => ‖z u‖ ^ 4)
      (hz.norm.pow_const 4) hD hb hScaledPos).2
  have hGPotential :
      |radialHartreePotential (fun u => ‖g u‖ ^ 4) (ell * r)| ≤
        radialHartreeRowBoundConstant * D := by
    have hb : ∀ u : ℝ, 0 < u →
        |‖g u‖ ^ 4| ≤ D * bubble u ^ 2 := by
      intro u hu
      rw [abs_of_nonneg (by positivity)]
      exact hgQuartic u hu
    exact (radialHartreePotential_bubble_sq_domination
      (fun u => ‖g u‖ ^ 4)
      (hgMeas.norm.pow_const 4) hD hb hScaledPos).2
  have hScaledZPotential :
      |radialHartreePotential
        (fun u => ‖rescalePhysicalRadiation ell z u‖ ^ 4) r| ≤
        ell * (radialHartreeRowBoundConstant * D) := by
    rw [actual_Hartree_critical_radiation_Riesz_scaling ell r hell z,
      abs_mul, abs_of_pos hell]
    exact mul_le_mul_of_nonneg_left hZPotential hell.le
  have hScaledGPotential :
      |radialHartreePotential
        (fun u => ‖rescalePhysicalRadiation ell g u‖ ^ 4) r| ≤
        ell * (radialHartreeRowBoundConstant * D) := by
    rw [actual_Hartree_critical_radiation_Riesz_scaling ell r hell g,
      abs_mul, abs_of_pos hell]
    exact mul_le_mul_of_nonneg_left hGPotential hell.le
  have hCutScale (x : ℝ) :
      chi x * rescalePhysicalRadiation ell z x =
        rescalePhysicalRadiation ell g x := by
    change chi x * ((Real.sqrt ell : ℂ) * z (ell * x)) =
      (Real.sqrt ell : ℂ) * (chi (ell * x / ell) * z (ell * x))
    have heq : ell * x / ell = x := by field_simp [hell.ne']
    rw [heq]
    ring
  have hCutPotential :
      |radialHartreePotential
        (fun u => ‖chi u * rescalePhysicalRadiation ell z u‖ ^ 4) r| ≤
        ell * (radialHartreeRowBoundConstant * D) := by
    have hfun :
        (fun u => ‖chi u * rescalePhysicalRadiation ell z u‖ ^ 4) =
        (fun u => ‖rescalePhysicalRadiation ell g u‖ ^ 4) := by
      funext u
      rw [hCutScale u]
    rw [hfun]
    exact hScaledGPotential
  have hAmpScaledSq :
      ‖rescalePhysicalRadiation ell z r‖ ^ 2 ≤ ell * B ^ 2 := by
    have hSq :
        ‖rescalePhysicalRadiation ell z r‖ ^ 2 =
          ell * ‖z (ell * r)‖ ^ 2 := by
      unfold rescalePhysicalRadiation
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg ell), mul_pow,
        Real.sq_sqrt hell.le]
    rw [hSq]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hzAmp (ell * r) hScaledPos) 2)
      hell.le
  have hSqrt : Real.sqrt ell ≤ 1 := by
    simpa only [Real.sqrt_one] using (Real.sqrt_le_sqrt hellSmall)
  have hAmpScaled :
      ‖rescalePhysicalRadiation ell z r‖ ≤ B := by
    have hn :
        ‖rescalePhysicalRadiation ell z r‖ =
          Real.sqrt ell * ‖z (ell * r)‖ := by
      unfold rescalePhysicalRadiation
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg ell)]
    calc
      _ = Real.sqrt ell * ‖z (ell * r)‖ := hn
      _ ≤ Real.sqrt ell * B :=
        mul_le_mul_of_nonneg_left (hzAmp (ell * r) hScaledPos)
          (Real.sqrt_nonneg ell)
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right hSqrt hB
      _ = B := one_mul _
  have hP : 0 ≤ ell * (radialHartreeRowBoundConstant * D) :=
    mul_nonneg hell.le (mul_nonneg radialHartreeRowBoundConstant_pos.le hD)
  have hQ : 0 ≤ ell * B ^ 2 := by positivity
  have hComm := radial_Hartree_nonlinear_cutoff_commutator_le
    chi (rescalePhysicalRadiation ell z) r
    (ell * (radialHartreeRowBoundConstant * D))
    (ell * B ^ 2) B
    hP hQ (hChi r) hScaledZPotential hCutPotential
    hAmpScaledSq hAmpScaled
  change
      ‖complexRadialHartreeNonlinearity
          (fun x => chi x * rescalePhysicalRadiation ell z x) r -
        chi r *
          complexRadialHartreeNonlinearity
            (rescalePhysicalRadiation ell z) r‖ ≤
      2 * radialHartreeRowBoundConstant * D * B ^ 3 * ell ^ 2
  calc
    _ ≤ 2 * (ell * (radialHartreeRowBoundConstant * D)) *
          (ell * B ^ 2) * B := hComm
    _ = 2 * radialHartreeRowBoundConstant * D * B ^ 3 * ell ^ 2 := by ring

end HBL.TypeIIDynamicSelection
