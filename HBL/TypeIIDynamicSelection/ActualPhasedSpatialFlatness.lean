import HBL.TypeIIDynamicSelection.ActualRadiationSpatialFlatness
import HBL.TypeIIDynamicSelection.ActualOneOrbitTerminalRadiation
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

/-!
# Original HBL radiation flat source with the true phase and center cutoff

The manuscript's regular radiation is decomposed into its nontrivial
complex center jet j(t)=z(t,0) and spatial remainder
z^flat(t,r)=z(t,r)-j(t)χ(r), χ=1 on the physical core r<=1.

Unlike the older terminal-support argument, neither z(t,r) nor
z^flat(t,r) is assumed compactly supported for t<T. The actual
energy-critical rescaling and full complex phase are included.

Two applications of the actual C² radial mean-value lemma show
‖e^(-i gamma) sqrt(ell) z^flat(t,ell R)‖
<= M ell² sqrt(ell) R²
on the moving core ell R<=1. This is the literal source factor
in manuscript eq:flat-core-stage3; no Type II blowup rate is assumed.

The fixed physical C² bound and regular-origin slope are visible
high-regularity Hartree flow obligations. Genuine H±, Kummer and
remote source matching, and all time derivatives, are still missing
from the full original one-layer proposition 2.12.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The original radial cutoff χ equals one on [0,1] and zero
for r>=2. It is a physical-space cutoff, not support persistence
for the Hartree flow. -/
def actualHartreeFlatCenterCutoff (r : ℝ) : ℝ :=
  1 - cutoff r

theorem actual_Hartree_flat_center_cutoff_one
    (r : ℝ) (hr : r ≤ 1) :
    actualHartreeFlatCenterCutoff r = 1 := by
  have hcut : cutoff r = 0 := cutoff_zero_of_le_one r hr
  simp [actualHartreeFlatCenterCutoff, hcut]

/-- Genuine time-dependent spatially flat remainder: subtract only
the centered jet times a smooth physical cutoff. -/
def actualHartreeFlatRadiation (z : ℝ → ℂ) (r : ℝ) : ℂ :=
  z r - ((actualHartreeFlatCenterCutoff r : ℝ) : ℂ) * z 0

theorem actual_Hartree_flat_radiation_core_eq
    (z : ℝ → ℂ) (r : ℝ) (hr : r ≤ 1) :
    actualHartreeFlatRadiation z r = z r - z 0 := by
  rw [actualHartreeFlatRadiation,
    actual_Hartree_flat_center_cutoff_one r hr]
  simp

/-- The real Hartree phase is unitary; its exact complex norm is one. -/
theorem actual_Hartree_unit_complex_phase (gamma : ℝ) :
    ‖Complex.exp (Complex.I * ((-gamma : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hreal : (Complex.I * ((-gamma : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  rw [hreal, Real.exp_zero]

/-- The original phased critical-scaling remainder in bubble variables. -/
def actualPhasedHartreeFlatRadiation
    (z : ℝ → ℂ) (ell gamma R : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((-gamma : ℝ) : ℂ)) *
    rescalePhysicalRadiation ell (actualHartreeFlatRadiation z) R

/-- The true decomposition, on the actual physical core, agrees
exactly with the centered spatial difference used in the MVT
proof. This identity keeps both the radial cutoff and complex phase. -/
theorem actual_phased_Hartree_flat_radiation_core_eq
    (z : ℝ → ℂ) (ell gamma R : ℝ) (hCore : ell * R ≤ 1) :
    actualPhasedHartreeFlatRadiation z ell gamma R =
      Complex.exp (Complex.I * ((-gamma : ℝ) : ℂ)) *
        rescalePhysicalRadiation ell (fun r => z r - z 0) R := by
  unfold actualPhasedHartreeFlatRadiation
  congr 1
  unfold rescalePhysicalRadiation
  rw [actual_Hartree_flat_radiation_core_eq z (ell * R) hCore]

/-- Original manuscript spatial-flatness source estimate with the
ACTUAL phase and centered cutoff, derived by real-space radial C²
Taylor bounds and the critical Hartree pullback. -/
theorem actual_phased_Hartree_radial_spatial_flatness
    (z zr zrr : ℝ → ℝ → ℂ)
    (time ell gamma R M : ℝ)
    (hell : 0 < ell) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hCore : ell * R ≤ 1)
    (hFlow : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivAt (z time) (zr time x) x)
    (hFlowR : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivAt (zr time) (zrr time x) x)
    (hRegBound : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖zrr time x‖ ≤ M)
    (hRegularOrigin : zr time 0 = 0) :
    ‖actualPhasedHartreeFlatRadiation (z time) ell gamma R‖ ≤
      (M * ell ^ 2 * Real.sqrt ell) * R ^ 2 := by
  rw [actual_phased_Hartree_flat_radiation_core_eq
    (z time) ell gamma R hCore, norm_mul,
    actual_Hartree_unit_complex_phase, one_mul]
  exact actual_Hartree_rescaled_radial_spatial_flatness
    z zr zrr time ell R M hell hR hM hCore
    hFlow hFlowR hRegBound hRegularOrigin

end HBL.TypeIIDynamicSelection
