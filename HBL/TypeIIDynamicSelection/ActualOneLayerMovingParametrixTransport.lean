import HBL.TypeIIDynamicSelection.ActualOneLayerPDEResidual
import HBL.TypeIIDynamicSelection.ActualCutoffUniformTransport
import Mathlib.Tactic

/-!
# HBL manuscript 2.12: exact moving-cutoff parametrix rather than false C1 gluing

The normalized Kummer Green inverse has both Wronskian endpoint
normalizations, so no free homogeneous coefficients remain.  Rather
than postulating simultaneous inner/Kummer/remote boundary matching,
localize the genuine candidate with the ACTUAL moving cutoff

  chi(s,r) = 1 - cutoff(r/R(s)).

The SAME full nonlinear radial Hartree PDE has a material cutoff
commutator. Its time derivative and modulation dilation must be
combined, not estimated independently.  The exact coefficient is

  (r/R)*(R_s/R - b)*cutoff'(r/R).

The full residual has precisely this local transport term, the
genuine first/second radial cutoff derivatives R^(-1),R^(-2), and
the COMPLETE nonlocal Riesz nonlinear commutator.  All are
explicit, without an abstract regional solver or source-order input.

The actual derivative bound follows from the concrete smooth cutoff,
not an assumed new hypothesis.  The final original 2.12 gain still
requires actual offterminal field/derivative bounds, a modulation
estimate on R_s/R-b, and a full nonlocal commutator estimate.
This lemma does not claim original one-layer acceptance.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The *actual* moving cutoff's material velocity, after combining
the time derivative with the b*Lambda transport term. -/
def actualOneLayerMaterialCutoffCoefficient
    (radius radiusSpeed b r : ℝ) : ℝ :=
  (r / radius) * (radiusSpeed / radius - b) *
    deriv cutoff (r / radius)

/-- Real-valued algebra behind the exact Hartree moving overlap transport.
No decay order of the coefficient has been postulated. -/
theorem actual_one_layer_material_coefficient_exact
    (radius radiusSpeed b r : ℝ) (hRadius : radius ≠ 0) :
    deriv cutoff (r / radius) * (r * radiusSpeed / radius ^ 2) +
        b * r * (-deriv cutoff (r / radius) / radius) =
      actualOneLayerMaterialCutoffCoefficient radius radiusSpeed b r := by
  unfold actualOneLayerMaterialCutoffCoefficient
  field_simp [hRadius]
  ring

/-- Exact MATERIAL derivative of the original moving cutoff:
chi_s+b*r*chi_r. The separation of these two terms into
unrelated source atoms is invalid at the one-layer weight. -/
theorem actual_one_layer_material_cutoff_derivative_exact
    (R : ℝ → ℝ) (b : ℝ) {s r Rs : ℝ}
    (hR : HasDerivAt R Rs s) (hRne : R s ≠ 0) :
    deriv (fun t : ℝ => actualOneLayerInnerOverlapCutoff (R t) r) s +
      (b : ℂ) * (r : ℂ) *
        deriv (actualOneLayerInnerOverlapCutoff (R s)) r =
      (actualOneLayerMaterialCutoffCoefficient (R s) Rs b r : ℂ) := by
  rw [(actual_one_layer_moving_overlap_cutoff_hasDerivAt
        R hR hRne (r := r)).deriv,
      (actual_one_layer_overlap_cutoff_hasDerivAt (R s) r).deriv]
  have hre := actual_one_layer_material_coefficient_exact
    (R s) Rs b r hRne
  exact_mod_cast hre

/-- The FULL original renormalized Hartree PDE residual of an ACTUAL
moving-cutoff profile.  This is the parametrix source to estimate:
time/dilation transport combines exactly; the radial derivative
costs are literally R^(-1), R^(-2); and every quartic nonlocal
Riesz interaction remains visible, not replaced by a local cubic. -/
theorem actual_one_layer_moving_parametrix_true_Hartree_source
    (R : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (b omega : ℝ) {s r Rs : ℝ}
    (hR : HasDerivAt R Rs s) (hRne : R s ≠ 0)
    (hfTime : DifferentiableAt ℝ (fun t => f t r) s)
    (hfSpace : ∀ x : ℝ, DifferentiableAt ℝ (f s) x)
    (hf2 : DifferentiableAt ℝ (deriv (f s)) r) :
    complexRadialRenormalizedResidual
        (fun t x => actualOneLayerInnerOverlapCutoff (R t) x * f t x)
        b omega s r -
      actualOneLayerInnerOverlapCutoff (R s) r *
        complexRadialRenormalizedResidual f b omega s r =
      Complex.I *
          (actualOneLayerMaterialCutoffCoefficient (R s) Rs b r : ℂ) *
            f s r +
        2 * ((-deriv cutoff (r / R s) / R s : ℝ) : ℂ) *
          deriv (f s) r +
        (((-deriv (deriv cutoff) (r / R s) / (R s) ^ 2 : ℝ) : ℂ) +
          (2 / (r : ℂ)) *
            ((-deriv cutoff (r / R s) / R s : ℝ) : ℂ)) * f s r +
        (complexRadialHartreeNonlinearity
          (fun x => actualOneLayerInnerOverlapCutoff (R s) x * f s x) r -
          actualOneLayerInnerOverlapCutoff (R s) r *
            complexRadialHartreeNonlinearity (f s) r) := by
  have hFull := actual_one_layer_moving_cutoff_radial_Hartree_residual
    R f b omega hR hRne hfTime hfSpace hf2 (r := r)
  have hMaterial := actual_one_layer_material_cutoff_derivative_exact
    R b hR hRne (r := r)
  have htransport :
      Complex.I *
        ((deriv cutoff (r / R s) * (r * Rs / (R s) ^ 2) : ℝ) : ℂ) *
          f s r +
      Complex.I * (b : ℂ) * (r : ℂ) *
        ((-deriv cutoff (r / R s) / R s : ℝ) : ℂ) * f s r =
      Complex.I *
        (actualOneLayerMaterialCutoffCoefficient (R s) Rs b r : ℂ) *
          f s r := by
    have hc :
        ((deriv cutoff (r / R s) * (r * Rs / (R s) ^ 2) : ℝ) : ℂ) +
          (b : ℂ) * (r : ℂ) *
            ((-deriv cutoff (r / R s) / R s : ℝ) : ℂ) =
          (actualOneLayerMaterialCutoffCoefficient (R s) Rs b r : ℂ) := by
      exact_mod_cast (actual_one_layer_material_coefficient_exact
        (R s) Rs b r hRne)
    calc
      _ = Complex.I *
            (((deriv cutoff (r / R s) * (r * Rs / (R s) ^ 2) : ℝ) : ℂ) +
              (b : ℂ) * (r : ℂ) *
                ((-deriv cutoff (r / R s) / R s : ℝ) : ℂ)) *
              f s r := by ring
      _ = _ := by rw [hc]
  calc
    _ = Complex.I *
          ((deriv cutoff (r / R s) * (r * Rs / (R s) ^ 2) : ℝ) : ℂ) *
            f s r +
        2 * ((-deriv cutoff (r / R s) / R s : ℝ) : ℂ) *
          deriv (f s) r +
        (((-deriv (deriv cutoff) (r / R s) / (R s) ^ 2 : ℝ) : ℂ) +
          (2 / (r : ℂ)) *
            ((-deriv cutoff (r / R s) / R s : ℝ) : ℂ)) * f s r +
        Complex.I * (b : ℂ) * (r : ℂ) *
          ((-deriv cutoff (r / R s) / R s : ℝ) : ℂ) * f s r +
        (complexRadialHartreeNonlinearity
          (fun x => actualOneLayerInnerOverlapCutoff (R s) x * f s x) r -
          actualOneLayerInnerOverlapCutoff (R s) r *
            complexRadialHartreeNonlinearity (f s) r) := hFull
    _ = (Complex.I *
          ((deriv cutoff (r / R s) * (r * Rs / (R s) ^ 2) : ℝ) : ℂ) *
            f s r +
        Complex.I * (b : ℂ) * (r : ℂ) *
          ((-deriv cutoff (r / R s) / R s : ℝ) : ℂ) * f s r) +
        2 * ((-deriv cutoff (r / R s) / R s : ℝ) : ℂ) *
          deriv (f s) r +
        (((-deriv (deriv cutoff) (r / R s) / (R s) ^ 2 : ℝ) : ℂ) +
          (2 / (r : ℂ)) *
            ((-deriv cutoff (r / R s) / R s : ℝ) : ℂ)) * f s r +
        (complexRadialHartreeNonlinearity
          (fun x => actualOneLayerInnerOverlapCutoff (R s) x * f s x) r -
          actualOneLayerInnerOverlapCutoff (R s) r *
            complexRadialHartreeNonlinearity (f s) r) := by ring
    _ = _ := by rw [htransport]

/-- First quantitative result for the true transition shell, requiring
only the already PROVED global fixed-cutoff derivative bound. Unlike a
GeneratedTerm record, its coefficient is the actual PDE commutator. -/
theorem actual_one_layer_material_transport_shell_bound
    (radius radiusSpeed b r : ℝ)
    (hRadius : 0 < radius) (hrLeft : radius ≤ r)
    (hrRight : r ≤ 2 * radius) :
    ∃ Cχ : ℝ, 0 < Cχ ∧
      |actualOneLayerMaterialCutoffCoefficient radius radiusSpeed b r| ≤
        2 * Cχ * |radiusSpeed / radius - b| := by
  obtain ⟨Cχ,hCχ,hCut⟩ :=
    exists_actual_fixed_cutoff_uniform_deriv_bound
  have hrNonneg : 0 ≤ r / radius :=
    div_nonneg (le_trans hRadius.le hrLeft) hRadius.le
  have hrTwo : r / radius ≤ 2 := by
    apply (div_le_iff₀ hRadius).2
    linarith
  have hrEq :
      |actualOneLayerMaterialCutoffCoefficient radius radiusSpeed b r| =
        (r / radius) * |radiusSpeed / radius - b| *
          |deriv cutoff (r / radius)| := by
    unfold actualOneLayerMaterialCutoffCoefficient
    rw [abs_mul, abs_mul, abs_of_nonneg hrNonneg]
  refine ⟨Cχ,hCχ,?_⟩
  rw [hrEq]
  have hP : 0 ≤ |radiusSpeed / radius - b| := abs_nonneg _
  have hBound : (r / radius) * |radiusSpeed / radius - b| *
      |deriv cutoff (r / radius)| ≤
      (2 * |radiusSpeed / radius - b|) * Cχ := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hrTwo hP
    · exact hCut (r / radius)
    · exact abs_nonneg _
    · positivity
  calc
    _ ≤ (2 * |radiusSpeed / radius - b|) * Cχ := hBound
    _ = 2 * Cχ * |radiusSpeed / radius - b| := by ring

end HBL.TypeIIDynamicSelection
