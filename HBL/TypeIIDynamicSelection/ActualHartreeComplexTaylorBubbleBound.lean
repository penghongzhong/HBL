import HBL.TypeIIDynamicSelection.ActualHartreeComplexTaylor
import HBL.RadialHartreeBubbleExact

/-!
Quadratic Taylor control for the actual nonlocal Hartree operator at
an arbitrary complex background. Both background and perturbation use
the displayed bubble envelope. The perturbation may have a 1/r tail:
unweighted L2 membership is not assumed. All Riesz rows are shown to
converge and every nonlinear nonlocal contribution is retained.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualHartreeComplexLinearization (U h : ℝ → ℂ) (r : ℝ) : ℂ :=
  (radialHartreePotential (fun rho => ‖U rho‖ ^ 4) r : ℂ) *
      actualHartreeComplexCubicLinear (U r) (h r) +
    (radialHartreePotential
      (fun rho => actualHartreeComplexDensityLinear (U rho) (h rho)) r : ℂ) *
      actualHartreeComplexCubic (U r)

/-- This is the difference of the actual nonlinear operator and its
actual first-order term, not a supplied remainder estimate. -/
def actualHartreeComplexTaylorRemainder (U h : ℝ → ℂ) (r : ℝ) : ℂ :=
  complexRadialHartreeNonlinearity (fun rho => U rho + h rho) r -
    complexRadialHartreeNonlinearity U r -
    actualHartreeComplexLinearization U h r

/-- Domination by W^4 uses the exact original Hartree row and retains
its spatial factor W(r)^2. -/
theorem actual_Hartree_bubble_four_potential_domination
    (F : ℝ → ℝ) (hF : Measurable F) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ rho : ℝ, 0 < rho → |F rho| ≤ A * bubble rho ^ 4)
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun rho => rho * hartreeRadialLog r rho * F rho) (Ioi 0) ∧
      |radialHartreePotential F r| ≤ 3 * A * bubble r ^ 2 := by
  have hrow := radialHartreeBubble_four_integrable hr
  have hlog : Measurable (hartreeRadialLog r) := by
    unfold hartreeRadialLog
    fun_prop
  have hmeas := (measurable_id.mul hlog).mul hF
  have hpoint : ∀ rho ∈ Ioi (0 : ℝ),
      |rho * hartreeRadialLog r rho * F rho| ≤
        A * (rho * hartreeRadialLog r rho * bubble rho ^ 4) := by
    intro rho hrho
    have hl := hartreeRadialLog_nonneg r rho hr hrho
    rw [abs_mul, abs_mul, abs_of_pos hrho, abs_of_nonneg hl]
    calc
      _ ≤ rho * hartreeRadialLog r rho * (A * bubble rho ^ 4) :=
        mul_le_mul_of_nonneg_left (hbound rho hrho) (mul_nonneg hrho.le hl)
      _ = _ := by ring
  have hi : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho * F rho) (Ioi 0) := by
    apply (hrow.const_mul A).mono' hmeas.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    rw [Real.norm_eq_abs]
    exact hpoint rho hrho
  have hInt : |∫ rho in Ioi (0 : ℝ), rho * hartreeRadialLog r rho * F rho| ≤
      A * ∫ rho in Ioi (0 : ℝ), rho * hartreeRadialLog r rho * bubble rho ^ 4 := by
    calc
      _ ≤ ∫ rho in Ioi (0 : ℝ), |rho * hartreeRadialLog r rho * F rho| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ rho in Ioi (0 : ℝ),
          A * (rho * hartreeRadialLog r rho * bubble rho ^ 4) := by
        apply integral_mono_ae hi.abs (hrow.const_mul A)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
        exact hpoint rho hrho
      _ = _ := by rw [integral_const_mul]
  have hc : 0 ≤ 2 * Real.pi * hartreeKappa / r := by
    unfold hartreeKappa
    positivity
  refine ⟨hi, ?_⟩
  calc
    |radialHartreePotential F r| =
        (2 * Real.pi * hartreeKappa / r) *
          |∫ rho in Ioi (0 : ℝ), rho * hartreeRadialLog r rho * F rho| := by
      rw [radialHartreePotential, abs_mul, abs_of_nonneg hc]
    _ ≤ (2 * Real.pi * hartreeKappa / r) *
        (A * ∫ rho in Ioi (0 : ℝ),
          rho * hartreeRadialLog r rho * bubble rho ^ 4) :=
      mul_le_mul_of_nonneg_left hInt hc
    _ = A * radialHartreePotential (fun rho => bubble rho ^ 4) r := by
      unfold radialHartreePotential
      ring
    _ = 3 * A * bubble r ^ 2 := by
      rw [radialHartreePotential_bubble_four hr]
      ring

/-- Exact nonlocal expansion. All three independent row integrability
conditions remain explicit here; the final bound derives them below. -/
theorem actual_Hartree_complex_Taylor_nonlocal_identity
    (U h : ℝ → ℂ) (r : ℝ)
    (h0 : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho * ‖U rho‖ ^ 4) (Ioi 0))
    (h1 : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        actualHartreeComplexDensityLinear (U rho) (h rho)) (Ioi 0))
    (hR : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        actualHartreeComplexDensityRemainder (U rho) (h rho)) (Ioi 0)) :
    actualHartreeComplexTaylorRemainder U h r =
      (radialHartreePotential (fun rho => ‖U rho‖ ^ 4) r : ℂ) *
        actualHartreeComplexCubicRemainder (U r) (h r) +
      (radialHartreePotential
        (fun rho => actualHartreeComplexDensityLinear (U rho) (h rho)) r : ℂ) *
        (actualHartreeComplexCubicLinear (U r) (h r) +
          actualHartreeComplexCubicRemainder (U r) (h r)) +
      (radialHartreePotential
        (fun rho => actualHartreeComplexDensityRemainder (U rho) (h rho)) r : ℂ) *
        (actualHartreeComplexCubic (U r) +
          actualHartreeComplexCubicLinear (U r) (h r) +
          actualHartreeComplexCubicRemainder (U r) (h r)) := by
  have hp : radialHartreePotential (fun rho => ‖U rho + h rho‖ ^ 4) r =
      radialHartreePotential (fun rho => ‖U rho‖ ^ 4) r +
      radialHartreePotential
        (fun rho => actualHartreeComplexDensityLinear (U rho) (h rho)) r +
      radialHartreePotential
        (fun rho => actualHartreeComplexDensityRemainder (U rho) (h rho)) r := by
    have hi : (∫ rho in Ioi (0 : ℝ),
        rho * hartreeRadialLog r rho * ‖U rho + h rho‖ ^ 4) =
        ((∫ rho in Ioi (0 : ℝ), rho * hartreeRadialLog r rho * ‖U rho‖ ^ 4) +
        (∫ rho in Ioi (0 : ℝ), rho * hartreeRadialLog r rho *
          actualHartreeComplexDensityLinear (U rho) (h rho))) +
        (∫ rho in Ioi (0 : ℝ), rho * hartreeRadialLog r rho *
          actualHartreeComplexDensityRemainder (U rho) (h rho)) := by
      calc
        _ = ∫ rho in Ioi (0 : ℝ),
            ((rho * hartreeRadialLog r rho * ‖U rho‖ ^ 4) +
              (rho * hartreeRadialLog r rho *
                actualHartreeComplexDensityLinear (U rho) (h rho))) +
              (rho * hartreeRadialLog r rho *
                actualHartreeComplexDensityRemainder (U rho) (h rho)) := by
          apply integral_congr_ae
          filter_upwards with rho
          rw [(actual_Hartree_complex_Taylor_polynomial_identity (U rho) (h rho)).1]
          ring
        _ = _ := by
          rw [integral_add (h0.add h1) hR, integral_add h0 h1]
    unfold radialHartreePotential
    rw [hi]
    ring
  have hN (v : ℝ → ℂ) : complexRadialHartreeNonlinearity v r =
      (radialHartreePotential (fun rho => ‖v rho‖ ^ 4) r : ℂ) *
        actualHartreeComplexCubic (v r) := by
    unfold complexRadialHartreeNonlinearity actualHartreeComplexCubic
    ring
  unfold actualHartreeComplexTaylorRemainder
  rw [hN, hN, hp,
    (actual_Hartree_complex_Taylor_polynomial_identity (U r) (h r)).2]
  unfold actualHartreeComplexLinearization
  push_cast
  ring

private theorem three_product_bound (P0 P1 PR c0 c1 cr : ℂ)
    {A0 A1 AR B0 B1 BR : ℝ}
    (hp0 : ‖P0‖ ≤ A0) (hp1 : ‖P1‖ ≤ A1) (hpR : ‖PR‖ ≤ AR)
    (hc0 : ‖c0‖ ≤ B0) (hc1 : ‖c1‖ ≤ B1) (hcr : ‖cr‖ ≤ BR) :
    ‖P0 * cr + P1 * (c1 + cr) + PR * (c0 + c1 + cr)‖ ≤
      A0 * BR + A1 * (B1 + BR) + AR * (B0 + B1 + BR) := by
  have h1 := (norm_add_le c1 cr).trans (add_le_add hc1 hcr)
  have h0 := (norm_add_le (c0 + c1) cr).trans
    (add_le_add ((norm_add_le c0 c1).trans (add_le_add hc0 hc1)) hcr)
  calc
    _ ≤ (‖P0 * cr‖ + ‖P1 * (c1 + cr)‖) + ‖PR * (c0 + c1 + cr)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (‖P0‖ * ‖cr‖ + ‖P1‖ * ‖c1 + cr‖) + ‖PR‖ * ‖c0 + c1 + cr‖ := by
      simp only [norm_mul]
    _ ≤ _ := add_le_add
      (add_le_add (mul_le_mul hp0 hcr (norm_nonneg _) ((norm_nonneg P0).trans hp0))
        (mul_le_mul hp1 h1 (norm_nonneg _) ((norm_nonneg P1).trans hp1)))
      (mul_le_mul hpR h0 (norm_nonneg _) ((norm_nonneg PR).trans hpR))

/-- A quadratic estimate for the original seventh-order nonlocal operator.
The constants M,e are the displayed envelope amplitudes, so cutoff-radius
losses in producing those amplitudes cannot be hidden in this theorem. -/
theorem actual_Hartree_complex_Taylor_bubble_bound
    (U h : ℝ → ℂ) (hU : Measurable U) (hh : Measurable h)
    (M e : ℝ) (hM : 0 ≤ M) (he : 0 ≤ e)
    (hUB : ∀ rho : ℝ, 0 < rho → ‖U rho‖ ≤ M * bubble rho)
    (hhB : ∀ rho : ℝ, 0 < rho → ‖h rho‖ ≤ e * bubble rho)
    (r : ℝ) (hr : 0 < r) :
    ‖actualHartreeComplexTaylorRemainder U h r‖ ≤
      63 * (M + e) ^ 5 * e ^ 2 * bubble r ^ 5 := by
  let D : ℝ := 6 * M ^ 2 * e ^ 2 + 4 * M * e ^ 3 + e ^ 4
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hW (rho : ℝ) : 0 ≤ bubble rho := by unfold bubble; positivity
  have hpoly (rho : ℝ) (hrho : 0 < rho) :=
    actual_Hartree_complex_Taylor_polynomial_bounds (U rho) (h rho)
      (mul_nonneg hM (hW rho)) (mul_nonneg he (hW rho))
      (hUB rho hrho) (hhB rho hrho)
  have hb0 (rho : ℝ) (hrho : 0 < rho) :
      |‖U rho‖ ^ 4| ≤ M ^ 4 * bubble rho ^ 4 := by
    rw [abs_of_nonneg (by positivity)]
    simpa only [mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (hUB rho hrho) 4
  have hb1 (rho : ℝ) (hrho : 0 < rho) :
      |actualHartreeComplexDensityLinear (U rho) (h rho)| ≤
        (4 * M ^ 3 * e) * bubble rho ^ 4 := by
    calc
      _ ≤ 4 * (M * bubble rho) ^ 3 * (e * bubble rho) := (hpoly rho hrho).1
      _ = _ := by ring
  have hbR (rho : ℝ) (hrho : 0 < rho) :
      |actualHartreeComplexDensityRemainder (U rho) (h rho)| ≤
        D * bubble rho ^ 4 := by
    calc
      _ ≤ 6 * (M * bubble rho) ^ 2 * (e * bubble rho) ^ 2 +
          4 * (M * bubble rho) * (e * bubble rho) ^ 3 + (e * bubble rho) ^ 4 :=
        (hpoly rho hrho).2.1
      _ = _ := by dsimp [D]; ring
  have hm1 : Measurable
      (fun rho => actualHartreeComplexDensityLinear (U rho) (h rho)) := by
    unfold actualHartreeComplexDensityLinear actualHartreeComplexRealPair
    fun_prop
  have hmR : Measurable
      (fun rho => actualHartreeComplexDensityRemainder (U rho) (h rho)) := by
    unfold actualHartreeComplexDensityRemainder actualHartreeComplexRealPair
    fun_prop
  have hp0 := actual_Hartree_bubble_four_potential_domination
    (fun rho => ‖U rho‖ ^ 4) (hU.norm.pow_const 4) (by positivity) hb0 hr
  have hp1 := actual_Hartree_bubble_four_potential_domination
    (fun rho => actualHartreeComplexDensityLinear (U rho) (h rho))
      hm1 (by positivity) hb1 hr
  have hpR := actual_Hartree_bubble_four_potential_domination
    (fun rho => actualHartreeComplexDensityRemainder (U rho) (h rho))
      hmR hD hbR hr
  have hc0 : ‖actualHartreeComplexCubic (U r)‖ ≤ M ^ 3 * bubble r ^ 3 := by
    simpa only [mul_pow] using (hpoly r hr).2.2.1
  have hc1 : ‖actualHartreeComplexCubicLinear (U r) (h r)‖ ≤
      (3 * M ^ 2 * e) * bubble r ^ 3 := by
    calc
      _ ≤ 3 * (M * bubble r) ^ 2 * (e * bubble r) := (hpoly r hr).2.2.2.1
      _ = _ := by ring
  have hcR : ‖actualHartreeComplexCubicRemainder (U r) (h r)‖ ≤
      (3 * M * e ^ 2 + e ^ 3) * bubble r ^ 3 := by
    calc
      _ ≤ (3 * (M * bubble r) + e * bubble r) * (e * bubble r) ^ 2 :=
        (hpoly r hr).2.2.2.2
      _ = _ := by ring
  have hP0 : ‖(radialHartreePotential (fun rho => ‖U rho‖ ^ 4) r : ℂ)‖ ≤
      3 * M ^ 4 * bubble r ^ 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hp0.2
  have hP1 : ‖(radialHartreePotential
      (fun rho => actualHartreeComplexDensityLinear (U rho) (h rho)) r : ℂ)‖ ≤
      3 * (4 * M ^ 3 * e) * bubble r ^ 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hp1.2
  have hPR : ‖(radialHartreePotential
      (fun rho => actualHartreeComplexDensityRemainder (U rho) (h rho)) r : ℂ)‖ ≤
      3 * D * bubble r ^ 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hpR.2
  have hB := three_product_bound _ _ _ _ _ _ hP0 hP1 hPR hc0 hc1 hcR
  rw [actual_Hartree_complex_Taylor_nonlocal_identity U h r hp0.1 hp1.1 hpR.1]
  have hcoef : 21 * M ^ 5 + 35 * M ^ 4 * e + 35 * M ^ 3 * e ^ 2 +
      21 * M ^ 2 * e ^ 3 + 7 * M * e ^ 4 + e ^ 5 ≤ 21 * (M + e) ^ 5 := by
    have hpos : 0 ≤ 70 * M ^ 4 * e + 175 * M ^ 3 * e ^ 2 +
        189 * M ^ 2 * e ^ 3 + 98 * M * e ^ 4 + 20 * e ^ 5 := by positivity
    nlinarith only [hpos]
  calc
    _ ≤ (3 * M ^ 4 * bubble r ^ 2) *
          ((3 * M * e ^ 2 + e ^ 3) * bubble r ^ 3) +
        (3 * (4 * M ^ 3 * e) * bubble r ^ 2) *
          ((3 * M ^ 2 * e) * bubble r ^ 3 +
            (3 * M * e ^ 2 + e ^ 3) * bubble r ^ 3) +
        (3 * D * bubble r ^ 2) *
          (M ^ 3 * bubble r ^ 3 + (3 * M ^ 2 * e) * bubble r ^ 3 +
            (3 * M * e ^ 2 + e ^ 3) * bubble r ^ 3) := hB
    _ = 3 * (21 * M ^ 5 + 35 * M ^ 4 * e + 35 * M ^ 3 * e ^ 2 +
          21 * M ^ 2 * e ^ 3 + 7 * M * e ^ 4 + e ^ 5) * e ^ 2 * bubble r ^ 5 := by
      dsimp [D]
      ring
    _ ≤ 3 * (21 * (M + e) ^ 5) * e ^ 2 * bubble r ^ 5 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoef (by norm_num)) (sq_nonneg e))
        (pow_nonneg (hW r) 5)
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
