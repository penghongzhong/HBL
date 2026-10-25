import HBL.AffineTailMinusZeroMode
import HBL.RadialDotH1Model
import HBL.RadialEnergyHilbertBridge

/-!
Repair branch: retain, rather than eliminate, the zero--centre coupling.

For the actual unbounded half-line phase differential operator Hminus,
a compact test zeta yields an energy-bounded coupling. Two integrations
by parts move the derivatives onto zeta. Its primitive then gives the
actual full-half-line L2 Riesz functional. No generator inverse, invariant
zero projection, or Sobolev-completion identification is postulated.

The theorem below certifies a genuine local block needed by a triangular
Hamilton system. It does NOT certify the nonlocal real-channel block,
the Hamilton evolution group, or the original manuscript Proposition 3.1.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace HBL.Modulation.TriangularRepair

open HBL.Modulation.AffineTail

private theorem potential_continuous : Continuous potential := by
  unfold potential
  apply Continuous.div continuous_const (by fun_prop)
  intro r
  positivity

private theorem phaseAppliedTest_continuous
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 2 zeta) :
    Continuous (hMinusApply zeta) := by
  have hd : ContDiff ℝ 1 (deriv zeta) := hzeta.deriv'
  exact hd.continuous_deriv_one.neg.sub
    (potential_continuous.mul hzeta.continuous)

/-- The coupling is a constructed continuous linear functional on the
full half-line energy coordinate q=(r f)', not a boundedness assumption. -/
def phaseThresholdCoupling (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 2 zeta) :
    FullRadialEnergyL2 →L[ℝ] ℝ :=
  (energyThresholdDual R hR (hMinusApply zeta)
    (phaseAppliedTest_continuous zeta hzeta)).comp
      (fullToFiniteRadialEnergy R)

private theorem actual_phase_green_identity
    (R : ℝ) (zeta f : ℝ → ℝ)
    (hzeta : ContDiff ℝ 2 zeta) (hf : ContDiff ℝ 2 f)
    (hz0 : zeta 0 = 0) (hzR : zeta R = 0)
    (hdzR : deriv zeta R = 0) :
    (∫ r in (0 : ℝ)..R, zeta r * hMinusApply (radialU f) r) =
      ∫ r in (0 : ℝ)..R, hMinusApply zeta r * radialU f r := by
  have hu : ContDiff ℝ 2 (radialU f) := contDiff_id.mul hf
  have hdz : ContDiff ℝ 1 (deriv zeta) := hzeta.deriv'
  have hdu : ContDiff ℝ 1 (deriv (radialU f)) := hu.deriv'
  have hleft : Continuous
      (fun r => zeta r * hMinusApply (radialU f) r) :=
    hzeta.continuous.mul (phaseAppliedTest_continuous (radialU f) hu)
  have hright : Continuous
      (fun r => hMinusApply zeta r * radialU f r) :=
    (phaseAppliedTest_continuous zeta hzeta).mul hu.continuous
  have hLi := hleft.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := R)
  have hRi := hright.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := R)
  have hG := green_localSchrodinger 0 R potential
    zeta (deriv zeta) (deriv (deriv zeta))
    (radialU f) (deriv (radialU f)) (deriv (deriv (radialU f)))
    (fun r => (hzeta.differentiable (by norm_num) r).hasDerivAt)
    (fun r => (hdz.differentiable (by norm_num) r).hasDerivAt)
    (fun r => (hu.differentiable (by norm_num) r).hasDerivAt)
    (fun r => (hdu.differentiable (by norm_num) r).hasDerivAt)
    (hLi.sub hRi)
  change (∫ r in (0 : ℝ)..R,
    zeta r * hMinusApply (radialU f) r -
      hMinusApply zeta r * radialU f r) = _ at hG
  rw [intervalIntegral.integral_sub hLi hRi] at hG
  have hboundary :
      greenBoundary zeta (deriv zeta) (radialU f) (deriv (radialU f)) R -
      greenBoundary zeta (deriv zeta) (radialU f) (deriv (radialU f)) 0 = 0 := by
    simp [greenBoundary, hz0, hzR, hdzR, radialU]
  rw [hboundary] at hG
  exact sub_eq_zero.mp hG

private theorem actual_phase_coupling_identity
    (R : ℝ) (hR : 0 ≤ R) (zeta f : ℝ → ℝ)
    (hzeta : ContDiff ℝ 2 zeta) (hf : ContDiff ℝ 2 f)
    (hz0 : zeta 0 = 0) (hzR : zeta R = 0)
    (hdzR : deriv zeta R = 0)
    (hmem : MemLp (deriv (radialU f)) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    (∫ r in (0 : ℝ)..R, zeta r * hMinusApply (radialU f) r) =
      phaseThresholdCoupling R hR zeta hzeta (smoothToRadialDotH1 f hmem) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  rw [actual_phase_green_identity R zeta f hzeta hf hz0 hzR hdzR]
  change _ = energyThresholdDual R hR (hMinusApply zeta)
    (phaseAppliedTest_continuous zeta hzeta)
    (fullToFiniteRadialEnergy R (smoothToRadialDotH1 f hmem))
  rw [smoothToRadialDotH1_restrict R hR f hf1 hmem,
    energyThresholdDual_on_radialCore]

private theorem bubble_contDiff_two : ContDiff ℝ 2 bubble := by
  have h : ContDiff ℝ 2 (fun r : ℝ => 1 + r ^ 2) := by fun_prop
  have hs := h.sqrt (fun r => (by positivity : (1 : ℝ) + r ^ 2 ≠ 0))
  exact hs.inv (fun r => ne_of_gt (Real.sqrt_pos.mpr (by positivity)))

/-- Complete actual local coupling statement: exact action of Hminus on
smooth finite-energy profiles, energy bound, two-input Lipschitz estimate,
and annihilation of the physical phase zero mode. In particular the
coupling survives, but factors through the quotient by the phase bubble. -/
theorem phaseThresholdCoupling_certified
    (R : ℝ) (hR : 0 ≤ R) (zeta : ℝ → ℝ)
    (hzeta : ContDiff ℝ 2 zeta)
    (hz0 : zeta 0 = 0) (hzR : zeta R = 0)
    (hdzR : deriv zeta R = 0) :
    (∀ (f : ℝ → ℝ) (_hf : ContDiff ℝ 2 f)
      (hmem : MemLp (deriv (radialU f)) 2 (volume.restrict (Ioi (0 : ℝ)))),
      (∫ r in (0 : ℝ)..R, zeta r * hMinusApply (radialU f) r) =
        phaseThresholdCoupling R hR zeta hzeta (smoothToRadialDotH1 f hmem)) ∧
    (∀ q : FullRadialEnergyL2,
      |phaseThresholdCoupling R hR zeta hzeta q| ≤
        ‖phaseThresholdCoupling R hR zeta hzeta‖ * ‖q‖) ∧
    (∀ q p : FullRadialEnergyL2,
      |phaseThresholdCoupling R hR zeta hzeta q -
        phaseThresholdCoupling R hR zeta hzeta p| ≤
        ‖phaseThresholdCoupling R hR zeta hzeta‖ * ‖q - p‖) ∧
    phaseThresholdCoupling R hR zeta hzeta fullBubbleRadialEnergyL2 = 0 ∧
    (∀ (q : FullRadialEnergyL2) (c : ℝ),
      phaseThresholdCoupling R hR zeta hzeta (q + c • fullBubbleRadialEnergyL2) =
        phaseThresholdCoupling R hR zeta hzeta q) := by
  have hzero : phaseThresholdCoupling R hR zeta hzeta fullBubbleRadialEnergyL2 = 0 := by
    have h := actual_phase_coupling_identity R hR zeta bubble hzeta
      bubble_contDiff_two hz0 hzR hdzR radialU_bubble_deriv_memLp
    rw [smoothBubbleToRadialDotH1_eq] at h
    have hpoint (r : ℝ) : hMinusApply (radialU bubble) r = 0 :=
      hMinus_resonanceMinus_zero r
    simpa only [hpoint, mul_zero, intervalIntegral.integral_zero] using h.symm
  refine ⟨?_, ?_, ?_, hzero, ?_⟩
  · intro f hf hmem
    exact actual_phase_coupling_identity R hR zeta f hzeta hf hz0 hzR hdzR hmem
  · intro q
    exact (phaseThresholdCoupling R hR zeta hzeta).le_opNorm q
  · intro q p
    rw [← map_sub]
    exact (phaseThresholdCoupling R hR zeta hzeta).le_opNorm (q - p)
  · intro q c
    rw [map_add, map_smul, hzero, smul_zero, add_zero]

end HBL.Modulation.TriangularRepair
