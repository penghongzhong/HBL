import HBL.TypeIIDynamicSelection.ActualOriginGreenTransmission
import HBL.TypeIIDynamicSelection.ActualHartreeUniformInnerMoment
import Mathlib.Tactic

/-!
Actual canonical inner data -> repaired original origin-gauge inverse.
The left mismatch is computed from the SAME full physical Hartree source.
It is not a freely assumed small boundary datum. Both normalized Fredholm
equations remain in the statement. The coordinate change rho=a*r keeps the
slope factor a and source factor a^2. The added interface forcing is retained
and bounded, NOT declared zero or given an unproved extra order.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel HBL.Profile.Kummer

def actualHartreeTransmissionPlusSource (ell c : ℝ) (z : ℝ → ℂ) : ℝ → ℝ :=
  fun r => (actualHartreeRadiallyConjugatedInnerSource
    (actualHartreeSlowInnerRadius ell) ell c z r).re

def actualHartreeTransmissionMinusSource (ell c : ℝ) (z : ℝ → ℂ) : ℝ → ℝ :=
  fun r => (actualHartreeRadiallyConjugatedInnerSource
    (actualHartreeSlowInnerRadius ell) ell c z r).im

/-- Merely abbreviates the TWO original equations; it is not a solver axiom. -/
def ActualHartreeTransmissionInnerSolve (ell c : ℝ) (z : ℝ → ℂ)
    (hp : InWeightedL2 (7/4 : ℝ) (actualHartreeTransmissionPlusSource ell c z))
    (hm : InWeightedL2 (7/4 : ℝ) (actualHartreeTransmissionMinusSource ell c z))
    (x : InnerCorrections) : Prop :=
  (1-weightedBirmanSchwingerOperator) (x.1 : RealL2 halfLineMeasure) =
    weightedSourceGreenOperator (7/4 : ℝ) (by norm_num)
      (weightedSourceDataL2 (7/4 : ℝ)
        (correctedPlusSource (actualHartreeTransmissionPlusSource ell c z))
        (correctedPlusSource_memWeightedL2 (7/4 : ℝ) (by norm_num) _ hp)) ∧
  (1-weightedPhaseBirman) (x.2 : RealL2 halfLineMeasure) =
    weightedSourceGreenOperator (7/4 : ℝ) (by norm_num)
      (weightedSourceDataL2 (7/4 : ℝ)
        (correctedMinusSource (actualHartreeTransmissionMinusSource ell c z))
        (correctedMinusSource_memWeightedL2 (7/4 : ℝ) (by norm_num) _ hm))

def actualHartreeTransmissionInnerPlus (ell c : ℝ) (z : ℝ → ℂ)
    (x : InnerCorrections) (r : ℝ) : ℝ :=
  affineRestore (innerGreenRepresentative
    (weightedPotentialOperator (x.1 : RealL2 halfLineMeasure))
    (correctedPlusSource (actualHartreeTransmissionPlusSource ell c z)))
    (actualPlusCharge (actualHartreeTransmissionPlusSource ell c z)) r / r

def actualHartreeTransmissionInnerMinus (ell c : ℝ) (z : ℝ → ℂ)
    (x : InnerCorrections) (r : ℝ) : ℝ :=
  affineRestore (innerGreenRepresentative ((3 : ℝ) • (x.2 : RealL2 halfLineMeasure))
    (correctedMinusSource (actualHartreeTransmissionMinusSource ell c z)))
    (actualMinusCharge (actualHartreeTransmissionMinusSource ell c z)) r / r

def actualHartreeTransmissionInnerJet (ell c : ℝ) (z : ℝ → ℂ)
    (x : InnerCorrections) (a r : ℝ) : ℂ × ℂ :=
  let up := actualHartreeTransmissionInnerPlus ell c z x
  let um := actualHartreeTransmissionInnerMinus ell c z x
  ((up (a*r) : ℂ) + Complex.I * (um (a*r) : ℂ),
    (a : ℂ) * (((deriv up (a*r) : ℝ) : ℂ) + Complex.I * ((deriv um (a*r) : ℝ) : ℂ)))

private theorem pair_norm (u v : ℝ) :
    ‖(u : ℂ)+Complex.I*(v : ℂ)‖ ≤ |u|+|v| := by
  exact (norm_add_le _ _).trans_eq (by simp [Complex.norm_real, Real.norm_eq_abs])

/-- An actual inner solution is constructed, and all physical coordinate
scales are quantified AFTER the constant and the solution. No incoming
jet estimate is assumed. Both forced affine charges remain. -/
theorem actual_Hartree_canonical_scaled_inner_jet_bound
    (B A : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ S : ℝ, 0 ≤ S ∧
      ∀ (ell c : ℝ), 0 < ell → ell ≤ 1 → |c| ≤ 1 →
      ∀ (z : ℝ → ℂ), Measurable z →
        (∀ u : ℝ, 0 < u → ‖z u‖ ≤ B) →
        (∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) →
      ∃ (hp : InWeightedL2 (7/4 : ℝ) (actualHartreeTransmissionPlusSource ell c z))
        (hm : InWeightedL2 (7/4 : ℝ) (actualHartreeTransmissionMinusSource ell c z))
        (x : InnerCorrections),
        ActualHartreeTransmissionInnerSolve ell c z hp hm x ∧
        ∀ (a R : ℝ), 0 < a → 0 < R → 2 < a*R →
          ‖(actualHartreeTransmissionInnerJet ell c z x a R).1‖ +
            R*‖(actualHartreeTransmissionInnerJet ell c z x a R).2‖ ≤
              S * ell^(1/16 : ℝ) := by
  obtain ⟨Cp,Cm,hCp,hCm,hUniform⟩ :=
    actual_Hartree_uniform_canonical_inner_moments_and_traces B A hB hA
  let Q := actualHartreePhysicalWeightedSourceConstant B A
  let T := |actualHartreePhysicalChargeTailConstant|
  have hQ : 0 ≤ Q := actualHartreePhysicalWeightedSourceConstant_nonneg B A hB hA
  have hT : 0 ≤ T := abs_nonneg _
  refine ⟨6*Q*T+Cp+Cm, by positivity, ?_⟩
  intro ell c hell hellOne hc z hz hSup hStrauss
  obtain ⟨hp,hm,x,hxp,hxm,_hMp,_hMm,hTrace⟩ :=
    hUniform ell c hell hellOne hc z hz hSup hStrauss
  refine ⟨hp,hm,x,⟨hxp,hxm⟩,?_⟩
  intro a R ha hR hAR
  let rho := a*R
  let e := ell^(1/16 : ℝ)
  let up := actualHartreeTransmissionInnerPlus ell c z x
  let um := actualHartreeTransmissionInnerMinus ell c z x
  let gp := actualHartreeTransmissionPlusSource ell c z
  let gm := actualHartreeTransmissionMinusSource ell c z
  let U : ℂ := (up rho : ℂ)+Complex.I*(um rho : ℂ)
  let V : ℂ := ((deriv up rho : ℝ) : ℂ)+Complex.I*((deriv um rho : ℝ) : ℂ)
  let alpha : ℂ := (actualPlusCharge gp : ℂ)+Complex.I*(actualMinusCharge gm : ℂ)
  have hrho : 0 < rho := mul_pos ha hR
  have he : 0 ≤ e := Real.rpow_nonneg hell.le _
  have hCs : 0 ≤ Cp+Cm := add_nonneg hCp hCm
  obtain ⟨hpv,hpd,hmv,hmd⟩ := hTrace rho hAR
  have hUeq : U-alpha = ((up rho-actualPlusCharge gp : ℝ) : ℂ)+
      Complex.I*((um rho-actualMinusCharge gm : ℝ) : ℂ) := by
    dsimp [U,alpha]
    push_cast
    ring
  have hU : ‖U-alpha‖ ≤ (Cp+Cm)*e/rho := by
    rw [hUeq]
    exact ((pair_norm _ _).trans (_root_.add_le_add hpv hmv)).trans_eq (by ring)
  have hV : ‖V‖ ≤ (Cp+Cm)*e/rho^2 := by
    exact ((pair_norm _ _).trans (_root_.add_le_add hpd hmd)).trans_eq (by ring)
  have hCharges := actual_Hartree_conjugated_inner_forced_charges_one_sixteenth
    ell c B A hell hellOne hc hB hA z hz hSup hStrauss
  have hAlpha : ‖alpha‖ ≤ (6*Q*T)*e := by
    calc
      _ ≤ |actualPlusCharge gp|+|actualMinusCharge gm| := pair_norm _ _
      _ ≤ 2*((2*Q)*e*actualHartreePhysicalChargeTailConstant)+
          (2*Q)*e*actualHartreePhysicalChargeTailConstant :=
        _root_.add_le_add hCharges.1 hCharges.2
      _ = (6*Q*e)*actualHartreePhysicalChargeTailConstant := by ring
      _ ≤ (6*Q*e)*T := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ = (6*Q*T)*e := by ring
  have hUabs : ‖U‖ ≤ (Cp+Cm)*e/rho+(6*Q*T)*e :=
    (norm_le_norm_sub_add U alpha).trans (_root_.add_le_add hU hAlpha)
  have hScaled : R*‖(a : ℂ)*V‖ ≤ (Cp+Cm)*e/rho := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    calc
      R*(a*‖V‖) = rho*‖V‖ := by dsimp [rho]; ring
      _ ≤ rho*((Cp+Cm)*e/rho^2) := mul_le_mul_of_nonneg_left hV hrho.le
      _ = (Cp+Cm)*e/rho := by field_simp [hrho.ne']; ring
  have hTail : 2*((Cp+Cm)*e/rho) ≤ (Cp+Cm)*e := by
    have h2 : (2 : ℝ)/rho ≤ 1 := (div_le_one hrho).2 hAR.le
    have h := mul_le_mul_of_nonneg_left h2 (mul_nonneg hCs he)
    nlinarith
  change ‖U‖+R*‖(a : ℂ)*V‖ ≤ (6*Q*T+Cp+Cm)*e
  have hSum := _root_.add_le_add hUabs hScaled
  nlinarith

/-- For the SAME actual canonical inner solution and full scaled Hartree
forcing, the original Green inverse can be repaired at the inner endpoint
while preserving both outer coordinates. The retained interface source is
O(ell^(1/16)), derived rather than postulated. The basis bound C is on the
specified annulus; no radius-uniform origin basis estimate is asserted. -/
theorem actual_Hartree_canonical_origin_transmission_small_defect
    (B A mu theta scale R C : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hR : 1 ≤ R) (hC : 0 ≤ C)
    (K : OriginKummerPair mu theta scale) (hK : OriginBasisOn K R (2*R) C) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (ell c a : ℝ), 0 < ell → ell ≤ 1 → |c| ≤ 1 → 0 < a → 2 < a*R →
      ∀ (z : ℝ → ℂ), Measurable z →
        (∀ u : ℝ, 0 < u → ‖z u‖ ≤ B) →
        (∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) →
      ∃ (hp : InWeightedL2 (7/4 : ℝ) (actualHartreeTransmissionPlusSource ell c z))
        (hm : InWeightedL2 (7/4 : ℝ) (actualHartreeTransmissionMinusSource ell c z))
        (x : InnerCorrections),
        ActualHartreeTransmissionInnerSolve ell c z hp hm x ∧
        (let J := actualHartreeTransmissionInnerJet ell c z x a R
         let F := actualHartreeLaplacianScaledKummerSource a ell c z
         actualOriginTransmissionValue K R F J.1 J.2 R = J.1 ∧
         actualOriginTransmissionSlope K R F J.1 J.2 R = J.2 ∧
         actualOriginTransmissionValue K R F J.1 J.2 (2*R) =
           originGreenValue K R (2*R) F (2*R) ∧
         actualOriginTransmissionSlope K R F J.1 J.2 (2*R) =
           originGreenSlope K R (2*R) F (2*R) ∧
         (∀ᵐ r ∂volume, r ∈ Icc R (2*R) →
           HasDerivAt (actualOriginTransmissionValue K R F J.1 J.2)
             (actualOriginTransmissionSlope K R F J.1 J.2 r) r ∧
           HasDerivAt (actualOriginTransmissionSlope K R F J.1 J.2)
             (F r-frozenFirstCoeff r*actualOriginTransmissionSlope K R F J.1 J.2 r-
               frozenZeroCoeff mu theta*actualOriginTransmissionValue K R F J.1 J.2 r+
               actualOriginTransmissionDefect K R F J.1 J.2 r) r) ∧
         ∀ r ∈ Icc R (2*R), ‖actualOriginTransmissionDefect K R F J.1 J.2 r‖ ≤
           D*ell^(1/16 : ℝ)) := by
  obtain ⟨S,hS,hInner⟩ := actual_Hartree_canonical_scaled_inner_jet_bound B A hB hA
  obtain ⟨C1,C2,hC1,hC2,hRepair⟩ := actual_origin_Green_transmission_defect_bound
  let Q := actualHartreePhysicalWeightedSourceConstant B A
  have hQ : 0 ≤ Q := actualHartreePhysicalWeightedSourceConstant_nonneg B A hB hA
  let H := 9*C2+15*C1+3+‖frozenZeroCoeff mu theta‖
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨H*(S+2*C^3*Q), by positivity, ?_⟩
  intro ell c a hell hellOne hc ha hAR z hz hSup hStrauss
  obtain ⟨hp,hm,x,hEq,hJet⟩ := hInner ell c hell hellOne hc z hz hSup hStrauss
  let J := actualHartreeTransmissionInnerJet ell c z x a R
  let F := actualHartreeLaplacianScaledKummerSource a ell c z
  let e := ell^(1/16 : ℝ)
  have hR0 : 0 < R := by linarith
  have hJ : ‖J.1‖+R*‖J.2‖ ≤ S*e := hJet a R ha hR0 hAR
  have hFI : IntervalIntegrable F volume R (2*R) :=
    actual_Hartree_scaled_Kummer_source_intervalIntegrable B A ell c a R (2*R)
      hB hA hell hellOne hc ha hR0 (by linarith) z hz hSup hStrauss
  have hFull := actual_origin_Green_repaired_transmission K hR0 hK F hFI J.1 J.2
  have hGreen := actual_Hartree_origin_outgoing_gain_on_annulus
    B A ell c a R (2*R) C hB hA hell hellOne hc ha hR0 (by linarith) hC
    z hz hSup hStrauss K hK
  have hAt : ‖originGreenValue K R (2*R) F R‖+
      ‖originGreenSlope K R (2*R) F R‖ ≤
      (2*C^3*(2*R-R)/R^2)*Q*ell^(1/8 : ℝ) :=
    hGreen.2.2.2.2.2 R ⟨le_refl _, by linarith⟩
  have he : 0 ≤ e := Real.rpow_nonneg hell.le _
  have he1 : e ≤ 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow hell.le hellOne (show (0 : ℝ) ≤ 1/16 by norm_num)
  have hSmall : ell^(1/8 : ℝ) ≤ e := by
    have hSplit : ell^(1/8 : ℝ) = e*e := by
      dsimp [e]
      rw [← Real.rpow_add hell]
      norm_num
    rw [hSplit]
    nlinarith
  have hMismatch : ‖J.1-originGreenValue K R (2*R) F R‖+
      R*‖J.2-originGreenSlope K R (2*R) F R‖ ≤ (S+2*C^3*Q)*e := by
    have hNorm := _root_.add_le_add
      (norm_sub_le J.1 (originGreenValue K R (2*R) F R))
      (mul_le_mul_of_nonneg_left
        (norm_sub_le J.2 (originGreenSlope K R (2*R) F R)) hR0.le)
    have hWeight : ‖originGreenValue K R (2*R) F R‖+
        R*‖originGreenSlope K R (2*R) F R‖ ≤
        R*(‖originGreenValue K R (2*R) F R‖+‖originGreenSlope K R (2*R) F R‖) := by
      nlinarith [norm_nonneg (originGreenValue K R (2*R) F R)]
    have hScaled := mul_le_mul_of_nonneg_left hAt hR0.le
    have hSimplify : R*((2*C^3*(2*R-R)/R^2)*Q*ell^(1/8 : ℝ)) =
        (2*C^3*Q)*ell^(1/8 : ℝ) := by field_simp [hR0.ne']; ring
    rw [hSimplify] at hScaled
    have hFinal := mul_le_mul_of_nonneg_left hSmall
      (show 0 ≤ 2*C^3*Q by positivity)
    nlinarith
  refine ⟨hp,hm,x,hEq,hFull.1,hFull.2.1,hFull.2.2.1,hFull.2.2.2.1,
    hFull.2.2.2.2.2.2.2,?_⟩
  intro r hr
  exact ((hRepair mu theta scale R K hR F J.1 J.2 r hr).trans
    (mul_le_mul_of_nonneg_left hMismatch hH)).trans_eq (by ring)

end HBL.TypeIIDynamicSelection
