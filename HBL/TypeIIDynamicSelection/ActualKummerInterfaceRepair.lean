import HBL.TypeIIDynamicSelection.ActualOriginGreenIntegrable
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalNonlocalCutoffGain
import HBL.TypeIIDynamicSelection.ActualOneLayerSpatialOverlapGain
import Mathlib.Tactic

/-!
A controlled transmission repair, not an assumed two-endpoint compatibility.
The SAME existing smooth cutoff is translated so that it is identically one
near R and identically zero near 2R. Multiplying the actual left jet mismatch
by an affine function matches both inner coordinates and leaves the outer
Green jet unchanged. Its COMPLETE frozen Kummer residual is retained.

This does not assert that the repaired function solves the unchanged source,
or that its residual has a stronger order than the mismatch. In particular
this is not yet the full nonlinear finite-profile theorem.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.Profile.Kummer

def actualKummerRepairCutoff (R r : ℝ) : ℂ :=
  actualOneLayerInnerOverlapCutoff (R / 3) (r - R)

def actualKummerInterfaceRepair (R : ℝ) (p q : ℂ) (r : ℝ) : ℂ :=
  actualKummerRepairCutoff R r * (p + ((r - R : ℝ) : ℂ) * q)

def actualKummerInterfaceRepairSlope (R : ℝ) (p q : ℂ) (r : ℝ) : ℂ :=
  deriv (actualKummerRepairCutoff R) r * (p + ((r - R : ℝ) : ℂ) * q) +
    actualKummerRepairCutoff R r * q

def actualKummerInterfaceRepairSecond (R : ℝ) (p q : ℂ) (r : ℝ) : ℂ :=
  deriv (deriv (actualKummerRepairCutoff R)) r *
      (p + ((r - R : ℝ) : ℂ) * q) +
    2 * deriv (actualKummerRepairCutoff R) r * q

def actualKummerInterfaceRepairResidual
    (mu theta R : ℝ) (p q : ℂ) (r : ℝ) : ℂ :=
  actualKummerInterfaceRepairSecond R p q r +
    frozenFirstCoeff r * actualKummerInterfaceRepairSlope R p q r +
    frozenZeroCoeff mu theta * actualKummerInterfaceRepair R p q r

private theorem repairCutoff_derivatives (R r : ℝ) (hR : R ≠ 0) :
    HasDerivAt (actualKummerRepairCutoff R)
      (deriv (actualOneLayerInnerOverlapCutoff (R/3)) (r-R)) r ∧
    HasDerivAt (deriv (actualKummerRepairCutoff R))
      (deriv (deriv (actualOneLayerInnerOverlapCutoff (R/3))) (r-R)) r := by
  have hFirst (x : ℝ) : HasDerivAt (actualKummerRepairCutoff R)
      (deriv (actualOneLayerInnerOverlapCutoff (R/3)) (x-R)) x := by
    have h := ((actual_one_layer_overlap_cutoff_hasDerivAt (R/3) (x-R)).differentiableAt.hasDerivAt).scomp
      x ((hasDerivAt_id x).sub_const R)
    simpa only [actualKummerRepairCutoff, Function.comp_def, id_eq, one_smul] using! h
  have heq : deriv (actualKummerRepairCutoff R) =
      (fun x => deriv (actualOneLayerInnerOverlapCutoff (R/3)) (x-R)) :=
    funext (fun x => (hFirst x).deriv)
  refine ⟨hFirst r, ?_⟩
  rw [heq]
  have h := ((actual_one_layer_overlap_cutoff_deriv_hasDerivAt
    (R/3) (r-R) (div_ne_zero hR (by norm_num))).differentiableAt.hasDerivAt).scomp
    r ((hasDerivAt_id r).sub_const R)
  simpa only [Function.comp_def, id_eq, one_smul] using! h

/-- Both derivatives are actual derivatives of the concrete smooth lift. -/
theorem actual_Kummer_interface_repair_derivatives
    (R r : ℝ) (hR : R ≠ 0) (p q : ℂ) :
    HasDerivAt (actualKummerInterfaceRepair R p q)
      (actualKummerInterfaceRepairSlope R p q r) r ∧
    HasDerivAt (actualKummerInterfaceRepairSlope R p q)
      (actualKummerInterfaceRepairSecond R p q r) r := by
  have hC := repairCutoff_derivatives R r hR
  have hC1 := hC.1.differentiableAt.hasDerivAt
  have hC2 := hC.2.differentiableAt.hasDerivAt
  have hP : HasDerivAt (fun x : ℝ => p + ((x-R : ℝ) : ℂ) * q) q r := by
    simpa using ((((hasDerivAt_id r).sub_const R).ofReal_comp).mul_const q).const_add p
  refine ⟨hC1.mul hP, ?_⟩
  convert (hC2.mul hP).add (hC1.mul_const q) using 1
  · rfl
  · unfold actualKummerInterfaceRepairSecond
    ring

/-- The frozen equation sees exactly the explicit residual, including drift. -/
theorem actual_Kummer_interface_repair_residual_exact
    (mu theta R r : ℝ) (hR : R ≠ 0) (p q : ℂ) :
    deriv (deriv (actualKummerInterfaceRepair R p q)) r +
      frozenFirstCoeff r * deriv (actualKummerInterfaceRepair R p q) r +
      frozenZeroCoeff mu theta * actualKummerInterfaceRepair R p q r =
      actualKummerInterfaceRepairResidual mu theta R p q r := by
  have hd := actual_Kummer_interface_repair_derivatives R r hR p q
  have heq : deriv (actualKummerInterfaceRepair R p q) =
      actualKummerInterfaceRepairSlope R p q :=
    funext (fun x => (actual_Kummer_interface_repair_derivatives R x hR p q).1.deriv)
  rw [heq, hd.2.deriv]
  rfl

/-- Left value AND slope are prescribed. The right value AND slope vanish.
Both endpoint identities come from constant cutoff neighbourhoods. -/
theorem actual_Kummer_interface_repair_endpoint_jets
    (R : ℝ) (hR : 0 < R) (p q : ℂ) :
    actualKummerInterfaceRepair R p q R = p ∧
    actualKummerInterfaceRepairSlope R p q R = q ∧
    actualKummerInterfaceRepair R p q (2*R) = 0 ∧
    actualKummerInterfaceRepairSlope R p q (2*R) = 0 := by
  have hLeft : actualKummerInterfaceRepair R p q =ᶠ[𝓝 R]
      (fun r : ℝ => p + ((r-R : ℝ) : ℂ) * q) := by
    filter_upwards [Iio_mem_nhds (show R < R + R/3 by linarith)] with r hr
    have hr' : r < R+R/3 := hr
    have hc : cutoff ((r-R)/(R/3)) = 0 :=
      cutoff_zero_of_le_one _ ((div_le_one (by positivity)).2 (by linarith))
    simp only [actualKummerInterfaceRepair, actualKummerRepairCutoff,
      actualOneLayerInnerOverlapCutoff, hc, sub_zero, Complex.ofReal_one, one_mul]
  have hRight : actualKummerInterfaceRepair R p q =ᶠ[𝓝 (2*R)] (fun _ => (0 : ℂ)) := by
    filter_upwards [Ioi_mem_nhds (show R+2*(R/3) < 2*R by linarith)] with r hr
    have hr' : R+2*(R/3) < r := hr
    have hc : cutoff ((r-R)/(R/3)) = 1 :=
      cutoff_one_of_two_le _ ((le_div_iff₀ (by positivity)).2 (by linarith))
    simp only [actualKummerInterfaceRepair, actualKummerRepairCutoff,
      actualOneLayerInnerOverlapCutoff, hc, sub_self, Complex.ofReal_zero, zero_mul]
  have hP : HasDerivAt (fun r : ℝ => p + ((r-R : ℝ) : ℂ)*q) q R := by
    simpa using ((((hasDerivAt_id R).sub_const R).ofReal_comp).mul_const q).const_add p
  have hDL := (actual_Kummer_interface_repair_derivatives R R hR.ne' p q).1
  have hDR := (actual_Kummer_interface_repair_derivatives R (2*R) hR.ne' p q).1
  refine ⟨?_, hDL.unique (hP.congr_of_eventuallyEq hLeft), ?_,
    hDR.unique ((hasDerivAt_const (2*R) (0 : ℂ)).congr_of_eventuallyEq hRight)⟩
  · simpa using hLeft.eq_of_nhds
  · exact hRight.eq_of_nhds

/-- Fixed cutoff constants control every scale R>=1. The displayed residual
is O(size of mismatch), NOT an unproved higher-order or vanishing error. -/
theorem actual_Kummer_interface_repair_uniform_bound :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
    ∀ (mu theta R r : ℝ), 1 ≤ R → r ∈ Icc R (2*R) →
    ∀ p q : ℂ,
      let D := ‖p‖ + R * ‖q‖
      ‖actualKummerInterfaceRepair R p q r‖ ≤ D ∧
      ‖actualKummerInterfaceRepairSlope R p q r‖ ≤ (3*C1+1)*D/R ∧
      ‖actualKummerInterfaceRepairSecond R p q r‖ ≤ (9*C2+6*C1)*D/R^2 ∧
      ‖actualKummerInterfaceRepairResidual mu theta R p q r‖ ≤
        (9*C2+15*C1+3+‖frozenZeroCoeff mu theta‖)*D := by
  obtain ⟨C1,C2,hC1,hC2,hBounds⟩ := actual_Hartree_overlap_cutoff_uniform_C2_spatial_scaling
  refine ⟨C1,C2,hC1,hC2,?_⟩
  intro mu theta R r hR1 hr p q
  let D := ‖p‖ + R * ‖q‖
  have hR : 0 < R := by linarith
  have hr0 : 0 < r := lt_of_lt_of_le hR hr.1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hq : ‖q‖ ≤ D/R := (le_div_iff₀ hR).2 (by dsimp [D]; nlinarith [norm_nonneg p])
  have hP : ‖p + ((r-R : ℝ) : ℂ)*q‖ ≤ D := by
    calc
      _ ≤ ‖p‖ + ‖((r-R : ℝ) : ℂ)*q‖ := norm_add_le _ _
      _ = ‖p‖ + (r-R)*‖q‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hr.1)]
      _ ≤ D := by dsimp [D]; nlinarith [norm_nonneg q, hr.2]
  have hChi : ‖actualKummerRepairCutoff R r‖ ≤ 1 :=
    actual_Hartree_one_layer_overlap_cutoff_norm_le_one (R/3) (r-R)
  have hDer := repairCutoff_derivatives R r hR.ne'
  have hChi1 : ‖deriv (actualKummerRepairCutoff R) r‖ ≤ 3*C1/R := by
    rw [hDer.1.deriv]
    exact ((hBounds (R/3) (r-R) (by positivity)).1).trans_eq (by field_simp)
  have hChi2 : ‖deriv (deriv (actualKummerRepairCutoff R)) r‖ ≤ 9*C2/R^2 := by
    rw [hDer.2.deriv]
    exact ((hBounds (R/3) (r-R) (by positivity)).2).trans_eq (by field_simp; norm_num)
  have hLift : ‖actualKummerInterfaceRepair R p q r‖ ≤ D := by
    unfold actualKummerInterfaceRepair
    rw [norm_mul]
    exact (mul_le_mul hChi hP (norm_nonneg _) (by norm_num)).trans_eq (one_mul D)
  have hSlope : ‖actualKummerInterfaceRepairSlope R p q r‖ ≤ (3*C1+1)*D/R := by
    unfold actualKummerInterfaceRepairSlope
    calc
      _ ≤ ‖deriv (actualKummerRepairCutoff R) r * (p+((r-R : ℝ):ℂ)*q)‖ +
          ‖actualKummerRepairCutoff R r*q‖ := norm_add_le _ _
      _ ≤ (3*C1/R)*D + 1*(D/R) := by
        rw [norm_mul, norm_mul]
        exact _root_.add_le_add (mul_le_mul hChi1 hP (norm_nonneg _) (by positivity))
          (mul_le_mul hChi hq (norm_nonneg _) (by norm_num))
      _ = _ := by ring
  have hSecond : ‖actualKummerInterfaceRepairSecond R p q r‖ ≤ (9*C2+6*C1)*D/R^2 := by
    unfold actualKummerInterfaceRepairSecond
    calc
      _ ≤ ‖deriv (deriv (actualKummerRepairCutoff R)) r * (p+((r-R : ℝ):ℂ)*q)‖ +
          ‖(2:ℂ)*deriv (actualKummerRepairCutoff R) r*q‖ := norm_add_le _ _
      _ ≤ (9*C2/R^2)*D + (2*(3*C1/R))*(D/R) := by
        norm_num only [norm_mul, Complex.norm_ofNat]
        exact _root_.add_le_add (mul_le_mul hChi2 hP (norm_nonneg _) (by positivity))
          (mul_le_mul (mul_le_mul_of_nonneg_left hChi1 (by norm_num)) hq
            (norm_nonneg _) (by positivity))
      _ = _ := by field_simp; ring
  have hFirst : ‖frozenFirstCoeff r‖ ≤ 2/R+R := by
    unfold frozenFirstCoeff
    calc
      _ ≤ ‖(2:ℂ)/(r:ℂ)‖ + ‖Complex.I*(r:ℂ)/2‖ := norm_add_le _ _
      _ = 2/r+r/2 := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      _ ≤ 2/R+R := _root_.add_le_add (div_le_div_of_nonneg_left (by norm_num) hR hr.1) (by linarith [hr.2])
  have hRaw : ‖actualKummerInterfaceRepairResidual mu theta R p q r‖ ≤
      ((9*C2+12*C1+2)/R^2 + 3*C1+1+‖frozenZeroCoeff mu theta‖)*D := by
    unfold actualKummerInterfaceRepairResidual
    calc
      _ ≤ ‖actualKummerInterfaceRepairSecond R p q r‖ +
          ‖frozenFirstCoeff r*actualKummerInterfaceRepairSlope R p q r‖ +
          ‖frozenZeroCoeff mu theta*actualKummerInterfaceRepair R p q r‖ :=
        (norm_add_le _ _).trans (_root_.add_le_add (norm_add_le _ _) (le_refl _))
      _ ≤ (9*C2+6*C1)*D/R^2 + (2/R+R)*((3*C1+1)*D/R) +
          ‖frozenZeroCoeff mu theta‖*D := by
        rw [norm_mul, norm_mul]
        exact _root_.add_le_add (_root_.add_le_add hSecond
          (mul_le_mul hFirst hSlope (norm_nonneg _) (by positivity)))
          (mul_le_mul_of_nonneg_left hLift (norm_nonneg _))
      _ = _ := by field_simp [hR.ne']; ring
  refine ⟨hLift,hSlope,hSecond,hRaw.trans ?_⟩
  have hPow : 1 ≤ R^2 := by nlinarith
  have hdiv : (9*C2+12*C1+2)/R^2 ≤ 9*C2+12*C1+2 := by
    apply (div_le_iff₀ (pow_pos hR 2)).2
    nlinarith [mul_nonneg (show 0 ≤ 9*C2+12*C1+2 by positivity) (sub_nonneg.mpr hPow)]
  apply mul_le_mul_of_nonneg_right _ hD
  linarith

end HBL.TypeIIDynamicSelection
