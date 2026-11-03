import HBL.TypeIIDynamicSelection.ActualHartreeKummerDefectEquation
import HBL.TypeIIDynamicSelection.ActualHartreeKummerCanonicalLocalizedSource
import HBL.TypeIIDynamicSelection.ActualHartreeKummerCoreSeparation
import Mathlib.Tactic

/-!
# Revised 2.13: exact localization of the genuine physical Hartree/Kummer defect

For the two classical H+/H- solutions reconstructed from the SAME Hartree
source, define U_K(r)=u_+(k r)+i u_-(k r), k=sqrt(q).
The actual frozen Kummer defect D_K=L_K U_K-F is NOT assumed zero.

On a positive annulus the original smooth moving cutoff gives the FULL
identity
  L_K(chi_R U_K)-chi_R F
    = chi_R D_K+2 chi_R' U_K'
        +(chi_R''+frozenFirstCoeff chi_R') U_K.
This retains both original nonzero Wronskian normalizations without adding
any free homogeneous mode. All differentiability follows from physical
C2 jets and the existing genuine cutoff.

An explicit uniform C2 cutoff bound leaves only the ACTUAL defect,
the physical value and slope as quantitative source obligations.
For an annulus strictly inside R, chi=1 and both cutoff derivatives
vanish, so the entire localized residual equals the physical defect.
No Type II rate or artificial source-order hypothesis is used.
These are supporting source identities, NOT full 2.13.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The genuine moving-cutoff physical H+/H- Kummer residual is
exactly the true operator defect plus the original radial C2
commutator, not a freely selected interface source. -/
theorem actual_Hartree_physical_Kummer_cutoff_defect_exact
    (mu theta R k a b r : ℝ) (hR : R ≠ 0)
    (hr : r ∈ Ioo a b) (ha : 0 < a)
    (up um : ℝ → ℝ)
    (hup : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ up (k * x))
    (hum : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ um (k * x))
    (hup2 : DifferentiableAt ℝ (deriv up) (k * r))
    (hum2 : DifferentiableAt ℝ (deriv um) (k * r))
    (F : ℝ → ℂ) :
    let U := actualHartreeInnerKummerProfile up um k
    let chi := actualOneLayerInnerOverlapCutoff R
    actualHartreeFrozenKummerRadialApply mu theta
        (fun x => chi x * U x) r - chi r * F r =
      chi r * actualHartreeInnerKummerSourceDefect mu theta up um k r F +
      (2 : ℂ) * deriv chi r * deriv U r +
        (deriv (deriv chi) r +
          frozenFirstCoeff r * deriv chi r) * U r := by
  dsimp only
  let U := actualHartreeInnerKummerProfile up um k
  let chi := actualOneLayerInnerOverlapCutoff R
  have hRpos : 0 < r := ha.trans hr.1
  have hU (x : ℝ) (hx : x ∈ Ioo a b) :
      DifferentiableAt ℝ U x :=
    (actual_Hartree_two_channel_inner_Kummer_chain_rule
      up um k x (hup x (ha.trans hx.1))
        (hum x (ha.trans hx.1))).differentiableAt
  have hU2 : DifferentiableAt ℝ (deriv U) r :=
    (actual_Hartree_two_channel_Kummer_C2_chain_rule
      up um k r hRpos hup hum hup2 hum2).differentiableAt
  have hComm := actual_Hartree_Kummer_actual_cutoff_commutator_local
      mu theta R hR U a b r hr hU hU2
  have hPhys := actual_Hartree_two_channel_physical_Kummer_defect_exact
    mu theta up um k r hRpos F hup hum hup2 hum2
  change actualHartreeFrozenKummerRadialApply mu theta
      (fun x => chi x * U x) r - chi r * F r =
    chi r * actualHartreeInnerKummerSourceDefect mu theta up um k r F +
      (2 : ℂ) * deriv chi r * deriv U r +
      (deriv (deriv chi) r +
        frozenFirstCoeff r * deriv chi r) * U r
  calc
    _ = (actualHartreeFrozenKummerRadialApply mu theta
          (fun x => chi x * U x) r -
          chi r * actualHartreeFrozenKummerRadialApply mu theta U r) +
        chi r * (actualHartreeFrozenKummerRadialApply mu theta U r - F r) := by ring
    _ = _ := by rw [hComm, hPhys]; ring

/-- Actual positive moving-cutoff C2 constants give a norm bound
without assuming a Type-II exponent, a weighted gain, or any
zero defect. This isolates precisely what 2.13 must still estimate. -/
theorem actual_Hartree_physical_Kummer_cutoff_defect_C2_bound
    (mu theta R k a b r : ℝ) (hR : 0 < R)
    (hr : r ∈ Ioo a b) (ha : 0 < a)
    (up um : ℝ → ℝ)
    (hup : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ up (k * x))
    (hum : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ um (k * x))
    (hup2 : DifferentiableAt ℝ (deriv up) (k * r))
    (hum2 : DifferentiableAt ℝ (deriv um) (k * r))
    (F : ℝ → ℂ) :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      let U := actualHartreeInnerKummerProfile up um k
      let chi := actualOneLayerInnerOverlapCutoff R
      ‖actualHartreeFrozenKummerRadialApply mu theta
          (fun x => chi x * U x) r - chi r * F r‖ ≤
        ‖chi r‖ *
          ‖actualHartreeInnerKummerSourceDefect mu theta up um k r F‖ +
        (2 * (C1 / R)) * ‖deriv U r‖ +
        (C2 / R ^ 2 + ‖frozenFirstCoeff r‖ * (C1 / R)) * ‖U r‖ := by
  obtain ⟨C1,C2,hC1,hC2,hGlobal⟩ :=
    actual_Hartree_overlap_cutoff_uniform_C2_spatial_scaling
  refine ⟨C1,C2,hC1,hC2,?_⟩
  dsimp only
  let U := actualHartreeInnerKummerProfile up um k
  let chi := actualOneLayerInnerOverlapCutoff R
  let D : ℂ := actualHartreeInnerKummerSourceDefect mu theta up um k r F
  have hc1 : ‖deriv chi r‖ ≤ C1 / R := (hGlobal R r hR).1
  have hc2 : ‖deriv (deriv chi) r‖ ≤ C2 / R ^ 2 :=
    (hGlobal R r hR).2
  have hA :
      ‖(2 : ℂ) * deriv chi r * deriv U r‖ ≤
        (2 * (C1 / R)) * ‖deriv U r‖ := by
    calc
      _ = (2 * ‖deriv chi r‖) * ‖deriv U r‖ := by
        norm_num [norm_mul]
      _ ≤ (2 * (C1 / R)) * ‖deriv U r‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hc1 (by norm_num))
          (norm_nonneg _)
  have hCoeff :
      ‖deriv (deriv chi) r + frozenFirstCoeff r * deriv chi r‖ ≤
        C2 / R ^ 2 + ‖frozenFirstCoeff r‖ * (C1 / R) := by
    calc
      _ ≤ ‖deriv (deriv chi) r‖ +
          ‖frozenFirstCoeff r * deriv chi r‖ := norm_add_le _ _
      _ = ‖deriv (deriv chi) r‖ +
          ‖frozenFirstCoeff r‖ * ‖deriv chi r‖ := by rw [norm_mul]
      _ ≤ _ := add_le_add hc2
        (mul_le_mul_of_nonneg_left hc1 (norm_nonneg _))
  have hB :
      ‖(deriv (deriv chi) r +
          frozenFirstCoeff r * deriv chi r) * U r‖ ≤
        (C2 / R ^ 2 +
          ‖frozenFirstCoeff r‖ * (C1 / R)) * ‖U r‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hCoeff (norm_nonneg _)
  have hExact :
      actualHartreeFrozenKummerRadialApply mu theta
        (fun x => chi x * U x) r - chi r * F r =
      chi r * D +
        (2 : ℂ) * deriv chi r * deriv U r +
        (deriv (deriv chi) r +
          frozenFirstCoeff r * deriv chi r) * U r :=
    actual_Hartree_physical_Kummer_cutoff_defect_exact
      mu theta R k a b r hR.ne' hr ha up um
      hup hum hup2 hum2 F
  change ‖actualHartreeFrozenKummerRadialApply mu theta
      (fun x => chi x * U x) r - chi r * F r‖ ≤
    ‖chi r‖ * ‖D‖ + (2 * (C1 / R)) * ‖deriv U r‖ +
      (C2 / R ^ 2 + ‖frozenFirstCoeff r‖ * (C1 / R)) * ‖U r‖
  rw [hExact]
  calc
    _ ≤ ‖chi r * D‖ +
      (‖(2 : ℂ) * deriv chi r * deriv U r‖ +
        ‖(deriv (deriv chi) r +
          frozenFirstCoeff r * deriv chi r) * U r‖) := by
      have h1 := norm_add_le
        (chi r * D + (2 : ℂ) * deriv chi r * deriv U r)
        ((deriv (deriv chi) r +
          frozenFirstCoeff r * deriv chi r) * U r)
      have h2 := norm_add_le (chi r * D)
        ((2 : ℂ) * deriv chi r * deriv U r)
      linarith
    _ = ‖chi r‖ * ‖D‖ +
      (‖(2 : ℂ) * deriv chi r * deriv U r‖ +
        ‖(deriv (deriv chi) r +
          frozenFirstCoeff r * deriv chi r) * U r‖) := by rw [norm_mul]
    _ ≤ ‖chi r‖ * ‖D‖ +
      ((2 * (C1 / R)) * ‖deriv U r‖ +
        (C2 / R ^ 2 + ‖frozenFirstCoeff r‖ * (C1 / R)) * ‖U r‖) :=
      add_le_add le_rfl (add_le_add hA hB)
    _ = _ := by ring

/-- In the genuine fixed Kummer annulus fully covered by the original
physical moving cutoff, there is NO differential interface error.
The actual physical localized source residual is exactly D_K.
This does not postulate or infer D_K=0. -/
theorem actual_Hartree_physical_Kummer_inside_cutoff_defect_exact
    {mu theta center eps : ℝ}
    (K : LocalKummerPair mu theta center eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (F : ℝ → ℂ) (hF : Continuous F)
    (k R : ℝ) (hR : 0 < R) (hCover : center + d ≤ R)
    (hLeft : 0 < center - d)
    (up um : ℝ → ℝ)
    (hup : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ up (k * x))
    (hum : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ um (k * x))
    (hup2 : ∀ x ∈ Ioo (center - d) (center + d),
      DifferentiableAt ℝ (deriv up) (k * x))
    (hum2 : ∀ x ∈ Ioo (center - d) (center + d),
      DifferentiableAt ℝ (deriv um) (k * x)) :
    ∀ r ∈ Ioo (center - d) (center + d),
      actualHartreeFrozenKummerRadialApply mu theta
        (fun x => actualOneLayerInnerOverlapCutoff R x *
          actualHartreeInnerKummerProfile up um k x) r -
          F r =
        actualHartreeInnerKummerSourceDefect mu theta up um k r F := by
  intro r hr
  obtain ⟨hChi,hChi1,hChi2,_⟩ :=
    actual_Hartree_normalized_Kummer_inside_physical_cutoff_exact
      K d hd hde F hF R hR hCover r hr
  have hEq := actual_Hartree_physical_Kummer_cutoff_defect_exact
    mu theta R k (center-d) (center+d) r hR.ne' hr hLeft
    up um hup hum (hup2 r hr) (hum2 r hr) F
  dsimp only at hEq
  rw [hChi,hChi1,hChi2] at hEq
  simpa only [one_mul,zero_mul,mul_zero,zero_add,add_zero] using hEq

end HBL.TypeIIDynamicSelection
