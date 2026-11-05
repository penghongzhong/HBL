import HBL.TypeIIDynamicSelection.ActualKummerInterfaceRepair
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedKummerShellGain
import HBL.MonopoleComplexResidual
import Mathlib.Tactic

/-!
# Physical pullback of the Kummer interface repair

The repair is made in the fixed Kummer coordinate z and pulled back by
y=a z. The exact physical scaled Kummer operator therefore sees a factor
a^(-2). This turns a same-size finite Kummer jet repair into a genuinely
small physical PDE source when a is large.

No remote solution, nonlinear Hartree estimate, or final profile recursion
is asserted here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Modulation.Monopole

def actualKummerPhysicalInterfaceRepair
    (a R : ℝ) (p q : ℂ) (y : ℝ) : ℂ :=
  actualKummerInterfaceRepair R p q (y / a)

def actualKummerPhysicalInterfaceRepairSlope
    (a R : ℝ) (p q : ℂ) : ℝ → ℂ :=
  (1 / a : ℝ) •
    (fun y => actualKummerInterfaceRepairSlope R p q (y / a))

def actualKummerPhysicalInterfaceRepairSecond
    (a R : ℝ) (p q : ℂ) : ℝ → ℂ :=
  (1 / a : ℝ) • ((1 / a : ℝ) •
    (fun y => actualKummerInterfaceRepairSecond R p q (y / a)))

theorem actual_Kummer_physical_interface_repair_derivatives
    (a R y : ℝ) (_ha : a ≠ 0) (hR : R ≠ 0) (p q : ℂ) :
    HasDerivAt (actualKummerPhysicalInterfaceRepair a R p q)
      (actualKummerPhysicalInterfaceRepairSlope a R p q y) y ∧
    HasDerivAt (actualKummerPhysicalInterfaceRepairSlope a R p q)
      (actualKummerPhysicalInterfaceRepairSecond a R p q y) y := by
  have hbase :=
    actual_Kummer_interface_repair_derivatives R (y / a) hR p q
  have hscale : HasDerivAt (fun t : ℝ => t / a) (1 / a) y :=
    (hasDerivAt_id y).div_const a
  have hfirst :=
    hbase.1.scomp y hscale
  have hsecond0 :=
    hbase.2.scomp y hscale
  constructor
  · change HasDerivAt
      (fun x : ℝ => actualKummerInterfaceRepair R p q (x / a))
      ((1 / a : ℝ) • actualKummerInterfaceRepairSlope R p q (y / a)) y
    simpa only [Function.comp_def] using hfirst
  · have hsecond := hsecond0.const_smul (1 / a : ℝ)
    change HasDerivAt
      ((1 / a : ℝ) •
        (fun x : ℝ => actualKummerInterfaceRepairSlope R p q (x / a)))
      ((1 / a : ℝ) • ((1 / a : ℝ) •
        actualKummerInterfaceRepairSecond R p q (y / a))) y
    exact hsecond

/-- Exact scaling identity: the complete frozen repair residual acquires
the physical factor a^(-2). -/
theorem actual_Kummer_physical_interface_repair_scaled_residual_exact
    (mu theta a R y : ℝ) (ha : 0 < a) (hR : 0 < R)
    (hy : y ∈ Icc (a * R) (2 * a * R)) (p q : ℂ) :
    actualMatchedScaledKummerApply mu theta a
        (actualKummerPhysicalInterfaceRepair a R p q) y =
      ((a ^ 2)⁻¹ : ℝ) •
        actualKummerInterfaceRepairResidual mu theta R p q (y / a) := by
  have hy0 : 0 < y := (mul_pos ha hR).trans_le hy.1
  have hd :=
    actual_Kummer_physical_interface_repair_derivatives
      a R y ha.ne' hR.ne' p q
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy0.ne'
  have hnear :
      deriv (actualKummerPhysicalInterfaceRepair a R p q) =ᶠ[𝓝 y]
        actualKummerPhysicalInterfaceRepairSlope a R p q := by
    filter_upwards with x
    exact (actual_Kummer_physical_interface_repair_derivatives
      a R x ha.ne' hR.ne' p q).1.deriv
  have hsecondPhysical :
      HasDerivAt (deriv (actualKummerPhysicalInterfaceRepair a R p q))
        (actualKummerPhysicalInterfaceRepairSecond a R p q y) y :=
    hd.2.congr_of_eventuallyEq hnear
  unfold actualMatchedScaledKummerApply complexRadialLaplacian
  rw [hsecondPhysical.deriv, hd.1.deriv]
  unfold actualKummerPhysicalInterfaceRepair
    actualKummerPhysicalInterfaceRepairSlope
    actualKummerPhysicalInterfaceRepairSecond
    actualKummerInterfaceRepairResidual frozenFirstCoeff
  simp only [Pi.smul_apply, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_div]
  field_simp [haC, hyC]
  norm_num
  ring

/-- Physical endpoint jets: the Kummer value is preserved at aR, the
physical slope is q/a there, and both vanish at 2aR. -/
theorem actual_Kummer_physical_interface_repair_endpoint_jets
    (a R : ℝ) (ha : 0 < a) (hR : 0 < R) (p q : ℂ) :
    actualKummerPhysicalInterfaceRepair a R p q (a*R) = p ∧
    actualKummerPhysicalInterfaceRepairSlope a R p q (a*R) =
      (1 / a : ℝ) • q ∧
    actualKummerPhysicalInterfaceRepair a R p q (2*a*R) = 0 ∧
    actualKummerPhysicalInterfaceRepairSlope a R p q (2*a*R) = 0 := by
  have hEnds := actual_Kummer_interface_repair_endpoint_jets R hR p q
  have h1 : (a * R) / a = R := by field_simp [ha.ne']
  have h2 : (2 * a * R) / a = 2 * R := by field_simp [ha.ne']
  unfold actualKummerPhysicalInterfaceRepair
    actualKummerPhysicalInterfaceRepairSlope
  simp only [Pi.smul_apply]
  rw [h1, h2, hEnds.1, hEnds.2.1, hEnds.2.2.1, hEnds.2.2.2]
  exact ⟨rfl, rfl, rfl, by simp⟩

/-- Uniform physical residual bound for every positive fixed Kummer radius.
The explicit R^(-2) loss is harmless after the exact a^(-2) pullback and
is intentionally retained. -/
theorem actual_Kummer_physical_interface_repair_residual_bound :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
    ∀ (mu theta a R y : ℝ), 0 < a → 0 < R →
      y ∈ Icc (a*R) (2*a*R) →
    ∀ p q : ℂ,
      let D := ‖p‖ + R * ‖q‖
      ‖actualMatchedScaledKummerApply mu theta a
          (actualKummerPhysicalInterfaceRepair a R p q) y‖ ≤
        (a ^ 2)⁻¹ *
          ((9*C2+12*C1+2)/R^2 + 3*C1+1+
            ‖frozenZeroCoeff mu theta‖) * D := by
  obtain ⟨C1,C2,hC1,hC2,hRepair⟩ :=
    actual_Kummer_interface_repair_positive_radius_bound
  refine ⟨C1,C2,hC1,hC2,?_⟩
  intro mu theta a R y ha hR hy p q
  dsimp only
  have hz : y / a ∈ Icc R (2*R) := by
    constructor
    · exact (le_div_iff₀ ha).2 (by simpa [mul_comm] using hy.1)
    · exact (div_le_iff₀ ha).2 (by nlinarith [hy.2])
  have hraw := (hRepair mu theta R (y/a) hR hz p q).2.2.2
  rw [actual_Kummer_physical_interface_repair_scaled_residual_exact
    mu theta a R y ha hR hy p q,
    norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg a))]
  have hh := mul_le_mul_of_nonneg_left hraw
    (inv_nonneg.mpr (sq_nonneg a))
  simpa only [mul_assoc] using hh

end HBL.TypeIIDynamicSelection
