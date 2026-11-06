import HBL.TypeIIDynamicSelection.ActualKummerPhysicalInterfaceRepair
import Mathlib.Tactic

/-!
# Exact time derivative of the physical Kummer replacement repair

The replacement repair is explicit:
  H(t,y)=Repair_R(p(t),q(t), y/a(t)).
Its time derivative therefore needs no differentiation of the Kummer Green
formula.  The exact chain rule separates:
* the physical scale speed a_s/a through the normalized coordinate;
* the two upper-jet speeds p_s and q_s.

This is the missing time-derivative interface for the actual PDE correction.
No decay estimate for these speeds is assumed or claimed here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection

/-- Public derivative certificate for the concrete translated repair cutoff. -/
theorem actual_Kummer_repair_cutoff_hasDerivAt
    (R x : ℝ) (hR : R ≠ 0) :
    HasDerivAt (actualKummerRepairCutoff R)
      (deriv (actualKummerRepairCutoff R) x) x := by
  have h :=
    (actual_Kummer_interface_repair_derivatives
      R x hR (1 : ℂ) (0 : ℂ)).1
  simpa [actualKummerInterfaceRepair,
    actualKummerInterfaceRepairSlope] using h

/-- Exact time derivative of the physical replacement repair.  The first
term is coordinate transport; the second is the actual upper-jet motion. -/
theorem actual_Kummer_physical_interface_repair_time_derivative
    (a : ℝ → ℝ) (p q : ℝ → ℂ)
    (R y s adot : ℝ) (pdot qdot : ℂ)
    (ha : HasDerivAt a adot s) (ha0 : a s ≠ 0)
    (hp : HasDerivAt p pdot s) (hq : HasDerivAt q qdot s)
    (hR : R ≠ 0) :
    let x := y / a s
    let xs := -(y * adot / (a s) ^ 2)
    HasDerivAt
      (fun t => actualKummerPhysicalInterfaceRepair
        (a t) R (p t) (q t) y)
      ((xs : ℝ) • actualKummerInterfaceRepairSlope
          R (p s) (q s) x +
        actualKummerRepairCutoff R x *
          (pdot + (((x - R : ℝ) : ℂ) * qdot))) s := by
  dsimp only
  let xfun : ℝ → ℝ := fun t => y / a t
  let xs : ℝ := -(y * adot / (a s) ^ 2)
  have hx : HasDerivAt xfun xs s := by
    have hraw := (hasDerivAt_const s y).div ha ha0
    dsimp [xfun, xs]
    convert hraw using 1 <;> ring
  have hcut0 :=
    actual_Kummer_repair_cutoff_hasDerivAt R (xfun s) hR
  have hcut :=
    hcut0.scomp s hx
  have hxr : HasDerivAt (fun t => xfun t - R) xs s :=
    hx.sub_const R
  have hxrC :
      HasDerivAt (fun t => ((xfun t - R : ℝ) : ℂ)) (xs : ℂ) s :=
    hxr.ofReal_comp
  have hlin :
      HasDerivAt
        (fun t => p t + ((xfun t - R : ℝ) : ℂ) * q t)
        (pdot + (xs : ℂ) * q s +
          ((xfun s - R : ℝ) : ℂ) * qdot) s :=
    hp.add (hxrC.mul hq)
  have hprod := hcut.mul hlin
  change HasDerivAt
      (fun t =>
        actualKummerRepairCutoff R (xfun t) *
          (p t + ((xfun t - R : ℝ) : ℂ) * q t)) _ s
  convert hprod using 1
  · funext t
    rfl
  · simp only [Complex.real_smul]
    unfold actualKummerInterfaceRepairSlope
    ring

/-- A norm form of the exact identity.  It isolates the only quantities
still needing time-order estimates: normalized-coordinate speed and upper-jet
speeds. -/
theorem actual_Kummer_physical_interface_repair_time_derivative_norm
    (a : ℝ → ℝ) (p q : ℝ → ℂ)
    (R y s adot : ℝ) (pdot qdot : ℂ)
    (ha : HasDerivAt a adot s) (ha0 : a s ≠ 0)
    (hp : HasDerivAt p pdot s) (hq : HasDerivAt q qdot s)
    (hR : R ≠ 0) :
    let x := y / a s
    let xs := -(y * adot / (a s) ^ 2)
    ‖deriv
        (fun t => actualKummerPhysicalInterfaceRepair
          (a t) R (p t) (q t) y) s‖ ≤
      |xs| * ‖actualKummerInterfaceRepairSlope R (p s) (q s) x‖ +
        ‖pdot‖ + |x - R| * ‖qdot‖ := by
  dsimp only
  let x := y / a s
  let xs := -(y * adot / (a s) ^ 2)
  have hd :=
    actual_Kummer_physical_interface_repair_time_derivative
      a p q R y s adot pdot qdot ha ha0 hp hq hR
  rw [hd.deriv]
  have hcut :
      ‖actualKummerRepairCutoff R x‖ ≤ 1 := by
    unfold actualKummerRepairCutoff
    exact actual_Hartree_one_layer_overlap_cutoff_norm_le_one
      (R / 3) (x - R)
  calc
    ‖(xs : ℝ) • actualKummerInterfaceRepairSlope R (p s) (q s) x +
        actualKummerRepairCutoff R x *
          (pdot + (((x - R : ℝ) : ℂ) * qdot))‖
        ≤ ‖(xs : ℝ) • actualKummerInterfaceRepairSlope R (p s) (q s) x‖ +
          ‖actualKummerRepairCutoff R x *
            (pdot + (((x - R : ℝ) : ℂ) * qdot))‖ :=
      norm_add_le _ _
    _ = |xs| * ‖actualKummerInterfaceRepairSlope R (p s) (q s) x‖ +
        ‖actualKummerRepairCutoff R x‖ *
          ‖pdot + (((x - R : ℝ) : ℂ) * qdot)‖ := by
      rw [norm_smul, Real.norm_eq_abs, norm_mul]
    _ ≤ |xs| * ‖actualKummerInterfaceRepairSlope R (p s) (q s) x‖ +
        1 * (‖pdot‖ + ‖(((x - R : ℝ) : ℂ) * qdot)‖) := by
      gcongr
      · exact hcut
      · exact norm_add_le _ _
    _ = |xs| * ‖actualKummerInterfaceRepairSlope R (p s) (q s) x‖ +
        (‖pdot‖ + |x - R| * ‖qdot‖) := by
      rw [one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
