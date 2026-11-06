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
    (R x : ℝ) (_hR : R ≠ 0) :
    HasDerivAt (actualKummerRepairCutoff R)
      (deriv (actualKummerRepairCutoff R) x) x := by
  apply DifferentiableAt.hasDerivAt
  unfold actualKummerRepairCutoff
  have hinner :=
    actual_one_layer_overlap_cutoff_hasDerivAt (R / 3) (x - R)
  have hshift : HasDerivAt (fun t : ℝ => t - R) 1 x :=
    (hasDerivAt_id x).sub_const R
  simpa only [Function.comp_def, one_smul] using
    (hinner.scomp x hshift).differentiableAt

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
  have hlin0 := hp.add (hxrC.mul hq)
  have hlin :
      HasDerivAt
        (fun t => p t + ((xfun t - R : ℝ) : ℂ) * q t)
        (pdot + (xs : ℂ) * q s +
          ((xfun s - R : ℝ) : ℂ) * qdot) s := by
    simpa only [Pi.add_apply, Pi.mul_apply, add_assoc] using hlin0
  have hprod := hcut.mul hlin
  change HasDerivAt
      (fun t =>
        actualKummerRepairCutoff R (xfun t) *
          (p t + ((xfun t - R : ℝ) : ℂ) * q t)) _ s
  convert hprod using 1
  · funext t
    rfl
  · simp only [Function.comp_apply, Complex.real_smul]
    unfold actualKummerInterfaceRepairSlope
    ring_nf

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
      exact add_le_add_right
        (mul_le_mul hcut (norm_add_le _ _)
          (norm_nonneg _) (by norm_num)) _
    _ = |xs| * ‖actualKummerInterfaceRepairSlope R (p s) (q s) x‖ +
        (‖pdot‖ + |x - R| * ‖qdot‖) := by
      rw [one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ = _ := by ring

/-- On the actual physical repair shell, the exact time derivative is controlled
by the relative scale speed and the two upper-jet speeds.  The constants are
the already verified fixed-cutoff constants; no new Kummer estimate enters. -/
theorem actual_Kummer_physical_interface_repair_time_shell_bound :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
    ∀ (a : ℝ → ℝ) (p q : ℝ → ℂ)
      (R y s adot : ℝ) (pdot qdot : ℂ),
      HasDerivAt a adot s → 0 < a s →
      HasDerivAt p pdot s → HasDerivAt q qdot s →
      0 < R → y ∈ Icc (a s * R) (2 * a s * R) →
      let D := ‖p s‖ + R * ‖q s‖
      ‖deriv
          (fun t => actualKummerPhysicalInterfaceRepair
            (a t) R (p t) (q t) y) s‖ ≤
        (2 * (3 * C1 + 1) * D) * (|adot| / a s) +
          ‖pdot‖ + R * ‖qdot‖ := by
  obtain ⟨C1,C2,hC1,hC2,hRepair⟩ :=
    actual_Kummer_interface_repair_positive_radius_bound
  refine ⟨C1,C2,hC1,hC2,?_⟩
  intro a p q R y s adot pdot qdot ha haPos hp hq hR hy
  dsimp only
  let x : ℝ := y / a s
  let D : ℝ := ‖p s‖ + R * ‖q s‖
  have hx : x ∈ Icc R (2 * R) := by
    constructor
    · apply (le_div_iff₀ haPos).2
      simpa only [x, mul_comm] using hy.1
    · apply (div_le_iff₀ haPos).2
      simpa only [x, mul_assoc, mul_comm, mul_left_comm] using hy.2
  have hSlope :
      ‖actualKummerInterfaceRepairSlope R (p s) (q s) x‖ ≤
        (3 * C1 + 1) * D / R := by
    simpa only [D] using
      (hRepair 0 0 R x hR hx (p s) (q s)).2.1
  have hxSub : |x - R| ≤ R := by
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
    linarith [hx.2]
  have hyPos : 0 < y := (mul_pos haPos hR).trans_le hy.1
  have hRel : 0 ≤ |adot| / a s :=
    div_nonneg (abs_nonneg adot) haPos.le
  have hxsEq :
      |-(y * adot / (a s) ^ 2)| =
        x * (|adot| / a s) := by
    dsimp [x]
    rw [abs_neg, abs_div, abs_mul, abs_of_pos hyPos,
      abs_of_pos (sq_pos_of_pos haPos)]
    field_simp [haPos.ne']
  have hxs :
      |-(y * adot / (a s) ^ 2)| ≤
        (2 * R) * (|adot| / a s) := by
    rw [hxsEq]
    exact mul_le_mul_of_nonneg_right hx.2 hRel
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hSlopeNonneg :
      0 ≤ (3 * C1 + 1) * D / R := by
    positivity
  have hFirst :
      |-(y * adot / (a s) ^ 2)| *
          ‖actualKummerInterfaceRepairSlope R (p s) (q s) x‖ ≤
        (2 * (3 * C1 + 1) * D) * (|adot| / a s) := by
    calc
      _ ≤ ((2 * R) * (|adot| / a s)) *
          ((3 * C1 + 1) * D / R) :=
        mul_le_mul hxs hSlope (norm_nonneg _) (by positivity)
      _ = _ := by
        field_simp [hR.ne']
  have hQ :
      |x - R| * ‖qdot‖ ≤ R * ‖qdot‖ :=
    mul_le_mul_of_nonneg_right hxSub (norm_nonneg qdot)
  have hBase :=
    actual_Kummer_physical_interface_repair_time_derivative_norm
      a p q R y s adot pdot qdot ha haPos.ne' hp hq hR.ne'
  dsimp only at hBase
  change ‖deriv
      (fun t => actualKummerPhysicalInterfaceRepair
        (a t) R (p t) (q t) y) s‖ ≤ _ at hBase ⊢
  calc
    _ ≤ |-(y * adot / (a s) ^ 2)| *
          ‖actualKummerInterfaceRepairSlope
            R (p s) (q s) x‖ +
        ‖pdot‖ + |x - R| * ‖qdot‖ := by
      simpa only [x] using hBase
    _ ≤ (2 * (3 * C1 + 1) * D) * (|adot| / a s) +
          ‖pdot‖ + R * ‖qdot‖ :=
      add_le_add (add_le_add hFirst le_rfl) hQ


end HBL.TypeIIDynamicSelection
