import HBL.KummerFrozenAnnulus
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic

/-!
# Actual local Kummer ODE solutions

On the physical annulus, z > 0, the frozen Hartree Kummer coefficient is
smooth.  We apply Mathlib Picard-Lindelöf to an autonomous augmented state
(time coordinate, field, first radial derivative), thereby constructing
real, non-placeholder local solutions of the actual frozen Kummer equation.

This is a local IVP theorem; extending it to the entire fixed annulus and
proving the full original one-layer statement remain separate obligations.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.Profile.Kummer

/-- Actual frozen Kummer first-order system: z'=1, u'=p,
p'=-a(z)p-b u. -/
abbrev KummerODEState := ℝ × (ℂ × ℂ)

def frozenKummerAugmentedField (mu theta : ℝ) :
    KummerODEState → KummerODEState :=
  fun x => (1,
    (x.2.2, -(frozenFirstCoeff x.1 * x.2.2 +
      frozenZeroCoeff mu theta * x.2.1)))

@[fun_prop]
theorem frozenFirstCoeff_contDiffAt
    (z : ℝ) (hz : z ≠ 0) :
    ContDiffAt ℝ 1 frozenFirstCoeff z := by
  have hcz : (z : ℂ) ≠ 0 := by exact_mod_cast hz
  have hcomplex :
      ContDiffAt ℂ 1 (fun w : ℂ =>
        (2 : ℂ) / w + Complex.I * w / 2) (z : ℂ) := by
    fun_prop (disch := exact hcz)
  have hcast : ContDiffAt ℝ 1 (fun x : ℝ => (x : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt
  have hr := (hcomplex.restrict_scalars ℝ).comp z hcast
  change ContDiffAt ℝ 1 (fun x : ℝ =>
    (2 : ℂ) / (x : ℂ) + Complex.I * (x : ℂ) / 2) z
  simpa only [Function.comp_def] using hr

theorem frozenZeroCoeff_contDiff
    (mu theta : ℝ) :
    ContDiff ℝ 1 (fun _ : ℝ => frozenZeroCoeff mu theta) := by
  fun_prop

theorem frozenKummerAugmentedField_contDiffAt
    (mu theta z : ℝ) (u p : ℂ) (hz : z ≠ 0) :
    ContDiffAt ℝ 1 (frozenKummerAugmentedField mu theta)
      (z, (u, p)) := by
  have ha := frozenFirstCoeff_contDiffAt z hz
  unfold frozenKummerAugmentedField
  fun_prop (disch := assumption)

theorem exists_local_frozenKummer_augmented_solution
    (mu theta z : ℝ) (u p : ℂ) (hz : 0 < z) :
    ∃ X : ℝ → KummerODEState,
      X 0 = (z, (u, p)) ∧
      ∃ eps : ℝ, 0 < eps ∧
        ∀ t ∈ Set.Ioo (-eps) eps,
          HasDerivAt X (frozenKummerAugmentedField mu theta (X t)) t := by
  have hreg := frozenKummerAugmentedField_contDiffAt
    mu theta z u p hz.ne'
  simpa only [zero_sub, zero_add] using
    (ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      hreg 0)


/-- Two genuinely constructed normalized local IVP solutions, sharing a
positive time interval and with Wronskian determinant one at the base point.
Neither solution nor the nondegenerate initial determinant is assumed. -/
theorem exists_local_normalized_frozenKummer_pair
    (mu theta z : ℝ) (hz : 0 < z) :
    ∃ X Y : ℝ → KummerODEState,
      ∃ eps : ℝ, 0 < eps ∧
        X 0 = (z, ((1 : ℂ), 0)) ∧
        Y 0 = (z, (0, (1 : ℂ))) ∧
        (∀ t ∈ Set.Ioo (-eps) eps,
          HasDerivAt X (frozenKummerAugmentedField mu theta (X t)) t) ∧
        (∀ t ∈ Set.Ioo (-eps) eps,
          HasDerivAt Y (frozenKummerAugmentedField mu theta (Y t)) t) ∧
        ((X 0).2.1 * (Y 0).2.2 -
            (X 0).2.2 * (Y 0).2.1 = (1 : ℂ)) := by
  obtain ⟨X, hX, epsX, hEX, hDX⟩ :=
    exists_local_frozenKummer_augmented_solution
      mu theta z (1 : ℂ) 0 hz
  obtain ⟨Y, hY, epsY, hEY, hDY⟩ :=
    exists_local_frozenKummer_augmented_solution
      mu theta z 0 (1 : ℂ) hz
  refine ⟨X, Y, min epsX epsY, lt_min hEX hEY,
    hX, hY, ?_, ?_, ?_⟩
  · intro t ht
    apply hDX t
    constructor
    · have he := min_le_left epsX epsY
      linarith [ht.1]
    · have he := min_le_left epsX epsY
      linarith [ht.2]
  · intro t ht
    apply hDY t
    constructor
    · have he := min_le_right epsX epsY
      linarith [ht.1]
    · have he := min_le_right epsX epsY
      linarith [ht.2]
  · rw [hX, hY]
    norm_num

#print axioms exists_local_normalized_frozenKummer_pair


/-- The Wronskian of two actual augmented first-order IVP trajectories. -/
def localPairWronskian
    (X Y : ℝ → KummerODEState) (t : ℝ) : ℂ :=
  (X t).2.1 * (Y t).2.2 - (X t).2.2 * (Y t).2.1

theorem localPairWronskian_continuousAt
    (X Y : ℝ → KummerODEState)
    (hX : ContinuousAt X 0) (hY : ContinuousAt Y 0) :
    ContinuousAt (localPairWronskian X Y) 0 := by
  unfold localPairWronskian
  exact (hX.snd.fst.mul hY.snd.snd).sub
    (hX.snd.snd.mul hY.snd.fst)

theorem localPairWronskian_nonzero_near_zero
    (X Y : ℝ → KummerODEState)
    (hX : ContinuousAt X 0) (hY : ContinuousAt Y 0)
    (hW0 : localPairWronskian X Y 0 = 1) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ t ∈ Set.Ioo (-eps) eps, localPairWronskian X Y t ≠ 0 := by
  have hne : localPairWronskian X Y 0 ≠ 0 := by
    rw [hW0]
    norm_num
  have hnear :=
    (localPairWronskian_continuousAt X Y hX hY).eventually_ne hne
  rw [Filter.eventually_iff_exists_mem] at hnear
  obtain ⟨U, hU, hUS⟩ := hnear
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨eps, heps, ?_⟩
  intro t ht
  apply hUS
  apply hball
  have habs : |t| < eps := abs_lt.mpr ht
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using habs

/-- The two normalized frozen Kummer IVPs are actually nondegenerate on a
common positive-length interval. Neither their existence nor the
Wronskian nonvanishing is a supplied hypothesis. -/
theorem exists_local_nondegenerate_frozenKummer_pair
    (mu theta z : ℝ) (hz : 0 < z) :
    ∃ X Y : ℝ → KummerODEState,
      ∃ eps : ℝ, 0 < eps ∧
        X 0 = (z, ((1 : ℂ), 0)) ∧
        Y 0 = (z, (0, (1 : ℂ))) ∧
        (∀ t ∈ Set.Ioo (-eps) eps,
          HasDerivAt X (frozenKummerAugmentedField mu theta (X t)) t) ∧
        (∀ t ∈ Set.Ioo (-eps) eps,
          HasDerivAt Y (frozenKummerAugmentedField mu theta (Y t)) t) ∧
        (∀ t ∈ Set.Ioo (-eps) eps, localPairWronskian X Y t ≠ 0) := by
  obtain ⟨X, Y, e, he, hX, hY, hDX, hDY, hW⟩ :=
    exists_local_normalized_frozenKummer_pair mu theta z hz
  have hzero : (0 : ℝ) ∈ Set.Ioo (-e) e := by
    constructor <;> linarith
  have hcX : ContinuousAt X 0 := (hDX 0 hzero).continuousAt
  have hcY : ContinuousAt Y 0 := (hDY 0 hzero).continuousAt
  have hW0 : localPairWronskian X Y 0 = 1 := by
    simpa only [localPairWronskian] using hW
  obtain ⟨d, hd, hWD⟩ :=
    localPairWronskian_nonzero_near_zero X Y hcX hcY hW0
  refine ⟨X, Y, min e d, lt_min he hd, hX, hY, ?_, ?_, ?_⟩
  · intro t ht
    apply hDX
    constructor
    · have hmin := min_le_left e d
      linarith [ht.1]
    · have hmin := min_le_left e d
      linarith [ht.2]
  · intro t ht
    apply hDY
    constructor
    · have hmin := min_le_left e d
      linarith [ht.1]
    · have hmin := min_le_left e d
      linarith [ht.2]
  · intro t ht
    apply hWD
    constructor
    · have hmin := min_le_right e d
      linarith [ht.1]
    · have hmin := min_le_right e d
      linarith [ht.2]

#print axioms localPairWronskian_nonzero_near_zero
#print axioms exists_local_nondegenerate_frozenKummer_pair

#print axioms frozenFirstCoeff_contDiffAt
#print axioms frozenKummerAugmentedField_contDiffAt
#print axioms exists_local_frozenKummer_augmented_solution

end HBL.Profile.Kummer
