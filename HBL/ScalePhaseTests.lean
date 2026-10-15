import HBL.PhaseChannel

/-!
Exact scale-phase form of the two tested constraints in the first manuscript
lemma. The two scale-dependent, bounded real test functionals are the only
remaining analytic family to construct from compactly supported radial tests.
The smooth phase rotation is treated here with explicit channel formulas.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace HBL.Modulation

section ScalePhaseTest

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The two orthogonality tests after scale transport and phase rotation.
The pair of state components represents the real and imaginary radial fields.
-/
def scalePhaseObservable
    (Splus Sminus : ℝ → (V →L[ℝ] ℝ))
    (v : (V × V) × Param) : Param :=
  (Real.cos v.2.2 * Splus v.2.1 v.1.1 +
       Real.sin v.2.2 * Splus v.2.1 v.1.2,
    -Real.sin v.2.2 * Sminus v.2.1 v.1.1 +
       Real.cos v.2.2 * Sminus v.2.1 v.1.2)

/-- The entire joint state-parameter test is C1 as soon as the two
scale-transported test functionals are C1 in operator norm. In particular
no differentiability of the scale action on arbitrary energy states is used.
-/
theorem scalePhaseObservable_contDiffAt
    (Splus Sminus : ℝ → (V →L[ℝ] ℝ)) (u₀ : V × V)
    (hPlus : ContDiffAt ℝ 1 Splus (0 : ℝ))
    (hMinus : ContDiffAt ℝ 1 Sminus (0 : ℝ)) :
    ContDiffAt ℝ 1 (scalePhaseObservable Splus Sminus)
      (u₀, (0 : Param)) := by
  have hScale :
      ContDiffAt ℝ 1 (fun v : (V × V) × Param => v.2.1)
        (u₀, (0 : Param)) := by fun_prop
  have hPhase :
      ContDiffAt ℝ 1 (fun v : (V × V) × Param => v.2.2)
        (u₀, (0 : Param)) := by fun_prop
  have hReal :
      ContDiffAt ℝ 1 (fun v : (V × V) × Param => v.1.1)
        (u₀, (0 : Param)) := by fun_prop
  have hImag :
      ContDiffAt ℝ 1 (fun v : (V × V) × Param => v.1.2)
        (u₀, (0 : Param)) := by fun_prop
  have hPlusFam :
      ContDiffAt ℝ 1 (fun v : (V × V) × Param => Splus v.2.1)
        (u₀, (0 : Param)) :=
    hPlus.comp _ hScale
  have hMinusFam :
      ContDiffAt ℝ 1 (fun v : (V × V) × Param => Sminus v.2.1)
        (u₀, (0 : Param)) :=
    hMinus.comp _ hScale
  have hPR :
      ContDiffAt ℝ 1
        (fun v : (V × V) × Param => Splus v.2.1 v.1.1)
        (u₀, (0 : Param)) :=
    hPlusFam.clm_apply hReal
  have hPI :
      ContDiffAt ℝ 1
        (fun v : (V × V) × Param => Splus v.2.1 v.1.2)
        (u₀, (0 : Param)) :=
    hPlusFam.clm_apply hImag
  have hMR :
      ContDiffAt ℝ 1
        (fun v : (V × V) × Param => Sminus v.2.1 v.1.1)
        (u₀, (0 : Param)) :=
    hMinusFam.clm_apply hReal
  have hMI :
      ContDiffAt ℝ 1
        (fun v : (V × V) × Param => Sminus v.2.1 v.1.2)
        (u₀, (0 : Param)) :=
    hMinusFam.clm_apply hImag
  have hCos :
      ContDiffAt ℝ 1
        (fun v : (V × V) × Param => Real.cos v.2.2)
        (u₀, (0 : Param)) :=
    Real.contDiff_cos.contDiffAt.comp _ hPhase
  have hSin :
      ContDiffAt ℝ 1
        (fun v : (V × V) × Param => Real.sin v.2.2)
        (u₀, (0 : Param)) :=
    Real.contDiff_sin.contDiffAt.comp _ hPhase
  change ContDiffAt ℝ 1
    (fun v : (V × V) × Param =>
      (Real.cos v.2.2 * Splus v.2.1 v.1.1 +
          Real.sin v.2.2 * Splus v.2.1 v.1.2,
        -Real.sin v.2.2 * Sminus v.2.1 v.1.1 +
          Real.cos v.2.2 * Sminus v.2.1 v.1.2))
      (u₀, (0 : Param))
  exact ((hCos.mul hPR).add (hSin.mul hPI)).prodMk
    ((hSin.neg.mul hMR).add (hCos.mul hMI))

/-- The real bubble has only the two indicated phase-scale channels. -/
theorem scalePhaseObservable_real_state
    (Splus Sminus : ℝ → (V →L[ℝ] ℝ)) (w : V) (p : Param) :
    scalePhaseObservable Splus Sminus ((w, 0), p) =
      (Real.cos p.2 * Splus p.1 w, -Real.sin p.2 * Sminus p.1 w) := by
  simp [scalePhaseObservable]

end ScalePhaseTest

end HBL.Modulation
