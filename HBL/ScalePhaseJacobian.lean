import HBL.ScalePhaseTests

/-!
The two columns of the first manuscript's modulation Jacobian.

At a real bubble, the logarithmic-scale column is determined by the
scale derivative of the positive-channel test, while the phase column
is determined by the negative-channel normalization.  Once the tested
constraints are C1, these two one-variable calculations determine the
full two-by-two Fréchet derivative without extra assumptions.
-/

noncomputable section

open scoped Topology ContDiff

namespace HBL.Modulation

section FullJacobian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The exact -I2 Jacobian from one scale derivative and one phase
normalization, without postulating the full Jacobian. -/
theorem scalePhase_slice_hasFDerivAt
    (Splus Sminus : ℝ → (V →L[ℝ] ℝ)) (w : V)
    (hPlusC1 : ContDiffAt ℝ 1 Splus (0 : ℝ))
    (hMinusC1 : ContDiffAt ℝ 1 Sminus (0 : ℝ))
    (hScale : HasDerivAt (fun a : ℝ => Splus a w) (-1) 0)
    (hMinusNorm : Sminus 0 w = 1) :
    HasFDerivAt
      (fun p : Param => scalePhaseObservable Splus Sminus ((w, 0), p))
      parameterNegId (0 : Param) := by
  let G : Param → Param :=
    fun p => scalePhaseObservable Splus Sminus ((w, 0), p)
  have hEmbed :
      ContDiffAt ℝ 1 (fun p : Param => ((w, (0 : V)), p))
        (0 : Param) := by fun_prop
  have hGC1 : ContDiffAt ℝ 1 G (0 : Param) :=
    (scalePhaseObservable_contDiffAt Splus Sminus (w, 0)
      hPlusC1 hMinusC1).comp (0 : Param) hEmbed
  have hGD :
      HasFDerivAt G (fderiv ℝ G (0 : Param)) (0 : Param) :=
    (hGC1.differentiableAt (by norm_num)).hasFDerivAt
  have hAxisScale0 :
      HasDerivAt (fun a : ℝ => (Splus a w, (0 : ℝ)))
        (-1, 0) (0 : ℝ) := by
    simpa using
      (hScale.hasFDerivAt.prodMk
        (hasFDerivAt_const (0 : ℝ) (0 : ℝ))).hasDerivAt
  have hAxisScale :
      HasDerivAt (fun a : ℝ => G (a, 0)) (-1, 0) (0 : ℝ) := by
    have heq :
        (fun a : ℝ => G (a, 0)) =
          (fun a : ℝ => (Splus a w, (0 : ℝ))) := by
      funext a
      simp [G, scalePhaseObservable]
    rw [heq]
    exact hAxisScale0
  have hAxisPhase :
      HasDerivAt (fun gamma : ℝ => G (0, gamma))
        (0, -1) (0 : ℝ) := by
    have heq :
        (fun gamma : ℝ => G (0, gamma)) =
          (fun gamma : ℝ =>
            phaseChannelTest (Splus 0) (Sminus 0) (w, 0) gamma) := by
      funext gamma
      simp [G, scalePhaseObservable, phaseChannelTest]
    rw [heq]
    exact phaseChannelTest_hasDerivAt_real_state
      (Splus 0) (Sminus 0) w hMinusNorm
  have hScaleIn :
      HasFDerivAt (fun a : ℝ => (a, (0 : ℝ)))
        (ContinuousLinearMap.inl ℝ ℝ ℝ) (0 : ℝ) :=
    hasFDerivAt_prodMk_left (0 : ℝ) (0 : ℝ)
  have hPhaseIn :
      HasFDerivAt (fun gamma : ℝ => ((0 : ℝ), gamma))
        (ContinuousLinearMap.inr ℝ ℝ ℝ) (0 : ℝ) :=
    hasFDerivAt_prodMk_right (0 : ℝ) (0 : ℝ)
  have hScaleComp :
      HasDerivAt (fun a : ℝ => G (a, 0))
        ((fderiv ℝ G (0 : Param)) ((1 : ℝ), 0)) (0 : ℝ) := by
    have h : HasFDerivAt
        (G ∘ fun a : ℝ => (a, (0 : ℝ)))
        ((fderiv ℝ G (0 : Param)).comp
          (ContinuousLinearMap.inl ℝ ℝ ℝ)) (0 : ℝ) :=
      hGD.comp (f := fun a : ℝ => (a, (0 : ℝ))) (0 : ℝ) hScaleIn
    simpa [Function.comp_def] using h.hasDerivAt
  have hPhaseComp :
      HasDerivAt (fun gamma : ℝ => G (0, gamma))
        ((fderiv ℝ G (0 : Param)) ((0 : ℝ), 1)) (0 : ℝ) := by
    have h : HasFDerivAt
        (G ∘ fun gamma : ℝ => ((0 : ℝ), gamma))
        ((fderiv ℝ G (0 : Param)).comp
          (ContinuousLinearMap.inr ℝ ℝ ℝ)) (0 : ℝ) :=
      hGD.comp (f := fun gamma : ℝ => ((0 : ℝ), gamma)) (0 : ℝ) hPhaseIn
    simpa [Function.comp_def] using h.hasDerivAt
  have hDScale :
      (fderiv ℝ G (0 : Param)) ((1 : ℝ), 0) = (-1, 0) :=
    hScaleComp.unique hAxisScale
  have hDPhase :
      (fderiv ℝ G (0 : Param)) ((0 : ℝ), 1) = (0, -1) :=
    hPhaseComp.unique hAxisPhase
  have hDecomp (p : Param) :
      p = p.1 • ((1 : ℝ), (0 : ℝ)) +
            p.2 • ((0 : ℝ), (1 : ℝ)) := by
    rcases p with ⟨a, gamma⟩
    ext <;> simp
  have hD : fderiv ℝ G (0 : Param) = parameterNegId := by
    apply ContinuousLinearMap.ext
    intro p
    calc
      (fderiv ℝ G (0 : Param)) p =
          (fderiv ℝ G (0 : Param))
            (p.1 • ((1 : ℝ), 0) + p.2 • ((0 : ℝ), 1)) := by
              rw [← hDecomp p]
      _ = p.1 • (fderiv ℝ G (0 : Param)) ((1 : ℝ), 0) +
            p.2 • (fderiv ℝ G (0 : Param)) ((0 : ℝ), 1) := by
              rw [map_add, map_smul, map_smul]
      _ = parameterNegId p := by
            rw [hDScale, hDPhase]
            rcases p with ⟨a, gamma⟩
            simp [parameterNegId]
  change HasFDerivAt G parameterNegId (0 : Param)
  rw [← hD]
  exact hGD

end FullJacobian

end HBL.Modulation
