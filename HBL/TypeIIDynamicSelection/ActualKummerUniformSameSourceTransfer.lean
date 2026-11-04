import HBL.TypeIIDynamicSelection.ActualKummerShearedGronwall

/-!
The same source cancels by the previously accepted exact transfer identity.
Its difference is a genuine classical homogeneous Kummer solution, regardless
of whether the inhomogeneous forcing is continuous. The dyadic annulus bound
is derived, not inserted as a uniform fundamental-pair hypothesis.
No identification with an independently prescribed remote solution is claimed.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_Kummer_uniform_transfer_constant_explicit (b : ℂ) :
    actualKummerUniformTransferConstant b =
      (1 + 2 * ‖b‖) ^ 2 * Real.exp ((1 + 2 * ‖b‖) ^ 2) := by
  unfold actualKummerUniformTransferConstant actualKummerShearCoefficient
  norm_num [norm_mul, Complex.norm_I]

/-- The original physical Kummer right transfer is uniformly bounded in
the scaled Cauchy norm on a dyadic positive annulus. The coefficient depends
ONLY on the frozen zero-order coefficient, not on the annulus radius, pair
normalization, source, or Cauchy data. Both solutions use EXACTLY the same F. -/
theorem actual_Kummer_same_source_scaled_transfer_uniform
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (hRatio : z + d ≤ 2 * (z - d))
    (F : ℝ → ℂ) (U DU A DA : ℂ) :
    max
      ‖(actualKummerPhysicalRightTransfer K d F U DU).1 -
        (actualKummerPhysicalRightTransfer K d F A DA).1‖
      ((z + d) * ‖(actualKummerPhysicalRightTransfer K d F U DU).2 -
        (actualKummerPhysicalRightTransfer K d F A DA).2‖) ≤
      actualKummerUniformTransferConstant (frozenZeroCoeff mu theta) *
        max ‖U - A‖ ((z - d) * ‖DU - DA‖) := by
  let ap := actualKummerMatchPhi K (-d) (U-A) (DU-DA)
  let cp := actualKummerMatchPsi K (-d) (U-A) (DU-DA)
  let h : ℝ → ℂ := fun r => ap * K.phi (r-z) + cp * K.psi (r-z)
  let dh : ℝ → ℂ := fun r => ap * K.dphi (r-z) + cp * K.dpsi (r-z)
  have ht0 : -d ∈ Icc (-eps) eps := ⟨by linarith, by linarith⟩
  have hr0 : 0 < z - d := by
    simpa only [sub_eq_add_neg] using K.radial_pos (-d) ht0
  have ht (r : ℝ) (hr : r ∈ Icc (z-d) (z+d)) :
      r-z ∈ Icc (-eps) eps := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hDer (r : ℝ) (hr : r ∈ Icc (z-d) (z+d)) :
      HasDerivAt h (dh r) r := by
    have hs : HasDerivAt (fun x : ℝ => x-z) 1 r := (hasDerivAt_id r).sub_const z
    have hp : HasDerivAt (fun x => K.phi (x-z)) (K.dphi (r-z)) r := by
      simpa only [Function.comp_def, one_smul] using
        (K.phi_hasDeriv (r-z) (ht r hr)).scomp r hs
    have hq : HasDerivAt (fun x => K.psi (x-z)) (K.dpsi (r-z)) r := by
      simpa only [Function.comp_def, one_smul] using
        (K.psi_hasDeriv (r-z) (ht r hr)).scomp r hs
    exact (hp.const_mul ap).add (hq.const_mul cp)
  have hDer2 (r : ℝ) (hr : r ∈ Icc (z-d) (z+d)) :
      HasDerivAt dh
        (-((2 / (r : ℂ) + Complex.I * (r : ℂ) / 2) * dh r +
          frozenZeroCoeff mu theta * h r)) r := by
    have hs : HasDerivAt (fun x : ℝ => x-z) 1 r := (hasDerivAt_id r).sub_const z
    have hp := (K.dphi_hasDeriv (r-z) (ht r hr)).scomp r hs
    have hq := (K.dpsi_hasDeriv (r-z) (ht r hr)).scomp r hs
    rw [show z + (r-z) = r by ring] at hp hq
    simp only [Function.comp_def, one_smul] at hp hq
    have H := (hp.const_mul ap).add (hq.const_mul cp)
    convert H using 1
    dsimp [h, dh, frozenFirstCoeff]
    ring
  have hLeft := actual_Kummer_Wronskian_two_Cauchy_jets_match
    K (-d) ht0 (U-A) (DU-DA)
  have hh0 : h (z-d) = U-A := by
    dsimp [h]
    rw [show z-d-z = -d by ring]
    exact hLeft.1
  have hd0 : dh (z-d) = DU-DA := by
    dsimp [dh]
    rw [show z-d-z = -d by ring]
    exact hLeft.2
  have hDiff := actual_Kummer_same_source_right_transfer_difference K d F U DU A DA
  have hh1 : h (z+d) =
      (actualKummerPhysicalRightTransfer K d F U DU).1 -
        (actualKummerPhysicalRightTransfer K d F A DA).1 := by
    rw [hDiff.1]
    dsimp [h]
    rw [show z+d-z = d by ring]
  have hd1 : dh (z+d) =
      (actualKummerPhysicalRightTransfer K d F U DU).2 -
        (actualKummerPhysicalRightTransfer K d F A DA).2 := by
    rw [hDiff.2]
    dsimp [dh]
    rw [show z+d-z = d by ring]
  have hUniform := actual_Kummer_homogeneous_dyadic_uniform_bound
    (frozenZeroCoeff mu theta) h dh (z-d) (z+d)
    hr0 (by linarith) hRatio hDer hDer2
  simpa only [actualKummerScaledJet, hh0, hd0, hh1, hd1] using hUniform

end HBL.TypeIIDynamicSelection
