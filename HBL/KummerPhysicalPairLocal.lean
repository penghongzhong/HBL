import HBL.KummerPhysicalLocal

/-!
# Genuine nondegenerate physical Kummer basis on a positive local annulus

Combine the actual normalized Picard-Lindelöf IVPs with the verified
physical-coordinate identity.  This yields two genuine linearly independent
solutions of the frozen Kummer second-order equation on a common interval
strictly inside the positive radial half-line.

No globally defined fundamental pair or positive-annulus continuation is
asserted.  Both are distinct obligations for the full one-layer result.
-/

noncomputable section
set_option autoImplicit false

open Set

namespace HBL.Profile.Kummer

theorem exists_local_physical_nondegenerate_kummer_basis
    (mu theta z : ℝ) (hz : 0 < z) :
    ∃ X Y : ℝ → KummerODEState,
      ∃ eps : ℝ, 0 < eps ∧
        X 0 = (z, ((1 : ℂ), 0)) ∧
        Y 0 = (z, (0, (1 : ℂ))) ∧
        (∀ t ∈ Ioo (-eps) eps,
          (X t).1 = z + t ∧
          (Y t).1 = z + t ∧
          0 < z + t ∧
          HasDerivAt (fun s : ℝ => (X s).2.1)
            (X t).2.2 t ∧
          HasDerivAt (fun s : ℝ => (X s).2.2)
            (-(frozenFirstCoeff (z + t) * (X t).2.2 +
              frozenZeroCoeff mu theta * (X t).2.1)) t ∧
          HasDerivAt (fun s : ℝ => (Y s).2.1)
            (Y t).2.2 t ∧
          HasDerivAt (fun s : ℝ => (Y s).2.2)
            (-(frozenFirstCoeff (z + t) * (Y t).2.2 +
              frozenZeroCoeff mu theta * (Y t).2.1)) t ∧
          localPairWronskian X Y t ≠ 0) := by
  obtain ⟨X, Y, eps0, heps0, hX0, hY0, hDX, hDY, hW⟩ :=
    exists_local_nondegenerate_frozenKummer_pair mu theta z hz
  let eps := min eps0 (z / 2)
  have heps : 0 < eps := lt_min heps0 (half_pos hz)
  refine ⟨X, Y, eps, heps, hX0, hY0, ?_⟩
  intro t ht
  have ht0 : t ∈ Ioo (-eps0) eps0 := by
    have hle : eps ≤ eps0 := min_le_left _ _
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have htpos : 0 < z + t := by
    have hle : eps ≤ z / 2 := min_le_right _ _
    linarith [ht.1]
  have hXtime :=
    frozenKummer_trajectory_time_coordinate
      mu theta z (1 : ℂ) 0 eps0 heps0 X hX0 hDX t ht0
  have hYtime :=
    frozenKummer_trajectory_time_coordinate
      mu theta z 0 (1 : ℂ) eps0 heps0 Y hY0 hDY t ht0
  have hXode :=
    frozenKummer_local_physical_equation
      mu theta z (1 : ℂ) 0 eps0 heps0 X hX0 hDX t ht0
  have hYode :=
    frozenKummer_local_physical_equation
      mu theta z 0 (1 : ℂ) eps0 heps0 Y hY0 hDY t ht0
  exact ⟨hXtime, hYtime, htpos,
    hXode.1, hXode.2, hYode.1, hYode.2, hW t ht0⟩

#print axioms exists_local_physical_nondegenerate_kummer_basis

end HBL.Profile.Kummer
