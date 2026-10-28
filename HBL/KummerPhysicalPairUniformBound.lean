import HBL.KummerPhysicalPairLocal
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-!
# Uniform local Kummer IVP bounds on a smaller closed positive annulus

The genuine pair of second-order physical Kummer solutions constructed by
Picard-Lindelof is nondegenerate near its initial radial point z0 > 0.
On a strictly smaller compact interval we bound both solutions, both first
radial derivatives, and the reciprocal Wronskian by one finite constant.

This is a true localized consequence of the physical Hartree Kummer ODE;
it introduces no abstract fundamental-pair hypothesis. A bound uniform in
external parameters or over a larger prescribed annulus is not yet claimed.
-/

noncomputable section
set_option autoImplicit false

open Set

namespace HBL.Profile.Kummer

/-- All four physical solution components and the inverse Wronskian. -/
def localKummerBoundVector
    (X Y : ℝ → KummerODEState) (t : ℝ) :
    ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ :=
  ⟨⟨⟨(X t).2.1, (X t).2.2⟩,
      ⟨(Y t).2.1, (Y t).2.2⟩⟩,
    (localPairWronskian X Y t)⁻¹⟩

theorem exists_uniformlyBounded_localPhysicalKummerPair
    (mu theta z : ℝ) (hz : 0 < z) :
    ∃ (X Y : ℝ → KummerODEState) (eps C : ℝ),
      0 < eps ∧ 0 < C ∧
      X 0 = (z, ((1 : ℂ), 0)) ∧
      Y 0 = (z, (0, (1 : ℂ))) ∧
      (∀ t ∈ Icc (-eps) eps,
        (X t).1 = z + t ∧
        (Y t).1 = z + t ∧
        0 < z + t ∧
        HasDerivAt (fun s : ℝ => (X s).2.1) (X t).2.2 t ∧
        HasDerivAt (fun s : ℝ => (X s).2.2)
          (-(frozenFirstCoeff (z + t) * (X t).2.2 +
            frozenZeroCoeff mu theta * (X t).2.1)) t ∧
        HasDerivAt (fun s : ℝ => (Y s).2.1) (Y t).2.2 t ∧
        HasDerivAt (fun s : ℝ => (Y s).2.2)
          (-(frozenFirstCoeff (z + t) * (Y t).2.2 +
            frozenZeroCoeff mu theta * (Y t).2.1)) t ∧
        localPairWronskian X Y t ≠ 0 ∧
        ‖localKummerBoundVector X Y t‖ ≤ C) := by
  obtain ⟨X, Y, eps0, heps0, hX0, hY0, hprops⟩ :=
    exists_local_physical_nondegenerate_kummer_basis mu theta z hz
  let eps : ℝ := min (eps0 / 2) (z / 4)
  have heps : 0 < eps := by
    dsimp [eps]
    exact lt_min (half_pos heps0) (by positivity)
  have hsubset :
      Icc (-eps) eps ⊆ Ioo (-eps0) eps0 := by
    intro t ht
    have hle : eps ≤ eps0 / 2 := min_le_left _ _
    exact ⟨by linarith [ht.1, heps0], by linarith [ht.2, heps0]⟩
  have hcont :
      ContinuousOn (localKummerBoundVector X Y) (Icc (-eps) eps) := by
    intro t ht
    obtain ⟨_hxt, _hyt, _hpos, hDuX, hDpX, hDuY, hDpY, hW⟩ :=
      hprops t (hsubset ht)
    have hU : ContinuousAt (fun s : ℝ => (X s).2.1) t :=
      hDuX.continuousAt
    have hP : ContinuousAt (fun s : ℝ => (X s).2.2) t :=
      hDpX.continuousAt
    have hV : ContinuousAt (fun s : ℝ => (Y s).2.1) t :=
      hDuY.continuousAt
    have hQ : ContinuousAt (fun s : ℝ => (Y s).2.2) t :=
      hDpY.continuousAt
    have hWcont : ContinuousAt (localPairWronskian X Y) t := by
      unfold localPairWronskian
      exact (hU.mul hQ).sub (hP.mul hV)
    have hinv : ContinuousAt
        (fun s : ℝ => (localPairWronskian X Y s)⁻¹) t :=
      hWcont.inv₀ hW
    exact (((hU.prodMk hP).prodMk (hV.prodMk hQ)).prodMk hinv)
      |>.continuousWithinAt
  obtain ⟨C0, hC0⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hcont
  let C : ℝ := max C0 1
  have hC : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_max_right C0 1)
  refine ⟨X, Y, eps, C, heps, hC, hX0, hY0, ?_⟩
  intro t ht
  obtain ⟨hxt, hyt, htpos, hDuX, hDpX, hDuY, hDpY, hW⟩ :=
    hprops t (hsubset ht)
  exact ⟨hxt, hyt, htpos, hDuX, hDpX, hDuY, hDpY, hW,
    (hC0 t ht).trans (le_max_left C0 1)⟩

#print axioms exists_uniformlyBounded_localPhysicalKummerPair

end HBL.Profile.Kummer
