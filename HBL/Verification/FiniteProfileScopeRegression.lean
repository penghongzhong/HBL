import HBL.FiniteProfile
import HBL.TypeIIDynamicSelection.ActualOneLayerPDEResidual

/-!
Scope regression, NOT a new manuscript proof.

The historical finiteProfile_recursion_certified theorem is a valid
structural theorem. Its inputs do not connect packets or assigned orders
to a physical profile. This regression exhibits its empty-packet outputs
alongside a smooth radial probe with a genuinely nonzero ORIGINAL Hartree
PDE residual at s=0,r=1. It is not a counterexample to the Type-II existence
conjecture or to any correctly stated conditional theorem.

Purpose: prevent a structural CI success from being used as the acceptance
certificate for manuscript 2.13. The missing residual realization must be
proved, not filled by a source-order parameter or a renamed identity map.
-/
noncomputable section
set_option autoImplicit false

namespace HBL.Verification.FiniteProfileScope
open HBL.Profile.OneLayer HBL.Profile.FiniteProfile
open HBL.TypeIIDynamicSelection HBL.Modulation.Monopole

/-- The cutoff is constant near zero and vanishes beyond radius two.
At time zero this probe is identically zero, but its time derivative is not. -/
def radialProbe (s r : ℝ) : ℂ :=
  (s : ℂ) * actualOneLayerInnerOverlapCutoff 1 r

/-- The ORIGINAL residual is nonzero; no surrogate residual is introduced. -/
theorem radialProbe_original_residual :
    complexRadialRenormalizedResidual radialProbe 0 0 0 1 = Complex.I := by
  have hc : actualOneLayerInnerOverlapCutoff 1 1 = (1 : ℂ) := by
    norm_num [actualOneLayerInnerOverlapCutoff,
      HBL.Modulation.AffineTail.cutoff_zero_of_le_one]
  have ht : HasDerivAt (fun s : ℝ => radialProbe s 1) (1 : ℂ) 0 := by
    simpa only [radialProbe, hc, mul_one] using
      (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hz : radialProbe 0 = (fun _ : ℝ => (0 : ℂ)) := by
    funext r
    simp only [radialProbe, Complex.ofReal_zero, zero_mul]
  unfold complexRadialRenormalizedResidual
  rw [ht.deriv, hz]
  simp [complexRadialLaplacian, complexRadialDilation,
    complexRadialHartreeNonlinearity]

/-- All recursive bookkeeping outputs coexist with an unrelated nonzero
actual PDE residual. No solver or generated term is even needed by the
empty packet list. Hence these outputs ALONE cannot be an acceptance gate
for the actual finite-profile construction. -/
theorem structural_terminal_allows_empty_packets_and_nonzero_residual
    (P : GainParameters) (N : ℝ) :
    (∃ Vcorr : ℂ, Vcorr = finiteProfileCorrection P []) ∧
    (∀ q ∈ ([] : List (Σ rho : ℝ, LayerPacket ℂ P rho)),
      PacketCertified q.2) ∧
    (∃ J : ℕ, N ≤ (J : ℝ) * kappaProfile P) ∧
    complexRadialRenormalizedResidual radialProbe 0 0 0 1 ≠ 0 := by
  let rho : ℕ → ℝ := fun j => (j : ℝ) * kappaProfile P
  have hstep : ∀ j : ℕ, rho j + kappaProfile P ≤ rho (j + 1) := by
    intro j
    dsimp [rho]
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith
  have h := finiteProfile_recursion_certified (E := ℂ)
    P [] rho N 1 1 1 0 0 hstep
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · simpa only [rho] using h.2.2.1
  · rw [radialProbe_original_residual]
    exact Complex.I_ne_zero

end HBL.Verification.FiniteProfileScope
