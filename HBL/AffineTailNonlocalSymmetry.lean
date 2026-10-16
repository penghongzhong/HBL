import HBL.AffineTailGreenLocal
import Mathlib.MeasureTheory.Integral.Prod

/-!
Nonlocal symmetry step for the real-channel affine-tail Green identity.

For a symmetric kernel K and absolutely integrable bilinear density
  psi(r) K(r,rho) q(rho),
Fubini gives the exact full-line cancellation
  integral psi(r) (T q)(r) dr
    = integral q(r) (T psi)(r) dr.

This is intentionally a full-space statement.  It is the rigorous
replacement for dropping the nonlocal term inside a finite-R Green identity.
-/

noncomputable section

open MeasureTheory

namespace HBL.Modulation.AffineTail

/-- Fubini plus kernel symmetry gives the exact nonlocal pairing symmetry. -/
theorem symmetricKernel_pairing
    {α : Type*} [MeasurableSpace α]
    (mu : Measure α) [SigmaFinite mu]
    (K : α → α → ℝ) (psi q : α → ℝ)
    (hKsym : ∀ x y, K x y = K y x)
    (hint : Integrable
      (Function.uncurry (fun x y => psi x * K x y * q y))
      (mu.prod mu)) :
    (∫ x, psi x * (∫ y, K x y * q y ∂mu) ∂mu) =
      ∫ y, q y * (∫ x, K y x * psi x ∂mu) ∂mu := by
  have hswap :=
    MeasureTheory.integral_integral_swap hint
  calc
    (∫ x, psi x * (∫ y, K x y * q y ∂mu) ∂mu) =
        ∫ x, ∫ y, psi x * K x y * q y ∂mu ∂mu := by
          apply integral_congr_ae
          filter_upwards with x
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with y
          ring
    _ = ∫ y, ∫ x, psi x * K x y * q y ∂mu ∂mu := hswap
    _ = ∫ y, q y * (∫ x, K y x * psi x ∂mu) ∂mu := by
          apply integral_congr_ae
          filter_upwards with y
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with x
          rw [hKsym x y]
          ring

/-- Equivalent vanishing of the nonlocal commutator pairing. -/
theorem symmetricKernel_commutator_zero
    {α : Type*} [MeasurableSpace α]
    (mu : Measure α) [SigmaFinite mu]
    (K : α → α → ℝ) (psi q : α → ℝ)
    (hKsym : ∀ x y, K x y = K y x)
    (hint : Integrable
      (Function.uncurry (fun x y => psi x * K x y * q y))
      (mu.prod mu)) :
    (∫ x, psi x * (∫ y, K x y * q y ∂mu) ∂mu) -
      (∫ y, q y * (∫ x, K y x * psi x ∂mu) ∂mu) = 0 := by
  rw [symmetricKernel_pairing mu K psi q hKsym hint]
  exact sub_self _

end HBL.Modulation.AffineTail
