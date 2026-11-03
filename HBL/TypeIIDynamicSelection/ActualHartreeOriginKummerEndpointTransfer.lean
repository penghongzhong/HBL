import HBL.KummerOriginBasis.CompactBasis
import HBL.KummerOriginBasis.PhysicalWronskian
import HBL.RadialHartreeBubbleBound
import Mathlib.Tactic

/-!
# HBL revised 2.13: origin-normalized Kummer source and center-Green endpoint transfer

The physical Kummer origin basis (Phi,Psi) and its exactly normalized,
nonzero radial Wronskian have already been constructed and audited.
The genuine Green source is F(r)/Wronskian(r), not an independently
chosen homogeneous correction.

For ANY positive-annulus source whose four interval integrals
actually converge, the original two-boundary Green is the
center-Cauchy Green PLUS TWO EXPLICIT homogeneous solutions:
  G_ab(F)(r)-G_mm(F)(r)
     = Phi(r)*int_m^b Psi(s) F(s)/W(s) ds
       + Psi(r)*int_a^m Phi(s) F(s)/W(s) ds.

This follows from exact oriented interval-integral splitting,
without asymptotic surrogates or invented matching constants.
The endpoint coefficients are determined by the SAME physical source,
not postulated free parameters. No Type-II time rate is assumed.

This is the missing algebraic boundary-normalization bridge,
NOT by itself proof of far-endpoint trace estimates or the full
finite-profile theorem; revised 2.13 remains OPEN until those
actual PDE quantitative and nonlinear recursion steps are established.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- The physical origin-normalized Kummer Wronskian is explicitly
nonzero at every positive radial point in the constructed basis
domain. This prevents introducing free homogeneous matching data. -/
theorem actual_origin_Kummer_physical_Wronskian_ne_zero
    {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R)
    (r : ℝ) (hr : r ∈ Icc 0 R) (hr0 : r ≠ 0) :
    originPhysicalValue K.y r * originPhysicalSlope K.x K.dx r -
      originPhysicalSlope K.y K.dy r * originPhysicalValue K.x r ≠ 0 := by
  rw [origin_physical_wronskian_exact K hr hr0]
  have hn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hn))
    (Complex.exp_ne_zero _)

/-- The true physical variation-of-parameters source, always using
the ORIGINAL origin-normalized Wronskian. -/
def actualOriginKummerPhysicalGreenDensity
    {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R)
    (F : ℝ → ℂ) (s : ℝ) : ℂ :=
  F s / (originPhysicalValue K.y s * originPhysicalSlope K.x K.dx s -
    originPhysicalSlope K.y K.dy s * originPhysicalValue K.x s)

/-- The original TWO-ENDPOINT Kummer Green source with its actual
origin-normalized singular and regular basis. -/
def actualOriginKummerTwoEndpointGreen
    {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R)
    (g : ℝ → ℂ) (a b r : ℝ) : ℂ :=
  originPhysicalValue K.y r *
      (∫ s in r..b, originPhysicalValue K.x s * g s) +
  originPhysicalValue K.x r *
      (∫ s in a..r, originPhysicalValue K.y s * g s)

/-- Its Cauchy-normalized counterpart about an arbitrary interface m. -/
def actualOriginKummerCenterGreen
    {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R)
    (g : ℝ → ℂ) (m r : ℝ) : ℂ :=
  originPhysicalValue K.y r *
      (∫ s in r..m, originPhysicalValue K.x s * g s) +
  originPhysicalValue K.x r *
      (∫ s in m..r, originPhysicalValue K.y s * g s)

/-- Exact physical two-endpoint minus center-Green transfer, with BOTH
endpoint coefficients computed from the identical original source.
There is no assumed matching coefficient. In particular, the
center-Cauchy solution is not falsely substituted for the manuscript's
origin/outgoing Green. -/
theorem actual_origin_Kummer_two_endpoint_center_Green_transfer
    {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R)
    (g : ℝ → ℂ) (a m b r : ℝ)
    (hPsiRM : IntervalIntegrable
      (fun s : ℝ => originPhysicalValue K.x s * g s) volume r m)
    (hPsiMB : IntervalIntegrable
      (fun s : ℝ => originPhysicalValue K.x s * g s) volume m b)
    (hPhiAM : IntervalIntegrable
      (fun s : ℝ => originPhysicalValue K.y s * g s) volume a m)
    (hPhiMR : IntervalIntegrable
      (fun s : ℝ => originPhysicalValue K.y s * g s) volume m r) :
    actualOriginKummerTwoEndpointGreen K g a b r -
        actualOriginKummerCenterGreen K g m r =
      originPhysicalValue K.y r *
        (∫ s in m..b, originPhysicalValue K.x s * g s) +
      originPhysicalValue K.x r *
        (∫ s in a..m, originPhysicalValue K.y s * g s) := by
  have hPsi : (∫ s in r..b, originPhysicalValue K.x s * g s) =
      (∫ s in r..m, originPhysicalValue K.x s * g s) +
      (∫ s in m..b, originPhysicalValue K.x s * g s) :=
    (intervalIntegral.integral_add_adjacent_intervals hPsiRM hPsiMB).symm
  have hPhi : (∫ s in a..r, originPhysicalValue K.y s * g s) =
      (∫ s in a..m, originPhysicalValue K.y s * g s) +
      (∫ s in m..r, originPhysicalValue K.y s * g s) :=
    (intervalIntegral.integral_add_adjacent_intervals hPhiAM hPhiMR).symm
  unfold actualOriginKummerTwoEndpointGreen actualOriginKummerCenterGreen
  rw [hPsi, hPhi]
  ring

end HBL.TypeIIDynamicSelection
