import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedMatchedKummer
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Time derivative of the forced regular origin coefficient

The regular coefficient in the matched origin-gauge Kummer solution is
source-independent after the Green endpoint normalization:
  beta_reg = (y(r0) DU - y'(r0) U) / W(r0).

Hence its time derivative does not require differentiating the outer source.
It depends only on the moving lower interface and the actual lower Cauchy
jet.  This is the Fredholm/regular part of the scalar gamma derivative used
by the upper Kummer jet.

The remaining source-dependent part of gamma is exactly
  originGreenCoeffB K r0 F B
and is handled separately.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

def actualOriginRegularCoeffFromMovingJet
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (r0 : ℝ → ℝ) (U DU : ℝ → ℂ) (t : ℝ) : ℂ :=
  (originPhysicalValue K.y (r0 t) * DU t -
      originPhysicalSlope K.y K.dy (r0 t) * U t) /
    originGreenWronskian K (r0 t)

def actualOriginRegularCoeffFromMovingJetDot
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (r0 : ℝ → ℝ) (U DU : ℝ → ℂ)
    (s r0dot : ℝ) (Udot DUdot : ℂ) : ℂ :=
  let r := r0 s
  let Y := originPhysicalValue K.y r
  let Yp := originPhysicalSlope K.y K.dy r
  let Ypp := -(frozenFirstCoeff r * Yp +
    frozenZeroCoeff mu theta * Y)
  let W := originGreenWronskian K r
  let Wp := -(frozenFirstCoeff r * W)
  let N := Y * DU s - Yp * U s
  let Ndot := (r0dot • Yp) * DU s + Y * DUdot -
    ((r0dot • Ypp) * U s + Yp * Udot)
  let Wdot := r0dot • Wp
  (Ndot * W - N * Wdot) / W ^ 2

theorem actual_origin_regular_coeff_from_moving_jet_hasDerivAt
    {mu theta scale lo hi C : ℝ}
    (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K lo hi C)
    (r0 : ℝ → ℝ) (U DU : ℝ → ℂ)
    (s r0dot : ℝ) (Udot DUdot : ℂ)
    (hr : r0 s ∈ Ioo lo hi)
    (hr0 : HasDerivAt r0 r0dot s)
    (hU : HasDerivAt U Udot s)
    (hDU : HasDerivAt DU DUdot s) :
    HasDerivAt
      (actualOriginRegularCoeffFromMovingJet K r0 U DU)
      (actualOriginRegularCoeffFromMovingJetDot
        K r0 U DU s r0dot Udot DUdot) s := by
  let r := r0 s
  have hrcc : r ∈ Icc lo hi := ⟨hr.1.le, hr.2.le⟩
  obtain ⟨hY0,hYp0,hX0,hXp0,_hWexact,hWne,
    _hYb,_hYpb,_hXb,_hXpb,_hWinv⟩ := hK r hrcc
  have hY := hY0.scomp s hr0
  have hYp := hYp0.scomp s hr0
  have hX := hX0.scomp s hr0
  have hXp := hXp0.scomp s hr0
  let Wfun : ℝ → ℂ := fun t => originGreenWronskian K (r0 t)
  have hWsp :
      HasDerivAt (originGreenWronskian K)
        (-(frozenFirstCoeff r * originGreenWronskian K r)) r := by
    unfold originGreenWronskian
    have h0 := (hY0.mul hXp0).sub (hYp0.mul hX0)
    convert h0 using 1
    ring
  have hW :
      HasDerivAt Wfun
        (r0dot • (-(frozenFirstCoeff r * originGreenWronskian K r))) s := by
    dsimp [Wfun]
    exact hWsp.scomp s hr0
  let Nfun : ℝ → ℂ :=
    (originPhysicalValue K.y ∘ r0) * DU -
      (originPhysicalSlope K.y K.dy ∘ r0) * U
  have hN :=
    (hY.mul hDU).sub (hYp.mul hU)
  have hDiv := hN.div hW hWne
  have hFun :
      actualOriginRegularCoeffFromMovingJet K r0 U DU =
        Nfun / Wfun := by
    funext t
    rfl
  rw [hFun]
  convert hDiv using 1
  · rfl
  · dsimp [actualOriginRegularCoeffFromMovingJetDot, Nfun, Wfun, r]
    ring

/-- The source appearing in the matched Kummer formula is irrelevant for
the regular coefficient derivative: the exact Green normalization removes
it pointwise before differentiation. -/
theorem actual_origin_matched_regular_coeff_moving_hasDerivAt
    {mu theta scale lo hi : ℝ}
    (K : OriginKummerPair mu theta scale)
    (C B : ℝ) (hK : OriginBasisOn K lo hi C)
    (r0 : ℝ → ℝ) (F : ℝ → ℝ → ℂ)
    (U DU : ℝ → ℂ)
    (s r0dot : ℝ) (Udot DUdot : ℂ)
    (hr : r0 s ∈ Ioo lo hi)
    (hr0 : HasDerivAt r0 r0dot s)
    (hU : HasDerivAt U Udot s)
    (hDU : HasDerivAt DU DUdot s) :
    HasDerivAt
      (fun t =>
        actualOriginMatchedRegularCoeff K (r0 t) B (F t) (U t) (DU t))
      (actualOriginRegularCoeffFromMovingJetDot
        K r0 U DU s r0dot Udot DUdot) s := by
  have hbase :=
    actual_origin_regular_coeff_from_moving_jet_hasDerivAt
      K hK r0 U DU s r0dot Udot DUdot hr hr0 hU hDU
  have heq :
      (fun t =>
        actualOriginMatchedRegularCoeff K (r0 t) B (F t) (U t) (DU t)) =
      actualOriginRegularCoeffFromMovingJet K r0 U DU := by
    funext t
    rw [actual_origin_matched_Kummer_regular_coefficient]
    rfl
  rw [heq]
  exact hbase

end HBL.TypeIIDynamicSelection
