import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedMatchedKummerClassical
import Mathlib.Tactic

/-!
# True matched Kummer spectral correction with the original Fredholm left jet

The isolated Green correction G₀[dG₀[F]] changes the left C¹ transmission
data. Here we correct the COMPLETE matched solution w₀, not just G₀[F].
Let q=d w₀ and let w₁ be the genuine origin Kummer solution of L₀w₁=q
with ZERO value and slope at the original left interface.

Then w=w₀-w₁ preserves BOTH original Fredholm left Cauchy coordinates and
satisfies the exact variable-spectral equation L_d w = F-dw₁, so the
first-order spectral error cancels. Its upper outgoing defect is identified
exactly as -Obstruction[q,0,0], which must be removed by a further
compatibility selection rather than simply declared zero.

No artificial independent boundary traces, inverse operator, rate,
uniform shrinking-annulus basis or full nonlinear PDE residual is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- The source for the first spectral correction is the complete matched
Kummer profile, including its forced regular homogeneous coefficient. -/
def actualHartreeMatchedSpectralFirstSource
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b : ℝ) (F : ℝ → ℂ) (U DU d : ℂ) (r : ℝ) : ℂ :=
  d * actualOriginMatchedKummerValue K a b F U DU r

/-- Corrected Kummer field: subtract the REAL original Green/Cramer solve
with zero initial Cauchy jet, preserving both physical Fredholm traces. -/
def actualHartreeMatchedSpectralCorrectedValue
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b : ℝ) (F : ℝ → ℂ) (U DU d : ℂ) (r : ℝ) : ℂ :=
  actualOriginMatchedKummerValue K a b F U DU r -
    actualOriginMatchedKummerValue K a b
      (actualHartreeMatchedSpectralFirstSource K a b F U DU d) 0 0 r

/-- Genuine original Kummer differential equation and EXACT preserved
left value/slope after one nontrivial matched spectral correction.
The missing upper outgoing condition is intentionally not assumed. -/
theorem actual_Hartree_matched_spectral_corrected_left_C1_and_exact_equation
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < scale)
    (F : ℝ → ℂ) (hF : ∀ r ∈ Ioo 0 scale, ContinuousAt F r)
    (U DU d : ℂ) :
    let q := actualHartreeMatchedSpectralFirstSource K a b F U DU d
    let w1 := actualOriginMatchedKummerValue K a b q 0 0
    let v := actualHartreeMatchedSpectralCorrectedValue K a b F U DU d
    v a = U ∧ HasDerivAt v DU a ∧
      ∀ r ∈ Ioo 0 scale,
        deriv (deriv v) r + frozenFirstCoeff r * deriv v r +
          (frozenZeroCoeff mu theta + d) * v r = F r - d * w1 r := by
  dsimp only
  let u : ℝ → ℂ := actualOriginMatchedKummerValue K a b F U DU
  let q : ℝ → ℂ := actualHartreeMatchedSpectralFirstSource K a b F U DU d
  let w1 : ℝ → ℂ := actualOriginMatchedKummerValue K a b q 0 0
  let v : ℝ → ℂ := actualHartreeMatchedSpectralCorrectedValue K a b F U DU d
  have hU := actual_origin_matched_Kummer_classical_on_positive_interval
      K ha hab hb F hF U DU
  have hQcont : ∀ r ∈ Ioo 0 scale, ContinuousAt q r := by
    intro r hr
    have hu : ContinuousAt u r := (hU r hr).1.continuousAt
    simpa only [q, actualHartreeMatchedSpectralFirstSource, u] using
      (continuousAt_const.mul hu : ContinuousAt (fun x : ℝ => d * u x) r)
  have hW := actual_origin_matched_Kummer_classical_on_positive_interval
      K ha hab hb q hQcont 0 0
  have hLeftU := actual_origin_matched_Kummer_actual_endpoint_jets
      K ha hab hb F hF U DU
  have hLeftW := actual_origin_matched_Kummer_actual_endpoint_jets
      K ha hab hb q hQcont 0 0
  have hVdef : ∀ r, v r = u r - w1 r := by intro r; rfl
  have hDeriv (r : ℝ) (hr : r ∈ Ioo 0 scale) :
      deriv v r = deriv u r - deriv w1 r := by
    have hDer : HasDerivAt (fun t => u t - w1 t)
        (actualOriginMatchedKummerSlope K a b F U DU r -
         actualOriginMatchedKummerSlope K a b q 0 0 r) r :=
      (hU r hr).1.sub (hW r hr).1
    have hEq : v = (fun t => u t - w1 t) := by funext t; rfl
    rw [hEq]
    rw [hDer.deriv, (hU r hr).1.deriv, (hW r hr).1.deriv]
  have hSecond (r : ℝ) (hr : r ∈ Ioo 0 scale) :
      deriv (deriv v) r = deriv (deriv u) r - deriv (deriv w1) r := by
    have hNear : deriv v =ᶠ[𝓝 r] (fun t => deriv u t - deriv w1 t) := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
      exact hDeriv t ht
    have hDiff := (hU r hr).2.1.sub (hW r hr).2.1
    exact (hDiff.congr_of_eventuallyEq hNear).deriv
  have hLeftV : v a = U := by
    rw [hVdef a, hLeftU.1, hLeftW.1]
    simp
  have hLeftD : HasDerivAt v DU a := by
    have hv : HasDerivAt (fun t => u t - w1 t) (DU - 0) a :=
      hLeftU.2.1.sub hLeftW.2.1
    have hEq : v = (fun t => u t - w1 t) := by funext t; rfl
    rw [hEq]
    simpa only [sub_zero] using hv
  refine ⟨hLeftV, hLeftD, ?_⟩
  intro r hr
  have h0 := (hU r hr).2.2
  have h1 := (hW r hr).2.2
  change deriv (deriv v) r + frozenFirstCoeff r * deriv v r +
    (frozenZeroCoeff mu theta + d) * v r = F r - d * w1 r
  rw [hSecond r hr, hDeriv r hr, hVdef r]
  have hq : q r = d * u r := rfl
  calc
    deriv (deriv u) r - deriv (deriv w1) r +
        frozenFirstCoeff r * (deriv u r - deriv w1 r) +
        (frozenZeroCoeff mu theta + d) * (u r - w1 r)
        =
        (deriv (deriv u) r + frozenFirstCoeff r * deriv u r +
           frozenZeroCoeff mu theta * u r) -
        (deriv (deriv w1) r + frozenFirstCoeff r * deriv w1 r +
           frozenZeroCoeff mu theta * w1 r) + d * (u r - w1 r) := by ring
    _ = F r - q r + d * (u r - w1 r) := by rw [h0,h1]
    _ = F r - d * w1 r := by rw [hq]; ring

/-- Exact upper outgoing defect caused by this boundary-preserving matched
spectral correction. The defect is not discarded: the matching speed must
be selected again if this scalar is nonzero. -/
theorem actual_Hartree_matched_spectral_upper_defect_exact
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < scale)
    (F : ℝ → ℂ) (hF : ∀ r ∈ Ioo 0 scale, ContinuousAt F r)
    (U DU d : ℂ)
    (hCompatible : actualMomentLockedIntervalObstruction K a b F U DU = 0) :
    let q := actualHartreeMatchedSpectralFirstSource K a b F U DU d
    let v := actualHartreeMatchedSpectralCorrectedValue K a b F U DU d
    actualOriginOutgoingTrace K b (v b) (deriv v b) =
      -actualMomentLockedIntervalObstruction K a b q 0 0 := by
  dsimp only
  let u : ℝ → ℂ := actualOriginMatchedKummerValue K a b F U DU
  let q : ℝ → ℂ := actualHartreeMatchedSpectralFirstSource K a b F U DU d
  let w1 : ℝ → ℂ := actualOriginMatchedKummerValue K a b q 0 0
  let v : ℝ → ℂ := actualHartreeMatchedSpectralCorrectedValue K a b F U DU d
  have hU := actual_origin_matched_Kummer_classical_on_positive_interval
      K ha hab hb F hF U DU
  have hQcont : ∀ r ∈ Ioo 0 scale, ContinuousAt q r := by
    intro r hr
    have hu : ContinuousAt u r := (hU r hr).1.continuousAt
    simpa only [q, actualHartreeMatchedSpectralFirstSource, u] using
      (continuousAt_const.mul hu : ContinuousAt (fun x : ℝ => d * u x) r)
  have hW := actual_origin_matched_Kummer_classical_on_positive_interval
      K ha hab hb q hQcont 0 0
  have hbIn : b ∈ Ioo 0 scale := ⟨ha.trans_le hab, hb⟩
  have hDeriv : deriv v b = deriv u b - deriv w1 b := by
    have hDer : HasDerivAt (fun t => u t - w1 t)
        (actualOriginMatchedKummerSlope K a b F U DU b -
          actualOriginMatchedKummerSlope K a b q 0 0 b) b :=
      (hU b hbIn).1.sub (hW b hbIn).1
    have hEq : v = (fun t => u t - w1 t) := by funext t; rfl
    rw [hEq]
    rw [hDer.deriv, (hU b hbIn).1.deriv, (hW b hbIn).1.deriv]
  have hOriginal :=
    actual_origin_matched_Kummer_actual_upper_trace K ha hab hb F hF U DU
  have hCorrection :=
    actual_origin_matched_Kummer_actual_upper_trace K ha hab hb q hQcont 0 0
  have hvValue : v b = u b - w1 b := rfl
  rw [hvValue, hDeriv]
  calc
    actualOriginOutgoingTrace K b (u b - w1 b)
      (deriv u b - deriv w1 b) =
      actualOriginOutgoingTrace K b (u b) (deriv u b) -
        actualOriginOutgoingTrace K b (w1 b) (deriv w1 b) := by
        unfold actualOriginOutgoingTrace
        ring
    _ = actualMomentLockedIntervalObstruction K a b F U DU -
          actualMomentLockedIntervalObstruction K a b q 0 0 := by
          rw [hOriginal, hCorrection]
    _ = -actualMomentLockedIntervalObstruction K a b q 0 0 := by
          rw [hCompatible]
          ring

end HBL.TypeIIDynamicSelection
