import HBL.AffineTailPVWeightDecomposition

/-!
A single explicit primitive for the weighted rational kernel produced by
the affine logarithmic integration-by-parts identity.

The already verified finite-interval decomposition shows that
  (2r/(r^2-rho^2)) P(rho)
is the sum of two regular rational kernels and one simple Cauchy kernel.
We package the corresponding primitives into one scalar function.  Its
far-end limit and symmetric jump are then immediate from the previously
verified arctangent, second-rational, and PV primitive limits.
-/

noncomputable section

open Filter
open scoped Topology

namespace HBL.Modulation.AffineTail

/-- Unified primitive for the weighted rational derivative term. -/
def affinePVWeightedPrimitive (r rho : ℝ) : ℝ :=
  (r / 2) *
    ((r ^ 2 / (1 + r ^ 2) ^ 2) * Real.arctan rho -
      (1 / (1 + r ^ 2)) * secondRationalPrimitive rho +
      (r ^ 2 / (1 + r ^ 2) ^ 2) *
        pvRationalPrimitive r rho)

/-- The unified primitive differentiates to the exact weighted kernel
away from the two simple poles. -/
theorem affinePVWeightedPrimitive_hasDerivAt
    (r rho : ℝ) (hr : r ≠ 0)
    (hp : r + rho ≠ 0) (hm : r - rho ≠ 0) :
    HasDerivAt (affinePVWeightedPrimitive r)
      ((2 * r / (r ^ 2 - rho ^ 2)) * radialLogPrimitive rho) rho := by
  let A : ℝ := r ^ 2 / (1 + r ^ 2) ^ 2
  let B : ℝ := 1 / (1 + r ^ 2)
  have hA := (Real.hasDerivAt_arctan' rho).const_mul A
  have hB := (secondRationalPrimitive_hasDerivAt rho).const_mul B
  have hC :=
    (pvRationalPrimitive_hasDerivAt r rho hr hp hm).const_mul A
  have hsum := (hA.sub hB).add hC
  have hscaled := hsum.const_mul (r / 2)
  convert hscaled using 1
  · funext x
    change
      (r / 2) *
        ((r ^ 2 / (1 + r ^ 2) ^ 2) * Real.arctan x -
          (1 / (1 + r ^ 2)) * secondRationalPrimitive x +
          (r ^ 2 / (1 + r ^ 2) ^ 2) *
            pvRationalPrimitive r x) =
      (r / 2) *
        (A * Real.arctan x -
          B * secondRationalPrimitive x +
          A * pvRationalPrimitive r x)
    rfl
  · have hsep : r ^ 2 - rho ^ 2 ≠ 0 := by
      intro hz
      have hz' : (r + rho) * (r - rho) = 0 := by nlinarith [hz]
      exact (mul_ne_zero hp hm) hz'
    simpa only [A, B] using
      (pv_weight_decomposition r rho hsep)

@[simp]
theorem affinePVWeightedPrimitive_zero (r : ℝ) :
    affinePVWeightedPrimitive r 0 = 0 := by
  simp [affinePVWeightedPrimitive, secondRationalPrimitive,
    pvRationalPrimitive]

/-- Far-end value of the complete weighted rational primitive. -/
theorem affinePVWeightedPrimitive_tendsto_atTop
    (r : ℝ) (hr : 0 < r) :
    Tendsto (affinePVWeightedPrimitive r) atTop
      (𝓝 (Real.pi * r * (r ^ 2 - 1) /
        (8 * (1 + r ^ 2) ^ 2))) := by
  let A : ℝ := r ^ 2 / (1 + r ^ 2) ^ 2
  let B : ℝ := 1 / (1 + r ^ 2)
  have ha : Tendsto Real.arctan atTop
      (𝓝 (Real.pi / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop
  have hA := ha.const_mul A
  have hB := secondRationalPrimitive_tendsto_pi_div_four.const_mul B
  have hC := (pvRationalPrimitive_tendsto_zero_atTop r hr).const_mul A
  have hsum := (hA.sub hB).add hC
  have hscaled := hsum.const_mul (r / 2)
  have hden : (1 + r ^ 2 : ℝ) ≠ 0 := by positivity
  have hval :
      (r / 2) *
        (A * (Real.pi / 2) - B * (Real.pi / 4) + A * 0) =
      Real.pi * r * (r ^ 2 - 1) /
        (8 * (1 + r ^ 2) ^ 2) := by
    dsimp [A, B]
    field_simp [hden]
    ring
  rw [hval] at hscaled
  convert hscaled using 1
  funext x
  change
    (r / 2) *
      ((r ^ 2 / (1 + r ^ 2) ^ 2) * Real.arctan x -
        (1 / (1 + r ^ 2)) * secondRationalPrimitive x +
        (r ^ 2 / (1 + r ^ 2) ^ 2) *
          pvRationalPrimitive r x) =
    (r / 2) *
      (A * Real.arctan x -
        B * secondRationalPrimitive x +
        A * pvRationalPrimitive r x)
  rfl

/-- The symmetric jump of the complete primitive at rho=r vanishes.
The singular part cancels in principal value and the two regular parts
cancel by ordinary continuity. -/
theorem affinePVWeightedPrimitive_gap_tendsto_zero
    (r : ℝ) (hr : 0 < r) :
    Tendsto
      (fun e : ℝ =>
        affinePVWeightedPrimitive r (r - e) -
          affinePVWeightedPrimitive r (r + e))
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  let A : ℝ := r ^ 2 / (1 + r ^ 2) ^ 2
  let B : ℝ := 1 / (1 + r ^ 2)
  have hargL :
      Tendsto (fun e : ℝ => r - e) (𝓝 0) (𝓝 r) := by
    have h : ContinuousAt (fun e : ℝ => r - e) 0 := by fun_prop
    simpa using h.tendsto
  have hargR :
      Tendsto (fun e : ℝ => r + e) (𝓝 0) (𝓝 r) := by
    have h : ContinuousAt (fun e : ℝ => r + e) 0 := by fun_prop
    simpa using h.tendsto
  have hArcL :=
    Real.continuous_arctan.continuousAt.tendsto.comp hargL
  have hArcR :=
    Real.continuous_arctan.continuousAt.tendsto.comp hargR
  have hArc :
      Tendsto
        (fun e : ℝ =>
          Real.arctan (r - e) - Real.arctan (r + e))
        (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using hArcL.sub hArcR
  have hSecL :=
    (secondRationalPrimitive_hasDerivAt r).continuousAt.tendsto.comp hargL
  have hSecR :=
    (secondRationalPrimitive_hasDerivAt r).continuousAt.tendsto.comp hargR
  have hSec :
      Tendsto
        (fun e : ℝ =>
          secondRationalPrimitive (r - e) -
            secondRationalPrimitive (r + e))
        (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using hSecL.sub hSecR
  have hPV :=
    symmetricPV_primitive_gap_tendsto_zero r hr
  have hcomb :=
    ((hArc.const_mul A).sub (hSec.const_mul B)).add
      (hPV.const_mul A)
  have hscaled := hcomb.const_mul (r / 2)
  have hscaled0 :
      Tendsto
        (fun e : ℝ =>
          (r / 2) *
            (A * (Real.arctan (r - e) - Real.arctan (r + e)) -
              B * (secondRationalPrimitive (r - e) -
                secondRationalPrimitive (r + e)) +
              A * (pvRationalPrimitive r (r - e) -
                pvRationalPrimitive r (r + e))))
        (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hscaled
  convert hscaled0 using 1
  funext e
  dsimp [affinePVWeightedPrimitive, A, B]
  ring

end HBL.Modulation.AffineTail
