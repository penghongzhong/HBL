import HBL.AffineTailPVFiniteAssembly

/-!
Exact symmetric cutoff factorization for the rational Hartree primitive.

The factorization proves that the singular logarithmic boundary term
contains epsilon * log(epsilon), which tends to zero. The rational
coefficient is continuous and has no pole at epsilon=0.
-/

noncomputable section
open Filter
open scoped Topology

namespace HBL.Modulation.AffineTail

/-- Regular rational coefficient in the symmetric primitive difference. -/
def symmetricPrimitiveSlope (r e : ℝ) : ℝ :=
  r * (r ^ 2 - e ^ 2 - 1) * (r ^ 2 - e ^ 2 + 1) /
    ((1 + (r - e) ^ 2) ^ 2 * (1 + (r + e) ^ 2) ^ 2)

/-- The difference of the rational primitives is exactly O(epsilon). -/
theorem radialLogPrimitive_symmetric_gap_factor (r e : ℝ) :
    radialLogPrimitive (r - e) - radialLogPrimitive (r + e) =
      e * symmetricPrimitiveSlope r e := by
  have hm : (1 + (r - e) ^ 2 : ℝ) ≠ 0 := by positivity
  have hp : (1 + (r + e) ^ 2 : ℝ) ≠ 0 := by positivity
  unfold radialLogPrimitive symmetricPrimitiveSlope
  field_simp [hm, hp] <;> ring

/-- This coefficient is continuous across the collapsed exclusion gap. -/
theorem symmetricPrimitiveSlope_continuous (r : ℝ) :
    Continuous (symmetricPrimitiveSlope r) := by
  unfold symmetricPrimitiveSlope
  fun_prop (discharger := intro; positivity)

/-- The logarithmically singular part has a vanishing boundary jump. -/
theorem radialLogPrimitive_log_gap_tendsto_zero (r : ℝ) :
    Tendsto
      (fun e : ℝ =>
        (radialLogPrimitive (r - e) -
          radialLogPrimitive (r + e)) * Real.log e)
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hco := (symmetricPrimitiveSlope_continuous r).continuousAt.tendsto
  have hlim :
      Tendsto
        (fun e : ℝ =>
          (e * Real.log e) * symmetricPrimitiveSlope r e)
        (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := logBoundary_tendsto_zero.mul hco
    simpa only [zero_mul] using h
  apply hlim.congr'
  exact Filter.Eventually.of_forall (fun e : ℝ => by
    rw [radialLogPrimitive_symmetric_gap_factor]
    ring)

end HBL.Modulation.AffineTail
