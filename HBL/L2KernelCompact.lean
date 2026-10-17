import HBL.L2KernelOperator
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
Compactness of the operator associated with an `L²` kernel.

The proof is measure-theoretic: finite unions of measurable rectangles are
dense in the product measure algebra, their indicators are finite sums of
product vectors, and the kernel-to-operator map is norm-continuous.
-/

noncomputable section

open MeasureTheory MeasurableSpace Set ENNReal Real TopologicalSpace
open scoped ENNReal symmDiff

namespace HBL.L2Kernel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]

/-- Measurable rectangles in the square of the underlying measure space. -/
def measurableRectangles : Set (Set (α × α)) :=
  Set.image2 (· ×ˢ ·) {s : Set α | MeasurableSet s}
    {t : Set α | MeasurableSet t}

theorem measurableRectangles_generate :
    MeasurableSpace.generateFrom (measurableRectangles (α := α)) =
      Prod.instMeasurableSpace := by
  exact generateFrom_prod

theorem measurableRectangles_measurable {q : Set (α × α)}
    (hq : q ∈ measurableRectangles (α := α)) : MeasurableSet q := by
  rcases hq with ⟨s, hs, t, ht, rfl⟩
  exact hs.prod ht

theorem measurableRectangles_isSetSemiring :
    IsSetSemiring (measurableRectangles (α := α)) where
  empty_mem := by
    exact ⟨∅, MeasurableSet.empty, ∅, MeasurableSet.empty, by simp⟩
  inter_mem := by
    rintro _ ⟨s, hs, t, ht, rfl⟩ _ ⟨u, hu, v, hv, rfl⟩
    refine ⟨s ∩ u, hs.inter hu, t ∩ v, ht.inter hv, ?_⟩
    ext p
    simp only [mem_inter_iff, mem_prod]
    tauto
  sdiff_eq_sUnion' := by
    rintro _ ⟨s, hs, t, ht, rfl⟩ _ ⟨u, hu, v, hv, rfl⟩
    let A : Set (α × α) := s ×ˢ (t \ v)
    let B : Set (α × α) := (s \ u) ×ˢ (t ∩ v)
    refine ⟨{A, B}, ?_, ?_, ?_⟩
    · intro q hq
      simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
        mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · exact ⟨s, hs, t \ v, ht.diff hv, rfl⟩
      · exact ⟨s \ u, hs.diff hu, t ∩ v, ht.inter hv, rfl⟩
    · simp only [Finset.coe_insert, Finset.coe_singleton]
      rw [pairwiseDisjoint_insert]
      refine ⟨pairwiseDisjoint_singleton B id, ?_⟩
      intro q hq
      rw [mem_singleton_iff] at hq
      subst q
      intro _
      rw [disjoint_comm]
      refine Set.disjoint_left.2 ?_
      intro p hpB hpA
      exact hpA.2.2 hpB.2.2
    · ext p
      simp only [A, B, mem_sdiff, mem_prod, mem_inter_iff,
        Finset.coe_insert, Finset.coe_singleton, sUnion_insert,
        sUnion_singleton, mem_union]
      tauto

/-- For a sigma-finite measure, finite unions from a generating semiring are
measure-dense.  The finite-measure reduction is included explicitly because
the usual finite-measure density lemma is not sufficient on the half-line. -/
theorem measureDense_supClosure_of_generateFrom_isSetSemiring
    {X : Type*} [mX : MeasurableSpace X] {ν : Measure X} [SigmaFinite ν]
    {C : Set (Set X)} (hC : IsSetSemiring C)
    (S : ν.FiniteSpanningSetsIn C)
    (hgen : mX = MeasurableSpace.generateFrom C) :
    ν.MeasureDense (supClosure C) where
  measurable s hs := by
    rw [hgen]
    exact measurableSet_generateFrom_of_mem_supClosure hs
  approx s ms hνs ε hε := by
    let T := accumulate S.set
    have hRing : IsSetRing (supClosure C) := hC.isSetRing_supClosure
    have T_mem (n : ℕ) : T n ∈ supClosure C := by
      simpa using! hRing.biUnion_mem {k | k ≤ n}.toFinset
        (fun k _ => subset_supClosure (S.set_mem k))
    have T_meas (n : ℕ) : MeasurableSet (T n) := by
      rw [hgen]
      exact measurableSet_generateFrom_of_mem_supClosure (T_mem n)
    have T_finite (n : ℕ) : ν (T n) < ∞ := by
      simpa using! measure_biUnion_lt_top {k | k ≤ n}.toFinset.finite_toSet
        (fun k _ => S.finite k)
    have T_spanning : ⋃ n, T n = univ := S.spanning ▸ iUnion_accumulate
    have hmono : Monotone (fun n => (T n) ∩ s) := fun m n hmn =>
      inter_subset_inter_left s
        (biUnion_subset_biUnion_left fun k hkm => Nat.le_trans hkm hmn)
    have hlim := tendsto_measure_iUnion_atTop (μ := ν) hmono
    rw [← tendsto_toReal_iff] at hlim
    · rcases Metric.tendsto_atTop.1 hlim (ε / 2) (by linarith) with ⟨N, hN⟩
      letI : Fact (ν (T N) < ∞) := Fact.mk (T_finite N)
      have hgenRing : mX = MeasurableSpace.generateFrom (supClosure C) := by
        rw [hgen]
        apply le_antisymm (generateFrom_mono subset_supClosure)
        apply generateFrom_le
        intro t ht
        exact measurableSet_generateFrom_of_mem_supClosure ht
      have hcover : ∃ D : Set (Set X), D.Countable ∧ D ⊆ supClosure C ∧
          (ν.restrict (T N)) (⋃₀ D)ᶜ = 0 := by
        refine ⟨{T N}, Set.countable_singleton _, ?_, ?_⟩
        · simpa using T_mem N
        · simp [T_meas N]
      have hsfinite : (ν.restrict (T N)) s ≠ ∞ := by
        exact ne_of_lt (lt_of_le_of_lt (ν.restrict_apply_le _ s) hνs.lt_top)
      rcases exists_measure_symmDiff_lt_of_generateFrom_isSetRing
          (μ := ν.restrict (T N)) hRing hcover hgenRing ms
          (ε := ENNReal.ofReal (ε / 2)) (by positivity) with
        ⟨t, htC, ht⟩
      refine ⟨t ∩ T N, hRing.inter_mem htC (T_mem N), ?_⟩
      calc
        ν (s ∆ (t ∩ T N))
            ≤ ν (s \ (s ∩ T N)) + ν ((s ∆ t) ∩ T N) := by
              rw [← symmDiff_of_le (inter_subset_left ..), symmDiff_comm _ s,
                inter_symmDiff_distrib_right]
              exact measure_symmDiff_le _ _ _
        _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
              apply ENNReal.add_lt_add
              · rw [measure_sdiff
                    (inter_subset_left ..)
                    (ms.inter (T_meas N)).nullMeasurableSet
                    (ne_top_of_le_ne_top hνs (measure_mono (inter_subset_left ..))),
                  lt_ofReal_iff_toReal_lt (sub_ne_top hνs),
                  toReal_sub_of_le (measure_mono (inter_subset_left ..)) hνs]
                apply lt_of_le_of_lt (sub_le_dist ..)
                nth_rw 1 [← univ_inter s]
                rw [inter_comm s, dist_comm, ← T_spanning, iUnion_inter _ T]
                exact hN N (le_refl _)
              · rw [← ν.restrict_apply' (T_meas N)]
                simpa only [symmDiff_comm] using ht
        _ = ENNReal.ofReal ε := by
              rw [← ofReal_add (by linarith) (by linarith), add_halves]
    · exact fun n => ne_top_of_le_ne_top hνs
        (measure_mono (inter_subset_right ..))
    · exact ne_top_of_le_ne_top hνs
        (measure_mono (iUnion_subset fun i => inter_subset_right))

theorem measurableRectangleUnions_measureDense :
    (μ.prod μ).MeasureDense
      (supClosure (measurableRectangles (α := α))) := by
  apply measureDense_supClosure_of_generateFrom_isSetSemiring
    measurableRectangles_isSetSemiring
  · exact μ.toFiniteSpanningSetsIn.prod μ.toFiniteSpanningSetsIn
  · exact measurableRectangles_generate.symm

theorem rectangleIndicator_eq_tensor
    (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (c : ℝ) :
    indicatorConstLp 2 (hs.prod ht) (by
      rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top hμs hμt) c =
      tensor (indicatorConstLp 2 hs hμs c)
        (indicatorConstLp 2 ht hμt (1 : ℝ)) := by
  apply Lp.ext (μ := μ.prod μ)
  filter_upwards [
    (indicatorConstLp_coeFn (μ := μ.prod μ) (p := (2 : ℝ≥0∞))
      (hs := hs.prod ht) (hμs := by
        rw [Measure.prod_prod]
        exact ENNReal.mul_ne_top hμs hμt) (c := c)),
    tensor_ae (indicatorConstLp 2 hs hμs c)
      (indicatorConstLp 2 ht hμt (1 : ℝ)),
    Measure.quasiMeasurePreserving_fst.ae
      (indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs)
        (hμs := hμs) (c := c)),
    Measure.quasiMeasurePreserving_snd.ae
      (indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := ht)
        (hμs := hμt) (c := (1 : ℝ)))] with p hp hten hsind htind
  rw [hp, hten, hsind, htind]
  by_cases hps : p.1 ∈ s <;> by_cases hpt : p.2 ∈ t <;>
    simp [hps, hpt]

theorem rectangleIndicator_mem_tensorSpan
    (c : ℝ) (q : Set (α × α))
    (hq : q ∈ measurableRectangles (α := α))
    (hμq : (μ.prod μ) q ≠ ∞) :
    indicatorConstLp 2
      (measurableRectangles_measurable hq) hμq c ∈
      tensorSpan (μ := μ) := by
  rcases hq with ⟨s, hs, t, ht, rfl⟩
  by_cases hs0 : μ s = 0
  · have hprod0 : (μ.prod μ) (s ×ˢ t) = 0 := by
      rw [Measure.prod_prod, hs0, zero_mul]
    have hz : indicatorConstLp 2 (hs.prod ht) hμq c = 0 := by
      apply norm_eq_zero.mp
      rw [norm_indicatorConstLp (by norm_num) (by norm_num), measureReal_def,
        hprod0]
      simp
    rw [hz]
    exact Submodule.zero_mem _
  by_cases ht0 : μ t = 0
  · have hprod0 : (μ.prod μ) (s ×ˢ t) = 0 := by
      rw [Measure.prod_prod, ht0, mul_zero]
    have hz : indicatorConstLp 2 (hs.prod ht) hμq c = 0 := by
      apply norm_eq_zero.mp
      rw [norm_indicatorConstLp (by norm_num) (by norm_num), measureReal_def,
        hprod0]
      simp
    rw [hz]
    exact Submodule.zero_mem _
  have hprod : μ s * μ t ≠ ∞ := by
    rwa [← Measure.prod_prod]
  have hμs : μ s ≠ ∞ := by
    intro hsinf
    apply hprod
    rw [ENNReal.mul_eq_top]
    exact Or.inr ⟨hsinf, ht0⟩
  have hμt : μ t ≠ ∞ := by
    intro htinf
    apply hprod
    rw [ENNReal.mul_eq_top]
    exact Or.inl ⟨hs0, htinf⟩
  rw [rectangleIndicator_eq_tensor s t hs ht hμs hμt c]
  exact Submodule.subset_span ⟨
    (indicatorConstLp 2 hs hμs c,
      indicatorConstLp 2 ht hμt (1 : ℝ)), rfl⟩

theorem finiteRectangleUnion_measurable
    (J : Finset (Set (α × α)))
    (hJ : (J : Set (Set (α × α))) ⊆ measurableRectangles (α := α)) :
    MeasurableSet (⋃₀ (J : Set (Set (α × α)))) := by
  rw [← measurableRectangles_generate]
  apply measurableSet_generateFrom_of_mem_supClosure
  rw [sUnion_eq_biUnion]
  exact measurableRectangles_isSetSemiring.isSetRing_supClosure.biUnion_mem J
    (fun q hq => subset_supClosure (hJ hq))

theorem finiteDisjointRectangleUnionIndicator_mem_tensorSpan
    (J : Finset (Set (α × α)))
    (hJ : (J : Set (Set (α × α))) ⊆ measurableRectangles (α := α))
    (hdisj : (J : Set (Set (α × α))).PairwiseDisjoint id)
    (c : ℝ) (hμJ : (μ.prod μ) (⋃₀ (J : Set (Set (α × α)))) ≠ ∞) :
    indicatorConstLp 2 (finiteRectangleUnion_measurable J hJ) hμJ c ∈
      tensorSpan (μ := μ) := by
  classical
  induction J using Finset.induction with
  | empty =>
      simpa using (Submodule.zero_mem (tensorSpan (μ := μ)))
  | @insert a J ha ih =>
      have haC : a ∈ measurableRectangles (α := α) :=
        hJ (by simp)
      have hJC : (J : Set (Set (α × α))) ⊆
          measurableRectangles (α := α) := by
        intro q hq
        exact hJ (by simp [hq])
      have hpair : (J : Set (Set (α × α))).PairwiseDisjoint id ∧
          ∀ q ∈ (J : Set (Set (α × α))), a ≠ q → Disjoint a q := by
        simpa only [Finset.coe_insert, Set.pairwiseDisjoint_insert, id_eq] using hdisj
      let U : Set (α × α) := ⋃₀ (J : Set (Set (α × α)))
      have h_union : ⋃₀ ((insert a J : Finset (Set (α × α))) :
          Set (Set (α × α))) = a ∪ U := by
        simp [U]
      have ha_sub : a ⊆ ⋃₀ ((insert a J : Finset (Set (α × α))) :
          Set (Set (α × α))) := by
        rw [h_union]
        exact subset_union_left
      have hU_sub : U ⊆ ⋃₀ ((insert a J : Finset (Set (α × α))) :
          Set (Set (α × α))) := by
        rw [h_union]
        exact subset_union_right
      have hμa : (μ.prod μ) a ≠ ∞ :=
        ne_top_of_le_ne_top hμJ (measure_mono ha_sub)
      have hμU : (μ.prod μ) U ≠ ∞ :=
        ne_top_of_le_ne_top hμJ (measure_mono hU_sub)
      have haMeas : MeasurableSet a := measurableRectangles_measurable haC
      have hUMeas : MeasurableSet U := finiteRectangleUnion_measurable J hJC
      have haSpan := rectangleIndicator_mem_tensorSpan c a haC hμa
      have hUSpan := ih hJC hpair.1 hμU
      have haU : Disjoint a U := by
        apply Set.disjoint_sUnion_right.mpr
        intro q hq
        exact hpair.2 q hq (ne_of_mem_of_not_mem hq ha).symm
      have hsum : indicatorConstLp 2 (haMeas.union hUMeas)
          (by finiteness) c ∈ tensorSpan (μ := μ) := by
        rw [indicatorConstLp_disjoint_union haMeas hUMeas hμa hμU haU c]
        exact Submodule.add_mem _ haSpan hUSpan
      simpa only [h_union] using hsum

theorem rectangleUnionIndicator_mem_tensorSpan
    (c : ℝ) (s : Set (α × α))
    (hs : s ∈ supClosure (measurableRectangles (α := α)))
    (hμs : (μ.prod μ) s ≠ ∞) :
    indicatorConstLp 2
      ((measurableRectangleUnions_measureDense (μ := μ)).measurable s hs) hμs c ∈
      tensorSpan (μ := μ) := by
  classical
  rcases measurableRectangles_isSetSemiring.mem_supClosure_iff.mp hs with
    ⟨P, hP⟩
  have hUnion : ⋃₀ (P.parts : Set (Set (α × α))) = s := by
    rw [← Finset.sup_id_set_eq_sUnion, P.sup_parts]
  have hμP : (μ.prod μ) (⋃₀ (P.parts : Set (Set (α × α)))) ≠ ∞ := by
    rwa [hUnion]
  have hmem := finiteDisjointRectangleUnionIndicator_mem_tensorSpan
    P.parts hP P.disjoint c hμP
  simpa only [hUnion] using hmem

theorem tensorSpan_dense :
    (tensorSpan (μ := μ)).topologicalClosure = ⊤ := by
  apply tensorSpan_dense_of_measureDense
    (supClosure (measurableRectangles (α := α)))
    (measurableRectangleUnions_measureDense (μ := μ))
  intro c s hs hμs
  exact (tensorSpan (μ := μ)).le_topologicalClosure
    (rectangleUnionIndicator_mem_tensorSpan c s hs hμs)

/-- Every square-integrable kernel over a sigma-finite measure defines a
compact operator. -/
theorem operator_isCompactOperator (K : RealKernelL2 μ) :
    IsCompactOperator (operator K) :=
  operator_isCompactOperator_of_tensorSpan_dense tensorSpan_dense K

end HBL.L2Kernel
