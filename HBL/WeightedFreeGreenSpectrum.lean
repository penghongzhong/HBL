import HBL.WeightedFreeGreenODE

/-!
Explicit oscillatory solutions for the weighted free Green equation.

The change of variable `theta = arctan r` conjugates
`-q'' = (k^2-1) (1+r^2)^(-2) q` to the constant-coefficient
Dirichlet equation.  We keep the conjugation pointwise so that no
change-of-measure theorem is needed in the later spectral exclusion.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

/-- Dirichlet oscillation pulled back from the finite interval by `arctan`. -/
def greenOscillation (k r : ℝ) : ℝ :=
  Real.sqrt (1 + r ^ 2) * Real.sin (k * Real.arctan r)

/-- Its radial derivative, written without `deriv`. -/
def greenOscillationVelocity (k r : ℝ) : ℝ :=
  (r * Real.sin (k * Real.arctan r) +
    k * Real.cos (k * Real.arctan r)) /
      Real.sqrt (1 + r ^ 2)

theorem greenOscillation_hasDerivAt (k r : ℝ) :
    HasDerivAt (greenOscillation k) (greenOscillationVelocity k r) r := by
  have hs0 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * r) r := by
    convert (hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2) using 1
    · funext x
      rfl
    · simp only [id_eq]
      ring
  have hsne : Real.sqrt (1 + r ^ 2) ≠ 0 := by positivity
  have hs : HasDerivAt (fun x : ℝ => Real.sqrt (1 + x ^ 2))
      (r / Real.sqrt (1 + r ^ 2)) r := by
    convert hs0.sqrt (by positivity) using 1
    field_simp [hsne]
  have ht : HasDerivAt (fun x : ℝ => k * Real.arctan x)
      (k * (1 + r ^ 2)⁻¹) r := by
    convert (Real.hasDerivAt_arctan' r).const_mul k using 1 <;> ring
  have hsin := ht.sin
  convert hs.mul hsin using 1
  · funext x
    rfl
  · unfold greenOscillationVelocity
    have hs2 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
      Real.sq_sqrt (by positivity)
    field_simp [hsne]
    rw [hs2]
    ring

theorem greenOscillationVelocity_hasDerivAt (k r : ℝ) :
    HasDerivAt (greenOscillationVelocity k)
      (-(k ^ 2 - 1) * weightedGreenDecay r ^ 2 *
        greenOscillation k r) r := by
  have hs0 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * r) r := by
    convert (hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2) using 1
    · funext x
      rfl
    · simp only [id_eq]
      ring
  have hsne : Real.sqrt (1 + r ^ 2) ≠ 0 := by positivity
  have hs : HasDerivAt (fun x : ℝ => Real.sqrt (1 + x ^ 2))
      (r / Real.sqrt (1 + r ^ 2)) r := by
    convert hs0.sqrt (by positivity) using 1
    field_simp [hsne]
  have ht : HasDerivAt (fun x : ℝ => k * Real.arctan x)
      (k * (1 + r ^ 2)⁻¹) r := by
    convert (Real.hasDerivAt_arctan' r).const_mul k using 1 <;> ring
  have hsin := ht.sin
  have hcos := ht.cos
  have hnum : HasDerivAt
      (fun x : ℝ => x * Real.sin (k * Real.arctan x) +
        k * Real.cos (k * Real.arctan x))
      (Real.sin (k * Real.arctan r) +
        r * (k * (1 + r ^ 2)⁻¹ * Real.cos (k * Real.arctan r)) -
        k ^ 2 * (1 + r ^ 2)⁻¹ * Real.sin (k * Real.arctan r)) r := by
    convert ((hasDerivAt_id r).mul hsin).add (hcos.const_mul k) using 1
    · funext x
      rfl
    · simp only [id_eq]
      ring
  convert hnum.div hs hsne using 1
  · funext x
    rfl
  · have hs2 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hs4 : Real.sqrt (1 + r ^ 2) ^ 4 = (1 + r ^ 2) ^ 2 := by
      calc
        Real.sqrt (1 + r ^ 2) ^ 4 =
            (Real.sqrt (1 + r ^ 2) ^ 2) ^ 2 := by ring
        _ = (1 + r ^ 2) ^ 2 := by rw [hs2]
    unfold weightedGreenDecay greenOscillation
    field_simp [hsne]
    rw [hs2, hs4]
    ring

@[simp]
theorem greenOscillation_zero (k : ℝ) : greenOscillation k 0 = 0 := by
  simp [greenOscillation]

@[simp]
theorem greenOscillationVelocity_zero (k : ℝ) :
    greenOscillationVelocity k 0 = k := by
  simp [greenOscillationVelocity]

theorem bubble_tendsto_zero :
    Tendsto bubble atTop (𝓝 (0 : ℝ)) := by
  have h := resonanceMinus_tendsto_one.mul tendsto_inv_atTop_zero
  have h' : Tendsto (fun r : ℝ => resonanceMinus r * r⁻¹) atTop
      (𝓝 (0 : ℝ)) := by simpa using h
  apply h'.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with r hr
  rw [resonanceMinus_def]
  field_simp [hr]

theorem greenOscillationVelocity_tendsto (k : ℝ) :
    Tendsto (greenOscillationVelocity k) atTop
      (𝓝 (Real.sin (k * (Real.pi / 2)))) := by
  have ha : Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop
  have hphase : Tendsto (fun r : ℝ => k * Real.arctan r) atTop
      (𝓝 (k * (Real.pi / 2))) := ha.const_mul k
  have hsin : Tendsto (fun r : ℝ => Real.sin (k * Real.arctan r)) atTop
      (𝓝 (Real.sin (k * (Real.pi / 2)))) :=
    Real.continuous_sin.continuousAt.tendsto.comp hphase
  have hcos : Tendsto (fun r : ℝ => Real.cos (k * Real.arctan r)) atTop
      (𝓝 (Real.cos (k * (Real.pi / 2)))) :=
    Real.continuous_cos.continuousAt.tendsto.comp hphase
  have h := resonanceMinus_tendsto_one.mul hsin |>.add
    ((bubble_tendsto_zero.const_mul k).mul hcos)
  have h' : Tendsto
      (fun r : ℝ => resonanceMinus r * Real.sin (k * Real.arctan r) +
        k * bubble r * Real.cos (k * Real.arctan r)) atTop
      (𝓝 (Real.sin (k * (Real.pi / 2)))) := by simpa using h
  apply h'.congr'
  filter_upwards with r
  simp only [greenOscillationVelocity, resonanceMinus_def, bubble]
  ring

/-- First-order system for a general nonzero Green eigenvalue. -/
def greenEigenODEField (mu r : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.2, -mu⁻¹ * weightedGreenDecay r ^ 2 * z.1)

def greenEigenODELipschitzConstant (mu : ℝ) : NNReal where
  val := 1 + |mu⁻¹|
  property := by positivity

theorem greenEigenODEField_lipschitz (mu r : ℝ) :
    LipschitzWith (greenEigenODELipschitzConstant mu)
      (greenEigenODEField mu r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Prod.dist_eq, Prod.dist_eq]
  simp only [greenEigenODEField, Real.dist_eq]
  have ha0 : 0 ≤ weightedGreenDecay r := weightedGreenDecay_nonneg r
  have ha1 : weightedGreenDecay r ≤ 1 := weightedGreenDecay_le_one r
  have hcoef : |-mu⁻¹ * weightedGreenDecay r ^ 2| ≤ 1 + |mu⁻¹| := by
    rw [abs_mul, abs_neg]
    rw [abs_of_nonneg (sq_nonneg (weightedGreenDecay r))]
    have hsquare : weightedGreenDecay r ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (weightedGreenDecay r),
        mul_self_le_mul_self ha0 ha1]
    calc
      |mu⁻¹| * weightedGreenDecay r ^ 2 ≤ |mu⁻¹| * 1 :=
        mul_le_mul_of_nonneg_left hsquare (abs_nonneg _)
      _ ≤ 1 + |mu⁻¹| := by linarith
  apply max_le
  · calc
      |x.2 - y.2| ≤ max |x.1 - y.1| |x.2 - y.2| := le_max_right _ _
      _ ≤ (1 + |mu⁻¹|) * max |x.1 - y.1| |x.2 - y.2| := by
        have hm : 0 ≤ max |x.1 - y.1| |x.2 - y.2| :=
          le_trans (abs_nonneg _) (le_max_left _ _)
        nlinarith [abs_nonneg mu⁻¹]
  · calc
      |-mu⁻¹ * weightedGreenDecay r ^ 2 * x.1 -
          -mu⁻¹ * weightedGreenDecay r ^ 2 * y.1| =
          |-mu⁻¹ * weightedGreenDecay r ^ 2| * |x.1 - y.1| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ (1 + |mu⁻¹|) * max |x.1 - y.1| |x.2 - y.2| := by
        exact mul_le_mul hcoef (le_max_left _ _)
          (abs_nonneg _) (by positivity)

def greenFrequency (mu : ℝ) : ℝ := Real.sqrt (1 + mu⁻¹)

theorem greenFrequency_pos {mu : ℝ} (hmu : 0 < mu) :
    0 < greenFrequency mu := by
  unfold greenFrequency
  exact Real.sqrt_pos.2 (by positivity)

theorem greenFrequency_sq_sub_one {mu : ℝ} (hmu : 0 < mu) :
    greenFrequency mu ^ 2 - 1 = mu⁻¹ := by
  unfold greenFrequency
  rw [Real.sq_sqrt (by positivity)]
  ring

/-- Phase-space form of a pulled-back finite-interval oscillation. -/
def greenOscillationODEState (c k : ℝ) (r : ℝ) : ℝ × ℝ :=
  (c * greenOscillation k r, c * greenOscillationVelocity k r)

theorem greenOscillationODEState_hasDerivAt
    {mu : ℝ} (hmu : 0 < mu) (c r : ℝ) :
    HasDerivAt (greenOscillationODEState c (greenFrequency mu))
      (greenEigenODEField mu r
        (greenOscillationODEState c (greenFrequency mu) r)) r := by
  have hq := (greenOscillation_hasDerivAt (greenFrequency mu) r).const_mul c
  have hv :=
    (greenOscillationVelocity_hasDerivAt (greenFrequency mu) r).const_mul c
  convert hq.prodMk hv using 1
  · rfl
  · unfold greenEigenODEField greenOscillationODEState
    apply Prod.ext
    · rfl
    · simp only [Prod.fst, Prod.snd]
      rw [greenFrequency_sq_sub_one hmu]
      ring

theorem greenOscillationODEState_continuousOn
    (c k : ℝ) (s : Set ℝ) :
    ContinuousOn (greenOscillationODEState c k) s := by
  intro r _
  exact (((greenOscillation_hasDerivAt k r).const_mul c).prodMk
    ((greenOscillationVelocity_hasDerivAt k r).const_mul c)).continuousAt.continuousWithinAt

theorem greenODEState_eigen_hasDerivWithinAt
    {mu : ℝ} (hmu : mu ≠ 0) (f : RealL2 halfLineMeasure)
    (heig : weightedFreeGreenOperator f = mu • f)
    {r : ℝ} (hr : 0 ≤ r) :
    HasDerivWithinAt
      (greenODEState (weightedGreenEigenSource mu f))
      (greenEigenODEField mu r
        (greenODEState (weightedGreenEigenSource mu f) r))
      (Ici r) r := by
  have hbase := greenODEState_hasDerivWithinAt
    (weightedGreenEigenSource_continuous mu f)
    (weightedGreenEigenSource_integrableOn hmu f heig) hr
  have hsource : weightedGreenEigenSource mu f r =
      mu⁻¹ * weightedGreenDecay r ^ 2 *
        halfLineMinGreen (weightedGreenEigenSource mu f) r := by
    change mu⁻¹ * weightedGreenDecay r ^ 2 * weightedGreenPrimitive f r = _
    rw [congrFun (weightedGreenPrimitive_eq_eigen_minGreen hmu f heig) r]
  convert hbase using 1
  unfold greenEigenODEField greenODEState
  apply Prod.ext
  · rfl
  · simp only [Prod.fst, Prod.snd]
    rw [hsource]
    ring

/-- Every positive Green eigenpair is a pulled-back Dirichlet oscillation,
including its outgoing derivative component. -/
theorem weightedGreenEigen_state_eq_oscillation
    {mu : ℝ} (hmu : 0 < mu) (f : RealL2 halfLineMeasure)
    (heig : weightedFreeGreenOperator f = mu • f) :
    ∃ c : ℝ, ∀ r : ℝ, 0 ≤ r →
      greenODEState (weightedGreenEigenSource mu f) r =
        greenOscillationODEState c (greenFrequency mu) r := by
  let h : ℝ → ℝ := weightedGreenEigenSource mu f
  let k : ℝ := greenFrequency mu
  let c : ℝ := halfLineGreenTail h 0 / k
  refine ⟨c, ?_⟩
  intro r hr
  let R : ℝ := r + 1
  have hR : r ∈ Icc (0 : ℝ) R := by
    constructor
    · exact hr
    · dsimp [R]
      linarith
  have huniq : EqOn (greenODEState h) (greenOscillationODEState c k)
      (Icc (0 : ℝ) R) := by
    apply ODE_solution_unique (K := greenEigenODELipschitzConstant mu)
        (v := greenEigenODEField mu)
    · exact greenEigenODEField_lipschitz mu
    · exact greenODEState_continuousOn_Icc
        (weightedGreenEigenSource_continuous mu f)
        (weightedGreenEigenSource_integrableOn hmu.ne' f heig) R
    · intro t ht
      exact greenODEState_eigen_hasDerivWithinAt hmu.ne' f heig ht.1
    · exact greenOscillationODEState_continuousOn c k (Icc 0 R)
    · intro t _
      dsimp [k]
      exact (greenOscillationODEState_hasDerivAt hmu c t).hasDerivWithinAt
    · unfold greenODEState greenOscillationODEState c k
      apply Prod.ext
      · simp
      · simp only [greenOscillationVelocity_zero]
        field_simp [(greenFrequency_pos hmu).ne']
  exact huniq hR

theorem weightedGreenEigen_oscillation_coefficient_ne_zero
    {mu : ℝ} (hmu : 0 < mu) (f : RealL2 halfLineMeasure) (hf : f ≠ 0)
    (heig : weightedFreeGreenOperator f = mu • f)
    {c : ℝ}
    (hstate : ∀ r : ℝ, 0 ≤ r →
      greenODEState (weightedGreenEigenSource mu f) r =
        greenOscillationODEState c (greenFrequency mu) r) :
    c ≠ 0 := by
  intro hc
  apply hf
  apply Lp.ext
  have hpoint := weightedFreeGreenOperator_ae_pointwise f
  rw [heig] at hpoint
  filter_upwards [hpoint, Lp.coeFn_smul mu f,
      ae_restrict_mem measurableSet_Ioi,
      Lp.coeFn_zero ℝ 2 halfLineMeasure]
      with r hpoint hsmul hr hzero
  rw [hsmul] at hpoint
  simp only [Pi.smul_apply, smul_eq_mul] at hpoint
  have hminzero :
      halfLineMinGreen (weightedGreenEigenSource mu f) r = 0 := by
    have h := congrArg Prod.fst (hstate r hr.le)
    simpa [greenODEState, greenOscillationODEState, hc] using h
  have hqzero : weightedGreenPrimitive f r = 0 := by
    rw [congrFun
      (weightedGreenPrimitive_eq_eigen_minGreen hmu.ne' f heig) r]
    exact hminzero
  unfold weightedFreeGreenPointwise at hpoint
  rw [hqzero, mul_zero] at hpoint
  rw [hzero]
  simp only [Pi.zero_apply]
  nlinarith

/-- The outgoing boundary condition quantizes every nonzero positive Green
eigenpair after the `arctan` conjugation. -/
theorem weightedGreenEigen_frequency_sin_eq_zero
    {mu : ℝ} (hmu : 0 < mu) (f : RealL2 halfLineMeasure) (hf : f ≠ 0)
    (heig : weightedFreeGreenOperator f = mu • f) :
    Real.sin (greenFrequency mu * (Real.pi / 2)) = 0 := by
  obtain ⟨c, hstate⟩ := weightedGreenEigen_state_eq_oscillation hmu f heig
  have hc : c ≠ 0 :=
    weightedGreenEigen_oscillation_coefficient_ne_zero hmu f hf heig hstate
  let h : ℝ → ℝ := weightedGreenEigenSource mu f
  have htail : Tendsto (halfLineGreenTail h) atTop (𝓝 (0 : ℝ)) := by
    unfold halfLineGreenTail
    exact tendsto_integral_Ioi_zero tendsto_id
  have heq : (halfLineGreenTail h) =ᶠ[atTop]
      fun r => c * greenOscillationVelocity (greenFrequency mu) r := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    have hs := congrArg Prod.snd (hstate r hr)
    simpa [h, greenODEState, greenOscillationODEState] using hs
  have hcand0 : Tendsto
      (fun r => c * greenOscillationVelocity (greenFrequency mu) r)
      atTop (𝓝 (0 : ℝ)) := htail.congr' heq
  have hcand := (greenOscillationVelocity_tendsto
    (greenFrequency mu)).const_mul c
  have hzero : c * Real.sin (greenFrequency mu * (Real.pi / 2)) = 0 :=
    tendsto_nhds_unique hcand hcand0
  exact (mul_eq_zero.mp hzero).resolve_left hc

/-- The only positive Green eigenvalue in the interval forced by a
Birman--Schwinger fixed vector and the Hartree norm bound is `1/15`. -/
theorem weightedFreeGreen_eigenvalue_eq_one_fifteen_of_band
    {mu : ℝ} (hlo : (1 / 21 : ℝ) ≤ mu) (hhi : mu ≤ (1 / 9 : ℝ))
    (f : RealL2 halfLineMeasure) (hf : f ≠ 0)
    (heig : weightedFreeGreenOperator f = mu • f) :
    mu = (1 / 15 : ℝ) := by
  have hmu : 0 < mu := lt_of_lt_of_le (by norm_num) hlo
  have hsin := weightedGreenEigen_frequency_sin_eq_zero hmu f hf heig
  rw [Real.sin_eq_zero_iff] at hsin
  obtain ⟨n, hn⟩ := hsin
  have hk : greenFrequency mu = 2 * (n : ℝ) := by
    apply (mul_right_cancel₀ Real.pi_ne_zero)
    calc
      greenFrequency mu * Real.pi = 2 * ((n : ℝ) * Real.pi) := by
        nlinarith [hn]
      _ = (2 * (n : ℝ)) * Real.pi := by ring
  have hkpos : 0 < greenFrequency mu := greenFrequency_pos hmu
  have hnpos : 0 < (n : ℝ) := by nlinarith [hk]
  have hinv_upper : mu⁻¹ ≤ 21 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 21) hlo
    norm_num at h ⊢
    simpa [one_div] using h
  have hinv_lower : 9 ≤ mu⁻¹ := by
    have h := one_div_le_one_div_of_le hmu hhi
    norm_num at h ⊢
    simpa [one_div] using h
  have hk_sq : greenFrequency mu ^ 2 = 1 + mu⁻¹ := by
    nlinarith [greenFrequency_sq_sub_one hmu]
  have hksq_lower : 10 ≤ greenFrequency mu ^ 2 := by linarith
  have hksq_upper : greenFrequency mu ^ 2 ≤ 22 := by linarith
  have hnsq_lower : (5 / 2 : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [hk] at hksq_lower
    nlinarith
  have hnsq_upper : (n : ℝ) ^ 2 ≤ (11 / 2 : ℝ) := by
    rw [hk] at hksq_upper
    nlinarith
  have hn_lower : (1 : ℝ) < (n : ℝ) := by
    by_contra h
    have hnle : (n : ℝ) ≤ 1 := le_of_not_gt h
    have hsq := mul_self_le_mul_self hnpos.le hnle
    nlinarith
  have hn_upper : (n : ℝ) < 3 := by
    by_contra h
    have hnge : (3 : ℝ) ≤ (n : ℝ) := le_of_not_gt h
    have hsq := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 3) hnge
    nlinarith
  have hn_lower_int : (1 : ℤ) < n := by exact_mod_cast hn_lower
  have hn_upper_int : n < (3 : ℤ) := by exact_mod_cast hn_upper
  have hn_two : n = 2 := by omega
  have hk_four : greenFrequency mu = 4 := by
    rw [hk, hn_two]
    norm_num
  have hinv : mu⁻¹ = 15 := by
    have h := greenFrequency_sq_sub_one hmu
    rw [hk_four] at h
    norm_num at h ⊢
    exact h.symm
  calc
    mu = (mu⁻¹)⁻¹ := (inv_inv mu).symm
    _ = (15 : ℝ)⁻¹ := by rw [hinv]
    _ = 1 / 15 := by norm_num

end HBL.Modulation.Monopole
