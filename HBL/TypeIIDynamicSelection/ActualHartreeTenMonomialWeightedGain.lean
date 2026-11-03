import HBL.TypeIIDynamicSelection.ActualHartreeTenTermEnvelopeMonotone
import HBL.TypeIIDynamicSelection.ActualHartreeThreeFredholmEnvelopes
import Mathlib.Tactic

/-!
# HBL revised 2.13: original ten-term Hartree interaction weighted positive order

The exact quartic inverse-square Hartree interaction has ten nonnegative
scalar monomials. From the previously strictly verified three radial
Riesz potentials and actual monopole/Strauss envelopes, this lemma
deduces the ENTIRE ten-term scalar sigma=7/4 source bound of order
ell^(1/8). No radiation speed, created source order, matching datum
or Type-II rate is postulated. The lemma is a scalar bridge and not a
proof of actual Hartree PDE three-region matching or finite recursion.
-/

noncomputable section
set_option autoImplicit false
open scoped Topology

namespace HBL.TypeIIDynamicSelection

def actualHartreeTenTermSourceConstant
    (D E Cm Cz Cc : ℝ) : ℝ :=
  (Cm * D ^ 3 + 4 * Cm * D ^ 2 * E + Cz * D ^ 3 +
    4 * Cc * D ^ 2 * E) +
  (4 * Cm * D * E ^ 2 + 4 * Cz * D ^ 2 * E +
    4 * Cc * D * E ^ 2) +
  (Cm * E ^ 3 + 4 * Cz * D * E ^ 2 + Cc * E ^ 3)

/-- All ten actual Hartree quartic×cubic interaction monomials inherit
the spatial Fredholm sigma=7/4, physical length epsilon=1/8 estimate.
The hypotheses are exactly the separate source and field bounds
proved in other original-kernel HBL files. -/
theorem actual_Hartree_all_ten_monomials_weighted_one_eighth_gain
    (ell r D E Cm Cz Cc pm pz pc v z : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hr : 0 ≤ r)
    (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hCm : 0 ≤ Cm) (hCz : 0 ≤ Cz) (hCc : 0 ≤ Cc)
    (hpm0 : 0 ≤ pm) (hpz0 : 0 ≤ pz) (hpc0 : 0 ≤ pc)
    (hv0 : 0 ≤ v) (hz0 : 0 ≤ z)
    (hPm : pm ≤ Cm * Real.sqrt ell / (1 + r))
    (hPz : pz ≤ Cz * ell / (1 + ell * r))
    (hPc : pc ≤ Cc / (1 + r))
    (hV : v ≤ D / (1 + r))
    (hZ : z ≤ E * Real.sqrt ell / (1 + ell * r)) :
    (1 + r) ^ (7 / 4 : ℝ) *
      (pm * (v ^ 3 + (2 * v + z) ^ 2 * z) +
       pz * ((v + 2 * z) ^ 2 * v) +
       pc * ((2 * v + z) ^ 2 * z)) ≤
      actualHartreeTenTermSourceConstant D E Cm Cz Cc *
        ell ^ (1 / 8 : ℝ) * (1 + r) ^ (-(5 / 8 : ℝ)) := by
  let d : ℝ := 1 + r
  let q : ℝ := 1 + ell * r
  let s : ℝ := Real.sqrt ell
  have hd : 0 < d := by dsimp [d]; linarith
  have hq : 0 < q := by dsimp [q]; positivity
  have hs0 : 0 ≤ s := Real.sqrt_nonneg ell
  have hssq : s ^ 2 = ell := Real.sq_sqrt hell.le
  have hs1 : s ≤ 1 := by
    dsimp [s]
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hellOne
  have hqle : q ≤ d := by
    dsimp [q,d]
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hellOne)]
  have hqdiv : q / d ≤ 1 :=
    (div_le_iff₀ hd).2 (by simpa using hqle)
  let pmB : ℝ := Cm * s / d
  let pzB : ℝ := Cz * s ^ 2 / q
  let pcB : ℝ := Cc / d
  let vB : ℝ := D / d
  let zB : ℝ := E * s / q
  have hpmB0 : 0 ≤ pmB := by dsimp [pmB]; positivity
  have hpzB0 : 0 ≤ pzB := by dsimp [pzB]; positivity
  have hpcB0 : 0 ≤ pcB := by dsimp [pcB]; positivity
  have hvB0 : 0 ≤ vB := by dsimp [vB]; positivity
  have hzB0 : 0 ≤ zB := by dsimp [zB]; positivity
  have hpm : pm ≤ pmB := by simpa only [pmB,s,d] using hPm
  have hpz : pz ≤ pzB := by
    change pz ≤ Cz * s ^ 2 / q
    rw [hssq]
    simpa only [q] using hPz
  have hpc : pc ≤ pcB := by simpa only [pcB,d] using hPc
  have hv : v ≤ vB := by simpa only [vB,d] using hV
  have hz : z ≤ zB := by simpa only [zB,s,q] using hZ
  have hMono :=
    actual_Hartree_complete_ten_term_polynomial_mono
      pm pz pc v z pmB pzB pcB vB zB
      hpm0 hpz0 hpc0 hv0 hz0 hpm hpz hpc hv hz
  let c1 : ℝ := Cm * D ^ 3
  let c2 : ℝ := 4 * Cm * D ^ 2 * E + Cz * D ^ 3
  let c3 : ℝ := 4 * Cc * D ^ 2 * E
  let c4 : ℝ := 4 * Cm * D * E ^ 2 + 4 * Cz * D ^ 2 * E
  let c5 : ℝ := 4 * Cc * D * E ^ 2
  let c6 : ℝ := Cm * E ^ 3 + 4 * Cz * D * E ^ 2
  let c7 : ℝ := Cc * E ^ 3
  have hc1 : 0 ≤ c1 := by dsimp [c1]; positivity
  have hc2 : 0 ≤ c2 := by dsimp [c2]; positivity
  have hc3 : 0 ≤ c3 := by dsimp [c3]; positivity
  have hc4 : 0 ≤ c4 := by dsimp [c4]; positivity
  have hc5 : 0 ≤ c5 := by dsimp [c5]; positivity
  have hc6 : 0 ≤ c6 := by dsimp [c6]; positivity
  have hc7 : 0 ≤ c7 := by dsimp [c7]; positivity
  let K1 : ℝ := c1 + c2 + c3
  let K2 : ℝ := c4 + c5
  let K3 : ℝ := c6 + c7
  have hK1 : 0 ≤ K1 := by dsimp [K1]; positivity
  have hK2 : 0 ≤ K2 := by dsimp [K2]; positivity
  have hK3 : 0 ≤ K3 := by dsimp [K3]; positivity
  let A1 : ℝ := s * d ^ (-(5 / 4 : ℝ)) / q
  let A2 : ℝ := s ^ 2 * d ^ (-(1 / 4 : ℝ)) / q ^ 2
  let A3 : ℝ := s ^ 3 * d ^ (3 / 4 : ℝ) / q ^ 3
  let T : ℝ := ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ))
  have hA1pos : 0 ≤ A1 := by dsimp [A1]; positivity
  have hA2pos : 0 ≤ A2 := by dsimp [A2]; positivity
  have hA3pos : 0 ≤ A3 := by dsimp [A3]; positivity
  obtain ⟨hS1,hS2,hS3⟩ :=
    actual_Hartree_three_Fredholm_scalar_envelopes ell r hell hellOne hr
  have hA1 : A1 ≤ T := by
    dsimp [A1,T,s,d,q]
    simpa only [Real.sqrt_eq_rpow] using hS1
  have hA2 : A2 ≤ T := by
    change s ^ 2 * d ^ (-(1 / 4 : ℝ)) / q ^ 2 ≤ T
    rw [hssq]
    simpa only [T,d,q,Real.rpow_one] using hS2
  have hs3 : s ^ 3 = ell ^ (3 / 2 : ℝ) := by
    dsimp [s]
    rw [Real.sqrt_eq_rpow]
    calc
      (ell ^ (1 / 2 : ℝ)) ^ 3 =
          ell ^ ((1 / 2 : ℝ) * (3 : ℝ)) :=
        (Real.rpow_mul hell.le (1 / 2 : ℝ) 3).symm
      _ = ell ^ (3 / 2 : ℝ) := by norm_num
  have hA3 : A3 ≤ T := by
    change s ^ 3 * d ^ (3 / 4 : ℝ) / q ^ 3 ≤ T
    rw [hs3]
    simpa only [T,d,q] using hS3
  have hPow3 : d ^ (7 / 4 : ℝ) / d ^ 3 =
      d ^ (-(5 / 4 : ℝ)) := by
    have he : d ^ (7 / 4 : ℝ) =
        d ^ (-(5 / 4 : ℝ)) * d ^ 3 := by
      calc
        _ = d ^ ((-(5 / 4 : ℝ)) + 3) := by norm_num
        _ = d ^ (-(5 / 4 : ℝ)) * d ^ 3 := by
          rw [Real.rpow_add hd]
          norm_num
    rw [he]
    field_simp [hd.ne']
  have hPow2 : d ^ (7 / 4 : ℝ) / d ^ 2 =
      d ^ (-(1 / 4 : ℝ)) := by
    have he : d ^ (7 / 4 : ℝ) =
        d ^ (-(1 / 4 : ℝ)) * d ^ 2 := by
      calc
        _ = d ^ ((-(1 / 4 : ℝ)) + 2) := by norm_num
        _ = d ^ (-(1 / 4 : ℝ)) * d ^ 2 := by
          rw [Real.rpow_add hd]
          norm_num
    rw [he]
    field_simp [hd.ne']
  have hPow1 : d ^ (7 / 4 : ℝ) / d =
      d ^ (3 / 4 : ℝ) := by
    have he : d ^ (7 / 4 : ℝ) =
        d ^ (3 / 4 : ℝ) * d := by
      calc
        _ = d ^ ((3 / 4 : ℝ) + 1) := by norm_num
        _ = d ^ (3 / 4 : ℝ) * d := by
          rw [Real.rpow_add hd]
          norm_num
    rw [he]
    field_simp [hd.ne']
  have hPow4 : d ^ (7 / 4 : ℝ) / d ^ 4 =
      d ^ (-(5 / 4 : ℝ)) / d := by
    calc
      _ = (d ^ (7 / 4 : ℝ) / d ^ 3) / d := by
        field_simp [hd.ne']
        ring
      _ = d ^ (-(5 / 4 : ℝ)) / d := by rw [hPow3]
  have hExpand :
      pmB * (vB ^ 3 + (2 * vB + zB) ^ 2 * zB) +
        pzB * ((vB + 2 * zB) ^ 2 * vB) +
        pcB * ((2 * vB + zB) ^ 2 * zB) =
      c1 * s / d ^ 4 +
        (c2 * s ^ 2 + c3 * s) / (d ^ 3 * q) +
        (c4 * s ^ 3 + c5 * s ^ 2) / (d ^ 2 * q ^ 2) +
        (c6 * s ^ 4 + c7 * s ^ 3) / (d * q ^ 3) := by
    dsimp [pmB,pzB,pcB,vB,zB,c1,c2,c3,c4,c5,c6,c7]
    field_simp [hd.ne',hq.ne']
    ring
  have hNormalize :
      d ^ (7 / 4 : ℝ) *
        (pmB * (vB ^ 3 + (2 * vB + zB) ^ 2 * zB) +
          pzB * ((vB + 2 * zB) ^ 2 * vB) +
          pcB * ((2 * vB + zB) ^ 2 * zB)) =
      A1 * (c1 * (q / d) + c2 * s + c3) +
        A2 * (c4 * s + c5) + A3 * (c6 * s + c7) := by
    rw [hExpand]
    have hReorder :
        d ^ (7 / 4 : ℝ) *
          (c1 * s / d ^ 4 +
            (c2 * s ^ 2 + c3 * s) / (d ^ 3 * q) +
            (c4 * s ^ 3 + c5 * s ^ 2) / (d ^ 2 * q ^ 2) +
            (c6 * s ^ 4 + c7 * s ^ 3) / (d * q ^ 3)) =
        (d ^ (7 / 4 : ℝ) / d ^ 4) * (c1 * s) +
        (d ^ (7 / 4 : ℝ) / d ^ 3) *
          ((c2 * s ^ 2 + c3 * s) / q) +
        (d ^ (7 / 4 : ℝ) / d ^ 2) *
          ((c4 * s ^ 3 + c5 * s ^ 2) / q ^ 2) +
        (d ^ (7 / 4 : ℝ) / d) *
          ((c6 * s ^ 4 + c7 * s ^ 3) / q ^ 3) := by
      ring
    rw [hReorder,hPow4,hPow3,hPow2,hPow1]
    dsimp [A1,A2,A3]
    field_simp [hd.ne',hq.ne']
    ring
  have hT1 : c1 * (q / d) + c2 * s + c3 ≤ K1 := by
    have h1 := mul_le_mul_of_nonneg_left hqdiv hc1
    have h2 := mul_le_mul_of_nonneg_left hs1 hc2
    dsimp [K1]
    linarith
  have hT2 : c4 * s + c5 ≤ K2 := by
    have h2 := mul_le_mul_of_nonneg_left hs1 hc4
    dsimp [K2]
    linarith
  have hT3 : c6 * s + c7 ≤ K3 := by
    have h3 := mul_le_mul_of_nonneg_left hs1 hc6
    dsimp [K3]
    linarith
  have hSums :
      A1 * (c1 * (q / d) + c2 * s + c3) +
        A2 * (c4 * s + c5) + A3 * (c6 * s + c7) ≤
      (K1 + K2 + K3) * T := by
    have hBoundK :
        A1 * (c1 * (q / d) + c2 * s + c3) +
          A2 * (c4 * s + c5) + A3 * (c6 * s + c7) ≤
        A1 * K1 + A2 * K2 + A3 * K3 := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left hT1 hA1pos)
          (mul_le_mul_of_nonneg_left hT2 hA2pos))
        (mul_le_mul_of_nonneg_left hT3 hA3pos)
    have hBoundA1 : A1 * K1 ≤ K1 * T := by
      simpa only [mul_comm] using
        (mul_le_mul_of_nonneg_left hA1 hK1)
    have hBoundA2 : A2 * K2 ≤ K2 * T := by
      simpa only [mul_comm] using
        (mul_le_mul_of_nonneg_left hA2 hK2)
    have hBoundA3 : A3 * K3 ≤ K3 * T := by
      simpa only [mul_comm] using
        (mul_le_mul_of_nonneg_left hA3 hK3)
    calc
      _ ≤ A1 * K1 + A2 * K2 + A3 * K3 := hBoundK
      _ ≤ K1 * T + K2 * T + K3 * T :=
        add_le_add (add_le_add hBoundA1 hBoundA2) hBoundA3
      _ = (K1 + K2 + K3) * T := by ring
  have hWeight : 0 ≤ d ^ (7 / 4 : ℝ) :=
    Real.rpow_nonneg hd.le _
  have hWeighted := mul_le_mul_of_nonneg_left hMono hWeight
  change d ^ (7 / 4 : ℝ) *
      (pm * (v ^ 3 + (2 * v + z) ^ 2 * z) +
        pz * ((v + 2 * z) ^ 2 * v) +
        pc * ((2 * v + z) ^ 2 * z)) ≤
    actualHartreeTenTermSourceConstant D E Cm Cz Cc *
      ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ))
  calc
    _ ≤ d ^ (7 / 4 : ℝ) *
        (pmB * (vB ^ 3 + (2 * vB + zB) ^ 2 * zB) +
          pzB * ((vB + 2 * zB) ^ 2 * vB) +
          pcB * ((2 * vB + zB) ^ 2 * zB)) := hWeighted
    _ = A1 * (c1 * (q / d) + c2 * s + c3) +
        A2 * (c4 * s + c5) + A3 * (c6 * s + c7) := hNormalize
    _ ≤ (K1 + K2 + K3) * T := hSums
    _ = actualHartreeTenTermSourceConstant D E Cm Cz Cc *
        ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ)) := by
      dsimp [K1,K2,K3,c1,c2,c3,c4,c5,c6,c7,
        T,actualHartreeTenTermSourceConstant]
      ring

end HBL.TypeIIDynamicSelection
