import HBL.KinematicSliceNormalizationBridge

/-!
The exact normalized physical-rate identity. It is an identity of positive
real quantities, before taking any limit along an actual parameter path.
-/

noncomputable section

namespace HBL.Kinematic

theorem inverseScale_div_physicalRate_eq {A Λ s l q : ℝ}
    (hA : 0 < A) (hΛ : 0 < Λ) (hs : 0 < s)
    (hl : 0 < l) (hq : 0 < q) :
    l⁻¹ / ((Λ ^ A * A ^ (-((A + 1) / 2))) *
        (q / l ^ 2) ^ ((A + 1) / 2)) =
      (q / (A * s)) ^ (-((A + 1) / 2)) *
        (l / (Λ * s ^ sliceBeta A)) ^ A := by
  have hAs : 0 < A * s := mul_pos hA hs
  have hb : 0 < Λ * s ^ sliceBeta A :=
    mul_pos hΛ (Real.rpow_pos_of_pos hs _)
  have hLa : 0 < Λ ^ A := Real.rpow_pos_of_pos hΛ _
  have hAa : 0 < A ^ (-((A + 1) / 2)) := Real.rpow_pos_of_pos hA _
  have hτ : 0 < q / l ^ 2 := div_pos hq (sq_pos_of_pos hl)
  have hqr : 0 < q / (A * s) := div_pos hq hAs
  have hlr : 0 < l / (Λ * s ^ sliceBeta A) := div_pos hl hb
  apply Real.log_injOn_pos
    (by change (0 : ℝ) < _; positivity) (by change (0 : ℝ) < _; positivity)
  rw [Real.log_div (inv_pos.mpr hl).ne'
      (mul_pos (mul_pos hLa hAa) (Real.rpow_pos_of_pos hτ _)).ne',
    Real.log_inv,
    Real.log_mul (mul_pos hLa hAa).ne' (Real.rpow_pos_of_pos hτ _).ne',
    Real.log_mul hLa.ne' hAa.ne',
    Real.log_rpow hΛ A, Real.log_rpow hA (-((A + 1) / 2)),
    Real.log_rpow hτ ((A + 1) / 2),
    Real.log_div hq.ne' (sq_pos_of_pos hl).ne', Real.log_pow,
    Real.log_mul (Real.rpow_pos_of_pos hqr _).ne' (Real.rpow_pos_of_pos hlr _).ne',
    Real.log_rpow hqr (-((A + 1) / 2)), Real.log_rpow hlr A,
    Real.log_div hq.ne' hAs.ne', Real.log_div hl.ne' hb.ne',
    Real.log_mul hA.ne' hs.ne',
    Real.log_mul hΛ.ne' (Real.rpow_pos_of_pos hs _).ne',
    Real.log_rpow hs (sliceBeta A)]
  unfold sliceBeta
  field_simp
  ring

end HBL.Kinematic
