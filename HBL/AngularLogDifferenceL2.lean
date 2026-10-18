import HBL.AngularLogDifference
import HBL.LogSinSquareIntegrability

/-!
`L²` control for the angular logarithmic Hartree kernel.

The only singularities are logarithmic.  The endpoint majorant proved in
`LogSinSquareIntegrability` therefore supplies the exact hypothesis needed
for the cross-term Parseval identity.
-/

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace HBL

theorem logAbsSin_sq_periodic :
    Function.Periodic (fun x : ℝ => logAbsSin x ^ 2) Real.pi := by
  intro x
  change logAbsSin (x + Real.pi) ^ 2 = logAbsSin x ^ 2
  rw [logAbsSin_periodic x]

theorem logAbsSin_sq_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => logAbsSin x ^ 2) volume a b := by
  have hbase : IntervalIntegrable (fun x : ℝ => logAbsSin x ^ 2)
      volume 0 Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le Real.pi_pos.le]
    simpa only [logAbsSin_eq_log_sin] using
      integrableOn_log_sin_sq_Ioo_zero_pi
  have hbase' : IntervalIntegrable (fun x : ℝ => logAbsSin x ^ 2)
      volume 0 (0 + Real.pi) := by simpa using hbase
  exact logAbsSin_sq_periodic.intervalIntegrable Real.pi_ne_zero hbase' a b

theorem memLp_logAbsSin_add_Ioc (theta : ℝ) :
    MemLp (fun s : ℝ => logAbsSin (theta + s)) 2
      (volume.restrict (Ioc 0 Real.pi)) := by
  have hsq : IntervalIntegrable
      (fun s : ℝ => logAbsSin (theta + s) ^ 2) volume 0 Real.pi := by
    have h := (logAbsSin_sq_intervalIntegrable theta
      (theta + Real.pi)).comp_add_right theta
    simpa only [sub_self, zero_add, add_comm theta,
      add_sub_cancel_right] using h
  have hm : AEStronglyMeasurable
      (fun s : ℝ => logAbsSin (theta + s))
      (volume.restrict (Ioc 0 Real.pi)) := by
    have hm0 : Measurable (fun s : ℝ => Real.sin (theta + s)) :=
      Real.continuous_sin.measurable.comp (measurable_const.add measurable_id)
    have hm1 : Measurable (fun s : ℝ => logAbsSin (theta + s)) := by
      simpa only [logAbsSin_eq_log_sin] using hm0.log
    exact hm1.aestronglyMeasurable.restrict
  exact (memLp_two_iff_integrable_sq hm).2 hsq.1

theorem memLp_logAbsSin_sub_Ioc (theta : ℝ) :
    MemLp (fun s : ℝ => logAbsSin (theta - s)) 2
      (volume.restrict (Ioc 0 Real.pi)) := by
  have hsq : IntervalIntegrable
      (fun s : ℝ => logAbsSin (theta - s) ^ 2) volume 0 Real.pi := by
    have h := (logAbsSin_sq_intervalIntegrable theta
      (theta - Real.pi)).comp_sub_left theta
    simpa only [sub_self, sub_sub_cancel] using h
  have hm : AEStronglyMeasurable
      (fun s : ℝ => logAbsSin (theta - s))
      (volume.restrict (Ioc 0 Real.pi)) := by
    have hm0 : Measurable (fun s : ℝ => Real.sin (theta - s)) :=
      Real.continuous_sin.measurable.comp (measurable_const.sub measurable_id)
    have hm1 : Measurable (fun s : ℝ => logAbsSin (theta - s)) := by
      simpa only [logAbsSin_eq_log_sin] using hm0.log
    exact hm1.aestronglyMeasurable.restrict
  exact (memLp_two_iff_integrable_sq hm).2 hsq.1

theorem memLp_angularLogDifference_Ioc (theta : ℝ) :
    MemLp (angularLogDifference theta) 2
      (volume.restrict (Ioc 0 Real.pi)) := by
  exact (memLp_logAbsSin_add_Ioc theta).sub (memLp_logAbsSin_sub_Ioc theta)

theorem memLp_angularLogDifferenceC_Ioc (theta : ℝ) :
    MemLp (angularLogDifferenceC theta) 2
      (volume.restrict (Ioc 0 Real.pi)) := by
  exact (memLp_angularLogDifference_Ioc theta).ofReal

end HBL
