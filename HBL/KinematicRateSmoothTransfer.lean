import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Asymptotics.Lemmas

/-! First-order error transfer through the smooth normalized rate factor. -/

noncomputable section

open Filter Asymptotics
open scoped Topology

namespace HBL.Kinematic

theorem normalizedRateFactor_sub_one_isBigO
    {α : Type*} {l : Filter α} (A : ℝ) {Q F d : α → ℝ}
    (hQ : Tendsto Q l (𝓝 1)) (hF : Tendsto F l (𝓝 0))
    (hQO : (fun x => Q x - 1) =O[l] d) (hFO : F =O[l] d) :
    (fun x => Q x ^ (-(1 / 2 : ℝ)) * Real.exp (-(A / 2) * F x) - 1)
      =O[l] d := by
  have hpder := Real.hasDerivAt_rpow_const
    (x := (1 : ℝ)) (p := -(1 / 2 : ℝ)) (Or.inl one_ne_zero)
  have hp : (fun x => Q x ^ (-(1 / 2 : ℝ)) - 1) =O[l] d := by
    have hp0 : (fun x => Q x ^ (-(1 / 2 : ℝ)) - 1) =O[l]
        (fun x => Q x - 1) := by
      simpa only [Function.comp_def, Real.one_rpow] using
        hpder.isBigO_sub.comp_tendsto hQ
    exact hp0.trans hQO
  have heder := ((hasDerivAt_id (0 : ℝ)).const_mul (-(A / 2))).exp
  have he : (fun x => Real.exp (-(A / 2) * F x) - 1) =O[l] d := by
    have he0 : (fun x => Real.exp (-(A / 2) * F x) - 1) =O[l] F := by
      simpa only [Function.comp_def, id_eq, mul_zero, Real.exp_zero, sub_zero] using
        heder.isBigO_sub.comp_tendsto hF
    exact he0.trans hFO
  have helim : Tendsto (fun x => Real.exp (-(A / 2) * F x)) l (𝓝 1) := by
    simpa only [Function.comp_def, mul_zero, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp (hF.const_mul (-(A / 2)))
  have hprod : (fun x => (Q x ^ (-(1 / 2 : ℝ)) - 1) *
      Real.exp (-(A / 2) * F x)) =O[l] d := by
    simpa only [mul_one] using hp.mul (helim.isBigO_one ℝ)
  have hsum := hprod.add he
  convert hsum using 1
  funext x
  ring

end HBL.Kinematic
