import HBL.AffineTailOperators
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
namespace HBL.Modulation.AffineTail
/-- Both actual operators depend only on the positive-half-line profile.
The nonlocal term is compared directly under its defining integral. -/
theorem actualHamilton_operators_congr
    (u w : ℝ → ℝ) (he : EqOn u w (Ioi (0 : ℝ))) :
    EqOn (hMinusApply u) (hMinusApply w) (Ioi (0 : ℝ)) ∧
    EqOn (hPlusApply u) (hPlusApply w) (Ioi (0 : ℝ)) := by
  have hnear (r : ℝ) (hr : 0 < r) : u =ᶠ[𝓝 r] w := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact he ht
  have hn (r : ℝ) : nonlocalApply u r = nonlocalApply w r := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [he ht]
  constructor
  · intro r hr
    simp only [hMinusApply, (hnear r hr).deriv.deriv_eq, he hr]
  · intro r hr
    simp only [hPlusApply, (hnear r hr).deriv.deriv_eq, he hr, hn r]
end HBL.Modulation.AffineTail
