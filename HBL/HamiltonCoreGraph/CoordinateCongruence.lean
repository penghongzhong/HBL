import HBL.RadialDotH1Model
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
namespace HBL.Modulation
/-- Positive-half-line radial equality suffices for equality of energy coordinates. -/
theorem smoothEnergy_coordinate_congr
    (f g : ℝ → ℝ)
    (hmf : MemLp (deriv (radialU f)) 2 (volume.restrict (Ioi (0 : ℝ))))
    (hmg : MemLp (deriv (radialU g)) 2 (volume.restrict (Ioi (0 : ℝ))))
    (he : EqOn (radialU f) (radialU g) (Ioi (0 : ℝ))) :
    smoothToRadialDotH1 f hmf = smoothToRadialDotH1 g hmg := by
  apply Lp.ext
  filter_upwards [smoothToRadialDotH1_ae f hmf, smoothToRadialDotH1_ae g hmg,
    ae_restrict_mem measurableSet_Ioi] with r hf hg hr
  rw [hf, hg]
  have hh : radialU f =ᶠ[𝓝 r] radialU g := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact he ht
  exact hh.deriv_eq
end HBL.Modulation
