import HBL.KinematicPhysicalPhase

/-! Conversion from positive remaining time to the physical left-hand endpoint. -/

noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace HBL.Kinematic

theorem remainingTime_tendsto_zero_right (T : ℝ) :
    Tendsto (fun t : ℝ => T - t) (𝓝[<] T) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : Continuous (fun t : ℝ => T - t) := continuous_const.sub continuous_id
    have ht : Tendsto (fun t : ℝ => T - t) (𝓝[<] T) (𝓝 (T - T)) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [sub_self] using ht
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change t < T at ht
    change 0 < T - t
    exact sub_pos.mpr ht

end HBL.Kinematic
