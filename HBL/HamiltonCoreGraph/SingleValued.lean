import HBL.HamiltonCoreGraph.Definitions
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.MainBackward
open HBL.Modulation HBL.Modulation.AffineTail
/-- The actual smooth graph is single-valued on radial energy equivalence classes. -/
theorem smoothHamiltonGraph_singleValued (q y z : CenterPair)
    (hy : SmoothHamiltonGraph q y) (hz : SmoothHamiltonGraph q z) : y = z := by
  obtain ⟨f,v,a,b,hf,hv,_ha,_hb,hfm,hvm,ham,hbm,hq,hy,hA,hB⟩ := hy
  obtain ⟨f',v',a',b',hf',hv',_ha',_hb',hfm',hvm',ham',hbm',hq',hz,hA',hB'⟩ := hz
  have he := hq.symm.trans hq'
  have hef := smoothEnergy_profile_injective f f' (hf.of_le (by norm_num))
    (hf'.of_le (by norm_num)) hfm hfm' (congrArg Prod.fst he)
  have hev := smoothEnergy_profile_injective v v' (hv.of_le (by norm_num))
    (hv'.of_le (by norm_num)) hvm hvm' (congrArg Prod.snd he)
  have huf : EqOn (radialU f) (radialU f') (Ioi (0 : ℝ)) :=
    fun r hr => by simp only [radialU, hef hr]
  have huv : EqOn (radialU v) (radialU v') (Ioi (0 : ℝ)) :=
    fun r hr => by simp only [radialU, hev hr]
  have hma := (actualHamilton_operators_congr _ _ huv).1
  have hmb := (actualHamilton_operators_congr _ _ huf).2
  rw [hy,hz]
  apply Prod.ext
  · apply smoothEnergy_coordinate_congr a a' ham ham'
    intro r hr
    rw [hA r hr, hA' r hr, hma hr]
  · apply smoothEnergy_coordinate_congr b b' hbm hbm'
    intro r hr
    rw [hB r hr, hB' r hr, hmb hr]
end HBL.MainBackward
