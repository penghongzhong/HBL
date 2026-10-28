import HBL.KummerLocalInverse.PhysicalDefinitions
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.ContinuousMap.Compact
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

abbrev PhysicalAnnulus (z d : ℝ) := Icc (z - d) (z + d)

def annulusSourceExtension (z d : ℝ) (hd : 0 ≤ d) (F : C(PhysicalAnnulus z d, ℂ)) (r : ℝ) : ℂ :=
  F (projIcc (z - d) (z + d) (by linarith) r)
end HBL.Profile.Kummer
