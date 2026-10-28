import HBL.KummerLocalInverse.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

variable {mu theta z eps : ℝ}

def physicalLocalKummerValue (K : LocalKummerPair mu theta z eps) (d : ℝ) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  localAnnulusValue K (-d) d (fun t => F (z + t)) (r - z)

def physicalLocalKummerDeriv (K : LocalKummerPair mu theta z eps) (d : ℝ) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  localAnnulusDeriv K (-d) d (fun t => F (z + t)) (r - z)

def physicalLocalKummerSecond (K : LocalKummerPair mu theta z eps) (d : ℝ) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  localAnnulusSecond K (-d) d (fun t => F (z + t)) (r - z)
end HBL.Profile.Kummer
