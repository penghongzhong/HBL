import HBL.KummerBoundaryUnique.HomogeneousZero
import HBL.KummerBoundaryUnique.SolutionDifference
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem kummer_base_boundary_solution_unique {mu theta z eps d : ℝ}
    (K : LocalKummerPair mu theta z eps) (hd : 0 < d) (hde : d < eps)
    (F : AnnulusSource z d) (U V : AnnulusJet z d)
    (hU : IsKummerBoundarySolution K d (frozenZeroCoeff mu theta) F U)
    (hV : IsKummerBoundarySolution K d (frozenZeroCoeff mu theta) F V) : U = V := by
  have hdiff := kummer_boundary_solution_sub K _ F F U V hU hV
  rw [sub_self] at hdiff
  obtain ⟨u,v,hjet,hD,hp,hm⟩ := hdiff
  have hshift : ∀ t ∈ Icc (-d) d,
      HasDerivAt (fun s => u (z+s)) (v (z+t)) t ∧
      HasDerivAt (fun s => v (z+s))
        (-(frozenFirstCoeff (z+t) * v (z+t) + frozenZeroCoeff mu theta * u (z+t))) t := by
    intro t ht
    have hr : z+t ∈ PhysicalAnnulus z d := by constructor <;> linarith [ht.1,ht.2]
    have hc : HasDerivAt (fun s : ℝ => z+s) 1 t := by
      simpa only [id_eq] using (hasDerivAt_id t).const_add z
    constructor
    · simpa only [Function.comp_def, one_smul] using (hD (z+t) hr).1.scomp t hc
    · have hv := (hD (z+t) hr).2.scomp t hc
      simp only [Function.comp_def, one_smul] at hv
      convert hv using 1
      change -(_+_) = (0-_ - _)
      ring
  have hz := kummer_homogeneous_boundary_zero K hd hde
    (fun s => u (z+s)) (fun s => v (z+s)) hshift hp
    (by simpa only [sub_eq_add_neg] using hm)
  apply sub_eq_zero.mp
  apply ContinuousMap.ext
  intro r
  have ht : (r:ℝ)-z ∈ Icc (-d) d := by
    constructor <;> linarith [r.property.1,r.property.2]
  have h := hz ((r:ℝ)-z) ht
  have he : z+((r:ℝ)-z) = r := by ring
  rw [he] at h
  change (U-V) r = (0 : ℂ × ℂ)
  rw [hjet,h.1,h.2]
  rfl
end HBL.Profile.Kummer
