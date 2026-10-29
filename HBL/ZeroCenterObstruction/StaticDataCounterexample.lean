import HBL.ZeroCenterObstruction.Definitions
noncomputable section
set_option autoImplicit false
namespace HBL.ZeroCenterObstruction

/-- This refutes an abstract inference from static form data to invariant splitting.
It is not a counterexample to the Hartree PDE or its main blow-up theorem. -/
theorem static_data_do_not_force_zero_center_splitting :
    (∀ x y, dot (J x) y = -dot x (J y)) ∧
    (∀ x, J (J x) = -x) ∧
    (∀ x y, dot (L x) y = dot x (L y)) ∧
    (∀ x, dot (L x) x = -x.1.1^2 + x.1.2^2 + x.2.2.1^2 + x.2.2.2^2) ∧
    (∀ x, A x = ((x.1.2,x.1.1),(x.2.2,0))) ∧
    (A plusMode = plusMode ∧ A minusMode = -minusMode) ∧
    (∀ x, A x = 0 ↔ ∃ z, x = zeroMode z) ∧
    (∀ c, dot (L (centerMode c)) (centerMode c) = c.1^2+c.2^2 ∧
      ‖c‖^2 ≤ dot (L (centerMode c)) (centerMode c)) ∧
    (∀ ell : Plane →ₗ[ℝ] Plane, ¬ ∀ c, ∃ b, A (graphMode ell c) = graphMode ell b) ∧
    ¬ HasInvariantZeroProjection := by
  have hA (x : State) : A x = ((x.1.2,x.1.1),(x.2.2,0)) := by
    ext <;> simp [A,J,L,symplecticLinear,hessianLinear]
  refine ⟨?_,?_,?_,?_,hA,?_,?_,?_,?_,?_⟩
  · intro x y
    simp [dot,J,symplecticLinear]
    ring
  · intro x
    ext <;> simp [J,symplecticLinear]
  · intro x y
    simp [dot,L,hessianLinear]
  · intro x
    simp [dot,L,hessianLinear]
    ring
  · constructor <;> rw [hA] <;> norm_num [plusMode,minusMode]
  · intro x
    constructor
    · intro hx
      rw [hA] at hx
      have hh := congrArg Prod.fst hx
      have hc := congrArg (fun y : State => y.2.1) hx
      refine ⟨x.2.1, ?_⟩
      have h1 := congrArg Prod.fst hh
      have h2 := congrArg Prod.snd hh
      apply Prod.ext
      · exact Prod.ext h2 h1
      · exact Prod.ext rfl hc
    · rintro ⟨z,rfl⟩
      rw [hA]
      rfl
  · intro c
    have hq : dot (L (centerMode c)) (centerMode c) = c.1^2+c.2^2 := by
      simp [dot,L,hessianLinear,centerMode]
      ring
    refine ⟨hq,?_⟩
    rw [hq, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_total |c.1| |c.2| with h | h
    · rw [max_eq_right h, sq_abs]
      nlinarith [sq_nonneg c.1]
    · rw [max_eq_left h, sq_abs]
      nlinarith [sq_nonneg c.2]
  · intro ell hg
    obtain ⟨b,hb⟩ := hg (1,0)
    rw [hA] at hb
    have hbottom : b = 0 := (congrArg (fun y : State => y.2.2) hb).symm
    have htop := congrArg (fun y : State => y.2.1.1) hb
    simp [graphMode,hbottom] at htop
  · rintro ⟨P,hfix,hker,hcomm⟩
    have h := hcomm (centerMode (1,0))
    rw [hker] at h
    have he : A (centerMode (1,0)) = zeroMode (1,0) := hA _
    rw [he,hfix] at h
    have hbad := congrArg (fun y : State => y.2.1.1) h
    norm_num [zeroMode] at hbad
end HBL.ZeroCenterObstruction
