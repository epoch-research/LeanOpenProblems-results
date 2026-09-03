import Submission.CubicBaseLocus

/-!
The first coordinate of the complete cubic parametrization has exactly three
rational projective zeros. This is an auxiliary arithmetic classification;
it does not assert the density estimate required by the conjecture.
-/
namespace Erdos1206.CubicCoordinateZeros
open CubicBaseLocus

lemma norm_zero_iff (a b : ℚ) : Q a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    dsimp [Q] at h
    have ha : a = 0 := by nlinarith [sq_nonneg (a-b),sq_nonneg b]
    subst a
    have hb : b = 0 := by nlinarith [sq_nonneg b]
    exact ⟨rfl,hb⟩
  · rintro ⟨rfl,rfl⟩
    norm_num [Q]

lemma first_second_difference (a b t : ℚ) :
    A a b t - B a b t = -3*b*Q (a-t) b := by
  dsimp [A,B,Q]
  ring

lemma first_third_difference (a b t : ℚ) :
    4*(A a b t-C a b t) =
      (2*a-b)*((2*t+3*b)^2+3*(2*a-b)^2) := by
  dsimp [A,C,Q]
  ring

lemma first_eq_second_iff (a b t : ℚ) : A a b t = B a b t ↔ b = 0 := by
  constructor
  · intro h
    have hz : -3*b*Q (a-t) b = 0 := by rw [←first_second_difference,h,sub_self]
    rcases mul_eq_zero.mp hz with hb | hq
    · rcases mul_eq_zero.mp hb with h3 | hb
      · norm_num at h3
      · exact hb
    · exact (norm_zero_iff _ _).mp hq |>.2
  · rintro rfl
    exact (zero_b_factorization a t).1.trans (zero_b_factorization a t).2.1.symm

lemma first_eq_third_iff (a b t : ℚ) : A a b t = C a b t ↔ b = 2*a := by
  constructor
  · intro h
    have hz : (2*a-b)*((2*t+3*b)^2+3*(2*a-b)^2) = 0 := by
      rw [←first_third_difference,h,sub_self,mul_zero]
    rcases mul_eq_zero.mp hz with hl | hq
    · linarith
    · nlinarith [sq_nonneg (2*t+3*b),sq_nonneg (2*a-b)]
  · rintro rfl
    exact (double_a_factorization a t).1.trans (double_a_factorization a t).2.2.1.symm

lemma identity (a b t : ℚ) : A a b t^3+D a b t^3=B a b t^3+C a b t^3 := by
  dsimp [A,B,C,D,Q]
  ring

/-- The three rational zero directions are `(-1,0,1)`, `(1,2,3)`, and
`(1,1,0)`. The origin is included in the displayed homogeneous description. -/
theorem first_zero_iff (a b t : ℚ) :
    A a b t = 0 ↔
      (b = 0 ∧ a = -t) ∨ (b = 2*a ∧ t = 3*a) ∨ (t = 0 ∧ a = b) := by
  constructor
  · intro hA
    have he : B a b t^3+C a b t^3=D a b t^3 := by
      have hh := identity a b t
      rw [hA,zero_pow (by decide : 3≠0),zero_add] at hh
      exact hh.symm
    have hz : B a b t = 0 ∨ C a b t = 0 ∨ D a b t = 0 := by
      by_contra hn
      push_neg at hn
      exact (fermatLastTheoremFor_iff_rat.mp fermatLastTheoremThree)
        _ _ _ hn.1 hn.2.1 hn.2.2 he
    rcases hz with hB | hC | hD
    · have hb : b = 0 := (first_eq_second_iff a b t).mp (hA.trans hB.symm)
      subst b
      have hh : (t+a)*(t^2+3*a^2) = 0 := (zero_b_factorization a t).1.symm.trans hA
      left
      refine ⟨rfl,?_⟩
      rcases mul_eq_zero.mp hh with hh | hh
      · linarith
      · have ha : a=0 := by nlinarith [sq_nonneg t,sq_nonneg a]
        have ht : t=0 := by nlinarith [sq_nonneg t,sq_nonneg a]
        simp [ha,ht]
    · have hb : b = 2*a := (first_eq_third_iff a b t).mp (hA.trans hC.symm)
      subst b
      have hh : (t-3*a)*(t^2+3*a^2) = 0 := (double_a_factorization a t).1.symm.trans hA
      right; left
      refine ⟨rfl,?_⟩
      rcases mul_eq_zero.mp hh with hh | hh
      · linarith
      · have ha : a=0 := by nlinarith [sq_nonneg t,sq_nonneg a]
        have ht : t=0 := by nlinarith [sq_nonneg t,sq_nonneg a]
        simp [ha,ht]
    · have hh : 2*t*(t^2+3*a^2) = 0 := by rw [←sum_outer,hA,hD,add_zero]
      have ht : t=0 := by
        rcases mul_eq_zero.mp hh with hh | hh
        · rcases mul_eq_zero.mp hh with h2 | ht
          · norm_num at h2
          · exact ht
        · nlinarith [sq_nonneg t,sq_nonneg a]
      subst t
      have hh : 3*Q a b*(a-b) = 0 := by simpa [A] using hA
      right; right
      refine ⟨rfl,?_⟩
      rcases mul_eq_zero.mp hh with hh | hh
      · have hq : Q a b=0 := (mul_eq_zero.mp hh).resolve_left (by norm_num)
        obtain ⟨rfl,rfl⟩ := (norm_zero_iff _ _).mp hq
        rfl
      · linarith
  · rintro (⟨rfl,ha⟩ | ⟨rfl,ht⟩ | ⟨rfl,ha⟩)
    · rw [(zero_b_factorization a t).1,ha]
      ring
    · rw [(double_a_factorization a t).1,ht]
      ring
    · simp [A,ha]

#print axioms first_zero_iff
/-- The same zero classification over the integers. -/
theorem first_zero_int_iff (a b t : ℤ) :
    A a b t = 0 ↔
      (b = 0 ∧ a = -t) ∨ (b = 2*a ∧ t = 3*a) ∨ (t = 0 ∧ a = b) := by
  have h := first_zero_iff (a : ℚ) (b : ℚ) (t : ℚ)
  have hcast : A (a : ℚ) (b : ℚ) (t : ℚ) = ((A a b t : ℤ) : ℚ) := by
    simp [A,Q]
  rw [hcast] at h
  exact_mod_cast h

lemma first_difference (a b c t : ℚ) :
    2*(A a b t-A a c t) =
      (c-b)*(3*(b+c-2*a)^2+3*b^2+3*c^2+4*t^2) := by
  dsimp [A,Q]
  ring

/-- A fixed integral value has at most one second parameter when the first
and third parameters are fixed. No bound on the other two parameters follows. -/
theorem first_strictAnti (a t : ℚ) : StrictAnti (fun b : ℚ => A a b t) := by
  intro b c hbc
  have hs : 0 < b^2+c^2 := by
    by_contra hh
    have hb : b=0 := by nlinarith [sq_nonneg b,sq_nonneg c]
    have hc : c=0 := by nlinarith [sq_nonneg b,sq_nonneg c]
    subst b; subst c
    exact (lt_irrefl 0) hbc
  have hp : 0 < 3*(b+c-2*a)^2+3*b^2+3*c^2+4*t^2 := by
    nlinarith [sq_nonneg (b+c-2*a),sq_nonneg t]
  have hm := mul_pos (sub_pos.mpr hbc) hp
  rw [←first_difference] at hm
  linarith

#print axioms first_zero_int_iff
#print axioms first_strictAnti

end Erdos1206.CubicCoordinateZeros
