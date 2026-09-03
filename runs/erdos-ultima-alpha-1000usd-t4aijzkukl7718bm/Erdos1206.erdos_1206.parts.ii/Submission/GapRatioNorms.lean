import Submission.InertPrimeCubes

/-! Restrictions on all reduced gap ratios of cubic collisions.
These do not establish positive density or its impossibility. -/

namespace Erdos1206

private lemma inert_cofactor_unit_nat {p a b : ℕ} (hp : p.Prime) (hp3 : p%3=2)
    (ha : ¬ p ∣ a) : ¬ p ∣ a^2+a*b+b^2 := by
  have haZ : ¬ (p : ℤ) ∣ (a : ℤ) := by exact_mod_cast ha
  have hh := inert_prime_not_dvd_cube_cofactor hp hp3 (b := (b : ℤ)) haZ
  exact_mod_cast hh

/-- At an inert prime, the quadratic cube cofactor has twice the valuation
of the common factor of its roots. -/
lemma inert_cube_cofactor_factorization {p : ℕ} (hp : p.Prime) (hp3 : p%3=2)
    {a : ℕ} (ha : 0<a) (b : ℕ) :
    (a^2+a*b+b^2).factorization p = 2*(Nat.gcd a b).factorization p := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases hpa : p ∣ a
    · by_cases hpb : p ∣ b
      · rcases hpa with ⟨x,rfl⟩
        rcases hpb with ⟨y,rfl⟩
        have hx : 0<x := Nat.pos_of_mul_pos_left ha
        have hxp : x<p*x := by have := hp.two_le; nlinarith
        have hh := ih x hxp hx y
        have hQ : 0<x^2+x*y+y^2 := by positivity
        have hg : 0<Nat.gcd x y := Nat.gcd_pos_of_pos_left y hx
        have he : (p*x)^2+(p*x)*(p*y)+(p*y)^2=p^2*(x^2+x*y+y^2) := by ring
        rw [he,Nat.gcd_mul_left,Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hQ.ne',
          Nat.factorization_mul hp.ne_zero hg.ne']
        simp only [Finsupp.add_apply,Nat.factorization_pow,Finsupp.smul_apply,
          smul_eq_mul,hp.factorization_self]
        omega
      · have hQ : ¬p ∣ a^2+a*b+b^2 := by
          simpa [add_comm,add_left_comm,add_assoc,mul_comm] using inert_cofactor_unit_nat hp hp3 hpb (b := a)
        have hg : ¬p ∣ Nat.gcd a b := fun h => hpb (h.trans (Nat.gcd_dvd_right a b))
        rw [Nat.factorization_eq_zero_of_not_dvd hQ,Nat.factorization_eq_zero_of_not_dvd hg]
    · have hQ := inert_cofactor_unit_nat hp hp3 hpa (b := b)
      have hg : ¬p ∣ Nat.gcd a b := fun h => hpa (h.trans (Nat.gcd_dvd_left a b))
      rw [Nat.factorization_eq_zero_of_not_dvd hQ,Nat.factorization_eq_zero_of_not_dvd hg]

/-- Exact valuation balance between the two gaps in equal differences of cubes. -/
lemma cube_collision_gap_factorization_balance {p h k b d : ℕ}
    (hp : p.Prime) (hp3 : p%3=2) (hh : 0<h) (hk : 0<k)
    (he : (b+h)^3+d^3=b^3+(d+k)^3) :
    h.factorization p + 2*(Nat.gcd (b+h) b).factorization p =
      k.factorization p + 2*(Nat.gcd (d+k) d).factorization p := by
  let Q₁ := (b+h)^2+(b+h)*b+b^2
  let Q₂ := (d+k)^2+(d+k)*d+d^2
  have hQ₁ : 0<Q₁ := by dsimp [Q₁]; positivity
  have hQ₂ : 0<Q₂ := by dsimp [Q₂]; positivity
  have he' : h*Q₁=k*Q₂ := by dsimp [Q₁,Q₂]; nlinarith only [he]
  have hf := congrArg (fun n : ℕ => n.factorization p) he'
  dsimp only at hf
  rw [Nat.factorization_mul hh.ne' hQ₁.ne',Nat.factorization_mul hk.ne' hQ₂.ne'] at hf
  simp only [Finsupp.add_apply] at hf
  dsimp only [Q₁,Q₂] at hf
  rw [inert_cube_cofactor_factorization hp hp3 (by omega) b,
    inert_cube_cofactor_factorization hp hp3 (by omega) d] at hf
  exact hf

/-- Every inert-prime exponent in either coprime numerator of a reduced gap
ratio is even. This is the Eisenstein-norm restriction on the ratio. -/
theorem cube_collision_reduced_gap_inert_even {p g u v b d : ℕ}
    (hp : p.Prime) (hp3 : p%3=2) (hg : 0<g) (hu : 0<u) (hv : 0<v)
    (hc : Nat.Coprime u v)
    (he : (b+g*u)^3+d^3=b^3+(d+g*v)^3) :
    Even (u.factorization p) ∧ Even (v.factorization p) := by
  have hf := cube_collision_gap_factorization_balance hp hp3 (Nat.mul_pos hg hu)
    (Nat.mul_pos hg hv) he
  rw [Nat.factorization_mul hg.ne' hu.ne',Nat.factorization_mul hg.ne' hv.ne'] at hf
  simp only [Finsupp.add_apply] at hf
  have hz : u.factorization p=0 ∨ v.factorization p=0 := by
    by_cases hpu : p ∣ u
    · have hpv : ¬p ∣ v := by
        intro hd
        have hh := Nat.dvd_gcd hpu hd
        rw [hc.gcd_eq_one] at hh
        exact hp.not_dvd_one hh
      exact Or.inr (Nat.factorization_eq_zero_of_not_dvd hpv)
    · exact Or.inl (Nat.factorization_eq_zero_of_not_dvd hpu)
  simp only [even_iff_two_dvd,Nat.dvd_iff_mod_eq_zero]
  omega

/-- As a special case, a reduced gap ratio of two is impossible. -/
theorem no_cube_collision_gap_ratio_two {g b d : ℕ} (hg : 0<g) :
    (b+g)^3+d^3 ≠ b^3+(d+2*g)^3 := by
  intro he
  have hh := cube_collision_reduced_gap_inert_even (p := 2) (g := g) (u := 1) (v := 2)
    (by norm_num) (by norm_num) hg (by norm_num) (by norm_num) (by norm_num)
    (by simpa [mul_comm] using he)
  norm_num at hh

#print axioms inert_cube_cofactor_factorization
#print axioms cube_collision_gap_factorization_balance
#print axioms cube_collision_reduced_gap_inert_even
#print axioms no_cube_collision_gap_ratio_two

end Erdos1206
