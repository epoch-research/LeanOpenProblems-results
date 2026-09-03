import Submission.PrimeBandProgressions

/-! The even-character part of the opposite-residue prime discrepancy
cancels exactly. No estimate of the remaining odd-character sum is claimed. -/

namespace Erdos371
open Finset

noncomputable def oddResidueDifference (p : ℕ) (x : ZMod p) : ℂ :=
  (if x = 1 then 1 else 0) - (if x = -1 then 1 else 0)

lemma odd_character_orthogonality (p : ℕ) [NeZero p] (x : ZMod p) :
    (p.totient : ℂ)*oddResidueDifference p x =
      2 * ∑ χ : DirichletCharacter ℂ p, if χ.Odd then χ x else 0 := by
  classical
  have he : (∑ χ : DirichletCharacter ℂ p, (χ x - χ (-x))) =
      2 * ∑ χ : DirichletCharacter ℂ p, if χ.Odd then χ x else 0 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro χ _
    rcases χ.even_or_odd with h | h
    · rw [DirichletCharacter.Even.eval_neg χ x h,if_neg h.not_odd]
      ring
    · rw [DirichletCharacter.Odd.eval_neg χ x h,if_pos h]
      ring
  rw [sum_sub_distrib,DirichletCharacter.sum_characters_eq,
    DirichletCharacter.sum_characters_eq] at he
  rw [← he]
  unfold oddResidueDifference
  have hneg : -x = 1 ↔ x = -1 := by exact neg_eq_iff_eq_neg
  simp only [hneg]
  split_ifs <;> ring

/-- The prime principal term, and all other even characters, vanish
before any absolute values are taken. -/
theorem oppositePrimeCount_odd_characters (C X p b : ℕ) [NeZero p] (hb : 0 < b) :
    (p.totient : ℂ)*((oppositePrimeCount C X p b true : ℂ)-
      oppositePrimeCount C X p b false) =
    2 * ∑ χ : DirichletCharacter ℂ p, if χ.Odd then
      χ (b : ZMod p) * ∑ q ∈ (Ioc C X).filter Nat.Prime, χ (q : ZMod p) else 0 := by
  classical
  have hcounts : ((oppositePrimeCount C X p b true : ℂ)-
      oppositePrimeCount C X p b false) =
      ∑ q ∈ (Ioc C X).filter Nat.Prime, oddResidueDifference p ((b : ZMod p)*(q : ZMod p)) := by
    unfold oppositePrimeCount
    rw [← sum_boole,← sum_boole,← sum_sub_distrib,sum_filter]
    apply sum_congr rfl
    intro q hq
    by_cases hqp : q.Prime
    · have hprod : 1 ≤ b*q := by have := hqp.pos; nlinarith
      simp only [if_true,Bool.false_eq_true,if_false,hqp,true_and,
        dvd_sub_one_iff_zmod p b q hprod,dvd_add_one_iff_zmod,oddResidueDifference]
    · simp [hqp]
  rw [hcounts,mul_sum]
  simp_rw [odd_character_orthogonality,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro χ _
  by_cases ho : χ.Odd
  · simp only [if_pos ho,map_mul,Finset.mul_sum]
  · simp [ho]

lemma odd_character_gram (p : ℕ) [Fact p.Prime] (a b : ZMod p) (ha : IsUnit a) :
    2 * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ p)).filter DirichletCharacter.Odd,
      (starRingEnd ℂ) (χ a) * χ b =
    (p.totient : ℂ)*((if a=b then 1 else 0)-(if a = -b then 1 else 0)) := by
  classical
  have hc (χ : DirichletCharacter ℂ p) : (starRingEnd ℂ) (χ a) = χ a⁻¹ := by
    rw [starRingEnd_apply,MulChar.star_apply',MulChar.inv_apply']
  rw [sum_filter]
  simp_rw [hc,← map_mul]
  rw [← odd_character_orthogonality]
  unfold oddResidueDifference
  have hpos := ZMod.inv_mul_eq_one_of_isUnit ha b
  have hneg : a⁻¹*b = -1 ↔ a = -b := by
    rw [← ZMod.inv_mul_eq_one_of_isUnit ha (-b),mul_neg,neg_eq_iff_eq_neg]
  simp only [hpos,hneg]

lemma odd_character_gram_initial (p A a b : ℕ) [Fact p.Prime]
    (hAp : 2*A < p) (ha : a ∈ Icc 1 A) (hb : b ∈ Icc 1 A) :
    2 * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ p)).filter DirichletCharacter.Odd,
      (starRingEnd ℂ) (χ (a : ZMod p)) * χ (b : ZMod p) =
    if a=b then (p.totient : ℂ) else 0 := by
  obtain ⟨ha0,haA⟩ := mem_Icc.mp ha
  obtain ⟨hb0,hbA⟩ := mem_Icc.mp hb
  have hap : a < p := by omega
  have hbp : b < p := by omega
  have hp : p.Prime := Fact.out
  have hac : a.Coprime p := by
    apply Nat.Coprime.symm
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    have := Nat.le_of_dvd ha0 hd
    omega
  have hapos : IsUnit (a : ZMod p) := (ZMod.isUnit_iff_coprime a p).mpr hac
  rw [odd_character_gram p _ _ hapos]
  have heq : (a : ZMod p) = (b : ZMod p) ↔ a=b := by
    rw [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt hap,Nat.mod_eq_of_lt hbp]
  have hneg : (a : ZMod p) ≠ -(b : ZMod p) := by
    intro he
    have hd : p ∣ a+b := (ZMod.natCast_eq_zero_iff (a+b) p).mp (by
      rw [Nat.cast_add,he,neg_add_cancel])
    have := Nat.le_of_dvd (by omega : 0 < a+b) hd
    omega
  simp only [heq,if_neg hneg,sub_zero]
  split_ifs <;> ring

/-- The odd-character energy of the cofactor interval is exactly half
of the full character energy when the interval and its negative do not
intersect modulo p. This is a finite orthogonality identity, not a prime
character-sum estimate. -/
theorem odd_initial_interval_energy (p A : ℕ) [Fact p.Prime] (hAp : 2*A < p) :
    2 * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ p)).filter DirichletCharacter.Odd,
      ‖∑ b ∈ Icc 1 A, χ (b : ZMod p)‖^2 = (p.totient : ℝ)*A := by
  classical
  have hc : (2 : ℂ) * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ p)).filter DirichletCharacter.Odd,
      (starRingEnd ℂ) (∑ b ∈ Icc 1 A, χ (b : ZMod p)) *
        (∑ b ∈ Icc 1 A, χ (b : ZMod p)) = (p.totient : ℂ)*A := by
    calc
      _ = ∑ a ∈ Icc 1 A, ∑ b ∈ Icc 1 A,
          2 * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ p)).filter DirichletCharacter.Odd,
            (starRingEnd ℂ) (χ (a : ZMod p)) * χ (b : ZMod p) := by
        simp_rw [map_sum,sum_mul_sum,mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro a ha
        rw [sum_comm]
      _ = ∑ a ∈ Icc 1 A, ∑ b ∈ Icc 1 A,
          if a=b then (p.totient : ℂ) else 0 := by
        apply sum_congr rfl
        intro a ha
        apply sum_congr rfl
        intro b hb
        exact odd_character_gram_initial p A a b hAp ha hb
      _ = _ := by
        simp only [sum_ite_eq,mem_Icc]
        have he (a : ℕ) (ha : a ∈ Icc 1 A) :
            (if 1 ≤ a ∧ a ≤ A then (p.totient : ℂ) else 0) = p.totient :=
          if_pos (mem_Icc.mp ha)
        rw [sum_congr rfl he]
        simp only [sum_const,nsmul_eq_mul,Nat.card_Icc]
        have hcard : A+1-1=A := by omega
        rw [hcard]
        ring
  simp_rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq] at hc
  exact_mod_cast hc

/-- A rectangular block: the prime interval does not depend on b here.
The original arithmetic sum has a hyperbolic endpoint X/b instead. -/
noncomputable def rectangularOppositePrimeSkew (C X p A : ℕ) : ℂ :=
  ∑ b ∈ Icc 1 A, ((oppositePrimeCount C X p b true : ℂ)-
    oppositePrimeCount C X p b false)

lemma rectangularOppositePrimeSkew_characters (C X p A : ℕ) [NeZero p] :
    (p.totient : ℂ)*rectangularOppositePrimeSkew C X p A =
    2 * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ p)).filter DirichletCharacter.Odd,
      (∑ b ∈ Icc 1 A, χ (b : ZMod p)) *
        (∑ q ∈ (Ioc C X).filter Nat.Prime, χ (q : ZMod p)) := by
  classical
  unfold rectangularOppositePrimeSkew
  rw [mul_sum]
  calc
    _ = ∑ b ∈ Icc 1 A,
        2 * ∑ χ : DirichletCharacter ℂ p, if χ.Odd then
          χ (b : ZMod p) * (∑ q ∈ (Ioc C X).filter Nat.Prime, χ (q : ZMod p)) else 0 := by
      apply sum_congr rfl
      intro b hb
      exact oppositePrimeCount_odd_characters C X p b (mem_Icc.mp hb).1
    _ = _ := by
      simp_rw [← sum_filter,mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro χ hχ
      rw [sum_comm]
      apply sum_congr rfl
      intro q hq
      simp only [sum_mul,mul_sum]

lemma complex_sum_mul_norm_sq_le {ι : Type*} (S : Finset ι) (f g : ι → ℂ) :
    ‖∑ i ∈ S, f i*g i‖^2 ≤ (∑ i ∈ S, ‖f i‖^2)*(∑ i ∈ S, ‖g i‖^2) := by
  have hnorm := norm_sum_le S (fun i => f i*g i)
  simp only [norm_mul] at hnorm
  have hnonneg : 0 ≤ ∑ i ∈ S, ‖f i‖*‖g i‖ := sum_nonneg (by intros; positivity)
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (sum_mul_sq_le_sq_mul_sq S (fun i => ‖f i‖) (fun i => ‖g i‖))

/-- A cofactor-averaged estimate. It leaves the odd prime-character
energy on the right; this energy is not estimated here. -/
theorem rectangularOppositePrimeSkew_energy_bound (C X p A : ℕ)
    [Fact p.Prime] (hAp : 2*A < p) :
    (p.totient : ℝ)*‖rectangularOppositePrimeSkew C X p A‖^2 ≤
      2*A * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ p)).filter DirichletCharacter.Odd,
        ‖∑ q ∈ (Ioc C X).filter Nat.Prime, χ (q : ZMod p)‖^2 := by
  classical
  let S := (univ : Finset (DirichletCharacter ℂ p)).filter DirichletCharacter.Odd
  let f : DirichletCharacter ℂ p → ℂ := fun χ => ∑ b ∈ Icc 1 A, χ (b : ZMod p)
  let g : DirichletCharacter ℂ p → ℂ := fun χ => ∑ q ∈ (Ioc C X).filter Nat.Prime, χ (q : ZMod p)
  have he : 2 * (∑ χ ∈ S, ‖f χ‖^2) = (p.totient : ℝ)*A :=
    odd_initial_interval_energy p A hAp
  have he' := congrArg (fun z : ℝ => 2*z*(∑ χ ∈ S, ‖g χ‖^2)) he
  have hc := complex_sum_mul_norm_sq_le S f g
  have hn := congrArg norm (rectangularOppositePrimeSkew_characters C X p A)
  change ‖(p.totient : ℂ)*rectangularOppositePrimeSkew C X p A‖ =
    ‖(2 : ℂ)*(∑ χ ∈ S, f χ*g χ)‖ at hn
  simp only [norm_mul,Complex.norm_natCast,Complex.norm_ofNat] at hn
  have hn' := congrArg (fun z : ℝ => z^2) hn
  simp only [mul_pow] at hn'
  norm_num only [OfNat.ofNat] at hn'
  have hp : 0 < (p.totient : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (show p.Prime from Fact.out).pos)
  change (p.totient : ℝ)*‖rectangularOppositePrimeSkew C X p A‖^2 ≤
    2*A*(∑ χ ∈ S, ‖g χ‖^2)
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith

#print axioms rectangularOppositePrimeSkew_energy_bound
#print axioms odd_initial_interval_energy
#print axioms odd_character_orthogonality
#print axioms oppositePrimeCount_odd_characters
end Erdos371
