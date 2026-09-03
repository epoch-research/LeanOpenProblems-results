import Submission.ShiftedLocalObstructions

/-!
# Reducing a shifted rational finite-divisor cover to a uniform modulus

This is auxiliary work, not a proof of Erdős 972. An eventual composite tail
is not assumed to admit a finite-divisor cover.
-/

namespace Explore972

private lemma linear_pair_admissible_of_coprime_constants (a b r s : ℤ)
    (hbr : IsCoprime b r) (has : IsCoprime a s) (hro : Odd r) (hso : Odd s) :
    ∀ l : ℕ, l.Prime → ∃ t : ℤ,
      ¬ (l : ℤ) ∣ b * t + r ∧ ¬ (l : ℤ) ∣ a * t + s := by
  intro l hl
  by_cases hl2 : l = 2
  · subst l
    refine ⟨0, ?_, ?_⟩
    · simpa using (show ¬ (2 : ℤ) ∣ r from fun h =>
        (Int.not_even_iff_odd.mpr hro) (even_iff_two_dvd.mpr h))
    · simpa using (show ¬ (2 : ℤ) ∣ s from fun h =>
        (Int.not_even_iff_odd.mpr hso) (even_iff_two_dvd.mpr h))
  letI : Fact l.Prime := ⟨hl⟩
  have hlarge : 2 < l := by have := hl.two_le; omega
  have hbr' : (b : ZMod l) ≠ 0 ∨ (r : ZMod l) ≠ 0 :=
    (hbr.intCast (R := ZMod l)).ne_zero_or_ne_zero
  have has' : (a : ZMod l) ≠ 0 ∨ (s : ZMod l) ≠ 0 :=
    (has.intCast (R := ZMod l)).ne_zero_or_ne_zero
  obtain ⟨t, ht₁, ht₂⟩ := exists_affine_pair_ne_zero
    (by simpa only [ZMod.card] using hlarge) (b : ZMod l) a r s hbr' has'
  refine ⟨(t.val : ℤ), ?_, ?_⟩
  · intro hdiv
    have he := (ZMod.intCast_zmod_eq_zero_iff_dvd (b * t.val + r) l).mpr hdiv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at he
    exact ht₁ he
  · intro hdiv
    have he := (ZMod.intCast_zmod_eq_zero_iff_dvd (a * t.val + s) l).mpr hdiv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at he
    exact ht₂ he

/-- Any eventual fixed-modulus obstruction for a shifted rational model forces
an obstruction modulo `2 * a`, independently of the original modulus and shift. -/
theorem shifted_tail_cover_reduces_to_twice_numerator
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (β : ℝ)
    (M : ℕ) (hM : 0 < M) (N : ℕ)
    (hcover : ∀ p : ℕ, N < p → p.Prime →
      ¬ (⌊(a : ℝ) / b * p + β⌋₊).Coprime M)
    (p : ℕ) (hp : p.Prime) (hpb : b < p) (hp2 : 2 < p) :
    ¬ (⌊(a : ℝ) / b * p + β⌋₊).Coprime (2 * a) := by
  intro hcop
  let q : ℕ := ⌊(a : ℝ) / b * p + β⌋₊
  have hqcop : q.Coprime (2 * a) := hcop
  have hqpos : 0 < q := by
    by_contra h
    have hqzero : q = 0 := by omega
    simp only [hqzero, Nat.coprime_zero_left] at hqcop
    omega
  have hx : 0 ≤ (a : ℝ) / b * p + β :=
    le_trans (by norm_num) (Nat.floor_pos.mp hqpos)
  have hqfloor : (q : ℤ) = ⌊(a : ℝ) / b * p + β⌋ :=
    Int.natCast_floor_eq_floor hx
  have hqc2 : q.Coprime 2 :=
    Nat.Coprime.of_dvd_right (dvd_mul_right 2 a) hqcop
  have hqca : q.Coprime a :=
    Nat.Coprime.of_dvd_right (dvd_mul_left a 2) hqcop
  have hpcb : p.Coprime b := hp.coprime_iff_not_dvd.mpr (by
    intro hdiv
    exact (not_le_of_gt hpb) (Nat.le_of_dvd hb hdiv))
  have hbr : IsCoprime (b : ℤ) (p : ℤ) := by
    exact Int.isCoprime_iff_nat_coprime.mpr (by simpa using hpcb.symm)
  have has : IsCoprime (a : ℤ) (q : ℤ) := by
    exact Int.isCoprime_iff_nat_coprime.mpr (by simpa using hqca.symm)
  have hpo : Odd (p : ℤ) := by
    exact_mod_cast hp.odd_of_ne_two (by omega)
  have hqo : Odd (q : ℤ) := by
    exact_mod_cast Nat.coprime_two_right.mp hqc2
  have hfloor : ∀ t : ℤ,
      ⌊(a : ℝ) / b * (((b : ℤ) * t + p : ℤ) : ℝ) + β⌋ =
        (a : ℤ) * t + q := by
    intro t
    have hbne : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
    have heq : (a : ℝ) / b * (((b : ℤ) * t + p : ℤ) : ℝ) + β =
        ((a : ℝ) / b * p + β) + (((a : ℤ) * t : ℤ) : ℝ) := by
      push_cast
      field_simp [hbne]; ring
    rw [heq, Int.floor_add_intCast, ← hqfloor]
    ring
  obtain ⟨p', hp'N, hp', hq'⟩ := shifted_prime_indices_coprime_of_model
    a b ha hb β p q hfloor
    (linear_pair_admissible_of_coprime_constants a b p q hbr has hpo hqo)
    M hM N
  exact hcover p' hp'N hp' hq'

#print axioms shifted_tail_cover_reduces_to_twice_numerator

end Explore972
