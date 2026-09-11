import FormalConjectures.Util.ProblemImports

open Nat

/--
Numbers whose prime divisors all end in the same digit.
-/
def A381159_condition (n : ℕ) : Prop :=
  Finset.card (n.primeFactors.image (fun p => p % 10)) ≤ 1

/--
A381159: Numbers whose prime divisors all end in the same digit.
-/
noncomputable def A381159 (n : ℕ) : ℕ := n.nth A381159_condition

/--
A381159 51st All-Russian Mathematical Olympiad for Schoolchildren. Problem.
Let us call a natural number "lopsided" if it is greater than 1 and all its prime divisors end with the same digit.
Is there an increasing arithmetic progression with a difference not exceeding 2025,
consisting of 150 natural numbers, each of which is "lopsided"? (A. Chironov)

We formalize the positive answer to the question/conjecture.
The condition for "lopsided" for n > 1 is exactly A381159_condition n.
We require the starting term a to be at least 2 to ensure all terms are > 1.
-/
theorem oeis_381159_conjecture_0 :
  ∃ (a d : ℕ),
    2 ≤ a ∧ -- The starting number 'a' must be lopsided, hence > 1. All subsequent terms will also be > 1.
    1 ≤ d ∧ -- 'd' must be positive for an increasing arithmetic progression
    d ≤ 2025 ∧ -- difference not exceeding 2025
    ∀ (i : Fin 150), A381159_condition (a + i.val * d)
  := by sorry

theorem oeis_381159_conjecture_0.disproof : ¬ (type_of% @oeis_381159_conjecture_0) := by
  -- A progression with difference coprime to m visits every residue modulo m.
  have hits_zero (a d m : ℕ) (hm : 0 < m) (hd : d.Coprime m) :
      ∃ i : ℕ, i < m ∧ m ∣ a + i * d := by
    letI : NeZero m := ⟨by omega⟩
    let x : ZMod m := -(a : ZMod m) * (d : ZMod m)⁻¹
    refine ⟨x.val, ZMod.val_lt x, ?_⟩
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    rw [ZMod.natCast_zmod_val]
    change (a : ZMod m) + (-(a : ZMod m) * (d : ZMod m)⁻¹) *
      (d : ZMod m) = 0
    rw [mul_assoc, mul_comm ((d : ZMod m)⁻¹), ZMod.coe_mul_inv_eq_one d hd]
    ring
  -- These five disjoint prime pairs have products below 150. To share a
  -- prime factor with every product requires a difference at least 2310.
  -- Check the resulting obstruction for the allowed finite range.
  have small_difference : ∀ d : Fin 2026, 1 ≤ d.val →
      d.val.Coprime (2 * 73) ∨ d.val.Coprime (3 * 47) ∨
      d.val.Coprime (5 * 29) ∨ d.val.Coprime (7 * 19) ∨
      d.val.Coprime (11 * 13) := by
    set_option maxRecDepth 10000 in
      set_option maxHeartbeats 0 in
        decide
  rintro ⟨a, d, ha, hd, hdmax, hterms⟩
  have bad_pair (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
      (hpq : p * q ≤ 150) (hlast : p % 10 ≠ q % 10)
      (hcop : d.Coprime (p * q)) : False := by
    obtain ⟨i, hi, hdiv⟩ := hits_zero a d (p * q) (Nat.mul_pos hp.pos hq.pos) hcop
    have hn : a + i * d ≠ 0 := by omega
    have hcard := Finset.card_le_one.mp (hterms ⟨i, lt_of_lt_of_le hi hpq⟩)
    apply hlast
    apply hcard
    · exact Finset.mem_image.mpr ⟨p,
        hp.mem_primeFactors (dvd_trans (Nat.dvd_mul_right p q) hdiv) hn, rfl⟩
    · exact Finset.mem_image.mpr ⟨q,
        hq.mem_primeFactors (dvd_trans (Nat.dvd_mul_left q p) hdiv) hn, rfl⟩
  rcases small_difference ⟨d, by omega⟩ hd with h | h | h | h | h
  · exact bad_pair 2 73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  · exact bad_pair 3 47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  · exact bad_pair 5 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  · exact bad_pair 7 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  · exact bad_pair 11 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
