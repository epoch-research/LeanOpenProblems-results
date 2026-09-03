import FormalConjecturesUtil

/-!
Exact ordered collision parameters. These are auxiliary results, not a settlement of Erdős 773.
-/

namespace Erdos773

lemma ordered_square_collision_parameters {a b c d : ℕ}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (he : a ^ 2 + d ^ 2 = b ^ 2 + c ^ 2) :
    ∃ z y k : ℕ, 0 < z ∧ 0 < y ∧ 0 < k ∧
      b = a + z + k ∧ c = a + z + k + y ∧ d = a + 2 * z + k + y ∧
      k * (2 * a + k) = 2 * z * (z + y) := by
  obtain ⟨x, hx⟩ := Nat.exists_eq_add_of_le hab.le
  obtain ⟨y, hy⟩ := Nat.exists_eq_add_of_le hbc.le
  obtain ⟨z, hz⟩ := Nat.exists_eq_add_of_le hcd.le
  have hxpos : 0 < x := by omega
  have hypos : 0 < y := by omega
  have hzpos : 0 < z := by omega
  have hzx : z < x := by
    by_contra! h
    have hprod := Nat.mul_le_mul h (show 2 * a + x ≤ 2 * c + z by omega)
    have he' : x * (2 * a + x) = z * (2 * c + z) := by
      nlinarith only [he, hx, hz]
    have hstrict : 2 * a + x < 2 * c + z := by omega
    have hmul := Nat.mul_lt_mul_of_pos_left hstrict hxpos
    nlinarith only [hprod, he', hmul, h, hzpos, hxpos]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hzx.le
  have hkpos : 0 < k := by omega
  refine ⟨z, y, k, hzpos, hypos, hkpos, by omega, by omega, by omega, ?_⟩
  rw [hx, hy, hx, hz, hy, hx, hk] at he
  nlinarith only [he]

lemma ordered_square_collision_of_parameters (a z y k : ℕ)
    (he : k * (2 * a + k) = 2 * z * (z + y)) :
    a ^ 2 + (a + 2 * z + k + y) ^ 2 =
      (a + z + k) ^ 2 + (a + z + k + y) ^ 2 := by
  nlinarith only [he]

lemma prime_roots_do_not_suffice :
    (∀ n ∈ ({19, 47, 71, 83} : Finset ℕ), Nat.Prime n ∧ n % 4 = 3) ∧
    ¬ IsSidon (({19, 47, 71, 83} : Finset ℕ).image (fun n => n ^ 2) : Set ℕ) := by
  constructor
  · norm_num
  · intro h
    have he := h (19 ^ 2) (by norm_num) (47 ^ 2) (by norm_num)
      (83 ^ 2) (by norm_num) (71 ^ 2) (by norm_num) (by norm_num)
    norm_num at he

#print axioms ordered_square_collision_parameters
#print axioms prime_roots_do_not_suffice

end Erdos773
