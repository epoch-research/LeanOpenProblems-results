import FormalConjecturesUtil

/-!
A quantitative obstruction to taking a full rationally shifted interval of roots.
This is not a disproof of Erdős 773: it places no such upper bound on arbitrary subsets.
-/

namespace Erdos773

lemma progression_collision_identity (q r : ℕ) :
    (q * (3 * q + r + 2) + r) ^ 2 +
      (q * (4 * q + 3 * r + 1) + r) ^ 2 =
    (q * (5 * q + 3 * r + 2) + r) ^ 2 +
      (q * (r + 1) + r) ^ 2 := by
  ring

lemma progression_squares_not_sidon (q r M : ℕ) (hq : 0 < q)
    (hM : 5 * q + 3 * r + 2 ≤ M) :
    ¬ IsSidon ((Finset.image (fun j : ℕ => (q * j + r) ^ 2)
      (Finset.Icc 1 M)) : Set ℕ) := by
  intro hs
  have hm (j : ℕ) (hj : 1 ≤ j ∧ j ≤ M) :
      (q * j + r) ^ 2 ∈ ((Finset.image (fun j : ℕ => (q * j + r) ^ 2)
        (Finset.Icc 1 M)) : Set ℕ) := by
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_Icc]
    exact ⟨j, hj, rfl⟩
  have ha := hm (3 * q + r + 2) (by omega)
  have hb := hm (4 * q + 3 * r + 1) (by omega)
  have hc := hm (5 * q + 3 * r + 2) (by omega)
  have hd := hm (r + 1) (by omega)
  have hac : q * (3 * q + r + 2) + r < q * (5 * q + 3 * r + 2) + r := by
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left (by omega) hq) r
  have hda : q * (r + 1) + r < q * (3 * q + r + 2) + r := by
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left (by omega) hq) r
  have hac2 := Nat.pow_lt_pow_left hac (by omega : (2 : ℕ) ≠ 0)
  have hda2 := Nat.pow_lt_pow_left hda (by omega : (2 : ℕ) ≠ 0)
  have he := hs _ ha _ hc _ hb _ hd (progression_collision_identity q r)
  rcases he with he | he <;> omega

lemma reduced_progression_squares_not_sidon (q r : ℕ) (hq : 0 < q) (hr : r < q) :
    ¬ IsSidon ((Finset.image (fun j : ℕ => (q * j + r) ^ 2)
      (Finset.Icc 1 (8 * q))) : Set ℕ) := by
  exact progression_squares_not_sidon q r (8 * q) hq (by omega)

lemma full_progression_sidon_length_bound (q r M : ℕ) (hq : 0 < q) (hr : r < q)
    (hs : IsSidon ((Finset.image (fun j : ℕ => (q * j + r) ^ 2)
      (Finset.Icc 1 M)) : Set ℕ)) :
    M ^ 2 ≤ 8 * (q * M + r) := by
  have hM : M < 8 * q := by
    by_contra! hM
    exact progression_squares_not_sidon q r M hq (by omega) hs
  have hmul := Nat.mul_le_mul_right M hM.le
  nlinarith only [hmul]

#print axioms reduced_progression_squares_not_sidon
#print axioms full_progression_sidon_length_bound

end Erdos773
