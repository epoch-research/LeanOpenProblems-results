import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

lemma term_mod_p_zero_of_ne_zero_of_ne_top {p r k : ℕ} (hp : Nat.Prime p)
    (hk0 : k ≠ 0) (hktop : k ≠ p ^ r) :
    ((p ^ r).choose k ^ 2 * (p ^ r).multichoose k : ℤ) ≡ 0 [ZMOD (p : ℕ)] := by
  have hdvd : p ∣ (p ^ r).choose k := hp.dvd_choose_pow hk0 hktop
  rw [Int.modEq_zero_iff_dvd]
  norm_num only [Nat.cast_mul, Nat.cast_pow]
  -- need show (p:Z) divides cast product
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hdvd) _) _

lemma a_prime_power_mod_p {p r : ℕ} (hp : Nat.Prime p) (hrpos : 0 < r) :
    (a (p ^ r) : ℤ) ≡ 1 [ZMOD (p : ℕ)] := by
  rw [a]
  have hNpos : 0 < p ^ r := pow_pos hp.pos r
  rw [← sum_range_succ (fun k => ((p ^ r).choose k ^ 2 * (p ^ r).multichoose k : ℤ)) (p ^ r - 1)]
  have hsimp : p ^ r - 1 + 1 = p ^ r := Nat.sub_add_cancel hNpos
  simp only [hsimp]
  -- after rw, target range (p^r) maybe no; need isolate k=0 by sum_eq_single?
  sorry

example (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p : ℕ)] := by
  have h1 : (a (p ^ r) : ℤ) ≡ 1 [ZMOD (p : ℕ)] := a_prime_power_mod_p hp (by omega)
  have h2 : (a (p ^ (r - 1)) : ℤ) ≡ 1 [ZMOD (p : ℕ)] := a_prime_power_mod_p hp (by omega)
  exact h1.trans h2.symm
