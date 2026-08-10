import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 5000000
open Nat Finset

def a (n : ℕ) : ℕ := ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

lemma square_ne_prime_cube {p n : ℕ} (hp : Nat.Prime p) : n ^ 2 ≠ p ^ 3 := by
  intro h
  have hf := congrArg (fun m : ℕ => m.factorization p) h
  have hnfac : (n ^ 2).factorization p = 2 * n.factorization p := by rw [Nat.factorization_pow]; rfl
  have hpfac : (p ^ 3).factorization p = 3 := by rw [Nat.factorization_pow, hp.factorization]; simp
  change (n ^ 2).factorization p = (p ^ 3).factorization p at hf
  rw [hnfac, hpfac] at hf
  omega

lemma int_square_ne_prime_cube {p n : ℕ} (hp : Nat.Prime p) : ((n : ℤ) ^ 2) ≠ ((p : ℤ) ^ 3) := by
  intro h
  have hn : n ^ 2 = p ^ 3 := by exact_mod_cast h
  exact square_ne_prime_cube hp hn

example (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℕ)] := by
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num) hp5
  have hpowcast_ne_lt : ∀ {m n : ℕ}, m < n → ((p : ℤ) ^ m) ≠ ((p : ℤ) ^ n) := by
    intro m n hmn hEq
    have hlt : p ^ m < p ^ n := Nat.pow_lt_pow_right hp1 hmn
    have hNatEq : p ^ m = p ^ n := by exact_mod_cast hEq
    exact (Nat.ne_of_lt hlt) hNatEq
  have hpowcast_ne_gt : ∀ {m n : ℕ}, n < m → ((p : ℤ) ^ m) ≠ ((p : ℤ) ^ n) := by
    intro m n hmn hEq
    exact hpowcast_ne_lt hmn hEq.symm
  have hsquarecut : ∀ n : ℕ, ((n : ℤ) ^ 2) ≠ ((p : ℤ) ^ 3) := fun n => int_square_ne_prime_cube hp
  have hfunneq : (fun x => (p ^ r).choose x ^ 2 * (p ^ r).multichoose x) ≠
      (fun x => (p ^ (r - 1)).choose x ^ 2 * (p ^ (r - 1)).multichoose x) := by
    intro h
    have h1 := congrFun h 1
    simp [Nat.choose_one_right, Nat.multichoose_one_right] at h1
    have hcube : (p ^ r) ^ 3 = (p ^ (r - 1)) ^ 3 := by simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h1
    have hpowlt' : p ^ (r - 1) < p ^ r := Nat.pow_lt_pow_right hp1 (by omega)
    have hlt3 : (p ^ (r - 1)) ^ 3 < (p ^ r) ^ 3 := Nat.pow_lt_pow_left hpowlt' (by norm_num)
    exact (Nat.ne_of_gt hlt3) hcube
  grind [a, Int.ModEq, Nat.Prime]
