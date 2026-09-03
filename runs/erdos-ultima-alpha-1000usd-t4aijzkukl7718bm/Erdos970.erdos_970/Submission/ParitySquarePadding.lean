import Submission.ParityRoughCounts

/-! Padding an odd-prime sieve by inactive primes and moving an interval endpoint
to the next square. These lemmas do not assume the Jacobsthal conjecture. -/
namespace Erdos970.ParityDiscrepancy
set_option maxHeartbeats 1000000
open Finset

def SquareParityBound (A : ℕ) : Prop :=
  ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ Odd p) →
    |alternatingCount P 1 (P.card ^ 2)| ≤ (A : ℚ) * P.card

lemma exists_padding (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Odd p)
    (k M : ℕ) (hk : P.card ≤ k) :
    ∃ Q : Finset ℕ, P ⊆ Q ∧ Q.card = k ∧ (∀ p ∈ Q, p.Prime ∧ Odd p) ∧
      ∀ p ∈ Q, p ∉ P → M < p := by
  have haux (t : ℕ) : ∃ Q : Finset ℕ, P ⊆ Q ∧ Q.card = P.card + t ∧
      (∀ p ∈ Q, p.Prime ∧ Odd p) ∧ ∀ p ∈ Q, p ∉ P → M < p := by
    induction t with
    | zero => exact ⟨P, Subset.rfl, by omega, hP, fun p hp hnp => False.elim (hnp hp)⟩
    | succ t ih =>
      obtain ⟨Q, hPQ, hcard, hQ, hnew⟩ := ih
      obtain ⟨p, hpbig, hpp⟩ := Nat.exists_infinite_primes (Q.sup id + M + 3)
      have hpQ : p ∉ Q := by
        intro hpQ
        have hh : p ≤ Q.sup id := by simpa only [id_eq] using le_sup (f := id) hpQ
        omega
      refine ⟨insert p Q, hPQ.trans (subset_insert _ _), by simp [hpQ, hcard]; omega, ?_, ?_⟩
      · intro q hq
        rcases mem_insert.mp hq with rfl | hq
        · exact ⟨hpp, hpp.odd_of_ne_two (by omega)⟩
        · exact hQ q hq
      · intro q hq hnP
        rcases mem_insert.mp hq with rfl | hq
        · omega
        · exact hnew q hq hnP
  obtain ⟨Q, hPQ, hcard, hQ, hnew⟩ := haux (k - P.card)
  exact ⟨Q, hPQ, by omega, hQ, hnew⟩

lemma alternatingCount_eq_of_padding (P Q : Finset ℕ) (hPQ : P ⊆ Q)
    (M m : ℕ) (hm : m ≤ M) (hnew : ∀ p ∈ Q, p ∉ P → M < p) :
    alternatingCount Q 1 m = alternatingCount P 1 m := by
  apply sum_congr rfl
  intro j hj
  have hjm := mem_range.mp hj
  have heq : (∀ p ∈ Q, ¬p ∣ 1 + j) ↔ ∀ p ∈ P, ¬p ∣ 1 + j := by
    constructor
    · exact fun h p hp => h p (hPQ hp)
    · intro h p hp hd
      by_cases hpP : p ∈ P
      · exact h p hpP hd
      · have hlarge := hnew p hp hpP
        have hle := Nat.le_of_dvd (by omega : 0 < 1 + j) hd
        omega
  simp only [survivorIndicator, heq]

lemma abs_alternatingCount_le (P : Finset ℕ) (a m : ℕ) :
    |alternatingCount P a m| ≤ m := by
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ range m, (1 : ℚ) := by
      apply sum_le_sum
      intro j hj
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, survivorIndicator]
      split_ifs <;> norm_num
    _ = _ := by simp

lemma alternatingCount_add (P : Finset ℕ) (a m n : ℕ) :
    alternatingCount P a (m + n) = alternatingCount P a m +
      (-1 : ℚ) ^ m * alternatingCount P (a + m) n := by
  rw [alternatingCount, sum_range_add]
  congr 1
  rw [alternatingCount, mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [pow_add, Nat.add_assoc]
  ring

lemma abs_alternatingCount_prefix (P : Finset ℕ) (a m n : ℕ) (hmn : m ≤ n) :
    |alternatingCount P a m| ≤ |alternatingCount P a n| + (n - m : ℕ) := by
  have heq := alternatingCount_add P a m (n - m)
  rw [Nat.add_sub_of_le hmn] at heq
  calc
    _ = |alternatingCount P a n - (-1 : ℚ) ^ m * alternatingCount P (a + m) (n - m)| := by
      congr 1
      linarith
    _ ≤ |alternatingCount P a n| + |(-1 : ℚ) ^ m * alternatingCount P (a + m) (n - m)| := abs_sub _ _
    _ = |alternatingCount P a n| + |alternatingCount P (a + m) (n - m)| := by
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    _ ≤ _ := by
      have hh := abs_alternatingCount_le P (a + m) (n - m)
      linarith

/-- A hypothetical exact-square bound extends to nearby lengths with an endpoint
error of at most twice the next square root. -/
theorem square_bound_to_short (A : ℕ) (hA : SquareParityBound A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Odd p) (m : ℕ)
    (hcard : P.card ≤ m.sqrt + 1) :
    |alternatingCount P 1 m| ≤ ((A : ℚ) + 2) * (m.sqrt + 1 : ℕ) := by
  let k := m.sqrt + 1
  have hmk : m ≤ k ^ 2 := (Nat.lt_succ_sqrt' m).le
  have hgap : k ^ 2 - m ≤ 2 * k := by
    have hs := Nat.sqrt_le m
    have hh : k ^ 2 ≤ m + 2 * k := by dsimp [k]; nlinarith
    omega
  obtain ⟨Q, hPQ, hQcard, hQ, hnew⟩ := exists_padding P hP k (k ^ 2) hcard
  have hbound := hA Q hQ
  rw [hQcard, alternatingCount_eq_of_padding P Q hPQ (k ^ 2) (k ^ 2) le_rfl hnew] at hbound
  have hprefix := abs_alternatingCount_prefix P 1 m (k ^ 2) hmk
  have hgapQ : ((k ^ 2 - m : ℕ) : ℚ) ≤ 2 * k := by exact_mod_cast hgap
  change |alternatingCount P 1 m| ≤ ((A : ℚ) + 2) * k
  nlinarith

lemma square_bound_in_window (A : ℕ) (hA : SquareParityBound A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Odd p) (s m : ℕ) (hs : 0 < s)
    (hcard : P.card ≤ s) (hlo : s ^ 2 ≤ m) (hhi : m ≤ 4 * s ^ 2) :
    |alternatingCount P 1 m| ≤ 3 * ((A : ℚ) + 2) * s := by
  have hrootlo : s ≤ m.sqrt := Nat.le_sqrt.mpr (by simpa only [pow_two] using hlo)
  have hroothi : m.sqrt ≤ 2 * s := by
    have h := Nat.sqrt_le_sqrt (show m ≤ (2 * s) ^ 2 by nlinarith)
    simpa only [Nat.sqrt_eq'] using h
  have hh := square_bound_to_short A hA P hP m (by omega)
  have hbound : (m.sqrt + 1 : ℕ) ≤ 3 * s := by omega
  have hboundQ : ((m.sqrt + 1 : ℕ) : ℚ) ≤ 3 * s := by exact_mod_cast hbound
  have hmul := mul_le_mul_of_nonneg_left hboundQ (by positivity : (0 : ℚ) ≤ A + 2)
  nlinarith

#print axioms exists_padding
#print axioms square_bound_to_short
end Erdos970.ParityDiscrepancy
