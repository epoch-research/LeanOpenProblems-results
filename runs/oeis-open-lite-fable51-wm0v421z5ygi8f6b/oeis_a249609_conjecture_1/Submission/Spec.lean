import FormalConjectures.Util.ProblemImports

open Nat List

/--
A249609: $a(n)$ is the smallest $m$, $1 \le m \le n$, such that $\binom{n}{m}$ is evil (A001969); $a(n)=0$ if there is no such $m$.
An evil number is one whose population count (number of set bits in binary) is even.
-/
def a (n : ℕ) : ℕ :=
  -- Define the evil property using the equivalent of popcount via bits and list count.
  let is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0

  -- Find the smallest $m$ in $[1, n]$ using bounded recursion.
  let rec find_min_m (m : ℕ) : ℕ :=
    if m > n then 0
    else if is_evil (n.choose m) then m
    else find_min_m (m + 1)

    -- Termination is guaranteed because m strictly increases and is bounded by n.
    termination_by n + 1 - m

  find_min_m 1

/-- Binary digits of a nonzero number: lowest bit, then the digits of `n / 2`. -/
theorem bits_of_ne_zero (n : ℕ) (hn : n ≠ 0) :
    n.bits = (decide (n % 2 = 1)) :: (n / 2).bits := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    have hk0 : k ≠ 0 := by rintro rfl; simp at hn
    rw [← two_mul, Nat.bit0_bits k hk0]
    have h1 : (2 * k) % 2 = 0 := by omega
    have h2 : (2 * k) / 2 = k := by omega
    simp [h1, h2]
  · subst hk
    rw [Nat.bit1_bits k]
    have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    simp [h1, h2]

theorem a_zero : a 0 = 0 := by
  unfold a; rw [a.find_min_m.eq_1]; simp
theorem a_one : a 1 = 0 := by
  unfold a
  iterate 2 (rw [a.find_min_m.eq_1]; simp [bits_of_ne_zero, Nat.choose_succ_succ])
theorem a_two : a 2 = 0 := by
  unfold a
  iterate 3 (rw [a.find_min_m.eq_1]; simp [bits_of_ne_zero, Nat.choose_succ_succ])
theorem a_seven : a 7 = 0 := by
  unfold a
  iterate 8 (rw [a.find_min_m.eq_1]; simp [bits_of_ne_zero, Nat.choose_succ_succ])
theorem a_eight : a 8 = 0 := by
  unfold a
  iterate 9 (rw [a.find_min_m.eq_1]; simp [bits_of_ne_zero, Nat.choose_succ_succ])

/--
Conjecture: there are only five n: 0,1,2,7,8, for which all entries of the n-th Pascal row (A007318) are odious (A000069).

The condition that all entries of the n-th Pascal row are odious is equivalent to $a(n)=0$.
An odious number is one whose population count is odd.
-/
theorem oeis_a249609_conjecture_1 (n : ℕ) : a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  constructor
  · -- Open direction (OEIS A249609 conjecture, Shevelev 2014): for every `n ∉ {0,1,2,7,8}`
    -- some binomial coefficient `C(n,m)` (`1 ≤ m ≤ n`) has even popcount.
    -- Verified computationally for all `n < 5·10^6`; no proof is known.
    sorry
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact a_zero
    · exact a_one
    · exact a_two
    · exact a_seven
    · exact a_eight

theorem oeis_a249609_conjecture_1.disproof : ¬ (type_of% @oeis_a249609_conjecture_1) := sorry
