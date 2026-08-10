import FormalConjectures.Util.ProblemImports

open Nat ArithmeticFunction Rat

/--
A243473(i) is the difference between the numerator $p$ and the denominator $q$
when the per-unit sum-of-divisors $\sigma_1(i)/i$ is written in its lowest terms $p/q$.
$$ \mathrm{A243473}(i) = \mathrm{num} \left( \frac{\sigma_1(i)}{i} \right) - \mathrm{den} \left( \frac{\sigma_1(i)}{i} \right) $$
-/
def A243473_val (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    -- r.num is Int, r.den is Nat. The subtraction is performed in Int, and then converted to Nat.
    (r.num - (r.den : ℤ)).toNat

/--
A243512: Least index $i$ for which $\mathrm{A243473}(i)=n$, or $0$ if no such index exists.
$$ a(n) = \min \{ i \in \mathbb{N} \mid i > 0 \land \mathrm{A243473}(i) = n \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- sInf finds the infimum of a set of natural numbers. For a non-empty set of positive integers,
  -- this is the minimum. For an empty set, this returns 0, which matches the OEIS definition.
  sInf {i : ℕ | 0 < i ∧ A243473_val i = n}

-- The example proofs are illustrative only and contain errors, so they are omitted.
-- I will only provide the formalization of the conjecture.

/--
Motivated by the observation that some small numbers (2,12,14,18,...) occur only very late
in the recently added sequence A243473, but all numbers seem to appear sooner or later.
(The definition is completed by "0 if no such index exists" to guarantee well-definedness
in absence of a proof, but I conjecture that no such 0 will ever occur.)
The conjecture is that the sequence $\mathrm{A243473\_val}$ is eventually surjective onto $\mathbb{N} \setminus \{0, 1\}$.
-/

theorem a_ne_zero_iff_nonempty (n : ℕ) : a n ≠ 0 ↔ {i : ℕ | 0 < i ∧ A243473_val i = n}.Nonempty := by
  constructor
  · intro h
    by_contra h_empty
    rw [Set.not_nonempty_iff_eq_empty] at h_empty
    unfold a at h
    rw [h_empty] at h
    exact h Nat.sInf_empty
  · intro h
    unfold a
    have h_mem := Nat.sInf_mem h
    simp only [Set.mem_setOf_eq] at h_mem
    exact Nat.ne_of_gt h_mem.1

theorem test0 : A243473_val 1 = 0 := by
  unfold A243473_val
  simp only [Nat.one_ne_zero, ↓reduceIte]
  rw [sigma_one]
  norm_num

lemma nonempty_0 : {i : ℕ | 0 < i ∧ A243473_val i = 0}.Nonempty := ⟨1, Nat.one_pos, test0⟩

theorem test1 : A243473_val 2 = 1 := by
  unfold A243473_val
  simp only [Nat.succ_ne_zero, ↓reduceIte]
  have h : sigma 1 2 = 3 := rfl
  rw [h]
  norm_num

lemma nonempty_1 : {i : ℕ | 0 < i ∧ A243473_val i = 1}.Nonempty := ⟨2, Nat.succ_pos 1, test1⟩

theorem oeis_243512_conjecture_0 (n : ℕ) : a n ≠ 0 := by
  rcases n with _ | n
  · rw [a_ne_zero_iff_nonempty]
    exact nonempty_0
  · rcases n with _ | n
    · rw [a_ne_zero_iff_nonempty]
      exact nonempty_1
    · sorry
