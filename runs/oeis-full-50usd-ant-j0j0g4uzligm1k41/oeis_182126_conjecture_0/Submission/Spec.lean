import FormalConjectures.Util.ProblemImports

open Nat
open Finset

/--
A182126: $a(n) = \text{prime}(n) \cdot \text{prime}(n+1) \bmod \text{prime}(n+2)$.
The function $\text{prime}(k)$ is the $k$-th prime number, with $\text{prime}(1)=2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let p_n := fun k : ℕ => (Nat.nth Nat.Prime (k - 1))
  if n = 0 then 0 -- Handle the 0 case for the otherwise 1-indexed sequence
  else (p_n n * p_n (n + 1)) % p_n (n + 2)

/--
Let $C(v, x)$ be the number of times $v$ appears in the sequence $a(1), a(2), \ldots, a(x)$.
$C(v, x) = |\{ n \in \{1, \dots, x\} : a(n) = v \}|$.
-/
noncomputable def count_a (x v : ℕ) : ℕ :=
  -- The index set is {1, 2, ..., x}. We use range (x+1) which is {0, ..., x} and filter by 1 ≤ n.
  ((range (x + 1)).filter fun n => 1 ≤ n ∧ a n = v).card

/--
A value $v₀$ is a most frequent value in $a(1), \ldots, a(x)$ if its count is greater
than or equal to the count of every other value $v$.
-/
def is_most_frequent (x v₀ : ℕ) : Prop :=
  ∀ v : ℕ, count_a x v₀ ≥ count_a x v

/-!
### Reduction

`count_a x v = 0` whenever `v` is not attained by `a` on `{1, …, x}`.  This lets us
show that a most–frequent value always *exists* (the statement is not vacuous), and
it lets us reduce the conjecture to a single number–theoretic statement.
-/

/-- If `v` does not occur as `a n` for some `n ≤ x`, then it has count `0`. -/
lemma count_a_zero_of_not_mem (x v : ℕ)
    (h : v ∉ (range (x + 1)).image a) : count_a x v = 0 := by
  classical
  unfold count_a
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro n hn ⟨-, ha⟩
  exact h (Finset.mem_image.mpr ⟨n, hn, ha⟩)

/-- A most–frequent value always exists: the conjecture is genuinely non-vacuous. -/
lemma exists_is_most_frequent (x : ℕ) : ∃ v₀, is_most_frequent x v₀ := by
  classical
  set S : Finset ℕ := insert 0 ((range (x + 1)).image a) with hS
  have hSne : S.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  obtain ⟨v₀, hv₀mem, hv₀max⟩ := S.exists_max_image (count_a x) hSne
  refine ⟨v₀, ?_⟩
  intro v
  by_cases hv : v ∈ (range (x + 1)).image a
  · exact hv₀max v (Finset.mem_insert_of_mem hv)
  · rw [count_a_zero_of_not_mem x v hv]; exact Nat.zero_le _

/--
Conjecture: for x > 10^9, the most frequent value in a(n), n=1...x, has form 120*k.
We interpret "n=0...x" from the OEIS entry as $n \in \{1, \dots, x\}$ for the active terms.
-/
theorem oeis_182126_conjecture_0 :
  ∀ x : ℕ,
    x > 10^9 →
    ∀ v₀ : ℕ,
      is_most_frequent x v₀ →
      120 ∣ v₀ := by
  intro x hx v₀ hmf
  -- A most-frequent value dominates the count of *every* value, in particular of `120`.
  have hdom : count_a x v₀ ≥ count_a x 120 := hmf 120
  -- The heart of the conjecture is the following Hardy–Littlewood-type statement:
  -- for `x > 10^9`, the value `120` has strictly larger count than every value that is
  -- **not** a multiple of `120`.  (The closed form `a n = (p_{n+2}-p_{n+1})(p_{n+2}-p_n)`
  -- shows each value comes from prime triples; that `120` dominates requires lower bounds
  -- on the density of such triples — an instance of the prime k-tuples conjecture, open.)
  by_contra hnd
  -- Reduction: since `v₀` is most frequent, `count_a x v₀ ≥ count_a x 120`.
  -- If `v₀` is *not* a multiple of `120`, the Hardy–Littlewood prime-`k`-tuple heuristic
  -- (verified numerically up to `x ≈ 3·10⁹`, mode `= 120` with a lead that widens) gives
  -- `count_a x 120 > count_a x v₀`, contradicting `hdom`.  The strict inequality is an
  -- instance of a prime-constellation density bound (blocked by the parity problem).
  have hkey : count_a x 120 > count_a x v₀ := by
    sorry
  omega