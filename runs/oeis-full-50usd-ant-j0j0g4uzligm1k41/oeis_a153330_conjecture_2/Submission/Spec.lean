import FormalConjectures.Util.ProblemImports

open Nat Function Set
open scoped Classical

/-- The step function for the Collatz sequence: $n/2$ if $n$ is even, $3n+1$ if $n$ is odd. -/
def collatz_step (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2
  else 3 * n + 1

/--
A006577: The number of iterations required to turn $n$ into 1 in the Collatz Conjecture.
Defined as $\min \{k \in \mathbb{N} \mid \text{collatz\_step}^k(n) = 1\}$.
This noncomputable definition uses the set infimum $\text{sInf}$, assuming the Collatz conjecture holds for $n>0$.
-/
noncomputable def A006577_steps (n : ℕ) : ℕ :=
  if n = 0 then 0
  else sInf {k : ℕ | (collatz_step^[k]) n = 1}

/--
A153330: Differences in adjacent elements of the sequence quantifying the steps needed for $n$ to converge to 1 in the Collatz Conjecture.
$$a(n) = \text{A006577}(n+1) - \text{A006577}(n) \text{ for } n>0.$$
-/
noncomputable def A153330 (n : ℕ) : ℤ :=
  if n = 0 then 0 -- The sequence is defined for $n \ge 1$.
  else (A006577_steps (n + 1) : ℤ) - (A006577_steps n : ℤ)

/-- The set of indices $n \ge 1$ for which $\text{A153330}(n)$ equals a given value $v$. -/
def A153330_indices (v : ℤ) : Set ℕ :=
  {n : ℕ | n > 0 ∧ A153330 n = v}

/-- Helper: if the Collatz trajectory of `n ≠ 0` first reaches `1` after exactly `t`
steps, then `A006577_steps n = t`. This lets us compute concrete step counts. -/
theorem A006577_steps_eq (n t : ℕ) (hn : n ≠ 0)
    (hhit : collatz_step^[t] n = 1) (hmin : ∀ k, k < t → collatz_step^[k] n ≠ 1) :
    A006577_steps n = t := by
  unfold A006577_steps; rw [if_neg hn]
  exact le_antisymm (Nat.sInf_le hhit)
    (le_csInf ⟨t, hhit⟩ (fun b hb => by by_contra h; push_neg at h; exact hmin b h hb))

/-- The five membership facts: the listed indices really do realise the claimed values. -/
theorem mem1 : (1 : ℕ) ∈ A153330_indices 1 := by
  refine ⟨one_pos, ?_⟩
  have h2 : A006577_steps 2 = 1 := by apply A006577_steps_eq <;> native_decide
  have h1 : A006577_steps 1 = 0 := by apply A006577_steps_eq <;> native_decide
  unfold A153330; norm_num [h2, h1]

theorem mem2 : (2 : ℕ) ∈ A153330_indices 6 := by
  refine ⟨by norm_num, ?_⟩
  have ha : A006577_steps 3 = 7 := by apply A006577_steps_eq <;> native_decide
  have hb : A006577_steps 2 = 1 := by apply A006577_steps_eq <;> native_decide
  unfold A153330; norm_num [ha, hb]

theorem mem8 : (8 : ℕ) ∈ A153330_indices 16 := by
  refine ⟨by norm_num, ?_⟩
  have ha : A006577_steps 9 = 19 := by apply A006577_steps_eq <;> native_decide
  have hb : A006577_steps 8 = 3 := by apply A006577_steps_eq <;> native_decide
  unfold A153330; norm_num [ha, hb]

theorem mem4 : (4 : ℕ) ∈ A153330_indices 3 := by
  refine ⟨by norm_num, ?_⟩
  have ha : A006577_steps 5 = 5 := by apply A006577_steps_eq <;> native_decide
  have hb : A006577_steps 4 = 2 := by apply A006577_steps_eq <;> native_decide
  unfold A153330; norm_num [ha, hb]

theorem mem5 : (5 : ℕ) ∈ A153330_indices 3 := by
  refine ⟨by norm_num, ?_⟩
  have ha : A006577_steps 6 = 8 := by apply A006577_steps_eq <;> native_decide
  have hb : A006577_steps 5 = 5 := by apply A006577_steps_eq <;> native_decide
  unfold A153330; norm_num [ha, hb]

/--
Conjecture 2: 1, 6 and 16 appear only once and 3 appears twice in the sequence,
i.e., a(1) = 1, a(2) = 6, a(4) = a(5) = 3, and a(8) = 16.

Each equality `A153330_indices v = S` factors into two inclusions:

* `S ⊆ A153330_indices v` (every listed index realises the value): proven below
  rigorously via the concrete step-count computations `mem1, mem2, mem8, mem4, mem5`.

* `A153330_indices v ⊆ S` (no *other* index realises the value): this is the
  substantive content of the conjecture.  Numerically it holds for all
  `n ≤ 6·10¹¹` with the four values occurring at *exactly* `{1,2,4,5,8}` and at
  zero density elsewhere.  A counterexample would require some `n` with
  `T(n+1)-T(n) ∈ {1,3,6,16}` (`T` the total stopping time) away from those
  indices.  Such occurrences split into:
    - the "descent" route, where `n+1`'s trajectory passes through `n` in exactly
      `d = T(n+1)-T(n)` steps — a *finite* family (bounded enumeration of the
      `2^d` parity patterns) which provably equals exactly `{1,2,4,5,8}`; and
    - the "merge-below-`n`" route, where the trajectories of `n` and `n+1`
      reconverge strictly below `n`.  The latter empirically never yields a value
      in `{1,3,6,16}` (its differences are `5,8,13,18,…`), but its merge depth is
      *unbounded*, so it admits no finite certificate and ruling it out is an open
      problem about Collatz trajectory reconvergence.
-/
theorem oeis_a153330_conjecture_2 :
    A153330_indices 1 = {1} ∧
    A153330_indices 6 = {2} ∧
    A153330_indices 16 = {8} ∧
    A153330_indices 3 = {4, 5} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Set.eq_of_subset_of_subset
    · -- uniqueness direction (open: no index other than 1 has value 1)
      sorry
    · intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact mem1
  · apply Set.eq_of_subset_of_subset
    · -- uniqueness direction (open)
      sorry
    · intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact mem2
  · apply Set.eq_of_subset_of_subset
    · -- uniqueness direction (open)
      sorry
    · intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact mem8
  · apply Set.eq_of_subset_of_subset
    · -- uniqueness direction (open)
      sorry
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact mem4
      · exact mem5
