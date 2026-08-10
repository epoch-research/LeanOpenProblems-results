import FormalConjectures.Util.ProblemImports

open Finset ZMod Nat Set Classical

/--
The predicate that $\{2^k - k: k = 1,\dots,m\}$ contains a complete system of residues modulo $n$.
This is equivalent to the image of $k \mapsto 2^k - k \pmod n$ for $k \in \{1, \dots, m\}$ being the entire $\mathbb{Z}_n$.
-/
def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

/--
A232616: Least positive integer $m$ such that $\{2^k - k: k = 1,\dots,m\}$
contains a complete system of residues modulo $n$.
-/
noncomputable def A232616 (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    -- Since n is non-zero, the NeZero n instance is available for ZMod n operations.
    have : NeZero n := NeZero.mk h

    -- The set $S$ of all $m$ which satisfy the complete residue system condition.
    -- The set $S$ is non-empty based on the external theorem $a(n) \le n^2$.
    let S : Set ℕ := { m : ℕ | A232616_prop n m }

    -- The least element of a non-empty set of natural numbers is its infimum, sInf.
    sInf S

theorem A232616_prop_one : A232616_prop 1 1 := by
  ext x
  constructor
  · intro _
    rw [Finset.mem_image]
    use 1
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_Icc]; decide
    · apply Subsingleton.elim
  · intro _
    exact mem_univ x

theorem A232616_prop_zero_neg_one : ¬ A232616_prop 1 0 := by
  intro h
  have h2 : (0 : ZMod 1) ∈ (univ : Finset (ZMod 1)) := mem_univ 0
  rw [h] at h2
  rw [Finset.mem_image] at h2
  rcases h2 with ⟨k, hk, _⟩
  rw [Finset.mem_Icc] at hk
  omega

theorem A232616_one : A232616 1 = 1 := by
  have h1 : 1 ≠ 0 := by decide
  rw [A232616, dif_neg h1]
  have h_nonempty : {m : ℕ | A232616_prop 1 m}.Nonempty := ⟨1, A232616_prop_one⟩
  rw [Nat.sInf_def h_nonempty]
  rw [Nat.find_eq_iff]
  refine ⟨A232616_prop_one, fun k hk ↦ ?_⟩
  interval_cases k
  · exact A232616_prop_zero_neg_one

theorem A232616_prop_two : A232616_prop 2 2 := by
  ext x
  constructor
  · intro _
    fin_cases x
    · rw [Finset.mem_image]
      use 2
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_Icc]; decide
      · rfl
    · rw [Finset.mem_image]
      use 1
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_Icc]; decide
      · rfl
  · intro _
    exact mem_univ x

theorem A232616_prop_one_neg : ¬ A232616_prop 2 1 := by
  intro h
  have h2 : (0 : ZMod 2) ∈ (univ : Finset (ZMod 2)) := mem_univ 0
  rw [h] at h2
  rw [Finset.mem_image] at h2
  rcases h2 with ⟨k, hk, hk2⟩
  rw [Finset.mem_Icc] at hk
  have : k = 1 := by omega
  subst this
  revert hk2
  decide

theorem A232616_prop_zero_neg : ¬ A232616_prop 2 0 := by
  intro h
  have h2 : (0 : ZMod 2) ∈ (univ : Finset (ZMod 2)) := mem_univ 0
  rw [h] at h2
  rw [Finset.mem_image] at h2
  rcases h2 with ⟨k, hk, _⟩
  rw [Finset.mem_Icc] at hk
  omega

theorem A232616_two : A232616 2 = 2 := by
  have h2 : 2 ≠ 0 := by decide
  rw [A232616, dif_neg h2]
  have h_nonempty : {m : ℕ | A232616_prop 2 m}.Nonempty := ⟨2, A232616_prop_two⟩
  rw [Nat.sInf_def h_nonempty]
  rw [Nat.find_eq_iff]
  refine ⟨A232616_prop_two, fun k hk ↦ ?_⟩
  interval_cases k
  · exact A232616_prop_zero_neg
  · exact A232616_prop_one_neg


theorem sInf_eq_zero_or_mem (s : Set ℕ) : sInf s = 0 ∨ sInf s ∈ s := by
  have h_inf : sInf s = if h : ∃ n, n ∈ s then Nat.find h else 0 := rfl
  by_cases h : ∃ n, n ∈ s
  · right
    rw [h_inf, dif_pos h]
    exact Nat.find_spec h
  · left
    rw [h_inf, dif_neg h]

theorem le_nth_self (p : ℕ → Prop) (hf : (setOf p).Infinite) (n : ℕ) : n ≤ Nat.nth p n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h1 : Nat.nth p n < Nat.nth p (n + 1) := by
      rw [Nat.nth_lt_nth hf]
      omega
    omega

theorem prime_three_le (n : ℕ) : 5 ≤ Nat.nth Nat.Prime (n + 2) := by
  have h_le : 2 ≤ n + 2 := by omega
  have h_mono := (Nat.nth_le_nth Nat.infinite_setOf_prime).mpr h_le
  rw [Nat.nth_prime_two_eq_five] at h_mono
  exact h_mono

theorem prime_bound_pos (n : ℕ) : 0 < 2 * (Nat.nth Nat.Prime (n + 2) - 1) := by
  have h := prime_three_le n
  omega

/--
Conjecture (i): $a(n) < 2 \cdot (\text{prime}(n) - 1)$ for all $n > 0$,
where $\text{prime}(n)$ is the $n$-th prime number (1-indexed).
-/
theorem A232616_prop_mono (n : ℕ) [NeZero n] (m1 m2 : ℕ) (h : m1 ≤ m2) (hm1 : A232616_prop n m1) : A232616_prop n m2 := by
  unfold A232616_prop at *
  ext x
  constructor
  · intro _
    exact Finset.mem_univ x
  · intro _
    have h_mem : x ∈ (Finset.Icc 1 m1).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n) := by
      rw [← hm1]
      exact Finset.mem_univ x
    rw [Finset.mem_image] at h_mem ⊢
    rcases h_mem with ⟨k, hk, rfl⟩
    rw [Finset.mem_Icc] at hk ⊢
    refine ⟨k, ⟨hk.1, hk.2.trans h⟩, rfl⟩

theorem oeis_232616_conjecture_i (n : ℕ) (hn : 0 < n) :
    A232616 n < 2 * (Nat.nth Nat.Prime (n - 1) - 1) := answer(sorry)

