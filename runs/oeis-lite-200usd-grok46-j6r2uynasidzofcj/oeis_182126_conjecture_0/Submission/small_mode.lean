import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped Classical

noncomputable def primeN' (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)
noncomputable def a' (n : ℕ) : ℕ :=
  if n = 0 then 0 else (primeN' n * primeN' (n + 1)) % primeN' (n + 2)
noncomputable def count_a' (x v : ℕ) : ℕ :=
  ((range (x + 1)).filter fun n => 1 ≤ n ∧ a' n = v).card
def is_most_frequent' (x v₀ : ℕ) : Prop :=
  ∀ v : ℕ, count_a' x v₀ ≥ count_a' x v

lemma a'_one : a' 1 = 1 := by simp [a', primeN']
lemma a'_two : a' 2 = 1 := by simp [a', primeN']
lemma a'_three : a' 3 = 2 := by simp [a', primeN']

lemma count_one : count_a' 3 1 = 2 := by
  unfold count_a'
  have : ((range 4).filter fun n => 1 ≤ n ∧ a' n = 1) = {1, 2} := by
    ext n
    simp only [mem_filter, mem_range, mem_insert, mem_singleton]
    constructor
    · intro ⟨hn, h1, ha⟩
      interval_cases n <;> simp_all [a'_one, a'_two, a'_three]
    · intro h
      rcases h with rfl | rfl
      · simp [a'_one]
      · simp [a'_two]
  rw [this]
  decide

lemma count_two : count_a' 3 2 = 1 := by
  unfold count_a'
  have : ((range 4).filter fun n => 1 ≤ n ∧ a' n = 2) = {3} := by
    ext n
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · intro ⟨hn, h1, ha⟩
      interval_cases n <;> simp_all [a'_one, a'_two, a'_three]
    · intro h
      subst h
      simp [a'_three]
  rw [this]
  decide

lemma one_is_mode_three : is_most_frequent' 3 1 := by
  intro v
  by_cases hv : v = 1
  · subst hv; exact le_rfl
  by_cases hv2 : v = 2
  · subst hv2; rw [count_one, count_two]; decide
  · have : count_a' 3 v = 0 := by
      unfold count_a'
      rw [card_eq_zero, filter_eq_empty_iff]
      intro n hn ⟨h1, ha⟩
      have hn' : n ≤ 3 := by
        simp [mem_range] at hn; omega
      interval_cases n
      · simp at h1
      · simp [a'_one] at ha; exact hv ha.symm
      · simp [a'_two] at ha; exact hv ha.symm
      · simp [a'_three] at ha; exact hv2 ha.symm
    rw [this]; exact Nat.zero_le _

theorem small_threshold_false :
    ¬ (∀ x : ℕ, x > 2 → ∀ v₀ : ℕ, is_most_frequent' x v₀ → 120 ∣ v₀) := by
  intro h
  have := h 3 (by decide) 1 one_is_mode_three
  decide
