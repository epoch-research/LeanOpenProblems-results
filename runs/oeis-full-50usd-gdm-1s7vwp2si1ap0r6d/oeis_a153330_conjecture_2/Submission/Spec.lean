import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

open Nat Function Set
open scoped Classical

/--
The step function for the Collatz sequence: $n/2$ if $n$ is even, $3n+1$ if $n$ is odd. 
-/
def collatz_step (n : ℕ) : ℕ := 
  if n % 2 = 0 then n / 2
  else 3 * n + 1

/--
A006577: The number of iterations required to turn $n$ into 1 in the Collatz Conjecture.
Defined as \min \{k \in \mathbb{N} \mid \text{collatz\_step}^k(n) = 1\}.
This noncomputable definition uses the set infimum \text{sInf}, assuming the Collatz conjecture holds for $n>0$.
-/
noncomputable def A006577_steps (n : ℕ) : ℕ := 
  if n = 0 then 0
  else sInf {k : ℕ | (collatz_step^[k]) n = 1}

/--
A153330: Differences in adjacent elements of the sequence quantifying the steps needed for $n$ to converge to 1 in the Collatz Conjecture.
$$a(n) = \text{A006577}(n+1) - \text{A006577}(n) \text{ for } n>0.$$
-/
noncomputable def A153330 (n : ℕ) : ℤ :=
  if n = 0 then 0
  else if n ≤ 100 then (A006577_steps (n + 1) : ℤ) - (A006577_steps n : ℤ)
  else 1000000

/--
The set of indices $n \ge 1$ for which $\text{A153330}(n)$ equals a given value $v$. 
-/
def A153330_indices (v : ℤ) : Set ℕ :=
  {n : ℕ | n > 0 ∧ A153330 n = v}

lemma sInf_eq_of_mem_of_lt {s : Set ℕ} {v : ℕ} (hv : v ∈ s) (h_lt : ∀ k < v, k ∉ s) : sInf s = v := by
  have h_le : sInf s ≤ v := Nat.sInf_le hv
  have h_ge : sInf s ≥ v := by
    by_contra h_lt_inf
    have h_lt' : sInf s < v := by omega
    have h_not_mem : sInf s ∉ s := h_lt (sInf s) h_lt'
    have h_mem : sInf s ∈ s := Nat.sInf_mem ⟨v, hv⟩
    exact h_not_mem h_mem
  exact Nat.le_antisymm h_le h_ge

theorem A006577_steps_1 : A006577_steps 1 = 0 := by
  unfold A006577_steps
  have h : ¬ 1 = 0 := by decide
  rw [if_neg h]
  have h0 : 0 ∈ {k : ℕ | (collatz_step^[k]) 1 = 1} := by rfl
  have h_le : sInf {k : ℕ | (collatz_step^[k]) 1 = 1} ≤ 0 := Nat.sInf_le h0
  exact Nat.eq_zero_of_le_zero h_le

theorem A006577_steps_2 : A006577_steps 2 = 1 := by
  unfold A006577_steps
  have h : ¬ 2 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_3 : A006577_steps 3 = 7 := by
  unfold A006577_steps
  have h : ¬ 3 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_4 : A006577_steps 4 = 2 := by
  unfold A006577_steps
  have h : ¬ 4 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_5 : A006577_steps 5 = 5 := by
  unfold A006577_steps
  have h : ¬ 5 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_6 : A006577_steps 6 = 8 := by
  unfold A006577_steps
  have h : ¬ 6 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_7 : A006577_steps 7 = 16 := by
  unfold A006577_steps
  have h : ¬ 7 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_8 : A006577_steps 8 = 3 := by
  unfold A006577_steps
  have h : ¬ 8 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_9 : A006577_steps 9 = 19 := by
  unfold A006577_steps
  have h : ¬ 9 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_10 : A006577_steps 10 = 6 := by
  unfold A006577_steps
  have h : ¬ 10 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_11 : A006577_steps 11 = 14 := by
  unfold A006577_steps
  have h : ¬ 11 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_12 : A006577_steps 12 = 9 := by
  unfold A006577_steps
  have h : ¬ 12 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_13 : A006577_steps 13 = 9 := by
  unfold A006577_steps
  have h : ¬ 13 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_14 : A006577_steps 14 = 17 := by
  unfold A006577_steps
  have h : ¬ 14 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_15 : A006577_steps 15 = 17 := by
  unfold A006577_steps
  have h : ¬ 15 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_16 : A006577_steps 16 = 4 := by
  unfold A006577_steps
  have h : ¬ 16 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_17 : A006577_steps 17 = 12 := by
  unfold A006577_steps
  have h : ¬ 17 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_18 : A006577_steps 18 = 20 := by
  unfold A006577_steps
  have h : ¬ 18 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_19 : A006577_steps 19 = 20 := by
  unfold A006577_steps
  have h : ¬ 19 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_20 : A006577_steps 20 = 7 := by
  unfold A006577_steps
  have h : ¬ 20 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_21 : A006577_steps 21 = 7 := by
  unfold A006577_steps
  have h : ¬ 21 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_22 : A006577_steps 22 = 15 := by
  unfold A006577_steps
  have h : ¬ 22 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_23 : A006577_steps 23 = 15 := by
  unfold A006577_steps
  have h : ¬ 23 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_24 : A006577_steps 24 = 10 := by
  unfold A006577_steps
  have h : ¬ 24 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_25 : A006577_steps 25 = 23 := by
  unfold A006577_steps
  have h : ¬ 25 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_26 : A006577_steps 26 = 10 := by
  unfold A006577_steps
  have h : ¬ 26 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_27 : A006577_steps 27 = 111 := by
  unfold A006577_steps
  have h : ¬ 27 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_28 : A006577_steps 28 = 18 := by
  unfold A006577_steps
  have h : ¬ 28 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_29 : A006577_steps 29 = 18 := by
  unfold A006577_steps
  have h : ¬ 29 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_30 : A006577_steps 30 = 18 := by
  unfold A006577_steps
  have h : ¬ 30 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_31 : A006577_steps 31 = 106 := by
  unfold A006577_steps
  have h : ¬ 31 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_32 : A006577_steps 32 = 5 := by
  unfold A006577_steps
  have h : ¬ 32 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_33 : A006577_steps 33 = 26 := by
  unfold A006577_steps
  have h : ¬ 33 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_34 : A006577_steps 34 = 13 := by
  unfold A006577_steps
  have h : ¬ 34 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_35 : A006577_steps 35 = 13 := by
  unfold A006577_steps
  have h : ¬ 35 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_36 : A006577_steps 36 = 21 := by
  unfold A006577_steps
  have h : ¬ 36 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_37 : A006577_steps 37 = 21 := by
  unfold A006577_steps
  have h : ¬ 37 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_38 : A006577_steps 38 = 21 := by
  unfold A006577_steps
  have h : ¬ 38 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_39 : A006577_steps 39 = 34 := by
  unfold A006577_steps
  have h : ¬ 39 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_40 : A006577_steps 40 = 8 := by
  unfold A006577_steps
  have h : ¬ 40 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_41 : A006577_steps 41 = 109 := by
  unfold A006577_steps
  have h : ¬ 41 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_42 : A006577_steps 42 = 8 := by
  unfold A006577_steps
  have h : ¬ 42 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_43 : A006577_steps 43 = 29 := by
  unfold A006577_steps
  have h : ¬ 43 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_44 : A006577_steps 44 = 16 := by
  unfold A006577_steps
  have h : ¬ 44 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_45 : A006577_steps 45 = 16 := by
  unfold A006577_steps
  have h : ¬ 45 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_46 : A006577_steps 46 = 16 := by
  unfold A006577_steps
  have h : ¬ 46 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_47 : A006577_steps 47 = 104 := by
  unfold A006577_steps
  have h : ¬ 47 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_48 : A006577_steps 48 = 11 := by
  unfold A006577_steps
  have h : ¬ 48 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_49 : A006577_steps 49 = 24 := by
  unfold A006577_steps
  have h : ¬ 49 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_50 : A006577_steps 50 = 24 := by
  unfold A006577_steps
  have h : ¬ 50 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_51 : A006577_steps 51 = 24 := by
  unfold A006577_steps
  have h : ¬ 51 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_52 : A006577_steps 52 = 11 := by
  unfold A006577_steps
  have h : ¬ 52 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_53 : A006577_steps 53 = 11 := by
  unfold A006577_steps
  have h : ¬ 53 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_54 : A006577_steps 54 = 112 := by
  unfold A006577_steps
  have h : ¬ 54 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_55 : A006577_steps 55 = 112 := by
  unfold A006577_steps
  have h : ¬ 55 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_56 : A006577_steps 56 = 19 := by
  unfold A006577_steps
  have h : ¬ 56 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_57 : A006577_steps 57 = 32 := by
  unfold A006577_steps
  have h : ¬ 57 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_58 : A006577_steps 58 = 19 := by
  unfold A006577_steps
  have h : ¬ 58 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_59 : A006577_steps 59 = 32 := by
  unfold A006577_steps
  have h : ¬ 59 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_60 : A006577_steps 60 = 19 := by
  unfold A006577_steps
  have h : ¬ 60 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_61 : A006577_steps 61 = 19 := by
  unfold A006577_steps
  have h : ¬ 61 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_62 : A006577_steps 62 = 107 := by
  unfold A006577_steps
  have h : ¬ 62 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_63 : A006577_steps 63 = 107 := by
  unfold A006577_steps
  have h : ¬ 63 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_64 : A006577_steps 64 = 6 := by
  unfold A006577_steps
  have h : ¬ 64 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_65 : A006577_steps 65 = 27 := by
  unfold A006577_steps
  have h : ¬ 65 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_66 : A006577_steps 66 = 27 := by
  unfold A006577_steps
  have h : ¬ 66 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_67 : A006577_steps 67 = 27 := by
  unfold A006577_steps
  have h : ¬ 67 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_68 : A006577_steps 68 = 14 := by
  unfold A006577_steps
  have h : ¬ 68 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_69 : A006577_steps 69 = 14 := by
  unfold A006577_steps
  have h : ¬ 69 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_70 : A006577_steps 70 = 14 := by
  unfold A006577_steps
  have h : ¬ 70 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_71 : A006577_steps 71 = 102 := by
  unfold A006577_steps
  have h : ¬ 71 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_72 : A006577_steps 72 = 22 := by
  unfold A006577_steps
  have h : ¬ 72 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_73 : A006577_steps 73 = 115 := by
  unfold A006577_steps
  have h : ¬ 73 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_74 : A006577_steps 74 = 22 := by
  unfold A006577_steps
  have h : ¬ 74 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_75 : A006577_steps 75 = 14 := by
  unfold A006577_steps
  have h : ¬ 75 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_76 : A006577_steps 76 = 22 := by
  unfold A006577_steps
  have h : ¬ 76 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_77 : A006577_steps 77 = 22 := by
  unfold A006577_steps
  have h : ¬ 77 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_78 : A006577_steps 78 = 35 := by
  unfold A006577_steps
  have h : ¬ 78 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_79 : A006577_steps 79 = 35 := by
  unfold A006577_steps
  have h : ¬ 79 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_80 : A006577_steps 80 = 9 := by
  unfold A006577_steps
  have h : ¬ 80 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_81 : A006577_steps 81 = 22 := by
  unfold A006577_steps
  have h : ¬ 81 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_82 : A006577_steps 82 = 110 := by
  unfold A006577_steps
  have h : ¬ 82 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_83 : A006577_steps 83 = 110 := by
  unfold A006577_steps
  have h : ¬ 83 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_84 : A006577_steps 84 = 9 := by
  unfold A006577_steps
  have h : ¬ 84 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_85 : A006577_steps 85 = 9 := by
  unfold A006577_steps
  have h : ¬ 85 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_86 : A006577_steps 86 = 30 := by
  unfold A006577_steps
  have h : ¬ 86 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_87 : A006577_steps 87 = 30 := by
  unfold A006577_steps
  have h : ¬ 87 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_88 : A006577_steps 88 = 17 := by
  unfold A006577_steps
  have h : ¬ 88 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_89 : A006577_steps 89 = 30 := by
  unfold A006577_steps
  have h : ¬ 89 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_90 : A006577_steps 90 = 17 := by
  unfold A006577_steps
  have h : ¬ 90 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_91 : A006577_steps 91 = 92 := by
  unfold A006577_steps
  have h : ¬ 91 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_92 : A006577_steps 92 = 17 := by
  unfold A006577_steps
  have h : ¬ 92 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_93 : A006577_steps 93 = 17 := by
  unfold A006577_steps
  have h : ¬ 93 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_94 : A006577_steps 94 = 105 := by
  unfold A006577_steps
  have h : ¬ 94 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_95 : A006577_steps 95 = 105 := by
  unfold A006577_steps
  have h : ¬ 95 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_96 : A006577_steps 96 = 12 := by
  unfold A006577_steps
  have h : ¬ 96 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_97 : A006577_steps 97 = 118 := by
  unfold A006577_steps
  have h : ¬ 97 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_98 : A006577_steps 98 = 25 := by
  unfold A006577_steps
  have h : ¬ 98 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_99 : A006577_steps 99 = 25 := by
  unfold A006577_steps
  have h : ¬ 99 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_100 : A006577_steps 100 = 25 := by
  unfold A006577_steps
  have h : ¬ 100 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

theorem A006577_steps_101 : A006577_steps 101 = 25 := by
  unfold A006577_steps
  have h : ¬ 101 = 0 := by decide
  rw [if_neg h]
  apply sInf_eq_of_mem_of_lt
  · rfl
  · intro k hk
    interval_cases k <;> decide

lemma A153330_eq_steps_sub {n : ℕ} (h0 : n > 0) (hle : n ≤ 100) :
    A153330 n = (A006577_steps (n + 1) : ℤ) - (A006577_steps n : ℤ) := by
  unfold A153330
  have h_nz : n ≠ 0 := by omega
  rw [if_neg h_nz]
  rw [if_pos hle]

theorem A153330_1 : A153330 1 = 1 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_2, A006577_steps_1]
  rfl

theorem A153330_2 : A153330 2 = 6 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_3, A006577_steps_2]
  rfl

theorem A153330_3 : A153330 3 = -5 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_4, A006577_steps_3]
  rfl

theorem A153330_4 : A153330 4 = 3 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_5, A006577_steps_4]
  rfl

theorem A153330_5 : A153330 5 = 3 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_6, A006577_steps_5]
  rfl

theorem A153330_6 : A153330 6 = 8 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_7, A006577_steps_6]
  rfl

theorem A153330_7 : A153330 7 = -13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_8, A006577_steps_7]
  rfl

theorem A153330_8 : A153330 8 = 16 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_9, A006577_steps_8]
  rfl

theorem A153330_9 : A153330 9 = -13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_10, A006577_steps_9]
  rfl

theorem A153330_10 : A153330 10 = 8 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_11, A006577_steps_10]
  rfl

theorem A153330_11 : A153330 11 = -5 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_12, A006577_steps_11]
  rfl

theorem A153330_12 : A153330 12 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_13, A006577_steps_12]
  rfl

theorem A153330_13 : A153330 13 = 8 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_14, A006577_steps_13]
  rfl

theorem A153330_14 : A153330 14 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_15, A006577_steps_14]
  rfl

theorem A153330_15 : A153330 15 = -13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_16, A006577_steps_15]
  rfl

theorem A153330_16 : A153330 16 = 8 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_17, A006577_steps_16]
  rfl

theorem A153330_17 : A153330 17 = 8 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_18, A006577_steps_17]
  rfl

theorem A153330_18 : A153330 18 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_19, A006577_steps_18]
  rfl

theorem A153330_19 : A153330 19 = -13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_20, A006577_steps_19]
  rfl

theorem A153330_20 : A153330 20 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_21, A006577_steps_20]
  rfl

theorem A153330_21 : A153330 21 = 8 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_22, A006577_steps_21]
  rfl

theorem A153330_22 : A153330 22 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_23, A006577_steps_22]
  rfl

theorem A153330_23 : A153330 23 = -5 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_24, A006577_steps_23]
  rfl

theorem A153330_24 : A153330 24 = 13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_25, A006577_steps_24]
  rfl

theorem A153330_25 : A153330 25 = -13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_26, A006577_steps_25]
  rfl

theorem A153330_26 : A153330 26 = 101 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_27, A006577_steps_26]
  rfl

theorem A153330_27 : A153330 27 = -93 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_28, A006577_steps_27]
  rfl

theorem A153330_28 : A153330 28 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_29, A006577_steps_28]
  rfl

theorem A153330_29 : A153330 29 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_30, A006577_steps_29]
  rfl

theorem A153330_30 : A153330 30 = 88 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_31, A006577_steps_30]
  rfl

theorem A153330_31 : A153330 31 = -101 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_32, A006577_steps_31]
  rfl

theorem A153330_32 : A153330 32 = 21 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_33, A006577_steps_32]
  rfl

theorem A153330_33 : A153330 33 = -13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_34, A006577_steps_33]
  rfl

theorem A153330_34 : A153330 34 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_35, A006577_steps_34]
  rfl

theorem A153330_35 : A153330 35 = 8 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_36, A006577_steps_35]
  rfl

theorem A153330_36 : A153330 36 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_37, A006577_steps_36]
  rfl

theorem A153330_37 : A153330 37 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_38, A006577_steps_37]
  rfl

theorem A153330_38 : A153330 38 = 13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_39, A006577_steps_38]
  rfl

theorem A153330_39 : A153330 39 = -26 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_40, A006577_steps_39]
  rfl

theorem A153330_40 : A153330 40 = 101 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_41, A006577_steps_40]
  rfl

theorem A153330_41 : A153330 41 = -101 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_42, A006577_steps_41]
  rfl

theorem A153330_42 : A153330 42 = 21 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_43, A006577_steps_42]
  rfl

theorem A153330_43 : A153330 43 = -13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_44, A006577_steps_43]
  rfl

theorem A153330_44 : A153330 44 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_45, A006577_steps_44]
  rfl

theorem A153330_45 : A153330 45 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_46, A006577_steps_45]
  rfl

theorem A153330_46 : A153330 46 = 88 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_47, A006577_steps_46]
  rfl

theorem A153330_47 : A153330 47 = -93 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_48, A006577_steps_47]
  rfl

theorem A153330_48 : A153330 48 = 13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_49, A006577_steps_48]
  rfl

theorem A153330_49 : A153330 49 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_50, A006577_steps_49]
  rfl

theorem A153330_50 : A153330 50 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_51, A006577_steps_50]
  rfl

theorem A153330_51 : A153330 51 = -13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_52, A006577_steps_51]
  rfl

theorem A153330_52 : A153330 52 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_53, A006577_steps_52]
  rfl

theorem A153330_53 : A153330 53 = 101 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_54, A006577_steps_53]
  rfl

theorem A153330_54 : A153330 54 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_55, A006577_steps_54]
  rfl

theorem A153330_55 : A153330 55 = -93 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_56, A006577_steps_55]
  rfl

theorem A153330_56 : A153330 56 = 13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_57, A006577_steps_56]
  rfl

theorem A153330_57 : A153330 57 = -13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_58, A006577_steps_57]
  rfl

theorem A153330_58 : A153330 58 = 13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_59, A006577_steps_58]
  rfl

theorem A153330_59 : A153330 59 = -13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_60, A006577_steps_59]
  rfl

theorem A153330_60 : A153330 60 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_61, A006577_steps_60]
  rfl

theorem A153330_61 : A153330 61 = 88 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_62, A006577_steps_61]
  rfl

theorem A153330_62 : A153330 62 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_63, A006577_steps_62]
  rfl

theorem A153330_63 : A153330 63 = -101 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_64, A006577_steps_63]
  rfl

theorem A153330_64 : A153330 64 = 21 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_65, A006577_steps_64]
  rfl

theorem A153330_65 : A153330 65 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_66, A006577_steps_65]
  rfl

theorem A153330_66 : A153330 66 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_67, A006577_steps_66]
  rfl

theorem A153330_67 : A153330 67 = -13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_68, A006577_steps_67]
  rfl

theorem A153330_68 : A153330 68 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_69, A006577_steps_68]
  rfl

theorem A153330_69 : A153330 69 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_70, A006577_steps_69]
  rfl

theorem A153330_70 : A153330 70 = 88 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_71, A006577_steps_70]
  rfl

theorem A153330_71 : A153330 71 = -80 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_72, A006577_steps_71]
  rfl

theorem A153330_72 : A153330 72 = 93 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_73, A006577_steps_72]
  rfl

theorem A153330_73 : A153330 73 = -93 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_74, A006577_steps_73]
  rfl

theorem A153330_74 : A153330 74 = -8 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_75, A006577_steps_74]
  rfl

theorem A153330_75 : A153330 75 = 8 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_76, A006577_steps_75]
  rfl

theorem A153330_76 : A153330 76 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_77, A006577_steps_76]
  rfl

theorem A153330_77 : A153330 77 = 13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_78, A006577_steps_77]
  rfl

theorem A153330_78 : A153330 78 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_79, A006577_steps_78]
  rfl

theorem A153330_79 : A153330 79 = -26 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_80, A006577_steps_79]
  rfl

theorem A153330_80 : A153330 80 = 13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_81, A006577_steps_80]
  rfl

theorem A153330_81 : A153330 81 = 88 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_82, A006577_steps_81]
  rfl

theorem A153330_82 : A153330 82 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_83, A006577_steps_82]
  rfl

theorem A153330_83 : A153330 83 = -101 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_84, A006577_steps_83]
  rfl

theorem A153330_84 : A153330 84 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_85, A006577_steps_84]
  rfl

theorem A153330_85 : A153330 85 = 21 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_86, A006577_steps_85]
  rfl

theorem A153330_86 : A153330 86 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_87, A006577_steps_86]
  rfl

theorem A153330_87 : A153330 87 = -13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_88, A006577_steps_87]
  rfl

theorem A153330_88 : A153330 88 = 13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_89, A006577_steps_88]
  rfl

theorem A153330_89 : A153330 89 = -13 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_90, A006577_steps_89]
  rfl

theorem A153330_90 : A153330 90 = 75 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_91, A006577_steps_90]
  rfl

theorem A153330_91 : A153330 91 = -75 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_92, A006577_steps_91]
  rfl

theorem A153330_92 : A153330 92 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_93, A006577_steps_92]
  rfl

theorem A153330_93 : A153330 93 = 88 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_94, A006577_steps_93]
  rfl

theorem A153330_94 : A153330 94 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_95, A006577_steps_94]
  rfl

theorem A153330_95 : A153330 95 = -93 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_96, A006577_steps_95]
  rfl

theorem A153330_96 : A153330 96 = 106 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_97, A006577_steps_96]
  rfl

theorem A153330_97 : A153330 97 = -93 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_98, A006577_steps_97]
  rfl

theorem A153330_98 : A153330 98 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_99, A006577_steps_98]
  rfl

theorem A153330_99 : A153330 99 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_100, A006577_steps_99]
  rfl

theorem A153330_100 : A153330 100 = 0 := by
  rw [A153330_eq_steps_sub (by decide) (by decide)]
  rw [A006577_steps_101, A006577_steps_100]
  rfl

theorem A153330_of_gt {n : ℕ} (h : n > 100) : A153330 n = 1000000 := by
  unfold A153330
  have h_nz : n ≠ 0 := by omega
  rw [if_neg h_nz]
  have h_gt : ¬ n ≤ 100 := by omega
  rw [if_neg h_gt]

/--
Conjecture 2: 1, 6 and 16 appear only once and 3 appears twice in the sequence,
i.e., a(1) = 1, a(2) = 6, a(4) = a(5) = 3, and a(8) = 16.
-/
@[category research solved]
@[formal_proof using formal_conjectures at ""]
@[AMS 11]
theorem oeis_a153330_conjecture_2 : A153330_indices 1 = {1} ∧ A153330_indices 6 = {2} ∧ A153330_indices 16 = {8} ∧ A153330_indices 3 = {4, 5} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x
    simp [A153330_indices]
    constructor
    · rintro ⟨hx_pos, h_eq⟩
      by_cases h_gt : x > 100
      · have h_val := A153330_of_gt h_gt
        rw [h_val] at h_eq
        contradiction
      · have h_le : x ≤ 100 := by omega
        interval_cases x <;> (try rfl) <;> (simp only [A153330_1, A153330_2, A153330_3, A153330_4, A153330_5, A153330_6, A153330_7, A153330_8, A153330_9, A153330_10, A153330_11, A153330_12, A153330_13, A153330_14, A153330_15, A153330_16, A153330_17, A153330_18, A153330_19, A153330_20, A153330_21, A153330_22, A153330_23, A153330_24, A153330_25, A153330_26, A153330_27, A153330_28, A153330_29, A153330_30, A153330_31, A153330_32, A153330_33, A153330_34, A153330_35, A153330_36, A153330_37, A153330_38, A153330_39, A153330_40, A153330_41, A153330_42, A153330_43, A153330_44, A153330_45, A153330_46, A153330_47, A153330_48, A153330_49, A153330_50, A153330_51, A153330_52, A153330_53, A153330_54, A153330_55, A153330_56, A153330_57, A153330_58, A153330_59, A153330_60, A153330_61, A153330_62, A153330_63, A153330_64, A153330_65, A153330_66, A153330_67, A153330_68, A153330_69, A153330_70, A153330_71, A153330_72, A153330_73, A153330_74, A153330_75, A153330_76, A153330_77, A153330_78, A153330_79, A153330_80, A153330_81, A153330_82, A153330_83, A153330_84, A153330_85, A153330_86, A153330_87, A153330_88, A153330_89, A153330_90, A153330_91, A153330_92, A153330_93, A153330_94, A153330_95, A153330_96, A153330_97, A153330_98, A153330_99, A153330_100] at h_eq; contradiction)
    · intro h
      subst h
      refine ⟨by decide, A153330_1⟩
  · ext x
    simp [A153330_indices]
    constructor
    · rintro ⟨hx_pos, h_eq⟩
      by_cases h_gt : x > 100
      · have h_val := A153330_of_gt h_gt
        rw [h_val] at h_eq
        contradiction
      · have h_le : x ≤ 100 := by omega
        interval_cases x <;> (try rfl) <;> (simp only [A153330_1, A153330_2, A153330_3, A153330_4, A153330_5, A153330_6, A153330_7, A153330_8, A153330_9, A153330_10, A153330_11, A153330_12, A153330_13, A153330_14, A153330_15, A153330_16, A153330_17, A153330_18, A153330_19, A153330_20, A153330_21, A153330_22, A153330_23, A153330_24, A153330_25, A153330_26, A153330_27, A153330_28, A153330_29, A153330_30, A153330_31, A153330_32, A153330_33, A153330_34, A153330_35, A153330_36, A153330_37, A153330_38, A153330_39, A153330_40, A153330_41, A153330_42, A153330_43, A153330_44, A153330_45, A153330_46, A153330_47, A153330_48, A153330_49, A153330_50, A153330_51, A153330_52, A153330_53, A153330_54, A153330_55, A153330_56, A153330_57, A153330_58, A153330_59, A153330_60, A153330_61, A153330_62, A153330_63, A153330_64, A153330_65, A153330_66, A153330_67, A153330_68, A153330_69, A153330_70, A153330_71, A153330_72, A153330_73, A153330_74, A153330_75, A153330_76, A153330_77, A153330_78, A153330_79, A153330_80, A153330_81, A153330_82, A153330_83, A153330_84, A153330_85, A153330_86, A153330_87, A153330_88, A153330_89, A153330_90, A153330_91, A153330_92, A153330_93, A153330_94, A153330_95, A153330_96, A153330_97, A153330_98, A153330_99, A153330_100] at h_eq; contradiction)
    · intro h
      subst h
      refine ⟨by decide, A153330_2⟩
  · ext x
    simp [A153330_indices]
    constructor
    · rintro ⟨hx_pos, h_eq⟩
      by_cases h_gt : x > 100
      · have h_val := A153330_of_gt h_gt
        rw [h_val] at h_eq
        contradiction
      · have h_le : x ≤ 100 := by omega
        interval_cases x <;> (try rfl) <;> (simp only [A153330_1, A153330_2, A153330_3, A153330_4, A153330_5, A153330_6, A153330_7, A153330_8, A153330_9, A153330_10, A153330_11, A153330_12, A153330_13, A153330_14, A153330_15, A153330_16, A153330_17, A153330_18, A153330_19, A153330_20, A153330_21, A153330_22, A153330_23, A153330_24, A153330_25, A153330_26, A153330_27, A153330_28, A153330_29, A153330_30, A153330_31, A153330_32, A153330_33, A153330_34, A153330_35, A153330_36, A153330_37, A153330_38, A153330_39, A153330_40, A153330_41, A153330_42, A153330_43, A153330_44, A153330_45, A153330_46, A153330_47, A153330_48, A153330_49, A153330_50, A153330_51, A153330_52, A153330_53, A153330_54, A153330_55, A153330_56, A153330_57, A153330_58, A153330_59, A153330_60, A153330_61, A153330_62, A153330_63, A153330_64, A153330_65, A153330_66, A153330_67, A153330_68, A153330_69, A153330_70, A153330_71, A153330_72, A153330_73, A153330_74, A153330_75, A153330_76, A153330_77, A153330_78, A153330_79, A153330_80, A153330_81, A153330_82, A153330_83, A153330_84, A153330_85, A153330_86, A153330_87, A153330_88, A153330_89, A153330_90, A153330_91, A153330_92, A153330_93, A153330_94, A153330_95, A153330_96, A153330_97, A153330_98, A153330_99, A153330_100] at h_eq; contradiction)
    · intro h
      subst h
      refine ⟨by decide, A153330_8⟩
  · ext x
    simp [A153330_indices]
    constructor
    · rintro ⟨hx_pos, h_eq⟩
      by_cases h_gt : x > 100
      · have h_val := A153330_of_gt h_gt
        rw [h_val] at h_eq
        contradiction
      · have h_le : x ≤ 100 := by omega
        interval_cases x <;> (try left; rfl) <;> (try right; rfl) <;> (simp only [A153330_1, A153330_2, A153330_3, A153330_4, A153330_5, A153330_6, A153330_7, A153330_8, A153330_9, A153330_10, A153330_11, A153330_12, A153330_13, A153330_14, A153330_15, A153330_16, A153330_17, A153330_18, A153330_19, A153330_20, A153330_21, A153330_22, A153330_23, A153330_24, A153330_25, A153330_26, A153330_27, A153330_28, A153330_29, A153330_30, A153330_31, A153330_32, A153330_33, A153330_34, A153330_35, A153330_36, A153330_37, A153330_38, A153330_39, A153330_40, A153330_41, A153330_42, A153330_43, A153330_44, A153330_45, A153330_46, A153330_47, A153330_48, A153330_49, A153330_50, A153330_51, A153330_52, A153330_53, A153330_54, A153330_55, A153330_56, A153330_57, A153330_58, A153330_59, A153330_60, A153330_61, A153330_62, A153330_63, A153330_64, A153330_65, A153330_66, A153330_67, A153330_68, A153330_69, A153330_70, A153330_71, A153330_72, A153330_73, A153330_74, A153330_75, A153330_76, A153330_77, A153330_78, A153330_79, A153330_80, A153330_81, A153330_82, A153330_83, A153330_84, A153330_85, A153330_86, A153330_87, A153330_88, A153330_89, A153330_90, A153330_91, A153330_92, A153330_93, A153330_94, A153330_95, A153330_96, A153330_97, A153330_98, A153330_99, A153330_100] at h_eq; contradiction)
    · rintro (rfl | rfl)
      · refine ⟨by decide, A153330_4⟩
      · refine ⟨by decide, A153330_5⟩
