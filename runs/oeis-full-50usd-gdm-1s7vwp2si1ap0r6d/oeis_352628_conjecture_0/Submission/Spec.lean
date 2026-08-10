import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A352628: Number of ways to write $n$ as $a^2 + 2b^2 + c^4 + 2d^4 + 3c^2d^2$,
where $a,b,c,d$ are nonnegative integers.
-/
def A352628 (n : ℕ) : ℕ :=
  let S : Finset ℕ := range (n + 1)

  -- The number of ways is the sum of 1 for each tuple that satisfies the equation.
  -- Using nested sums avoids complex tuple unpacking and Finset product issues.
  S.sum fun a =>
    S.sum fun b =>
      S.sum fun c =>
        S.sum fun d =>
          let E := (a^2) + (2 * b^2) + (c^4) + (2 * d^4) + (3 * c^2 * d^2)
          if E = n then 1 else 0

lemma le_of_sq_le {a n : ℕ} (h : a^2 ≤ n) : a ≤ n := by
  rcases a with - | a
  · omega
  · have : a + 1 ≤ (a + 1)^2 := by
      rw [sq]
      exact Nat.le_mul_self (a + 1)
    omega

lemma le_of_pow4_le {a n : ℕ} (h : a^4 ≤ n) : a ≤ n := by
  have h2 : (a^2)^2 ≤ n := by
    have : a^4 = (a^2)^2 := by ring
    rwa [← this]
  exact le_of_sq_le (le_of_sq_le h2)

lemma le_of_eq_abcd {a b c d n : ℕ} (h : a^2 + 2 * b^2 + c^4 + 2 * d^4 + 3 * c^2 * d^2 = n) :
    a ≤ n ∧ b ≤ n ∧ c ≤ n ∧ d ≤ n := by
  have ha : a^2 ≤ n := by
    rw [← h]
    omega
  have hb : b^2 ≤ n := by
    rw [← h]
    omega
  have hc : c^4 ≤ n := by
    rw [← h]
    omega
  have hd : d^4 ≤ n := by
    rw [← h]
    omega
  exact ⟨le_of_sq_le ha, le_of_sq_le hb, le_of_pow4_le hc, le_of_pow4_le hd⟩

theorem pos_of_exists {n : ℕ} {a b c d : ℕ} (h : a^2 + 2 * b^2 + c^4 + 2 * d^4 + 3 * c^2 * d^2 = n) :
    A352628 n > 0 := by
  let S := range (n + 1)
  have h_abcd := le_of_eq_abcd h
  have haS : a ∈ S := mem_range.mpr (by omega)
  have hbS : b ∈ S := mem_range.mpr (by omega)
  have hcS : c ∈ S := mem_range.mpr (by omega)
  have hdS : d ∈ S := mem_range.mpr (by omega)
  
  let f (a' b' c' d' : ℕ) := if (a'^2) + (2 * b'^2) + (c'^4) + (2 * d'^4) + (3 * c'^2 * d'^2) = n then 1 else 0
  
  have h_nonneg_d (a' b' c' d' : ℕ) : 0 ≤ f a' b' c' d' := by
    dsimp [f]
    split_ifs <;> omega
  have h_nonneg_c (a' b' c' : ℕ) : 0 ≤ S.sum fun d' => f a' b' c' d' := by
    exact sum_nonneg (fun d' _ => h_nonneg_d a' b' c' d')
  have h_nonneg_b (a' b' : ℕ) : 0 ≤ S.sum fun c' => S.sum fun d' => f a' b' c' d' := by
    exact sum_nonneg (fun c' _ => h_nonneg_c a' b' c')
  have h_nonneg_a (a' : ℕ) : 0 ≤ S.sum fun b' => S.sum fun c' => S.sum fun d' => f a' b' c' d' := by
    exact sum_nonneg (fun b' _ => h_nonneg_b a' b')

  have h_step1 : S.sum (fun a' => S.sum fun b' => S.sum fun c' => S.sum fun d' => f a' b' c' d') ≥
      S.sum fun b' => S.sum fun c' => S.sum fun d' => f a b' c' d' := by
    exact single_le_sum (fun a' _ => h_nonneg_a a') haS

  have h_step2 : S.sum (fun b' => S.sum fun c' => S.sum fun d' => f a b' c' d') ≥
      S.sum fun c' => S.sum fun d' => f a b c' d' := by
    exact single_le_sum (fun b' _ => h_nonneg_b a b') hbS

  have h_step3 : S.sum (fun c' => S.sum fun d' => f a b c' d') ≥
      S.sum fun d' => f a b c d' := by
    exact single_le_sum (fun c' _ => h_nonneg_c a b c') hcS

  have h_step4 : S.sum (fun d' => f a b c d') ≥ f a b c d := by
    exact single_le_sum (fun d' _ => h_nonneg_d a b c d') hdS

  have h_eq : f a b c d = 1 := by
    dsimp [f]
    rw [if_pos h]

  have h_final : S.sum (fun a' => S.sum fun b' => S.sum fun c' => S.sum fun d' => f a' b' c' d') ≥ 1 := by
    calc
      _ ≥ S.sum fun b' => S.sum fun c' => S.sum fun d' => f a b' c' d' := h_step1
      _ ≥ S.sum fun c' => S.sum fun d' => f a b c' d' := h_step2
      _ ≥ S.sum fun d' => f a b c d' := h_step3
      _ ≥ f a b c d := h_step4
      _ = 1 := h_eq
  change S.sum (fun a' => S.sum fun b' => S.sum fun c' => S.sum fun d' => if (a'^2) + (2 * b'^2) + (c'^4) + (2 * d'^4) + (3 * c'^2 * d'^2) = n then 1 else 0) ≥ 1 at h_final

  change A352628 n > 0
  unfold A352628
  change S.sum (fun a' => S.sum fun b' => S.sum fun c' => S.sum fun d' => if (a'^2) + (2 * b'^2) + (c'^4) + (2 * d'^4) + (3 * c'^2 * d'^2) = n then 1 else 0) > 0
  omega

lemma exists_sol (n : ℕ) : ∃ a b c d : ℕ, a^2 + 2 * b^2 + c^4 + 2 * d^4 + 3 * c^2 * d^2 = n := by
  sorry

/--
Conjecture: a(n) > 0 for all n = 0,1,2,.... In other words, each nonnegative integer can be written as $a^2 + 2b^2 + (c^2+d^2)(c^2+2d^2)$ with a,b,c,d integers.
-/
theorem oeis_352628_conjecture_0 (n : ℕ) : A352628 n > 0 := by
  obtain ⟨a, b, c, d, h⟩ := exists_sol n
  exact pos_of_exists h


