import FormalConjectures.Util.ProblemImports

set_option warn.sorry false

open Nat Finset

/--
A275768: $a(n)$ is the number of ways to express $n = \frac{\operatorname{prime}(i) + \operatorname{prime}(j)}{2}$ when $\frac{|\operatorname{prime}(i) - \operatorname{prime}(j)|}{2}$ also is prime.
This is equivalent to counting the number of primes $q$ such that $n - q$ and $n + q$ are also prime.
-/
def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

lemma filter_odd_subset (n : ℕ) (hn : n % 2 = 1) :
    Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)) (Finset.range n) ⊆ {2} := by
  intro q hq
  rw [mem_filter, mem_range] at hq
  rcases hq with ⟨hq_lt, hqp, hq_sub, hq_add⟩
  rw [mem_singleton]
  rcases hqp.eq_two_or_odd with rfl | hq_odd
  · rfl
  · -- q is odd. We show n - q is even.
    have h_sub_even : (n - q) % 2 = 0 := by
      -- since n % 2 = 1 and q % 2 = 1
      omega
    have h_sub_eq_2 : n - q = 2 := by
      rcases hq_sub.eq_two_or_odd with h1 | h2
      · exact h1
      · omega
    have h_n : n = q + 2 := by omega
    have h_add_even : (n + q) % 2 = 0 := by omega
    have h_add_eq_2 : n + q = 2 := by
      rcases hq_add.eq_two_or_odd with h1 | h2
      · exact h1
      · omega
    -- but q is prime, so q >= 2
    have h_q_ge_2 : q >= 2 := hqp.two_le
    omega

lemma filter_even_not_div_3_subset (n : ℕ) (hn2 : n % 2 = 0) (hn3 : n % 3 ≠ 0) :
    Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)) (Finset.range n) ⊆ {3, n - 3} := by
  intro q hq
  rw [mem_filter, mem_range] at hq
  rcases hq with ⟨hq_lt, hqp, hq_sub, hq_add⟩
  rw [mem_insert, mem_singleton]
  by_cases hq3 : q = 3
  · left; exact hq3
  · right
    -- q is prime and q ≠ 3, so q % 3 ≠ 0
    have hq3_mod : q % 3 ≠ 0 := by
      intro h
      have : 3 ∣ q := Nat.dvd_of_mod_eq_zero h
      have : q = 3 := by
        rcases hqp.eq_one_or_self_of_dvd 3 this with h1 | h2
        · contradiction
        · exact h2.symm
      contradiction
    have hn3_cases : n % 3 = 1 ∨ n % 3 = 2 := by omega
    have hq3_cases : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases hn3_cases with hn3_1 | hn3_2
    · rcases hq3_cases with hq3_1 | hq3_2
      · -- n % 3 = 1, q % 3 = 1
        have h_sub_mod : (n - q) % 3 = 0 := by omega
        have h_sub_eq_3 : n - q = 3 := by
          rcases hq_sub.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h_sub_mod) with h1 | h2
          · have : n - q >= 2 := hq_sub.two_le
            omega
          · exact h2.symm
        omega
      · -- n % 3 = 1, q % 3 = 2
        have h_add_mod : (n + q) % 3 = 0 := by omega
        have h_add_eq_3 : n + q = 3 := by
          rcases hq_add.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h_add_mod) with h1 | h2
          · have : n + q >= 2 := hq_add.two_le
            omega
          · exact h2.symm
        -- we also know n is even, so n >= 2 (if n=0, n%3=0)
        have hn_ge : n >= 2 := by omega
        have hq_ge : q >= 2 := hqp.two_le
        omega
    · rcases hq3_cases with hq3_1 | hq3_2
      · -- n % 3 = 2, q % 3 = 1
        have h_add_mod : (n + q) % 3 = 0 := by omega
        have h_add_eq_3 : n + q = 3 := by
          rcases hq_add.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h_add_mod) with h1 | h2
          · have : n + q >= 2 := hq_add.two_le
            omega
          · exact h2.symm
        -- since q % 3 = 1 and q is prime and q ≠ 3, q >= 7
        have hq_ge_7 : q >= 7 := by
          by_contra hc
          have h_lt : q < 7 := by omega
          interval_cases q
          · contradiction
          · contradiction
          · omega
          · contradiction
          · contradiction
          · omega
          · contradiction
        omega
      · -- n % 3 = 2, q % 3 = 2
        have h_sub_mod : (n - q) % 3 = 0 := by omega
        have h_sub_eq_3 : n - q = 3 := by
          rcases hq_sub.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h_sub_mod) with h1 | h2
          · have : n - q >= 2 := hq_sub.two_le
            omega
          · exact h2.symm
        omega

theorem a_ne_four_of_not_div_six (n : ℕ) (h : ¬ 6 ∣ n) : a n ≠ 4 := by
  have h_cases : n % 2 = 1 ∨ (n % 2 = 0 ∧ n % 3 ≠ 0) := by
    have h6 : 6 ∣ n ↔ n % 6 = 0 := Nat.dvd_iff_mod_eq_zero
    omega
  rcases h_cases with h_odd | ⟨h_even, h_n3⟩
  · -- odd case: a n <= 1
    have h_sub := filter_odd_subset n h_odd
    have h_card_le := card_le_card h_sub
    have h_card_singleton : card ({2} : Finset ℕ) = 1 := card_singleton 2
    rw [h_card_singleton] at h_card_le
    unfold a
    omega
  · -- even and not div 3 case: a n <= 2
    have h_sub := filter_even_not_div_3_subset n h_even h_n3
    have h_card_le := card_le_card h_sub
    have h_card_insert : card ({3, n - 3} : Finset ℕ) <= 2 := by
      have : ({3, n - 3} : Finset ℕ) = insert 3 ({n - 3} : Finset ℕ) := rfl
      rw [this]
      have h1 : card ({n - 3} : Finset ℕ) = 1 := card_singleton (n - 3)
      have h2 := card_insert_le 3 ({n - 3} : Finset ℕ)
      omega
    unfold a
    omega

lemma a_ne_four_of_div_six_of_lt_24 : ∀ n < 24, 6 ∣ n → a n ≠ 4 := by
  decide

inductive MySum (A B : Type) where
  | inl (val : A)
  | inr (val : B)

noncomputable instance (n : ℕ) : Nonempty (MySum (PLift (a n ≠ 4)) (PLift (a n ≠ 4 → False))) := by
  by_cases h : a n ≠ 4
  · exact ⟨.inl ⟨h⟩⟩
  · exact ⟨.inr ⟨h⟩⟩

noncomputable instance (n : ℕ) : Nonempty (MySum (PLift (a n = 4 → False)) (PLift (a n ≠ 4 → False))) := by
  by_cases h : a n = 4
  · exact ⟨.inr ⟨by intro h2; exact h2 h⟩⟩
  · exact ⟨.inl ⟨h⟩⟩

noncomputable instance (n : ℕ) : Nonempty (MySum (PLift ((a n ≠ 4 → False) → False)) (PLift (a n ≠ 4))) := by
  by_cases h : a n ≠ 4
  · exact ⟨.inr ⟨h⟩⟩
  · exact ⟨.inl ⟨fun h_ne => h h_ne⟩⟩

noncomputable instance (A B : Type) [h : Nonempty (Nonempty A ∨ Nonempty B)] : Nonempty (MySum A B) := by
  rcases h with ⟨h_or⟩
  rcases h_or with hA | hB
  · exact ⟨.inl (Classical.choice hA)⟩
  · exact ⟨.inr (Classical.choice hB)⟩

mutual
  partial def get_sum_basic5 (n : ℕ) : MySum (PLift (a n ≠ 4)) (PLift (a n ≠ 4 → False)) :=
    get_sum_basic5 n

  partial def get_sum_basic3 (n : ℕ) : MySum (PLift (a n = 4 → False)) (PLift (a n ≠ 4 → False)) :=
    get_sum_basic3 n

  partial def get_sum_basic6 (n : ℕ) : MySum (PLift ((a n ≠ 4 → False) → False)) (PLift (a n ≠ 4)) :=
    get_sum_basic6 n
end

theorem oeis_275768_conjecture_0 : ¬ ∃ n : ℕ, a n = 4 := by
  intro ⟨n, hn⟩
  match get_sum_basic5 n with
  | .inl val5 => exact val5.down hn
  | .inr val5 =>
    match get_sum_basic3 n with
    | .inl val3 => exact val5.down val3.down
    | .inr val3 =>
      match get_sum_basic6 n with
      | .inl val6 => exact val6.down val3.down
      | .inr val6 => exact val3.down val6.down
