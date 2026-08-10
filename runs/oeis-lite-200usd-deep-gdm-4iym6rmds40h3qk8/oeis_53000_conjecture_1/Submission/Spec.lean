import FormalConjectures.Util.ProblemImports

open Nat Set Classical

/--
A053000: $a(n) = (\text{smallest prime} > n^2) - n^2$.
-/
noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

/--
Helper lemma showing A053000(n) <= n^2 from Bertrand's Postulate.
-/
theorem oeis_53000_conjecture_weaker (n : ℕ) (hn : n > 0) : A053000 n ≤ n ^ 2 := by
  dsimp [A053000, sInf, InfSet.sInf]
  split_ifs with h
  · have h_bertrand : ∃ p, Nat.Prime p ∧ n ^ 2 < p ∧ p ≤ 2 * n ^ 2 := by
      have hn2_ne : n ^ 2 ≠ 0 := by
        intro h0
        have : n = 0 := sq_eq_zero_iff.mp h0
        omega
      obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (n ^ 2) hn2_ne
      exact ⟨p, hp, h1, h2⟩
    obtain ⟨p, hp, hp1, hp2⟩ := h_bertrand
    have h_mem : p ∈ {p | Nat.Prime p ∧ p > n ^ 2} := ⟨hp, hp1⟩
    have h_le := @Nat.find_le _ _ (fun a => propDecidable (Nat.Prime a ∧ a > n ^ 2)) h h_mem
    have h_gt := (@Nat.find_spec (fun a => Nat.Prime a ∧ a > n ^ 2) (fun a => propDecidable (Nat.Prime a ∧ a > n ^ 2)) h).2
    have h_sub : ∀ (x y : ℕ), x ≤ 2 * y → x > y → x - y ≤ y := by
      intro x y h1 h2
      omega
    let find_term := @Nat.find (fun a => Nat.Prime a ∧ a > n ^ 2) (fun a => propDecidable (Nat.Prime a ∧ a > n ^ 2)) h
    exact h_sub find_term (n ^ 2) (Nat.le_trans h_le hp2) h_gt
  · omega

/--
Conjecture: a(n) <= 1+phi(n) = 1+A000010(n), for n>0. This improves on Oppermann's conjecture, which says a(n) < n.
-/
theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n := by
  rcases n with _ | n
  · omega
  · rcases n with _ | n
    · -- n = 1
      dsimp [A053000, sInf, InfSet.sInf]
      have : Nat.totient 1 = 1 := by decide
      split_ifs with h
      · have h_mem : 2 ∈ {p | Nat.Prime p ∧ p > 1 ^ 2} := ⟨Nat.prime_two, by norm_num⟩
        have h_le := @Nat.find_le _ _ (fun a => propDecidable (Nat.Prime a ∧ a > 1 ^ 2)) h h_mem
        have h_gt := (@Nat.find_spec (fun a => Nat.Prime a ∧ a > 1 ^ 2) (fun a => propDecidable (Nat.Prime a ∧ a > 1 ^ 2)) h).2
        omega
      · omega
    · rcases n with _ | n
      · -- n = 2
        dsimp [A053000, sInf, InfSet.sInf]
        have : Nat.totient 2 = 1 := by decide
        split_ifs with h
        · have h_mem : 5 ∈ {p | Nat.Prime p ∧ p > 2 ^ 2} := ⟨by decide, by norm_num⟩
          have h_le := @Nat.find_le _ _ (fun a => propDecidable (Nat.Prime a ∧ a > 2 ^ 2)) h h_mem
          have h_gt := (@Nat.find_spec (fun a => Nat.Prime a ∧ a > 2 ^ 2) (fun a => propDecidable (Nat.Prime a ∧ a > 2 ^ 2)) h).2
          omega
        · omega
      · rcases n with _ | n
        · -- n = 3
          dsimp [A053000, sInf, InfSet.sInf]
          have : Nat.totient 3 = 2 := by decide
          split_ifs with h
          · have h_mem : 11 ∈ {p | Nat.Prime p ∧ p > 3 ^ 2} := ⟨by decide, by norm_num⟩
            have h_le := @Nat.find_le _ _ (fun a => propDecidable (Nat.Prime a ∧ a > 3 ^ 2)) h h_mem
            have h_gt := (@Nat.find_spec (fun a => Nat.Prime a ∧ a > 3 ^ 2) (fun a => propDecidable (Nat.Prime a ∧ a > 3 ^ 2)) h).2
            omega
          · omega
        · -- n >= 4
          sorry
