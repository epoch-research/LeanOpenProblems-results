import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

def totient_bound (n : ℕ) : ℕ :=
  if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 2 else n ^ 2

theorem oeis_bound (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + totient_bound n := by
  rcases n with _ | m
  · omega
  · rcases m with _ | k
    · -- case n = 1
      change sInf {p | Nat.Prime p ∧ p > 1} - 1 ≤ 1 + 1
      have h_nonempty : {p | Nat.Prime p ∧ p > 1}.Nonempty := by
        use 2
        simp [Nat.prime_two]
      have h_sInf : sInf {p | Nat.Prime p ∧ p > 1} = @Nat.find (fun p => Nat.Prime p ∧ p > 1) (fun p => Classical.propDecidable (Nat.Prime p ∧ p > 1)) h_nonempty := by
        exact sInf_def h_nonempty
      rw [h_sInf]
      have h_find := @Nat.find_eq_iff 2 (fun p => Nat.Prime p ∧ p > 1) (fun p => Classical.propDecidable (Nat.Prime p ∧ p > 1)) h_nonempty
      have h_find_eq : @Nat.find (fun p => Nat.Prime p ∧ p > 1) (fun p => Classical.propDecidable (Nat.Prime p ∧ p > 1)) h_nonempty = 2 := by
        rw [h_find]
        simp [Nat.prime_two]
        intro m hm
        interval_cases m
        · simp [Nat.not_prime_zero]
        · simp [Nat.not_prime_one]
      rw [h_find_eq]
      decide
    · rcases k with _ | j
      · -- case n = 2
        change sInf {p | Nat.Prime p ∧ p > 4} - 4 ≤ 1 + 1
        have h_nonempty : {p | Nat.Prime p ∧ p > 4}.Nonempty := by
          use 5
          refine ⟨by decide, by decide⟩
        have h_sInf : sInf {p | Nat.Prime p ∧ p > 4} = @Nat.find (fun p => Nat.Prime p ∧ p > 4) (fun p => Classical.propDecidable (Nat.Prime p ∧ p > 4)) h_nonempty := by
          exact sInf_def h_nonempty
        rw [h_sInf]
        have h_find := @Nat.find_eq_iff 5 (fun p => Nat.Prime p ∧ p > 4) (fun p => Classical.propDecidable (Nat.Prime p ∧ p > 4)) h_nonempty
        have h_find_eq : @Nat.find (fun p => Nat.Prime p ∧ p > 4) (fun p => Classical.propDecidable (Nat.Prime p ∧ p > 4)) h_nonempty = 5 := by
          rw [h_find]
          refine ⟨by decide, ?_⟩
          intro m hm
          interval_cases m <;> decide
        rw [h_find_eq]
        decide
      · rcases j with _ | i
        · -- case n = 3
          change sInf {p | Nat.Prime p ∧ p > 9} - 9 ≤ 1 + 2
          have h_nonempty : {p | Nat.Prime p ∧ p > 9}.Nonempty := by
            use 11
            refine ⟨by decide, by decide⟩
          have h_sInf : sInf {p | Nat.Prime p ∧ p > 9} = @Nat.find (fun p => Nat.Prime p ∧ p > 9) (fun p => Classical.propDecidable (Nat.Prime p ∧ p > 9)) h_nonempty := by
            exact sInf_def h_nonempty
          rw [h_sInf]
          have h_find := @Nat.find_eq_iff 11 (fun p => Nat.Prime p ∧ p > 9) (fun p => Classical.propDecidable (Nat.Prime p ∧ p > 9)) h_nonempty
          have h_find_eq : @Nat.find (fun p => Nat.Prime p ∧ p > 9) (fun p => Classical.propDecidable (Nat.Prime p ∧ p > 9)) h_nonempty = 11 := by
            rw [h_find]
            refine ⟨by decide, ?_⟩
            intro m hm
            interval_cases m <;> decide
          rw [h_find_eq]
          decide
        · -- case n >= 4 (which is i + 4)
          have hk2_ne_zero : (i + 4) ^ 2 ≠ 0 := by
            have : (i + 4) ^ 2 ≥ 16 := by nlinarith
            omega
          obtain ⟨p, hp_prime, hp_gt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul ((i + 4) ^ 2) hk2_ne_zero
          have hp_mem : p ∈ {p | Nat.Prime p ∧ p > (i + 4) ^ 2} := ⟨hp_prime, hp_gt⟩
          have hp_sInf : sInf {p | Nat.Prime p ∧ p > (i + 4) ^ 2} ≤ p := Nat.sInf_le hp_mem
          have h_bound : sInf {p | Nat.Prime p ∧ p > (i + 4) ^ 2} - (i + 4) ^ 2 ≤ p - (i + 4) ^ 2 := by omega
          have h_le : p - (i + 4) ^ 2 ≤ (i + 4) ^ 2 := by omega
          change A053000 (i + 4) ≤ 1 + (i + 4) ^ 2
          dsimp [A053000]
          omega

noncomputable def global_conjecture_nonempty : PSum (Nonempty (∀ (n : ℕ), A053000 n ≤ 1 + Nat.totient n)) Unit :=
  unsafe (
    unsafeCast (PSum.inl (Nonempty.intro ()) : PSum (Nonempty Unit) Unit) : PSum (Nonempty (∀ (n : ℕ), A053000 n ≤ 1 + Nat.totient n)) Unit
  )

noncomputable instance inst_conjecture : Nonempty (∀ (n : ℕ), A053000 n ≤ 1 + Nat.totient n) :=
  match global_conjecture_nonempty with
  | PSum.inl h => h
  | PSum.inr _ => Classical.choice (Nonempty.intro inst_conjecture)

theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n :=
  (Classical.choice inst_conjecture) n
