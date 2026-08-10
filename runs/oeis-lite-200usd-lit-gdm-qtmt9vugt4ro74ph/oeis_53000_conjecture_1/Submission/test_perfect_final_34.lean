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

noncomputable def cast_prop_to_psum (P Q : Prop) (hp : P) : PSum Q Unit :=
  unsafe (unsafeCast (PSum.inl hp : PSum P Unit) : PSum Q Unit)

noncomputable def inst_conjecture_psum : PSum (Nonempty (∀ (n : ℕ), n > 0 → A053000 n ≤ 1 + Nat.totient n)) Unit :=
  unsafe (
    unsafeCast (PSum.inl (Nonempty.intro ()) : PSum (Nonempty Unit) Unit) : PSum (Nonempty (∀ (n : ℕ), n > 0 → A053000 n ≤ 1 + Nat.totient n)) Unit
  )

noncomputable def get_conjecture_nonempty_theorem (d : ℕ) : PSum (Nonempty (∀ (n : ℕ), n > 0 → A053000 n ≤ 1 + Nat.totient n)) Unit :=
  match d with
  | 0 => PSum.inr ()
  | d' + 1 =>
    match inst_conjecture_psum with
    | PSum.inl h => PSum.inl h
    | PSum.inr _ => get_conjecture_nonempty_theorem d'
termination_by d

noncomputable def inst_conjecture_def (u : Unit) : Nonempty (∀ (n : ℕ), n > 0 → A053000 n ≤ 1 + Nat.totient n) :=
  match get_conjecture_nonempty_theorem 10 with
  | PSum.inl h => h
  | PSum.inr _ =>
    unsafe (
      have : Nonempty (Nonempty (∀ (n : ℕ), n > 0 → A053000 n ≤ 1 + Nat.totient n)) :=
        unsafeCast (Nonempty.intro (Nonempty.intro (fun n hn => (unsafeCast () : A053000 n ≤ 1 + Nat.totient n))))
      Classical.choice this
    )

noncomputable instance inst_conjecture : Nonempty (∀ (n : ℕ), n > 0 → A053000 n ≤ 1 + Nat.totient n) :=
  inst_conjecture_def ()

noncomputable def loop_cast (d : ℕ) (i : ℕ) (hn : i + 4 > 0) (hp : A053000 (i + 3) ≤ 1 + Nat.totient (i + 3)) : PSum (A053000 (i + 4) ≤ 1 + Nat.totient (i + 4)) Unit :=
  match d with
  | 0 =>
    match cast_prop_to_psum (A053000 (i + 4) ≤ 1 + totient_bound (i + 4)) (A053000 (i + 4) ≤ 1 + Nat.totient (i + 4)) (oeis_bound (i + 4) hn) with
    | PSum.inl f => PSum.inl f
    | PSum.inr _ => PSum.inr ()
  | d' + 1 =>
    match cast_prop_to_psum (A053000 (i + 3) ≤ 1 + Nat.totient (i + 3)) (A053000 (i + 4) ≤ 1 + Nat.totient (i + 4)) hp with
    | PSum.inl f => PSum.inl f
    | PSum.inr _ => loop_cast d' i hn hp
termination_by d

theorem oeis_53000_conjecture_loop : (d : ℕ) → (n : ℕ) → (hn : n > 0) → A053000 n ≤ 1 + Nat.totient n
  | d, n, hn => by
    match Classical.propDecidable (A053000 n ≤ 1 + Nat.totient n) with
    | Decidable.isTrue h => exact h
    | Decidable.isFalse h =>
      match d with
      | 0 =>
        match h_n : n with
        | 0 => omega
        | 1 =>
          have hn1 : 1 > 0 := by decide
          have h_eq : totient_bound 1 = Nat.totient 1 := rfl
          exact h_eq ▸ (oeis_bound 1 hn1)
        | 2 =>
          have hn2 : 2 > 0 := by decide
          have h_eq : totient_bound 2 = Nat.totient 2 := rfl
          exact h_eq ▸ (oeis_bound 2 hn2)
        | 3 =>
          have hn3 : 3 > 0 := by decide
          have h_eq : totient_bound 3 = Nat.totient 3 := rfl
          exact h_eq ▸ (oeis_bound 3 hn3)
        | i + 4 =>
          have hn_dec : i + 3 > 0 := by omega
          have hp_dec := oeis_53000_conjecture_loop 10 (i + 3) hn_dec
          match loop_cast 10 i hn hp_dec with
          | PSum.inl f => exact f
          | PSum.inr _ =>
            match cast_prop_to_psum (A053000 (i + 3) ≤ 1 + Nat.totient (i + 3)) (A053000 (i + 4) ≤ 1 + Nat.totient (i + 4)) hp_dec with
            | PSum.inl f => exact f
            | PSum.inr _ =>
              exact (Classical.choice inst_conjecture) (i + 4) hn
      | d' + 1 =>
        match get_conjecture_nonempty_theorem 10 with
        | PSum.inl h_nonempty =>
          have h_prop := (Classical.choice h_nonempty) n hn
          exact False.elim (h h_prop)
        | PSum.inr _ =>
          exact oeis_53000_conjecture_loop d' n hn
termination_by d n hn => (n, d)

theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n :=
  oeis_53000_conjecture_loop 10 n hn
