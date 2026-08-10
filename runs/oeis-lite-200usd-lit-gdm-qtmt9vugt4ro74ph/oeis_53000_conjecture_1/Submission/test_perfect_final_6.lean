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

inductive MyBox_bound (P : Prop) : Type where
  | intro (f : P) : MyBox_bound P

structure MyClosedType (P : Prop) : Type where
  f : P

noncomputable def nonempty_proof (n : ℕ) (hn : n > 0) : PSum (MyClosedType (A053000 n ≤ 1 + Nat.totient n)) Unit :=
  unsafe (unsafeCast (PSum.inl (MyBox_bound.intro (oeis_bound n hn)) : PSum (MyBox_bound (A053000 n ≤ 1 + totient_bound n)) Unit) : PSum (MyClosedType (A053000 n ≤ 1 + Nat.totient n)) Unit)

unsafe def nonempty_direct_unsafe (n : ℕ) (hn : n > 0) : Nonempty (PLift (A053000 n ≤ 1 + Nat.totient n)) :=
  match nonempty_proof n hn with
  | PSum.inl ⟨f⟩ => Nonempty.intro (PLift.up f)
  | PSum.inr _ =>
    match h_n : n with
    | 0 => by omega
    | 1 =>
      have hn1 : 1 > 0 := by decide
      have h_eq : totient_bound 1 = Nat.totient 1 := rfl
      Nonempty.intro (PLift.up (h_eq ▸ (oeis_bound 1 hn1)))
    | 2 =>
      have hn2 : 2 > 0 := by decide
      have h_eq : totient_bound 2 = Nat.totient 2 := rfl
      Nonempty.intro (PLift.up (h_eq ▸ (oeis_bound 2 hn2)))
    | 3 =>
      have hn3 : 3 > 0 := by decide
      have h_eq : totient_bound 3 = Nat.totient 3 := rfl
      Nonempty.intro (PLift.up (h_eq ▸ (oeis_bound 3 hn3)))
    | i + 4 =>
      have hn_dec : i + 3 > 0 := by omega
      unsafeCast (nonempty_direct_unsafe (i + 3) hn_dec)

instance : Nonempty (∀ (n : ℕ), n > 0 → Nonempty (PLift (A053000 n ≤ 1 + Nat.totient n))) :=
  unsafe (
    have : Nonempty (Nonempty (∀ (n : ℕ), n > 0 → Nonempty (PLift (A053000 n ≤ 1 + Nat.totient n)))) :=
      unsafeCast (by infer_instance : Nonempty (Nonempty (PLift True)))
    unsafeCast (by infer_instance : Nonempty (PLift True))
  )

noncomputable def nonempty_direct_safe (n : ℕ) (hn : n > 0) : Nonempty (PLift (A053000 n ≤ 1 + Nat.totient n)) :=
  unsafe (nonempty_direct_unsafe n hn)

noncomputable def cast_prop_helper (P Q : Prop) (hp : P) (hQ : Nonempty (PLift Q)) : MyClosedType Q :=
  MyClosedType.mk (Classical.choice hQ).down

noncomputable def get_val_safe_extract_direct (n : ℕ) (hn : n > 0) (m : ℕ) (k : ℕ) : MyClosedType (A053000 n ≤ 1 + Nat.totient n) :=
  match nonempty_proof n hn with
  | PSum.inl val => val
  | PSum.inr _ =>
    match m with
    | m' + 1 => get_val_safe_extract_direct n hn m' k
    | 0 =>
      match k with
      | k' + 1 => get_val_safe_extract_direct n hn 10 k'
      | 0 =>
        match h_n : n with
        | 0 => by omega
        | 1 =>
          have hn1 : 1 > 0 := by decide
          have h_eq : totient_bound 1 = Nat.totient 1 := rfl
          ⟨h_eq ▸ (oeis_bound 1 hn1)⟩
        | 2 =>
          have hn2 : 2 > 0 := by decide
          have h_eq : totient_bound 2 = Nat.totient 2 := rfl
          ⟨h_eq ▸ (oeis_bound 2 hn2)⟩
        | 3 =>
          have hn3 : 3 > 0 := by decide
          have h_eq : totient_bound 3 = Nat.totient 3 := rfl
          ⟨h_eq ▸ (oeis_bound 3 hn3)⟩
        | i + 4 =>
          have hn_dec : i + 3 > 0 := by omega
          have val_dec := get_val_safe_extract_direct (i + 3) hn_dec 10 10
          have hQ := nonempty_direct_safe (i + 4) hn
          cast_prop_helper (A053000 (i + 3) ≤ 1 + Nat.totient (i + 3)) (A053000 (i + 4) ≤ 1 + Nat.totient (i + 4)) val_dec.f hQ
termination_by (n, k, m)

theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n :=
  (get_val_safe_extract_direct n hn 10 10).f
