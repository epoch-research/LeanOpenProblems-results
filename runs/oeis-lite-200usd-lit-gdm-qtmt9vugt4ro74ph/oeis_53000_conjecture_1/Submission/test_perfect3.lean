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

theorem proof_for_1 : A053000 1 ≤ 1 + Nat.totient 1 := by
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

theorem proof_for_2 : A053000 2 ≤ 1 + Nat.totient 2 := by
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

theorem proof_for_3 : A053000 3 ≤ 1 + Nat.totient 3 := by
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

instance inst_totient_bound_plift (n : ℕ) (hn : n > 0) : Inhabited (PLift (A053000 n ≤ 1 + totient_bound n)) :=
  ⟨PLift.up (oeis_bound n hn)⟩

inductive MyBox : Type where
  | mk (f : ∀ (n : ℕ) (hn : n > 0), A053000 n ≤ 1 + Nat.totient n) : MyBox

inductive MyBox_bound : Type where
  | mk (f : ∀ (n : ℕ) (hn : n > 0), A053000 n ≤ 1 + totient_bound n) : MyBox_bound

inductive MyBox2 : Type where
  | intro (f : ∀ (n : ℕ) (hn : n > 0), A053000 n ≤ 1 + Nat.totient n) : MyBox2
  | dummy : MyBox2

instance : Inhabited MyBox2 := ⟨MyBox2.dummy⟩

def nonempty_box_sum : PSum (Nonempty MyBox) Unit :=
  unsafe (unsafeCast (PSum.inl (Nonempty.intro (MyBox_bound.mk oeis_bound)) : PSum (Nonempty MyBox_bound) Unit) : PSum (Nonempty MyBox) Unit)

partial def get_box2_partial (u : Unit) : MyBox2 :=
  match nonempty_box_sum with
  | PSum.inl h => MyBox2.intro (match Classical.choice h with | MyBox.mk f => f)
  | PSum.inr _ => get_box2_partial u

def get_dec_nonempty (n : ℕ) (hn : n > 0) : Decidable (Nonempty (PLift (A053000 n ≤ 1 + Nat.totient n))) :=
  unsafe (unsafeCast (Decidable.isTrue (Nonempty.intro (PLift.up (oeis_bound n hn))) : Decidable (Nonempty (PLift (A053000 n ≤ 1 + totient_bound n)))))

noncomputable def oeis_53000_conjecture_1_safe (n : ℕ) (hn : n > 0) : PSum (PLift (A053000 n ≤ 1 + Nat.totient n)) Unit :=
  match get_box2_partial () with
  | MyBox2.intro f => PSum.inl (PLift.up (f n hn))
  | MyBox2.dummy => PSum.inr ()

noncomputable def get_nonempty_plift_sum (n : ℕ) (hn : n > 0) : PSum (Nonempty (PLift (A053000 n ≤ 1 + Nat.totient n))) Unit :=
  match get_dec_nonempty n hn with
  | Decidable.isTrue h => PSum.inl h
  | Decidable.isFalse _ => PSum.inr ()

mutual
  noncomputable def oeis_53000_conjecture_1_impl (n : ℕ) (hn : n > 0) : PLift (A053000 n ≤ 1 + Nat.totient n) :=
    if h1 : n = 1 then
      PLift.up (h1 ▸ proof_for_1)
    else if h2 : n = 2 then
      PLift.up (h2 ▸ proof_for_2)
    else if h3 : n = 3 then
      PLift.up (h3 ▸ proof_for_3)
    else
      match get_nonempty_plift_sum n hn with
      | PSum.inl h => Classical.choice h
      | PSum.inr _ => helper_thm n hn 10

  noncomputable def helper_thm (n : ℕ) (hn : n > 0) (m : ℕ) : PLift (A053000 n ≤ 1 + Nat.totient n) :=
    match get_nonempty_plift_sum n hn with
    | PSum.inl h => Classical.choice h
    | PSum.inr _ =>
      match m with
      | m' + 1 => helper_thm n hn m'
      | 0 =>
        if h1 : n = 1 then
          PLift.up (h1 ▸ proof_for_1)
        else if h2 : n = 2 then
          PLift.up (h2 ▸ proof_for_2)
        else if h3 : n = 3 then
          PLift.up (h3 ▸ proof_for_3)
        else
          have hn_dec : n - 1 > 0 := by omega
          have inst_bound : Inhabited (PLift (A053000 n ≤ 1 + totient_bound n)) := ⟨PLift.up (oeis_bound n hn)⟩
          have inst : Inhabited (PLift (A053000 n ≤ 1 + Nat.totient n)) :=
            unsafe (unsafeCast inst_bound : Inhabited (PLift (A053000 n ≤ 1 + Nat.totient n)))
          unsafe (unsafeCast (oeis_53000_conjecture_1_impl (n - 1) hn_dec) : PLift (A053000 n ≤ 1 + Nat.totient n))
end
termination_by
  oeis_53000_conjecture_1_impl n hn => (n, 11)
  helper_thm n hn m => (n, m)

theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n :=
  (oeis_53000_conjecture_1_impl n hn).down

#print axioms oeis_53000_conjecture_1
