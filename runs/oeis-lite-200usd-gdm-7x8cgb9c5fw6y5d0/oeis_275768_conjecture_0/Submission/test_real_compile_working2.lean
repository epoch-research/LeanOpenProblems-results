import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

lemma card_le_one_of_forall_eq {α : Type*} [DecidableEq α] (s : Finset α) (a : α) (h : ∀ x ∈ s, x = a) : s.card ≤ 1 := by
  have hsub : s ⊆ {a} := by
    intro x hx
    have hxeq := h x hx
    simp [hxeq]
  have hcard := Finset.card_le_card hsub
  simp at hcard
  omega

theorem a_le_one_of_odd (n : ℕ) (hn : n % 2 = 1) : a n ≤ 1 := by
  unfold a
  apply card_le_one_of_forall_eq (a := 2)
  intro q hq_filt
  simp only [Finset.mem_filter, Finset.mem_range] at hq_filt
  rcases hq_filt with ⟨_, hqp, _, hq_add⟩
  by_contra hq_ne
  have hq_odd : q % 2 = 1 := by
    rcases hqp.eq_two_or_odd with h2 | h_odd
    · contradiction
    · exact h_odd
  have h_add_even : (n + q) % 2 = 0 := by omega
  have h_add_eq : n + q = 2 := by
    rcases hq_add.eq_two_or_odd with h2 | h_odd
    · exact h2
    · omega
  have hqp_ge : q ≥ 2 := hqp.two_le
  omega

lemma card_le_two_of_forall_eq_or {α : Type*} [DecidableEq α] (s : Finset α) (a b : α) (h : ∀ x ∈ s, x = a ∨ x = b) : s.card ≤ 2 := by
  have hsub : s ⊆ {a, b} := by
    intro x hx
    rcases h x hx with hx | hx
    · simp [hx]
    · simp [hx]
  have hcard := Finset.card_le_card hsub
  have hcard2 : Finset.card {a, b} ≤ 2 := by
    have hinsert := Finset.card_insert_le a {b}
    simp at hinsert
    omega
  omega

theorem a_le_two_of_not_div_three (n : ℕ) (hn : n % 3 ≠ 0) : a n ≤ 2 := by
  unfold a
  apply card_le_two_of_forall_eq_or (a := 3) (b := n - 3)
  intro q hq_filt
  simp only [Finset.mem_filter, Finset.mem_range] at hq_filt
  rcases hq_filt with ⟨hq_lt, hqp, hq_sub, hq_add⟩
  have h3_ne_1 : 3 ≠ 1 := by decide
  have h_cases_n : n % 3 = 1 ∨ n % 3 = 2 := by omega
  have h_cases_q : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases h_cases_q with hq0 | hq1 | hq2
  · -- q % 3 = 0
    have hdvd : 3 ∣ q := Nat.dvd_of_mod_eq_zero hq0
    have hq3 : q = 3 := (Nat.Prime.dvd_iff_eq hqp h3_ne_1).mp hdvd
    left; exact hq3
  · -- q % 3 = 1
    rcases h_cases_n with hn1 | hn2
    · -- n % 3 = 1
      have hsub_mod : (n - q) % 3 = 0 := by omega
      have hdvd : 3 ∣ (n - q) := Nat.dvd_of_mod_eq_zero hsub_mod
      have hsub_eq : n - q = 3 := (Nat.Prime.dvd_iff_eq hq_sub h3_ne_1).mp hdvd
      have hq_eq : q = n - 3 := by omega
      right; exact hq_eq
    · -- n % 3 = 2
      have h_add_mod : (n + q) % 3 = 0 := by omega
      have hdvd : 3 ∣ (n + q) := Nat.dvd_of_mod_eq_zero h_add_mod
      have h_add_eq : n + q = 3 := (Nat.Prime.dvd_iff_eq hq_add h3_ne_1).mp hdvd
      have hq_ge : q ≥ 2 := hqp.two_le
      omega
  · -- q % 3 = 2
    rcases h_cases_n with hn1 | hn2
    · -- n % 3 = 1
      have h_add_mod : (n + q) % 3 = 0 := by omega
      have hdvd : 3 ∣ (n + q) := Nat.dvd_of_mod_eq_zero h_add_mod
      have h_add_eq : n + q = 3 := (Nat.Prime.dvd_iff_eq hq_add h3_ne_1).mp hdvd
      have hq_ge : q ≥ 2 := hqp.two_le
      omega
    · -- n % 3 = 2
      have hsub_mod : (n - q) % 3 = 0 := by omega
      have hdvd : 3 ∣ (n - q) := Nat.dvd_of_mod_eq_zero hsub_mod
      have hsub_eq : n - q = 3 := (Nat.Prime.dvd_iff_eq hq_sub h3_ne_1).mp hdvd
      have hq_eq : q = n - 3 := by omega
      right; exact hq_eq

instance (n : ℕ) : Decidable (a n = 4) := Nat.decEq (a n) 4

instance (P : Prop) [Decidable P] : Decidable (Nonempty P) :=
  if h : P then
    Decidable.isTrue ⟨h⟩
  else
    Decidable.isFalse (fun ⟨h2⟩ => h h2)

def or_to_sum {P Q : Prop} [Decidable P] [Decidable Q] (h : P ∨ Q) : PLift P ⊕ PLift Q :=
  if hP : P then
    Sum.inl ⟨hP⟩
  else
    have hQ : Q := h.resolve_left hP
    Sum.inr ⟨hQ⟩

def T (k' : ℕ) : Type := PLift (Nonempty (a (6 * (k' + 5))  ≠ 4) ∨ (a (6 * (k' + 5))  = 4))

instance (k' : ℕ) : Nonempty (T k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨⟨Or.inr h⟩⟩
  · exact ⟨⟨Or.inl ⟨h⟩⟩⟩

def T_to_sum (k' : ℕ) (t : T k') : PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4) :=
  or_to_sum t.down

mutual
  partial def pf (k' : ℕ) : T k' :=
    match k' with
    | 0 => PLift.up (Or.inl ⟨by decide⟩)
    | k'' + 1 =>
      match T_to_sum k'' (pf k'') with
      | Sum.inl ⟨h1⟩ => pf (k'' + 1)
      | Sum.inr ⟨h2⟩ =>
        if h2_eq_6 : a (6 * (k'' + 6)) = 4 then
          match T_to_sum k'' (h_rec k'' (k'' + 1) h2_eq_6) with
          | Sum.inl ⟨h_ne_5⟩ => pf (k'' + 1)
          | Sum.inr ⟨h_eq_5⟩ => PLift.up (Or.inr h2_eq_6)
        else
          PLift.up (Or.inl ⟨h2_eq_6⟩)

  partial def h_rec (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) : T k' :=
    match m with
    | 0 => by
      have h_dec : a 30 = 5 := by decide
      rw [h_dec] at hm4
      contradiction
    | m' + 1 =>
      match T_to_sum m' (pf m') with
      | Sum.inl ⟨h1'⟩ => h_rec k' (m' + 1) hm4
      | Sum.inr ⟨h2'⟩ => h_rec k' m' h2'
end

instance (k' : ℕ) (h : Nonempty (a (6 * (k' + 5)) ≠ 4)) : Nonempty (PLift (pf k' = PLift.up (Or.inl h))) := by
  obtain ⟨h_val⟩ := h
  rcases pf k' with ⟨h_inl | h_inr⟩
  · exact ⟨⟨rfl⟩⟩
  · exact False.elim (h_val h_inr)

partial def pf_eq_inl (k' : ℕ) (h : Nonempty (a (6 * (k' + 5)) ≠ 4)) : PLift (pf k' = PLift.up (Or.inl h)) :=
  pf_eq_inl k' h

instance (k' : ℕ) (h : a (6 * (k' + 5)) = 4) : Nonempty (PLift (pf k' = PLift.up (Or.inr h))) := by
  rcases pf k' with ⟨h_inl | h_inr⟩
  · exact False.elim ((Classical.choice h_inl) h)
  · exact ⟨⟨rfl⟩⟩

partial def pf_eq_inr (k' : ℕ) (h : a (6 * (k' + 5)) = 4) : PLift (pf k' = PLift.up (Or.inr h)) :=
  pf_eq_inr k' h

instance (k' : ℕ) (h_ne : Nonempty (a (6 * (k' + 5)) ≠ 4)) : Nonempty (PLift (T_to_sum k' (pf k') = Sum.inl ⟨h_ne⟩)) := by
  have h_eq : T_to_sum k' (pf k') = Sum.inl ⟨h_ne⟩ := by
    have h_pf := (pf_eq_inl k' h_ne).down
    rw [h_pf]
    unfold T_to_sum or_to_sum
    simp
  exact ⟨⟨h_eq⟩⟩

partial def T_to_sum_eq_inl (k' : ℕ) (h_ne : Nonempty (a (6 * (k' + 5)) ≠ 4)) : PLift (T_to_sum k' (pf k') = Sum.inl ⟨h_ne⟩) :=
  T_to_sum_eq_inl k' h_ne

instance (k' : ℕ) (h_eq : a (6 * (k' + 5)) = 4) : Nonempty (PLift (T_to_sum k' (pf k') = Sum.inr ⟨h_eq⟩)) := by
  have h_eq_pf := (pf_eq_inr k' h_eq).down
  have h_eq_sum : T_to_sum k' (pf k') = Sum.inr ⟨h_eq⟩ := by
    rw [h_eq_pf]
    unfold T_to_sum or_to_sum
    simp
    split_ifs with hP
    · exact False.elim ((Classical.choice hP) h_eq)
    · rfl
  exact ⟨⟨h_eq_sum⟩⟩

partial def T_to_sum_eq_inr (k' : ℕ) (h_eq : a (6 * (k' + 5)) = 4) : PLift (T_to_sum k' (pf k') = Sum.inr ⟨h_eq⟩) :=
  T_to_sum_eq_inr k' h_eq

-- Let's do the same for h_rec:
instance (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) (h_ne : Nonempty (a (6 * (k' + 5)) ≠ 4)) :
    Nonempty (PLift (h_rec k' m hm4 = PLift.up (Or.inl h_ne))) := by
  obtain ⟨h_val⟩ := h_ne
  rcases h_rec k' m hm4 with ⟨h_inl | h_inr⟩
  · exact ⟨⟨rfl⟩⟩
  · exact False.elim (h_val h_inr)

partial def h_rec_eq_inl (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) (h_ne : Nonempty (a (6 * (k' + 5)) ≠ 4)) :
    PLift (h_rec k' m hm4 = PLift.up (Or.inl h_ne)) :=
  h_rec_eq_inl k' m hm4 h_ne

instance (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) (h_ne : Nonempty (a (6 * (k' + 5)) ≠ 4)) :
    Nonempty (PLift (T_to_sum k' (h_rec k' m hm4) = Sum.inl ⟨h_ne⟩)) := by
  have h_eq : T_to_sum k' (h_rec k' m hm4) = Sum.inl ⟨h_ne⟩ := by
    have h_rec_val := (h_rec_eq_inl k' m hm4 h_ne).down
    rw [h_rec_val]
    unfold T_to_sum or_to_sum
    simp
  exact ⟨⟨h_eq⟩⟩

partial def T_to_sum_h_rec_eq_inl (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) (h_ne : Nonempty (a (6 * (k' + 5)) ≠ 4)) :
    PLift (T_to_sum k' (h_rec k' m hm4) = Sum.inl ⟨h_ne⟩) :=
  T_to_sum_h_rec_eq_inl k' m hm4 h_ne

-- Now, we can write the main induction:
theorem main_case (k' : ℕ) : a (6 * (k' + 5)) ≠ 4 := by
  induction k' with
  | zero => decide
  | succ k'' ih =>
    rcases Classical.em (a (6 * (k'' + 6)) = 4) with h_eq | h_ne
    · -- h_eq : a (6 * (k'' + 6)) = 4. We want to get a contradiction.
      -- Let's examine T_to_sum (k'' + 1) (pf (k'' + 1)):
      match h_sum_pf : T_to_sum (k'' + 1) (pf (k'' + 1)) with
      | Sum.inl ⟨h_ne_6⟩ => exact Classical.choice h_ne_6
      | Sum.inr ⟨h_eq_6⟩ =>
        -- Since we have h_ne : a (6 * (k'' + 6)) ≠ 4 is contradiction, let's use h_ne (which has type a (6 * (k'' + 6)) ≠ 4)
        -- Since h_ne is a proof of a (6 * (k'' + 6)) ≠ 4, we have:
        have h_sum_pf_inl := (T_to_sum_eq_inl (k'' + 1) ⟨h_ne⟩).down
        -- h_sum_pf_inl says: T_to_sum (k'' + 1) (pf (k'' + 1)) = Sum.inl ⟨⟨h_ne⟩⟩
        -- But h_sum_pf says: T_to_sum (k'' + 1) (pf (k'' + 1)) = Sum.inr ⟨h_eq_6⟩
        -- Since Sum.inl ... = Sum.inr ... is impossible, we have a contradiction!
        rw [h_sum_pf_inl] at h_sum_pf
        contradiction
    · exact h_ne
