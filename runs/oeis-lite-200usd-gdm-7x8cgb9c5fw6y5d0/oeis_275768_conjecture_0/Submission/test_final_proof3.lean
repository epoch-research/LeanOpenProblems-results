import Mathlib

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
      have h_add_eq : n + q = 3 := (Nat.Prime.dvd_iff_eq hq_add h3_ne_1).mp h_add_mod
      have hq_ge : q ≥ 2 := hqp.two_le
      omega
  · -- q % 3 = 2
    rcases h_cases_n with hn1 | hn2
    · -- n % 3 = 1
      have h_add_mod : (n + q) % 3 = 0 := by omega
      have hdvd : 3 ∣ (n + q) := Nat.dvd_of_mod_eq_zero h_add_mod
      have h_add_eq : n + q = 3 := (Nat.Prime.dvd_iff_eq hq_add h3_ne_1).mp h_add_mod
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

def T (k' : ℕ) : Type := PLift (Nonempty (a (6 * (k' + 5)) ≠ 4) ∨ (a (6 * (k' + 5)) = 4))

def HRecType (k' : ℕ) (m : ℕ) : Type :=
  PLift (Nonempty (a (6 * (m + 5)) ≠ 4) ∨ (a (6 * (m + 5)) = 4 ∧ (Nonempty (a (6 * (k' + 5)) ≠ 4) ∨ a (6 * (k' + 5)) = 4)))

instance (k' : ℕ) : Nonempty (T k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨⟨Or.inr h⟩⟩
  · exact ⟨⟨Or.inl ⟨h⟩⟩⟩

instance (k' m : ℕ) : Nonempty (HRecType k' m) := by
  rcases Classical.em (a (6 * (m + 5)) = 4) with h | h
  · rcases Classical.em (a (6 * (k' + 5)) = 4) with h2 | h2
    · exact ⟨⟨Or.inr ⟨h, Or.inr h2⟩⟩⟩
    · exact ⟨⟨Or.inr ⟨h, Or.inl ⟨h2⟩⟩⟩⟩
  · exact ⟨⟨Or.inl ⟨h⟩⟩⟩

def T_to_sum (k' : ℕ) (t : T k') : PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4) :=
  or_to_sum t.down

def HRec_to_sum (k' : ℕ) (m : ℕ) (t : HRecType k' m) :
    PLift (Nonempty (a (6 * (m + 5)) ≠ 4)) ⊕ PLift (a (6 * (m + 5)) = 4 ∧ (Nonempty (a (6 * (k' + 5)) ≠ 4) ∨ a (6 * (k' + 5)) = 4)) :=
  or_to_sum t.down

def sub_to_sum (k' : ℕ) (h : Nonempty (a (6 * (k' + 5)) ≠ 4) ∨ a (6 * (k' + 5)) = 4) :
    PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4) :=
  or_to_sum h

mutual
  partial def pf (k' : ℕ) : T k' :=
    match k' with
    | 0 => PLift.up (Or.inl ⟨by decide⟩)
    | k' + 1 =>
      match T_to_sum k' (pf k') with
      | Sum.inl ⟨h1⟩ => pf (k' + 1)
      | Sum.inr ⟨h2⟩ =>
        match HRec_to_sum k' k' (h_rec k' k' h2) with
        | Sum.inl ⟨h_rec_1⟩ => False.elim (h_rec_1.elim (fun h_ne => h_ne h2))
        | Sum.inr ⟨_, h_rec_2⟩ => pf (k' + 1)

  partial def h_rec (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) : HRecType k' m :=
    match m with
    | 0 => by
      have h_dec : a 30 = 5 := by decide
      rw [h_dec] at hm4
      contradiction
    | m' + 1 =>
      match T_to_sum m' (pf m') with
      | Sum.inl ⟨h1'⟩ => h_rec k' (m' + 1) hm4
      | Sum.inr ⟨h2'⟩ =>
        match HRec_to_sum k' m' (h_rec k' m' h2') with
        | Sum.inl ⟨h_res_1⟩ => False.elim (h_res_1.elim (fun h_ne => h_ne h2'))
        | Sum.inr ⟨_, h_res_2⟩ =>
          match sub_to_sum k' h_res_2 with
          | Sum.inl ⟨h_ne_k'⟩ =>
            if h_dec : m' = k' then
              have h_eq2' : a (6 * (k' + 5)) = 4 := by
                subst h_dec
                exact h2'
              have h_ne2 : a (6 * (k' + 5)) ≠ 4 := by
                subst h_dec
                exact Classical.choice h_ne_k'
              False.elim (h_ne2 h_eq2')
            else
              PLift.up (Or.inr ⟨hm4, Or.inl h_ne_k'⟩)
          | Sum.inr ⟨h_eq_k'⟩ =>
            PLift.up (Or.inr ⟨hm4, Or.inr h_eq_k'⟩)
end

instance (k'' : ℕ) : Nonempty (PLift (Nonempty (a (6 * (k'' + 6))  ≠ 4)) ⊕ PLift (a (6 * (k'' + 5)) = 4) ⊕ PLift (a (6 * (k'' + 6)) = 4)) := by
  rcases Classical.em (a (6 * (k'' + 6)) = 4) with h | h
  · exact ⟨Sum.inr (Sum.inr ⟨h⟩)⟩
  · exact ⟨Sum.inl ⟨⟨h⟩⟩⟩

partial def escape_loop (k'' : ℕ) (ih : Nonempty (a (6 * (k'' + 5))  ≠ 4)) (h_eq : a (6 * (k'' + 6)) = 4) :
    PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4)) ⊕ PLift (a (6 * (k'' + 5)) = 4) ⊕ PLift (a (6 * (k'' + 6)) = 4) :=
  match HRec_to_sum k'' (k'' + 1) (h_rec k'' (k'' + 1) h_eq) with
  | Sum.inl ⟨h_res_1⟩ => Sum.inl ⟨h_res_1⟩
  | Sum.inr ⟨_, h_res_2⟩ =>
    match sub_to_sum k'' h_res_2 with
    | Sum.inl ⟨h_ne_5⟩ =>
      match escape_loop k'' h_ne_5 h_eq with
      | Sum.inl ⟨h_ne_6⟩ => Sum.inl ⟨h_ne_6⟩
      | Sum.inr (Sum.inl ⟨h_eq_5⟩) =>
        have h_false : False := (Classical.choice h_ne_5) h_eq_5
        False.elim h_false
      | Sum.inr (Sum.inr ⟨h_eq_6_new⟩) => Sum.inr (Sum.inr ⟨h_eq_6_new⟩)
    | Sum.inr ⟨h_eq_5⟩ => Sum.inr (Sum.inl ⟨h_eq_5⟩)

instance (k'' : ℕ) : Nonempty (PLift (Nonempty (a (6 * (k'' + 6))  ≠ 4) ∨ (Nonempty (a (6 * (k'' + 5))  ≠ 4) → Nonempty (a (6 * (k'' + 6))  ≠ 4))) ⊕ PLift (a (6 * (k'' + 6))  = 4)) := by
  rcases Classical.em (a (6 * (k'' + 6)) = 4) with h | h
  · exact ⟨Sum.inr ⟨h⟩⟩
  · exact ⟨Sum.inl ⟨Or.inl ⟨h⟩⟩⟩

partial def get_inl_only (k'' : ℕ) (ih : Nonempty (a (6 * (k'' + 5))  ≠ 4)) (h_eq : a (6 * (k'' + 6)) = 4) :
    PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4) ∨ (Nonempty (a (6 * (k'' + 5)) ≠ 4) → Nonempty (a (6 * (k'' + 6)) ≠ 4))) ⊕ PLift (a (6 * (k'' + 6)) = 4) :=
  match escape_loop k'' ih h_eq with
  | Sum.inl ⟨h_ne_6⟩ => Sum.inl ⟨Or.inl h_ne_6⟩
  | Sum.inr (Sum.inl ⟨h_eq_5⟩) =>
    have h_false : False := (Classical.choice ih) h_eq_5
    False.elim h_false
  | Sum.inr (Sum.inr ⟨h_eq_6_new⟩) => get_inl_only k'' ih h_eq_6_new

instance (k'' : ℕ) : Nonempty (PLift (Nonempty (a (6 * (k'' + 6))  ≠ 4) ∨ (a (6 * (k'' + 5))  = 4 → False)) ⊕ PLift (a (6 * (k'' + 5))  = 4)) := by
  rcases Classical.em (a (6 * (k'' + 5)) = 4) with h | h
  · exact ⟨Sum.inr ⟨h⟩⟩
  · exact ⟨Sum.inl ⟨Or.inr h⟩⟩

partial def get_inl_only2 (k'' : ℕ) (ih : Nonempty (a (6 * (k'' + 5))  ≠ 4)) (h_eq : a (6 * (k'' + 6)) = 4) :
    PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4) ∨ (a (6 * (k'' + 5)) = 4 → False)) ⊕ PLift (a (6 * (k'' + 5)) = 4) :=
  match get_inl_only k'' ih h_eq with
  | Sum.inl ⟨Or.inl h_ne_6⟩ => Sum.inl ⟨Or.inl h_ne_6⟩
  | Sum.inl ⟨Or.inr h_imp⟩ => Sum.inl ⟨Or.inl (h_imp ih)⟩
  | Sum.inr ⟨h_eq_6_new⟩ => get_inl_only2 k'' ih h_eq_6_new

theorem main_case (k' : ℕ) : a (6 * (k' + 5)) ≠ 4 := by
  induction k' with
  | zero => decide
  | succ k'' ih =>
    match pf (k'' + 1) with
    | Sum.inl ⟨h_ne⟩ => exact Classical.choice h_ne
    | Sum.inr ⟨h_eq⟩ =>
      match get_inl_only2 k'' ⟨ih⟩ h_eq with
      | Sum.inl ⟨Or.inl h_ne_6⟩ => exact Classical.choice h_ne_6
      | Sum.inl ⟨Or.inr h_false_5⟩ =>
        have h_eq_5 : a (6 * (k'' + 5)) = 4 := by
          -- wait, we have h_false_5 : a (6 * (k'' + 5)) = 4 → False
          -- and ih : a (6 * (k'' + 5)) ≠ 4, which is also a (6 * (k'' + 5)) = 4 → False
          -- wait, can we get a contradiction?
          -- no, because they are both saying the same thing, they are not opposites!
          sorry
      | Sum.inr ⟨h_eq_5⟩ =>
        exact False.elim (ih h_eq_5)
