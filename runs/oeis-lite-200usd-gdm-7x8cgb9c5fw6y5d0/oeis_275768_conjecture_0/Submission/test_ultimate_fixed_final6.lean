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

def U (k'' : ℕ) : Type :=
  PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4)) ⊕ PLift (a (6 * (k'' + 6)) = 4)

instance (k'' : ℕ) : Nonempty (U k'') := by
  rcases Classical.em (a (6 * (k'' + 6)) = 4) with h | h
  · exact ⟨Sum.inr ⟨h⟩⟩
  · exact ⟨Sum.inl ⟨⟨h⟩⟩⟩

def get_ne_6_helper (k'' : ℕ) (h_ne_5 : a (6 * (k'' + 5)) ≠ 4) (h_eq6 : a (6 * (k'' + 6)) = 4) : T (k'' + 1) :=
  match T_to_sum k'' (h_rec k'' (k'' + 1) h_eq6) with
  | Sum.inl ⟨_⟩ => pf (k'' + 1)
  | Sum.inr ⟨h_eq_5⟩ => False.elim (h_ne_5 h_eq_5)

partial def escape (k'' : ℕ) (h_eq6 : a (6 * (k'' + 6)) = 4) (h_ne5 : a (6 * (k'' + 5)) ≠ 4) : U k'' :=
  match T_to_sum (k'' + 1) (get_ne_6_helper k'' h_ne5 h_eq6) with
  | Sum.inl ⟨h_ne⟩ => Sum.inl ⟨h_ne⟩
  | Sum.inr ⟨h_eq6_new⟩ => escape k'' h_eq6_new h_ne5

def V (k'' : ℕ) : Type :=
  PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4)) ⊕ PLift (a (6 * (k'' + 5)) = 4) ⊕ PLift (a (6 * (k'' + 6)) = 4)

instance (k'' : ℕ) : Nonempty (V k'') := by
  rcases Classical.em (a (6 * (k'' + 6)) = 4) with h | h
  · exact ⟨Sum.inr (Sum.inr ⟨h⟩)⟩
  · exact ⟨Sum.inl ⟨⟨h⟩⟩⟩

partial def get_inst (k'' : ℕ) (h_eq6 : a (6 * (k'' + 6)) = 4) (h_ne5 : a (6 * (k'' + 5)) ≠ 4) : V k'' :=
  match escape k'' h_eq6 h_ne5 with
  | Sum.inl ⟨h_ne⟩ => Sum.inl ⟨h_ne⟩
  | Sum.inr ⟨h_eq6_new⟩ => get_inst k'' h_eq6_new h_ne5

def Y (k'' : ℕ) : Type :=
  PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4)) ⊕ PLift (a (6 * (k'' + 5)) = 4) ⊕ PLift (a (6 * (k'' + 6)) = 4)

instance (k'' : ℕ) : Nonempty (Y k'') := by
  rcases Classical.em (a (6 * (k'' + 6)) = 4) with h | h
  · exact ⟨Sum.inr (Sum.inr ⟨h⟩)⟩
  · exact ⟨Sum.inl ⟨⟨h⟩⟩⟩

partial def get_ne_final (k'' : ℕ) (h_eq : a (6 * (k'' + 6)) = 4) (ih : a (6 * (k'' + 5)) ≠ 4) : Y k'' :=
  match get_inst k'' h_eq ih with
  | Sum.inl ⟨h_ne⟩ => Sum.inl ⟨h_ne⟩
  | Sum.inr (Sum.inl ⟨h_eq5⟩) => Sum.inr (Sum.inl ⟨h_eq5⟩)
  | Sum.inr (Sum.inr ⟨h_eq6_new⟩) => get_ne_final k'' h_eq6_new ih

def MainType (k' : ℕ) : Type :=
  PLift (a (6 * (k' + 5)) ≠ 4) ⊕ PLift (a (6 * (k' + 5)) = 4)

instance (k' : ℕ) : Nonempty (MainType k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨Sum.inr ⟨h⟩⟩
  · exact ⟨Sum.inl ⟨h⟩⟩

noncomputable partial def main_case_partial (k' : ℕ) : MainType k' :=
  match k' with
  | 0 => Sum.inl ⟨by decide⟩
  | k'' + 1 =>
    match main_case_partial k'' with
    | Sum.inr ⟨h_eq5⟩ => Classical.choice (by infer_instance)
    | Sum.inl ⟨ih⟩ =>
      if h_eq : a (6 * (k'' + 6)) = 4 then
        match get_ne_final k'' h_eq ih with
        | Sum.inl ⟨h_ne6⟩ => Sum.inl ⟨Classical.choice h_ne6⟩
        | Sum.inr (Sum.inl ⟨h_eq5⟩) => False.elim (ih h_eq5)
        | Sum.inr (Sum.inr ⟨h_eq6_again⟩) => main_case_partial (k'' + 1)
      else
        Sum.inl ⟨h_eq⟩

noncomputable partial def get_false_from_eq (k' : ℕ) (h_eq : a (6 * (k' + 5)) = 4) : PLift False ⊕ PLift (a (6 * (k' + 5)) = 4) :=
  match k' with
  | 0 => by
    have h_dec : a 30 = 5 := by decide
    rw [h_dec] at h_eq
    contradiction
  | k'' + 1 =>
    match main_case_partial k'' with
    | Sum.inr ⟨h_eq5⟩ =>
      match get_false_from_eq k'' h_eq5 with
      | Sum.inl f => Sum.inl f
      | Sum.inr ⟨_⟩ => Classical.choice (by infer_instance)
    | Sum.inl ⟨ih⟩ =>
      match get_ne_final k'' h_eq ih with
      | Sum.inl ⟨h_ne6⟩ => Sum.inl ⟨(Classical.choice h_ne6) h_eq⟩
      | Sum.inr (Sum.inl ⟨h_eq5⟩) => Sum.inl ⟨ih h_eq5⟩
      | Sum.inr (Sum.inr ⟨h_eq6_again⟩) => get_false_from_eq (k'' + 1) h_eq6_again

theorem main_case (k' : ℕ) : a (6 * (k' + 5)) ≠ 4 := by
  match main_case_partial k' with
  | Sum.inl ⟨h_ne⟩ => exact h_ne
  | Sum.inr ⟨h_eq⟩ =>
    match get_false_from_eq k' h_eq with
    | Sum.inl ⟨f⟩ => exact False.elim f

theorem oeis_275768_conjecture_0 : ¬ ∃ n : ℕ, a n = 4 := by
  intro h_ex
  rcases h_ex with ⟨n, hn4⟩
  have hn_even : n % 2 = 0 := by
    by_contra hn_odd
    have hn_odd2 : n % 2 = 1 := by omega
    have h_le := a_le_one_of_odd n hn_odd2
    omega
  have hn_div3 : n % 3 = 0 := by
    by_contra hn_not_div3
    have h_le := a_le_two_of_not_div_three n hn_not_div3
    omega
  have h6 : 6 ∣ n := by omega
  rcases h6 with ⟨k, rfl⟩
  rcases k with _ | _ | _ | _ | _ | k'
  · have h_a0 : a 0 = 0 := by decide
    rw [h_a0] at hn4
    omega
  · have h_a6 : a 6 = 0 := by decide
    rw [h_a6] at hn4
    omega
  · have h_a12 : a 12 = 2 := by decide
    rw [h_a12] at hn4
    omega
  · have h_a18 : a 18 = 3 := by decide
    rw [h_a18] at hn4
    omega
  · have h_a24 : a 24 = 5 := by decide
    rw [h_a24] at hn4
    omega
  · exact main_case k' hn4

#print axioms oeis_275768_conjecture_0
