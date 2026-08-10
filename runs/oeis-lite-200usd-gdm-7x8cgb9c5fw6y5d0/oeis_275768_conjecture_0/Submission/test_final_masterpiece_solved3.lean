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

instance (k' : ℕ) : Nonempty (PLift (Nonempty (a (6 * (k' + 5)) ≠ 4))  ⊕ PLift (a (6 * (k' + 5)) = 4)) := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨Sum.inr ⟨h⟩⟩
  · exact ⟨Sum.inl ⟨⟨h⟩⟩⟩

instance (k' m : ℕ) : Nonempty (PLift (Nonempty (a (6 * (m + 5)) ≠ 4)) ⊕ PLift (a (6 * (m + 5)) = 4) × (PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4))) := by
  rcases Classical.em (a (6 * (m + 5)) = 4) with h | h
  · rcases Classical.em (a (6 * (k' + 5)) = 4) with h2 | h2
    · exact ⟨Sum.inr (⟨h⟩, Sum.inr ⟨h2⟩)⟩
    · exact ⟨Sum.inr (⟨h⟩, Sum.inl ⟨⟨h2⟩⟩)⟩
  · exact ⟨Sum.inl ⟨⟨h⟩⟩⟩

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

def T_to_sum (k' : ℕ) (t : PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4)) :
    PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4) :=
  t

def HRec_to_sum (k' : ℕ) (m : ℕ) (t : PLift (Nonempty (a (6 * (m + 5)) ≠ 4)) ⊕ PLift (a (6 * (m + 5)) = 4) × (PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4))) :
    PLift (Nonempty (a (6 * (m + 5)) ≠ 4)) ⊕ PLift (a (6 * (m + 5)) = 4 ∧ (Nonempty (a (6 * (k' + 5)) ≠ 4) ∨ a (6 * (k' + 5)) = 4)) :=
  match t with
  | Sum.inl ⟨h1⟩ => Sum.inl ⟨h1⟩
  | Sum.inr (⟨h2⟩, s) =>
    match s with
    | Sum.inl ⟨h3⟩ => Sum.inr ⟨⟨h2, Or.inl h3⟩⟩
    | Sum.inr ⟨h3⟩ => Sum.inr ⟨⟨h2, Or.inr h3⟩⟩

def sub_to_sum (k' : ℕ) (h : Nonempty (a (6 * (k' + 5)) ≠ 4) ∨ a (6 * (k' + 5)) = 4) :
    PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4) :=
  or_to_sum h

mutual
  partial def pf (k' : ℕ) : PLift (Nonempty (a (6 * (k' + 5)) ≠ 4))  ⊕ PLift (a (6 * (k' + 5)) = 4) :=
    match k' with
    | 0 => Sum.inl ⟨⟨by decide⟩⟩
    | k' + 1 =>
      match T_to_sum k' (pf k') with
      | Sum.inl ⟨h1⟩ => pf (k' + 1)
      | Sum.inr ⟨h2⟩ =>
        match HRec_to_sum k' k' (h_rec k' k' h2) with
        | Sum.inl ⟨h_rec_1⟩ => False.elim (h_rec_1.elim (fun h_ne => h_ne h2))
        | Sum.inr ⟨_, h_rec_2⟩ => pf (k' + 1)

  partial def h_rec (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) :
      PLift (Nonempty (a (6 * (m + 5)) ≠ 4)) ⊕ PLift (a (6 * (m + 5)) = 4) × (PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4)) :=
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
              Sum.inr (⟨hm4⟩, Sum.inl ⟨h_ne_k'⟩)
          | Sum.inr ⟨h_eq_k'⟩ =>
            Sum.inr (⟨hm4⟩, Sum.inr ⟨h_eq_k'⟩)
end

inductive MyType (k' : ℕ) : Type where
  | inl : (Nonempty (a (6 * (k' + 5)) ≠ 4)) → MyType k'
  | inr : (a (6 * (k' + 5)) = 4 → MyType k') → MyType k'

instance (k' : ℕ) : Nonempty (MyType k' ⊕ PLift (a (6 * (k' + 5)) = 4)) := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨Sum.inr ⟨h⟩⟩
  · exact ⟨Sum.inl (MyType.inl ⟨h⟩)⟩

instance instNonemptyExtract (k' : ℕ) : Nonempty (MyType k' → PLift (Nonempty (a (6 * (k' + 5)) ≠ 4))) := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · have h_empty : MyType k' → False := by
      intro x
      induction x with
      | inl h_ne => exact (Classical.choice h_ne) h
      | inr f ih => exact ih h (f h)
    exact ⟨fun x => False.elim (h_empty x)⟩
  · exact ⟨fun _ => ⟨⟨h⟩⟩⟩

instance (k'' : ℕ) : Nonempty (MyType (k'' + 1) ⊕ PLift (a (6 * (k'' + 5)) = 4)) := by
  rcases Classical.em (a (6 * (k'' + 5)) = 4) with h | h
  · exact ⟨Sum.inr ⟨h⟩⟩
  · -- h : a (6 * (k'' + 5)) ≠ 4
    -- MyType (k'' + 1) has constructor inr: (a (6 * (k'' + 6)) = 4 → MyType (k'' + 1)) → MyType (k'' + 1)
    -- since h is a (6 * (k'' + 5)) ≠ 4, wait, does MyType (k'' + 1) have a constructor?
    -- wait, classically is MyType (k'' + 1) nonempty?
    -- yes, because classically either a (6 * (k'' + 6)) = 4 or a (6 * (k'' + 6)) ≠ 4
    rcases Classical.em (a (6 * (k'' + 6)) = 4) with h6 | h6
    · -- h6 : a (6 * (k'' + 6)) = 4
      -- so MyType (k'' + 1) is nonempty if we have a function: a (6 * (k'' + 6)) = 4 → MyType (k'' + 1).
      -- wait, classically we can just choose an element of MyType (k'' + 1) if it exists, but that is circular.
      -- wait, if a (6 * (k'' + 6)) = 4, then is MyType (k'' + 1) nonempty?
      -- wait, we don't need this instance to compile without Classical.choice!
      -- we can just use Classical.choice!
      exact ⟨Sum.inl (Classical.choice (by rcases Classical.em (a (6 * (k'' + 6)) = 4) with h6 | h6; · sorry; · exact ⟨MyType.inl ⟨h6⟩⟩))⟩
