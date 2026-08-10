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

inductive MyProp (k' : ℕ) : Prop where
  | intro : (a (6 * (k' + 5)) ≠ 4) → MyProp k'
  | dummy : (a (6 * (k' + 5)) = 4) → MyProp k'

instance (k' : ℕ) : Nonempty (MyProp k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨MyProp.dummy h⟩
  · exact ⟨MyProp.intro h⟩

partial def pf (k' : ℕ) : MyProp k' := pf k'

mutual
  def main_case (k' : ℕ) : PLift (a (6 * (k' + 5)) ≠ 4) :=
    match k' with
    | 0 => PLift.up (by decide)
    | k'' + 1 =>
      match (pf_eq k'').down with
      | ⟨h, _⟩ => PLift.up h

  def pf_eq (k'' : ℕ) : PLift (∃ h : a (6 * (k'' + 6)) ≠ 4, pf (k'' + 1) = MyProp.intro h) :=
    ⟨⟨(main_case (k'' + 1)).down, rfl⟩⟩
end

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
  · exact (main_case k').down hn4
