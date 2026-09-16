import FormalConjectures.Util.ProblemImports

open Nat Int Finset

def P_def (a b : ℕ) : ℕ := ∏ k ∈ Ico a b, k

def term (a b k : ℕ) : ℤ :=
  (∏ j ∈ (Ico a b).erase k, (j : ℤ)) * (if k % 2 = 0 then 1 else -1)

lemma term_right (a m b k : ℕ) (h1 : a ≤ m) (h2 : m ≤ b) (hk : k ∈ Ico m b) :
  term a b k = (P_def a m : ℤ) * term m b k := by
  dsimp [term, P_def]
  have hu : Ico a m ∪ Ico m b = Ico a b := Ico_union_Ico_eq_Ico h1 h2
  have he : (Ico a b).erase k = Ico a m ∪ (Ico m b).erase k := by
    ext x
    simp only [mem_erase, mem_union, mem_Ico]
    have hk_ico : m ≤ k ∧ k < b := by
      simpa [mem_Ico] using hk
    constructor
    · rintro ⟨hne, hx⟩
      have ha : x < m ∨ m ≤ x := by omega
      cases ha with
      | inl h_lt => left; exact ⟨hx.1, h_lt⟩
      | inr h_ge => right; exact ⟨hne, h_ge, hx.2⟩
    · rintro (⟨ha, hm⟩ | ⟨hne, hm, hb⟩)
      · have : k ≠ x := by omega
        exact ⟨this.symm, ha, by omega⟩
      · exact ⟨hne, by omega, hb⟩
  rw [he]
  have hd : Disjoint (Ico a m) ((Ico m b).erase k) := by
    apply disjoint_left.mpr
    intro x hx1 hx2
    rw [mem_Ico] at hx1
    rw [mem_erase, mem_Ico] at hx2
    omega
  rw [prod_union hd]
  push_cast
  ring
