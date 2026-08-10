import FormalConjectures.Util.ProblemImports

open Nat Finset

def A352628 (n : ℕ) : ℕ :=
  let S : Finset ℕ := range (n + 1)
  S.sum fun a =>
    S.sum fun b =>
      S.sum fun c =>
        S.sum fun d =>
          let E := (a^2) + (2 * b^2) + (c^4) + (2 * d^4) + (3 * c^2 * d^2)
          if E = n then 1 else 0

lemma le_of_repr {n a b c d : ℕ}
    (h : a ^ 2 + 2 * b ^ 2 + c ^ 4 + 2 * d ^ 4 + 3 * c ^ 2 * d ^ 2 = n) :
    a ≤ n ∧ b ≤ n ∧ c ≤ n ∧ d ≤ n := by
  have ha2 : a ^ 2 ≤ n := by nlinarith [h]
  have hb2 : b ^ 2 ≤ n := by nlinarith [h]
  have hc4 : c ^ 4 ≤ n := by nlinarith [h]
  have hd4 : d ^ 4 ≤ n := by nlinarith [h]
  constructor
  · exact (Nat.le_self_pow (by decide : 2 ≠ 0) a).trans ha2
  constructor
  · exact (Nat.le_self_pow (by decide : 2 ≠ 0) b).trans hb2
  constructor
  · exact (Nat.le_self_pow (by decide : 4 ≠ 0) c).trans hc4
  · exact (Nat.le_self_pow (by decide : 4 ≠ 0) d).trans hd4

lemma A352628_pos_of_repr {n : ℕ}
    (h : ∃ a b c d : ℕ,
      a ^ 2 + 2 * b ^ 2 + c ^ 4 + 2 * d ^ 4 + 3 * c ^ 2 * d ^ 2 = n) :
    A352628 n > 0 := by
  rcases h with ⟨a,b,c,d,habcd⟩
  have hle := le_of_repr habcd
  rw [A352628]
  let f := fun a : ℕ => ∑ b ∈ range (n + 1), ∑ c ∈ range (n + 1), ∑ d ∈ range (n + 1),
          let E := (a^2) + (2 * b^2) + (c^4) + (2 * d^4) + (3 * c^2 * d^2)
          if E = n then 1 else 0
  have hfa_nonneg : ∀ x ∈ range (n + 1), 0 ≤ f x := by intro x hx; positivity
  have h_main : f a ≤ ∑ x ∈ range (n + 1), f x :=
    Finset.single_le_sum hfa_nonneg (by simpa [Nat.succ_eq_add_one] using (Finset.mem_range_succ_iff.mpr hle.1))
  have hfa_pos : 0 < f a := by
    dsimp [f]
    let g := fun b : ℕ => ∑ c ∈ range (n + 1), ∑ d ∈ range (n + 1),
          let E := (a^2) + (2 * b^2) + (c^4) + (2 * d^4) + (3 * c^2 * d^2)
          if E = n then 1 else 0
    have hg_nonneg : ∀ x ∈ range (n + 1), 0 ≤ g x := by intro x hx; positivity
    have hgb_le : g b ≤ ∑ x ∈ range (n + 1), g x :=
      Finset.single_le_sum hg_nonneg (by simpa [Nat.succ_eq_add_one] using (Finset.mem_range_succ_iff.mpr hle.2.1))
    have hgb_pos : 0 < g b := by
      dsimp [g]
      let k := fun c : ℕ => ∑ d ∈ range (n + 1),
          let E := (a^2) + (2 * b^2) + (c^4) + (2 * d^4) + (3 * c^2 * d^2)
          if E = n then 1 else 0
      have hk_nonneg : ∀ x ∈ range (n + 1), 0 ≤ k x := by intro x hx; positivity
      have hkc_le : k c ≤ ∑ x ∈ range (n + 1), k x :=
        Finset.single_le_sum hk_nonneg (by simpa [Nat.succ_eq_add_one] using (Finset.mem_range_succ_iff.mpr hle.2.2.1))
      have hkc_pos : 0 < k c := by
        dsimp [k]
        let l := fun d : ℕ =>
          let E := (a^2) + (2 * b^2) + (c^4) + (2 * d^4) + (3 * c^2 * d^2)
          if E = n then 1 else 0
        have hl_nonneg : ∀ x ∈ range (n + 1), 0 ≤ l x := by intro x hx; dsimp [l]; split <;> simp
        have hld_le : l d ≤ ∑ x ∈ range (n + 1), l x :=
          Finset.single_le_sum hl_nonneg (by simpa [Nat.succ_eq_add_one] using (Finset.mem_range_succ_iff.mpr hle.2.2.2))
        have hld_pos : 0 < l d := by
          dsimp [l]
          simp [habcd]
        exact lt_of_lt_of_le hld_pos hld_le
      exact lt_of_lt_of_le hkc_pos hkc_le
    exact lt_of_lt_of_le hgb_pos hgb_le
  exact lt_of_lt_of_le hfa_pos h_main
