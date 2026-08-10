import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix



def anti_diag_perm (p : ℕ) : Equiv.Perm (Fin p) where
  toFun i := ⟨p - 1 - i.val, by omega⟩
  invFun i := ⟨p - 1 - i.val, by omega⟩
  left_inv i := by
    ext
    dsimp
    omega
  right_inv i := by
    ext
    dsimp
    omega

def prod_swaps (k : ℕ) (p : ℕ) : Equiv.Perm (Fin p) :=
  match k with
  | 0 => 1
  | k + 1 =>
    if h : k < p ∧ p - 1 - k < p then
      prod_swaps k p * Equiv.swap ⟨k, h.1⟩ ⟨p - 1 - k, h.2⟩
    else
      prod_swaps k p

lemma sign_prod_swaps (k p : ℕ) (hk : k ≤ (p - 1) / 2) (hp2 : p ≠ 2) (hp_odd : p % 2 = 1) :
    (Equiv.Perm.sign (prod_swaps k p) : ℤ) = (-1 : ℤ)^k := by
  induction' k with k ih
  · simp [prod_swaps]
  · have hk' : k ≤ (p - 1) / 2 := by omega
    have h_lt : k < p ∧ p - 1 - k < p := by omega
    dsimp [prod_swaps]
    rw [dif_pos h_lt]
    rw [map_mul]
    simp only [Units.val_mul]
    rw [ih hk']
    have h_ne : (⟨k, h_lt.1⟩ : Fin p) ≠ ⟨p - 1 - k, h_lt.2⟩ := by
      intro hc
      have hc' : k = p - 1 - k := by injection hc
      omega
    rw [Equiv.Perm.sign_swap h_ne]
    simp only [Units.val_neg, Units.val_one]
    ring


lemma prod_swaps_apply (k p : ℕ) (hk : k ≤ (p - 1) / 2) (i : Fin p) :
    prod_swaps k p i = if i.val < k then ⟨p - 1 - i.val, by omega⟩
                      else if i.val ≥ p - k then ⟨p - 1 - i.val, by omega⟩
                      else i := by
  induction' k with k ih generalizing i
  · simp [prod_swaps]
  · have hk' : k ≤ (p - 1) / 2 := by omega
    have h_lt : k < p ∧ p - 1 - k < p := by omega
    have ih' (j : Fin p) := ih hk' j
    dsimp [prod_swaps]
    rw [dif_pos h_lt]
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    split_ifs
    · rw [ih' ⟨p - 1 - k, h_lt.2⟩]
      split_ifs <;> ext <;> dsimp <;> omega
    · rw [ih' ⟨k, h_lt.1⟩]
      split_ifs <;> ext <;> dsimp <;> omega
    · rw [ih' i]
      split_ifs <;> ext <;> dsimp <;> omega


lemma anti_diag_perm_eq_prod_swaps (p : ℕ) (hp2 : p ≠ 2) (hp_odd : p % 2 = 1) :
    anti_diag_perm p = prod_swaps ((p - 1) / 2) p := by
  ext i
  have hk0 : (p - 1) / 2 ≤ (p - 1) / 2 := by omega
  rw [prod_swaps_apply ((p - 1) / 2) p hk0 i]
  let k0 := (p - 1) / 2
  have hp_eq : p = 2 * k0 + 1 := by omega
  split_ifs <;> ext <;> dsimp [anti_diag_perm] <;> omega


lemma sign_anti_diag_perm (p : ℕ) (hp2 : p ≠ 2) (hp_odd : p % 2 = 1) :
    (Equiv.Perm.sign (anti_diag_perm p) : ℤ) = (-1 : ℤ)^((p - 1) / 2) := by
  rw [anti_diag_perm_eq_prod_swaps p hp2 hp_odd]
  exact sign_prod_swaps ((p - 1) / 2) p (by omega) hp_odd










lemma sum_eq_card_mul_of_le {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ℕ} {c : ℕ}
    (h : ∀ x ∈ s, f x ≤ c) (hsum : ∑ x ∈ s, f x = s.card * c) : ∀ x ∈ s, f x = c := by
  intro x hx
  by_contra h_lt
  have h_lt : f x < c := lt_of_le_of_ne (h x hx) h_lt
  have h_split : ∑ y ∈ s, f y = f x + ∑ y ∈ s.erase x, f y := (add_sum_erase s f hx).symm
  have h_card_pos : s.card > 0 := card_pos.mpr ⟨x, hx⟩
  have h_le : ∑ y ∈ s.erase x, f y ≤ (s.card - 1) * c := by
    have h_card : (s.erase x).card = s.card - 1 := card_erase_of_mem hx
    have h_le' := Finset.sum_le_card_nsmul (s.erase x) f c (fun y hy ↦ h y (mem_of_mem_erase hy))
    rwa [h_card] at h_le'
  have h_mul : s.card * c = (s.card - 1) * c + c := by
    have h_eq : s.card = (s.card - 1) + 1 := (Nat.sub_add_cancel h_card_pos).symm
    nth_rw 1 [h_eq]
    rw [add_mul, one_mul, add_comm]
  have h_strict : ∑ y ∈ s, f y < s.card * c := by
    rw [h_split, h_mul]
    omega
  omega

lemma sum_val_eq_sum_range (p : ℕ) :
    (∑ i : Fin p, i.val) = ∑ i ∈ range p, i := by
  exact Fin.sum_univ_eq_sum_range (fun i ↦ i) p

lemma sum_val_perm (p : ℕ) (σ : Equiv.Perm (Fin p)) :
    (∑ i : Fin p, (σ i).val) = ∑ i : Fin p, i.val := by
  exact Equiv.sum_comp σ (fun i ↦ i.val)

lemma sum_add_val_perm (p : ℕ) (σ : Equiv.Perm (Fin p)) :
    (∑ i : Fin p, (i.val + (σ i).val)) = p * (p - 1) := by
  rw [sum_add_distrib, sum_val_perm, ← two_mul, sum_val_eq_sum_range, mul_comm, sum_range_id_mul_two]

lemma val_add_perm_eq_pred_of_le (p : ℕ) (σ : Equiv.Perm (Fin p))
    (hle : ∀ i : Fin p, i.val + (σ i).val ≤ p - 1) : ∀ i : Fin p, i.val + (σ i).val = p - 1 := by
  intro i
  have h_univ : i ∈ (Finset.univ : Finset (Fin p)) := Finset.mem_univ i
  refine sum_eq_card_mul_of_le (s := Finset.univ) (f := fun i ↦ i.val + (σ i).val) (c := p - 1) ?_ ?_ i h_univ
  · intro x _
    exact hle x
  · rw [Finset.card_univ, Fintype.card_fin]
    exact sum_add_val_perm p σ

lemma det_collapse (p : ℕ) (M : Matrix (Fin p) (Fin p) (ZMod p))
    (h_zero : ∀ i j : Fin p, i.val + j.val ≥ p → M i j = 0) :
    M.det = (Equiv.Perm.sign (anti_diag_perm p)) • ∏ i : Fin p, M (anti_diag_perm p i) i := by
  rw [Matrix.det_apply]
  apply sum_eq_single (anti_diag_perm p)
  · intro σ _ h_ne
    have h_exists : ∃ i : Fin p, (σ i).val + i.val ≥ p := by
      by_contra hc
      push_neg at hc
      have h_le : ∀ i : Fin p, i.val + (σ i).val ≤ p - 1 := by
        intro i
        have h1 := hc i
        omega
      have h_eq := val_add_perm_eq_pred_of_le p σ h_le
      have h_eq_σ : σ = anti_diag_perm p := by
        ext i
        have h2 := h_eq i
        dsimp [anti_diag_perm]
        omega
      exact h_ne h_eq_σ
    rcases h_exists with ⟨i, hi⟩
    have h_term_zero : M (σ i) i = 0 := h_zero (σ i) i hi
    have h_prod_zero : ∏ j : Fin p, M (σ j) j = 0 := by
      exact prod_eq_zero (mem_univ i) h_term_zero
    rw [h_prod_zero, smul_zero]
  · intro h_not_mem
    exact False.elim (h_not_mem (mem_univ _))









