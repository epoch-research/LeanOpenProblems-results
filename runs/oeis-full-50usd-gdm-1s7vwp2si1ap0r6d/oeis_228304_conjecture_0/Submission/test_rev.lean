import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

def fin_equiv (n : ℕ) : Fin n ≃ { i : Fin (n + 2) // i ≠ (0 : Fin (n + 2)) ∧ i ≠ (⟨n + 1, by omega⟩ : Fin (n + 2)) } where
  toFun i := ⟨⟨i.val + 1, by omega⟩, by
    constructor
    · intro h1
      have : i.val + 1 = 0 := by injection h1
      omega
    · intro h2
      have : i.val + 1 = n + 1 := by injection h2
      have : i.val = n := by omega
      have := i.is_lt
      omega⟩
  invFun i := ⟨i.val.val - 1, by
    have h_zero : i.val.val ≠ 0 := by
      intro h
      have : i.val = 0 := by ext; exact h
      exact i.property.left this
    have h_last : i.val.val ≠ n + 1 := by
      intro h
      have : i.val = ⟨n + 1, by omega⟩ := by ext; exact h
      exact i.property.right this
    have h_lt : i.val.val < n + 2 := i.val.is_lt
    omega⟩
  left_inv i := by
    ext
    simp
  right_inv i := by
    ext
    have h_zero : i.val.val ≠ 0 := by
      intro h
      have : i.val = 0 := by ext; exact h
      exact i.property.left this
    simp
    omega


theorem revPerm_decomposition (n : ℕ) :
    (Fin.revPerm : Equiv.Perm (Fin (n + 2))) =
    Equiv.swap (0 : Fin (n + 2)) ⟨n + 1, by omega⟩ * Equiv.Perm.extendDomain (Fin.revPerm : Equiv.Perm (Fin n)) (fin_equiv n) := by
  ext i
  by_cases h0 : i = 0
  · rw [h0]
    simp
    have h_not_p : ¬ (0 ≠ (0 : Fin (n + 2)) ∧ (0 : Fin (n + 2)) ≠ ⟨n + 1, by omega⟩) := by simp
    rw [Equiv.Perm.extendDomain_apply_not_subtype (Fin.revPerm : Equiv.Perm (Fin n)) (fin_equiv n) h_not_p]
    simp
  · by_cases h_last : i = ⟨n + 1, by omega⟩
    · rw [h_last]
      simp
      have h_not_p : ¬ (⟨n + 1, by omega⟩ ≠ (0 : Fin (n + 2)) ∧ ⟨n + 1, by omega⟩ ≠ (⟨n + 1, by omega⟩ : Fin (n + 2))) := by simp
      rw [Equiv.Perm.extendDomain_apply_not_subtype (Fin.revPerm : Equiv.Perm (Fin n)) (fin_equiv n) h_not_p]
      simp
    · have h_prop : i ≠ 0 ∧ i ≠ ⟨n + 1, by omega⟩ := ⟨h0, h_last⟩
      set x : { i : Fin (n + 2) // i ≠ 0 ∧ i ≠ ⟨n + 1, by omega⟩ } := ⟨i, h_prop⟩
      have h_eq : i = x.val := rfl
      rw [h_eq]
      rw [Equiv.Perm.mul_apply]
      rw [Equiv.Perm.extendDomain_apply_subtype (Fin.revPerm : Equiv.Perm (Fin n)) (fin_equiv n) h_prop]
      simp
      have h_symm : ((fin_equiv n).symm x).val = i.val - 1 := rfl
      have h_rev : ((fin_equiv n).symm x).rev.val = n - i.val := by
        have : ((fin_equiv n).symm x).rev.val = n - (((fin_equiv n).symm x).val + 1) := rfl
        have h_left : i.val ≠ 0 := by
          intro h
          have : i = 0 := by ext; exact h
          exact h_prop.left this
        have h_right : i.val ≠ n + 1 := by
          intro h
          have : i = ⟨n + 1, by omega⟩ := by ext; exact h
          exact h_prop.right this
        omega
      have h_fe : (fin_equiv n ((fin_equiv n).symm x).rev).val.val = n - i.val + 1 := by
        change ((fin_equiv n).symm x).rev.val + 1 = n - i.val + 1
        rw [h_rev]
      have h_swap : Equiv.swap (0 : Fin (n + 2)) ⟨n + 1, by omega⟩ (fin_equiv n ((fin_equiv n).symm x).rev) = (fin_equiv n ((fin_equiv n).symm x).rev) := by
        rw [Equiv.swap_apply_of_ne_of_ne]
        · intro h
          have : (fin_equiv n ((fin_equiv n).symm x).rev).val.val = 0 := by rw [h]; rfl
          omega
        · intro h
          have : (fin_equiv n ((fin_equiv n).symm x).rev).val.val = n + 1 := by rw [h]
          omega
      rw [h_swap]
      rw [h_fe]
      omega

