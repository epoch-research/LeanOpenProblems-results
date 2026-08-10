import FormalConjectures.Util.ProblemImports

open Finset Nat

private def products (n : ℕ) : Finset ℕ :=
  (Icc 1 n).powerset.image (fun s : Finset ℕ => s.prod id)

lemma Icc_eq_insert (n : ℕ) (hn : n ≥ 1) : Icc 1 n = insert n (Icc 1 (n-1)) := by
  ext x
  simp only [mem_Icc, mem_insert]
  omega

lemma n_not_mem_Icc (n : ℕ) : n ∉ Icc 1 (n-1) := by
  simp only [mem_Icc]
  omega

lemma div_p_eq_p_of_mem_Icc (p : ℕ) (hp : Nat.Prime p) (y : ℕ) (hy : y ∈ Icc 1 p) (h_div : p ∣ y) : y = p := by
  have hy_mem := mem_Icc.1 hy
  have h_le : p ≤ y := Nat.le_of_dvd (by omega) h_div
  omega

lemma prod_pow (p : ℕ) (s : Finset ℕ) (g : ℕ → ℕ) : s.prod (fun x => p^(g x)) = p^(∑ x ∈ s, g x) := by
  induction' s using Finset.induction_on with x s hxs ih
  · simp
  · rw [prod_insert hxs, sum_insert hxs, pow_add, ih]

lemma padicValNat_prod {p : ℕ} [hp : Fact (Nat.Prime p)] (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ x ∈ s, f x ≠ 0) :
    padicValNat p (s.prod f) = ∑ x ∈ s, padicValNat p (f x) := by
  induction' s using Finset.induction_on with x s hxs ih
  · simp
  · rw [prod_insert hxs, sum_insert hxs]
    have h_fx : f x ≠ 0 := hf x (mem_insert_self x s)
    have h_prod : s.prod f ≠ 0 := by
      apply prod_ne_zero_iff.2
      intro y hy
      exact hf y (mem_insert_of_mem hy)
    rw [padicValNat.mul h_fx h_prod]
    have h_ih : padicValNat p (s.prod f) = ∑ x ∈ s, padicValNat p (f x) := by
      apply ih
      intro y hy
      exact hf y (mem_insert_of_mem hy)
    rw [h_ih]

lemma padicValNat_products_prime (p : ℕ) (hp : Nat.Prime p) (s : Finset ℕ) (hs : s ⊆ Icc 1 p) :
    padicValNat p (s.prod id) ≤ 1 := by
  have hp_fact : Fact (Nat.Prime p) := ⟨hp⟩
  have h_ne : ∀ x ∈ s, id x ≠ 0 := by
    intro x hx
    have hx' := hs hx
    rw [mem_Icc] at hx'
    omega
  rw [padicValNat_prod s id h_ne]
  by_cases hp_mem : p ∈ s
  · have h_eq : s = insert p (s.erase p) := (insert_erase hp_mem).symm
    rw [h_eq]
    rw [sum_insert (not_mem_erase p s)]
    have h_zero : ∑ x ∈ s.erase p, padicValNat p (id x) = 0 := by
      apply sum_eq_zero
      intro x hx
      rw [mem_erase] at hx
      have hx' := hs hx.2
      rw [mem_Icc] at hx'
      have h_not_div : ¬ p ∣ x := by
        intro h_div
        have h_eq' := div_p_eq_p_of_mem_Icc p hp x hx' h_div
        exact hx.1 h_eq'
      exact padicValNat.eq_zero_of_not_dvd h_not_div
    rw [h_zero, add_zero]
    dsimp
    rw [padicValNat_self]
  · have h_zero : ∑ x ∈ s, padicValNat p (id x) = 0 := by
      apply sum_eq_zero
      intro x hx
      have hx' := hs hx
      rw [mem_Icc] at hx'
      have h_not_div : ¬ p ∣ x := by
        intro h_div
        have h_eq' := div_p_eq_p_of_mem_Icc p hp x hx' h_div
        rw [h_eq'] at hx
        exact hp_mem hx
      exact padicValNat.eq_zero_of_not_dvd h_not_div
    rw [h_zero]
    omega
