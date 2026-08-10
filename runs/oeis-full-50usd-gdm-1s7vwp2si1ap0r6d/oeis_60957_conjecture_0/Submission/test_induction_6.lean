import FormalConjectures.Util.ProblemImports

open Finset Nat

private def products (n : ℕ) : Finset ℕ :=
  (Icc 1 n).powerset.image (fun s : Finset ℕ => s.prod id)

lemma Icc_eq_insert (n : ℕ) (hn : n ≥ 1) : Icc 1 n = insert n (Icc 1 (n-1)) := by
  ext x
  simp only [mem_Icc, mem_insert]
  omega

lemma div_p_eq_p_of_mem_Icc (p : ℕ) (hp : Nat.Prime p) (y : ℕ) (hy : y ∈ Icc 1 p) (h_div : p ∣ y) : y = p := by
  have hy_mem := mem_Icc.1 hy
  have h_le : p ≤ y := Nat.le_of_dvd (by omega) h_div
  omega

lemma coprime_prod_erase (p : ℕ) (hp : Nat.Prime p) (s : Finset ℕ) (hs : s ⊆ Icc 1 p) :
    Nat.Coprime p (s.erase p |>.prod id) := by
  apply Nat.Coprime.prod_right
  intro i hi
  rw [mem_erase] at hi
  have hi_mem : i ∈ Icc 1 p := hs hi.2
  have h_not_div : ¬ p ∣ i := by
    intro h_div
    have h_eq := div_p_eq_p_of_mem_Icc p hp i hi_mem h_div
    exact hi.1 h_eq
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 h_not_div

lemma not_p_sq_dvd_prod (p : ℕ) (hp : Nat.Prime p) (s : Finset ℕ) (hs : s ⊆ Icc 1 p) :
    ¬ p^2 ∣ s.prod id := by
  have h_coprime := coprime_prod_erase p hp s hs
  by_cases hp_mem : p ∈ s
  · have h_eq : s.prod id = p * (s.erase p).prod id := by
      conv_lhs => rw [← insert_erase hp_mem]
      rw [prod_insert (by simp)]
      rfl
    rw [h_eq]
    intro h_div
    -- we want to change p^2 to p * p
    have h_div' : p * p ∣ p * (s.erase p).prod id := by
      rwa [pow_two] at h_div
    have h_div_C : p ∣ (s.erase p).prod id := by
      rwa [mul_dvd_mul_iff_left hp.ne_zero] at h_div'
    have h_not_div := (Nat.Prime.coprime_iff_not_dvd hp).1 h_coprime
    exact h_not_div h_div_C
  · -- p ∉ s, so s.erase p = s
    have h_erase_eq : s.erase p = s := by simp [hp_mem]
    have h_coprime' : Nat.Coprime p (s.prod id) := by
      have h_temp := h_coprime
      rw [h_erase_eq] at h_temp
      exact h_temp
    intro h_div
    -- if p^2 ∣ C, then p ∣ C (since p ∣ p^2)
    have h_div_C : p ∣ s.prod id := by
      have h_p_dvd : p ∣ p^2 := dvd_pow_self p (by decide)
      exact dvd_trans h_p_dvd h_div
    have h_not_div := (Nat.Prime.coprime_iff_not_dvd hp).1 h_coprime'
    exact h_not_div h_div_C

lemma n_not_mem_Icc (n : ℕ) : n ∉ Icc 1 (n-1) := by
  simp only [mem_Icc]
  omega

lemma products_rec (n : ℕ) (hn : n ≥ 1) :
    products n = products (n-1) ∪ (products (n-1)).image (fun x => n * x) := by
  dsimp [products]
  rw [Icc_eq_insert n hn]
  rw [powerset_insert]
  rw [image_union]
  congr 1
  simp only [image_image]
  apply image_congr
  intro s hs
  simp at hs
  have hs_finset : s ⊆ Icc 1 (n-1) := by
    intro x hx
    have hx' : x ∈ Set.Icc 1 (n-1) := hs hx
    rwa [← coe_Icc] at hx'
  have h_not : n ∉ s := fun h => n_not_mem_Icc n (hs_finset h)
  dsimp only [Function.comp_apply]
  rw [prod_insert h_not]
  rfl

theorem oeis_60957_conjecture_0_induction (n : ℕ) :
    ∀ p, Nat.Prime p → p ≤ n →
    ∀ m a, m ∈ products n → (p ^ a * m) ∈ products n →
    ∀ k, 0 < k → k < a → (p ^ k * m) ∈ products n := by
  induction' n with n ih
  · intro p hp hpn m a hm hpa k hk hka
    have hp_ge2 : p ≥ 2 := hp.two_le
    omega
  · intro p hp hpn m a hm hpa k hk hka
    by_cases hp_eq : p = n + 1
    · by_cases hn_zero : n = 0
      · have hp_ge2 : p ≥ 2 := hp.two_le
        omega
      · have hp2 : p^2 ∣ p^a * m := by
          have : p^2 ∣ p^a := pow_dvd_pow p (by omega)
          exact dvd_mul_of_dvd_left this m
        dsimp [products] at hpa
        rw [mem_image] at hpa
        rcases hpa with ⟨s2, hs2, h_prod2⟩
        rw [mem_powerset] at hs2
        have hs2' : s2 ⊆ Icc 1 p := by rwa [← hp_eq] at hs2
        have h_not_div := not_p_sq_dvd_prod p hp s2 hs2'
        rw [h_prod2] at h_not_div
        exact (h_not_div hp2).elim
    · sorry
