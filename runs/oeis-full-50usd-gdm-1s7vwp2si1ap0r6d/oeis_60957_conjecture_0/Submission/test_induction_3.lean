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
    dsimp [id]
    omega
  rw [padicValNat_prod s id h_ne]
  by_cases hp_mem : p ∈ s
  · have h_eq : s = insert p (s.erase p) := (insert_erase hp_mem).symm
    rw [h_eq]
    rw [sum_insert (by simp)]
    have h_zero : ∑ x ∈ s.erase p, padicValNat p (id x) = 0 := by
      apply sum_eq_zero
      intro x hx
      rw [mem_erase] at hx
      have hx'_mem : x ∈ Icc 1 p := hs hx.2
      have hx' := hx'_mem
      rw [mem_Icc] at hx'
      have h_not_div : ¬ p ∣ x := by
        intro h_div
        have h_eq' := div_p_eq_p_of_mem_Icc p hp x hx'_mem h_div
        exact hx.1 h_eq'
      exact padicValNat.eq_zero_of_not_dvd h_not_div
    rw [h_zero, add_zero]
    dsimp [id]
    rw [padicValNat_self]
  · have h_zero : ∑ x ∈ s, padicValNat p (id x) = 0 := by
      apply sum_eq_zero
      intro x hx
      have hx'_mem : x ∈ Icc 1 p := hs hx
      have hx' := hx'_mem
      rw [mem_Icc] at hx'
      have h_not_div : ¬ p ∣ x := by
        intro h_div
        have h_eq' := div_p_eq_p_of_mem_Icc p hp x hx'_mem h_div
        rw [h_eq'] at hx
        exact hp_mem hx
      exact padicValNat.eq_zero_of_not_dvd h_not_div
    rw [h_zero]
    omega


lemma replacement_step (n p : ℕ) (hp : Nat.Prime p) (s2 : Finset ℕ) (hs2 : s2 ⊆ Icc 1 n)
    (x : ℕ) (hx : x ∈ s2) (h_div : p ∣ x) (hx_p : x / p ∉ s2) :
    ∃ s3, s3 ⊆ Icc 1 n ∧ s3.prod id = s2.prod id / p := by
  have hp_ge2 : p ≥ 2 := hp.two_le
  have h_x_mem : x ∈ Icc 1 n := hs2 hx
  rw [mem_Icc] at h_x_mem
  have h_x_pos : 1 ≤ x := h_x_mem.1
  have h_x_le : x ≤ n := h_x_mem.2
  have h_xp_le : x / p ≤ n := by
    have : x / p ≤ x := Nat.div_le_self x p
    omega
  have h_xp_pos : 1 ≤ x / p := by
    have h_div_eq : x = p * (x / p) := (Nat.mul_div_cancel' h_div).symm
    by_contra h_lt
    have h_zero : x / p = 0 := Nat.lt_one_iff.1 (Nat.lt_of_not_le h_lt)
    have h_x_zero : x = 0 := by
      rw [h_div_eq, h_zero, mul_zero]
    omega
  have h_xp_mem : x / p ∈ Icc 1 n := by
    rw [mem_Icc]
    exact ⟨h_xp_pos, h_xp_le⟩
  let s3 := insert (x / p) (s2.erase x)
  use s3
  constructor
  · rw [insert_subset_iff]
    constructor
    · exact h_xp_mem
    · exact subset_trans (erase_subset x s2) hs2
  · dsimp [s3]
    have h_not_mem : x / p ∉ s2.erase x := by
      rw [mem_erase]
      push_neg
      intro _
      exact hx_p
    rw [prod_insert h_not_mem]
    dsimp [id]
    have h_eq : s2.prod id = x * (s2.erase x).prod id := by
      conv_lhs => rw [← insert_erase hx]
      rw [prod_insert (by simp)]
      rfl
    have h_div_eq : x = p * (x / p) := (Nat.mul_div_cancel' h_div).symm
    rw [h_eq, h_div_eq]
    rw [mul_assoc]
    have hp_ne_zero : p ≠ 0 := by omega
    have h_cancel_lhs : p * (x / p) / p = x / p :=
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp_ne_zero)
    rw [h_cancel_lhs]
    have h_cancel : p * (x / p * (s2.erase (p * (x / p))).prod id) / p = x / p * (s2.erase (p * (x / p))).prod id :=
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp_ne_zero)
    rw [h_cancel]
    rfl


lemma exists_replacement (n p : ℕ) (hp : Nat.Prime p) (s2 : Finset ℕ) (hs2 : s2 ⊆ Icc 1 n)
    (s : Finset ℕ) (hs : s ⊆ Icc 1 n) (a : ℕ) (ha : a ≥ 2) (h_prod : s2.prod id = p^a * s.prod id) :
    ∃ x ∈ s2, p ∣ x ∧ x / p ∉ s2 := by
  have hp_ge2 : p ≥ 2 := hp.two_le
  have h_div_prod : p ∣ s2.prod id := by
    rw [h_prod]
    apply dvd_mul_of_dvd_left
    have : p ∣ p^a := dvd_pow_self p (by omega)
    exact this
  have h_exists_dvd : ∃ x ∈ s2, p ∣ x := by
    rcases ((Nat.Prime.prime hp).dvd_finset_prod_iff id).1 h_div_prod with ⟨x, hx, h_div⟩
    exact ⟨x, hx, h_div⟩
lemma exists_replacement_of_not_closed (n p : ℕ) (hp : Nat.Prime p) (s2 : Finset ℕ) (hs2 : s2 ⊆ Icc 1 n)
    (x : ℕ) (hx : x ∈ s2) (h_div : p ∣ x) (h_not_closed : ¬ (∀ j ≤ padicValNat p x, x / p^j ∈ s2)) :
    ∃ z ∈ s2, p ∣ z ∧ z / p ∉ s2 := by
  have hp_fact : Fact (Nat.Prime p) := ⟨hp⟩
  push_neg at h_not_closed
  rcases h_not_closed with ⟨J, hJ_le, hJ_not⟩
  have h_find_exists : ∃ j, j ≤ padicValNat p x ∧ x / p^j ∉ s2 := ⟨J, hJ_le, hJ_not⟩
  let k := Nat.find h_find_exists
  have h_k_spec := Nat.find_spec h_find_exists
  have h_k_le : k ≤ padicValNat p x := h_k_spec.1
  have h_k_not : x / p^k ∉ s2 := h_k_spec.2
  have h_k_pos : k ≥ 1 := by
    by_contra h_lt
    have : k = 0 := by omega
    rw [this, pow_zero, Nat.div_one] at h_k_not
    exact h_k_not hx
  have h_prev : k - 1 < k := by omega
  have h_prev_spec := Nat.find_min h_find_exists h_prev
  push_neg at h_prev_spec
  have h_prev_le : k - 1 ≤ padicValNat p x := by omega
  have h_prev_mem : x / p^(k - 1) ∈ s2 := h_prev_spec h_prev_le
  let z := x / p^(k - 1)
  use z
  constructor
  · exact h_prev_mem
  · constructor
    · -- we want to show p ∣ z
      have h_div_pow_prev : p^(k - 1) ∣ x := by
        have h_pow_dvd : p^(k - 1) ∣ p^(padicValNat p x) := pow_dvd_pow p (by omega)
        exact dvd_trans h_pow_dvd pow_padicValNat_dvd
      have h_div_pow : p^(k - 1) * p ∣ x := by
        have h_eq : p^(k - 1) * p = p^k := by rw [← pow_succ, Nat.sub_add_cancel h_k_pos]
        rw [h_eq]
        have h_pow_dvd : p^k ∣ p^(padicValNat p x) := pow_dvd_pow p h_k_le
        exact dvd_trans h_pow_dvd pow_padicValNat_dvd
      exact (Nat.dvd_div_iff_mul_dvd h_div_pow_prev).2 h_div_pow
    · -- we want to show z / p ∉ s2
      have h_z_div : z / p = x / p^k := by
        dsimp [z]
        rw [Nat.div_div_eq_div_mul]
        congr 2
        rw [← pow_succ, Nat.sub_add_cancel h_k_pos]
      rwa [h_z_div]


lemma padicValNat_le_of_subset_div (p : ℕ) [hp : Fact (Nat.Prime p)] (s2 s : Finset ℕ) (hs_ne : ∀ x ∈ s, x ≠ 0) (hs2_ne : ∀ x ∈ s2, x ≠ 0) (h_sub : ∀ x ∈ s2, p ∣ x → x ∈ s) :
    padicValNat p (s2.prod id) ≤ padicValNat p (s.prod id) := by
  rw [padicValNat_prod s2 id hs2_ne, padicValNat_prod s id hs_ne]
  have h_zero : ∀ x ∈ s2, x ∉ s → padicValNat p (id x) = 0 := by
    intro x hx_s2 hx_s
    dsimp [id]
    apply padicValNat.eq_zero_of_not_dvd
    intro h_div
    exact hx_s (h_sub x hx_s2 h_div)
  have h_sum1 : ∑ x ∈ s2 ∩ s, padicValNat p (id x) = ∑ x ∈ s2, padicValNat p (id x) := by
    apply sum_subset
    · intro x hx; simp only [mem_inter] at hx; exact hx.1
    · intro x hx_s2 hx_inter
      have hx_not_s : x ∉ s := by
        intro hc
        exact hx_inter (mem_inter.2 ⟨hx_s2, hc⟩)
      exact h_zero x hx_s2 hx_not_s
  have h_sum2 : ∑ x ∈ s2 ∩ s, padicValNat p (id x) ≤ ∑ x ∈ s, padicValNat p (id x) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx; simp only [mem_inter] at hx; exact hx.2
    · intro x _ _
      exact Nat.zero_le _
  omega
