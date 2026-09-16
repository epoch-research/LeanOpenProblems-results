import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  let L := n.choose 2 + 1
  let R := (n + 1).choose 2
  let is_composite (k : ℕ) : Prop := 1 < k ∧ ¬ k.Prime
  (Icc L R).filter is_composite |>.prod id

def M_val (p : ℕ) : ℕ := (p - 1) * (p - 3) / 2 * p + 1

lemma M_val_ge (p : ℕ) (hp : 5 ≤ p) : p ≤ M_val p := by
  dsimp [M_val]
  have H : 2 ≤ (p - 1) * (p - 3) := by
    have : 4 ≤ p - 1 := by omega
    have : 2 ≤ p - 3 := by omega
    nlinarith
  have h_div : 1 ≤ (p - 1) * (p - 3) / 2 := by
    rw [Nat.le_div_iff_mul_le (by decide)]
    exact H
  nlinarith

lemma M_val_mod (p : ℕ) : p ∣ M_val p - 1 := by
  dsimp [M_val]
  exact dvd_mul_left p ((p - 1) * (p - 3) / 2)

lemma hL_ineq (p M : ℕ) (hp : 5 ≤ p) (hM : p ≤ M) :
  p * M - p * p + 2 * p + 2 ≤ p * (M - p + 3) := by
  have H : ((p * M - p * p + 2 * p + 2 : ℕ) : ℤ) ≤ ((p * (M - p + 3) : ℕ) : ℤ) := by
    have h_sub : ((M - p + 3 : ℕ) : ℤ) = (M : ℤ) - p + 3 := by
      rw [Nat.cast_add, Nat.cast_sub hM]
      rfl
    have hp1 : p * p ≤ p * M := Nat.mul_le_mul_left p hM
    have H2 : ((p * M - p * p + 2 * p + 2 : ℕ) : ℤ) = (p : ℤ) * M - (p : ℤ) * p + 2 * p + 2 := by
      push_cast [Nat.cast_sub hp1]
      ring
    rw [H2]
    have : ((p * (M - p + 3) : ℕ) : ℤ) = (p : ℤ) * ((M - p + 3 : ℕ) : ℤ) := by push_cast; rfl
    rw [this, h_sub]
    nlinarith
  exact Nat.cast_le.mp H

lemma I1_subset (p : ℕ) (hp : 5 ≤ p) (M : ℕ) (hM : p ≤ M)
  (hL : p * M - p * p + 2 * p + 2 ≤ p * (M - p + 3)) :
  let n := p * (p - 2)
  let L1 := p * M - n + 2
  let R1 := p * M
  let S1 := (Icc L1 R1).filter (fun k => 1 < k ∧ ¬ k.Prime)
  (Icc (M - p + 3) M).image (fun x => p * x) ⊆ S1 := by
  intro n L1 R1 S1 y
  dsimp [S1]
  simp only [mem_image, mem_filter, mem_Icc]
  rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · dsimp [L1, n]
    have hp1 : p * (p - 2) ≤ p * M := by
      have : p - 2 ≤ M := by omega
      exact Nat.mul_le_mul_left p this
    have H1 : ((p * M - p * (p - 2) + 2 : ℕ) : ℤ) ≤ ((p * x : ℕ) : ℤ) := by
      have H2 : ((p * M - p * (p - 2) + 2 : ℕ) : ℤ) = (p : ℤ) * M - (p : ℤ) * p + 2 * p + 2 := by
        have hp_2 : (((p - 2 : ℕ) : ℤ)) = (p : ℤ) - 2 := by omega
        push_cast [Nat.cast_sub hp1, hp_2]
        ring
      have hx1_z : ((M - p + 3 : ℕ) : ℤ) ≤ (x : ℤ) := by exact_mod_cast hx1
      have hz : ((M - p + 3 : ℕ) : ℤ) = (M : ℤ) - p + 3 := by
        rw [Nat.cast_add, Nat.cast_sub hM]
        rfl
      rw [hz] at hx1_z
      have : (p * x : ℕ) = (p : ℤ) * (x : ℤ) := by push_cast; rfl
      rw [this, H2]
      have hl_z : (p : ℤ) * M - (p : ℤ) * p + 2 * p + 2 ≤ (p : ℤ) * ((M - p + 3 : ℕ) : ℤ) := by
        have hp2 : p * p ≤ p * M := Nat.mul_le_mul_left p hM
        have : ((p * M - p * p + 2 * p + 2 : ℕ) : ℤ) ≤ ((p * (M - p + 3) : ℕ) : ℤ) := by exact_mod_cast hL
        have H3 : ((p * M - p * p + 2 * p + 2 : ℕ) : ℤ) = (p : ℤ) * M - (p : ℤ) * p + 2 * p + 2 := by
          push_cast [Nat.cast_sub hp2]
          ring
        have H4 : ((p * (M - p + 3) : ℕ) : ℤ) = (p : ℤ) * ((M - p + 3 : ℕ) : ℤ) := by push_cast; rfl
        rw [H3, H4] at this
        exact this
      nlinarith
    exact Nat.cast_le.mp H1
  · exact Nat.mul_le_mul_left p hx2
  · have : p * 1 < p * x := by
      apply Nat.mul_lt_mul_of_pos_left
      · have : 3 ≤ M - p + 3 := by omega
        omega
      · omega
    omega
  · intro h_prime
    have hdvd : p ∣ p * x := dvd_mul_right p x
    have hx_gt1 : 1 < x := by
      have : 3 ≤ M - p + 3 := by omega
      omega
    have hp_gt1 : 1 < p := by omega
    have := h_prime.eq_one_or_self_of_dvd p hdvd
    rcases this with h1 | h2
    · omega
    · have : x = 1 := by nlinarith
      omega

lemma I2_subset (p : ℕ) (hp : 5 ≤ p) (M : ℕ) (hM : p ≤ M) :
  let n := p * (p - 2)
  let L2 := p * M + 1
  let R2 := p * M + n
  let S2 := (Icc L2 R2).filter (fun k => 1 < k ∧ ¬ k.Prime)
  (Icc (M + 1) (M + p - 2)).image (fun x => p * x) ⊆ S2 := by
  intro n L2 R2 S2 y
  dsimp [S2]
  simp only [mem_image, mem_filter, mem_Icc]
  rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · dsimp [L2]
    nlinarith
  · dsimp [R2, n]
    have hp2 : 2 ≤ p := by omega
    have H : ((p * x : ℕ) : ℤ) ≤ ((p * M + p * (p - 2) : ℕ) : ℤ) := by
      have hx2_z : (x : ℤ) ≤ (M : ℤ) + (p : ℤ) - 2 := by
        have : (M + p - 2 : ℤ) = (M : ℤ) + (p : ℤ) - 2 := by omega
        have H_le : (x : ℤ) ≤ ((M + p - 2 : ℕ) : ℤ) := by exact_mod_cast hx2
        omega
      have hz : ((p * M + p * (p - 2) : ℕ) : ℤ) = (p : ℤ) * M + (p : ℤ) * (p - 2 : ℕ) := by
        push_cast
        rfl
      have hp_2 : (((p - 2 : ℕ) : ℤ)) = (p : ℤ) - 2 := by omega
      have : (p : ℤ) * x ≤ (p : ℤ) * (M + p - 2 : ℤ) := by nlinarith
      rw [hz]
      have : (p : ℤ) * (M + p - 2 : ℤ) = (p : ℤ) * M + (p : ℤ) * (p - 2 : ℤ) := by ring
      have h1 : (p : ℤ) * x = ((p * x : ℕ) : ℤ) := by push_cast; rfl
      rw [← h1]
      have : (p : ℤ) * M + (p : ℤ) * (p - 2 : ℕ) = (p : ℤ) * M + (p : ℤ) * (p - 2 : ℤ) := by
        rw [hp_2]
      rw [this]
      nlinarith
    exact Nat.cast_le.mp H
  · have hx_gt1 : 1 < x := by omega
    nlinarith
  · intro h_prime
    have hdvd : p ∣ p * x := dvd_mul_right p x
    have hx_gt1 : 1 < x := by omega
    have hp_gt1 : 1 < p := by omega
    have := h_prime.eq_one_or_self_of_dvd p hdvd
    rcases this with h1 | h2
    · omega
    · have : x = 1 := by nlinarith
      omega

lemma padicValNat_add_of_not_dvd (p a b : ℕ) [Fact p.Prime] (h : p ∣ a) (h2 : ¬ p ∣ b) :
  padicValNat p (a + b) = 0 := by
  have : ¬ p ∣ a + b := by
    intro hdvd
    have : p ∣ (a + b) - a := Nat.dvd_sub hdvd h
    have h_eq : (a + b) - a = b := by omega
    rw [h_eq] at this
    exact h2 this
  exact padicValNat.eq_zero_of_not_dvd this

lemma padicValNat_pM_add_k (p M k : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hk1 : 1 ≤ k) (hk2 : k ≤ p * (p - 2))
  (hM : p ∣ M - 1) (hM_ge : 1 ≤ M) : padicValNat p (p * M + k) = if p ∣ k then 1 else 0 := by
  split_ifs with h
  · obtain ⟨j, hj⟩ := h
    have hj1 : 1 ≤ j := by
      rcases j with _ | j
      · omega
      · omega
    have hj2 : j ≤ p - 2 := by
      have : p * j ≤ p * (p - 2) := by omega
      exact Nat.le_of_mul_le_mul_left this (by omega)
    have : p * M + k = p * (M + j) := by
      rw [hj]
      ring
    rw [this]
    have h_ne : M + j ≠ 0 := by
      have : 1 ≤ M + j := by omega
      omega
    have hp_ne : p ≠ 0 := by omega
    rw [padicValNat.mul hp_ne h_ne]
    have hp_prime : p.Prime := Fact.out
    have : padicValNat p p = 1 := padicValNat.self hp_prime.one_lt
    rw [this]
    have h_not_dvd : ¬ p ∣ M + j := by
      intro hdvd
      have hM_mod : p ∣ M - 1 := hM
      have H1 : 1 ≤ M := by omega
      have H2 : p ∣ (M - 1) + (j + 1) := by
        have H3 : (M - 1) + (j + 1) = M + j := by omega
        rw [H3]
        exact hdvd
      have H4 : p ∣ ((M - 1) + (j + 1)) - (M - 1) := Nat.dvd_sub H2 hM_mod
      have H5 : ((M - 1) + (j + 1)) - (M - 1) = j + 1 := by omega
      rw [H5] at H4
      have H6 : j + 1 < p := by omega
      have H7 : j + 1 = 0 := Nat.eq_zero_of_dvd_of_lt H4 H6
      omega
    have : padicValNat p (M + j) = 0 := padicValNat.eq_zero_of_not_dvd h_not_dvd
    omega
  · apply padicValNat_add_of_not_dvd
    · exact dvd_mul_right p M
    · exact h

lemma sum_padicValNat_I2 (p M : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
  ((Icc 1 (p * (p - 2))).filter (fun k => p ∣ k)).card = p - 2 := by
  have : ((Icc 1 (p - 2)).image (fun x => p * x)) = (Icc 1 (p * (p - 2))).filter (fun k => p ∣ k) := by
    ext x
    simp only [mem_image, mem_filter, mem_Icc]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right p y⟩
      · have : 1 ≤ p := by omega
        nlinarith
      · exact Nat.mul_le_mul_left p hy2
    · rintro ⟨⟨hx1, hx2⟩, hdvd⟩
      obtain ⟨y, rfl⟩ := hdvd
      refine ⟨y, ⟨?_, ?_⟩, rfl⟩
      · rcases y with _ | y
        · omega
        · omega
      · exact Nat.le_of_mul_le_mul_left hx2 (by omega)
  rw [← this]
  have H : ((Icc 1 (p - 2)).image (fun x => p * x)).card = (Icc 1 (p - 2)).card := by
    apply Finset.card_image_of_injective
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by omega) hab
  rw [H, Nat.card_Icc]
  omega

lemma sum_padicValNat_I2_full (p M : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hM : p ∣ M - 1) (hM_ge : 1 ≤ M) :
  ∑ k ∈ Icc 1 (p * (p - 2)), padicValNat p (p * M + k) = p - 2 := by
  have H : ∑ k ∈ Icc 1 (p * (p - 2)), padicValNat p (p * M + k) =
           ∑ k ∈ Icc 1 (p * (p - 2)), (if p ∣ k then 1 else 0 : ℕ) := by
    apply sum_congr rfl
    intro k hk
    rw [mem_Icc] at hk
    exact padicValNat_pM_add_k p M k hp hk.1 hk.2 hM hM_ge
  rw [H]
  have H2 : ∑ k ∈ Icc 1 (p * (p - 2)), (if p ∣ k then 1 else 0 : ℕ) =
            ( (Icc 1 (p * (p - 2))).filter (fun k => p ∣ k) ).card := by
    rw [sum_ite]
    simp
  rw [H2]
  exact sum_padicValNat_I2 p M hp

lemma padicValNat_prod_of_coprime (p : ℕ) [Fact p.Prime] {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℕ) (hf : ∀ x ∈ s, f x ≠ 0) :
  padicValNat p (∏ x ∈ s, f x) = ∑ x ∈ s, padicValNat p (f x) := by
  induction' s using Finset.induction_on with a s has ih
  · simp
  · rw [prod_insert has, sum_insert has, padicValNat.mul]
    · rw [ih]
      intros x hx
      exact hf x (mem_insert_of_mem hx)
    · exact hf a (mem_insert_self a s)
    · exact prod_ne_zero_iff.mpr (fun x hx => hf x (mem_insert_of_mem hx))

lemma sum_subset_le (s t : Finset ℕ) (f : ℕ → ℕ) (h : s ⊆ t) :
  ∑ x ∈ s, f x ≤ ∑ x ∈ t, f x := by
  have : ∑ x ∈ t, f x = ∑ x ∈ s, f x + ∑ x ∈ t \ s, f x := by
    rw [← sum_union (disjoint_sdiff)]
    have : s ∪ t \ s = t := by
      ext x
      simp only [mem_union, mem_sdiff]
      tauto
    rw [this]
  rw [this]
  omega

lemma sum_image_px (p M : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hM : p ∣ M - 1) (hM_ge : p ≤ M) :
  p - 1 ≤ ∑ x ∈ Icc (M - p + 3) M, padicValNat p (p * x) := by
  have H1 : ∑ x ∈ Icc (M - p + 3) M, padicValNat p (p * x) =
            ∑ x ∈ Icc (M - p + 3) M, (1 + padicValNat p x) := by
    apply sum_congr rfl
    intro x hx
    have hp_ne : p ≠ 0 := by omega
    have hx_ne : x ≠ 0 := by
      rw [mem_Icc] at hx
      omega
    rw [padicValNat.mul hp_ne hx_ne]
    have hp_prime : p.Prime := Fact.out
    have : padicValNat p p = 1 := padicValNat.self hp_prime.one_lt
    rw [this]
  rw [H1]
  have H2 : ∑ x ∈ Icc (M - p + 3) M, (1 + padicValNat p x) =
            (Icc (M - p + 3) M).card + ∑ x ∈ Icc (M - p + 3) M, padicValNat p x := by
    rw [sum_add_distrib, sum_const]
    simp
  rw [H2, Nat.card_Icc]
  have H3 : M + 1 - (M - p + 3) = p - 2 := by omega
  rw [H3]
  have H4 : 1 ≤ padicValNat p (M - 1) := by
    have h_ne : M - 1 ≠ 0 := by omega
    exact one_le_padicValNat_of_dvd h_ne hM
  have H5 : M - 1 ∈ Icc (M - p + 3) M := by
    rw [mem_Icc]
    constructor <;> omega
  have H6 : 1 ≤ ∑ x ∈ Icc (M - p + 3) M, padicValNat p x := by
    have : padicValNat p (M - 1) ≤ ∑ x ∈ Icc (M - p + 3) M, padicValNat p x :=
      single_le_sum (fun _ _ => zero_le _) H5
    omega
  omega

lemma not_finite_of_unbounded (S : Set ℕ) (h : ∀ B, ∃ x ∈ S, B < x) : ¬ Set.Finite S := by
  intro hf
  have : BddAbove S := Set.Finite.bddAbove hf
  obtain ⟨B, hB⟩ := this
  obtain ⟨x, hx, hxB⟩ := h B
  have := hB hx
  omega

lemma n_choose_two_div (n : ℕ) (hn : 1 ≤ n) : (2 : ℤ) * ((n * (n - 1) / 2 : ℕ) : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  have H1 := Even.two_dvd (Nat.even_mul_pred_self n)
  have H2 : 2 * (n * (n - 1) / 2) = n * (n - 1) := Nat.mul_div_cancel' H1
  have H3 : (2 : ℤ) * ((n * (n - 1) / 2 : ℕ) : ℤ) = ((n * (n - 1) : ℕ) : ℤ) := by exact_mod_cast H2
  have H4 : ((n * (n - 1) : ℕ) : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hn]
    rfl
  rw [H4] at H3
  exact H3

lemma hL1_val_eq (p M : ℕ) (hp : 5 ≤ p) (hM_ge : p ≤ M) :
  p * (p - 2) * (p * (p - 2) - 1) / 2 = p * M ↔
  p * (p * p - 4 * p + 3) + 2 = 2 * M := by
  have hp2 : 2 ≤ p := by omega
  have H1 : (2 : ℤ) * ((p * (p - 2) * (p * (p - 2) - 1) / 2 : ℕ) : ℤ) = ((p * (p - 2) : ℕ) : ℤ) * (((p * (p - 2) : ℕ) : ℤ) - 1) := by
    have hn : 1 ≤ p * (p - 2) := by
      have : 3 ≤ p - 2 := by omega
      nlinarith
    exact n_choose_two_div (p * (p - 2)) hn
  have H2 : ((p * (p - 2) : ℕ) : ℤ) = (p : ℤ) * ((p : ℤ) - 2) := by
    rw [Nat.cast_mul, Nat.cast_sub hp2]
    rfl
  have H3 : ((p * (p - 2) : ℕ) : ℤ) * (((p * (p - 2) : ℕ) : ℤ) - 1) = (p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) * (p : ℤ) + 2 * (p : ℤ) := by
    rw [H2]
    ring
  rw [H3] at H1
  constructor
  · intro h
    have : ((p * M : ℕ) : ℤ) = ((p * (p - 2) * (p * (p - 2) - 1) / 2 : ℕ) : ℤ) := by exact_mod_cast h.symm
    have h1 : (2 : ℤ) * ((p * M : ℕ) : ℤ) = (2 : ℤ) * (p : ℤ) * (M : ℤ) := by push_cast; ring
    have h2 : (2 : ℤ) * (p : ℤ) * (M : ℤ) = (p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) * (p : ℤ) + 2 * (p : ℤ) := by
      nlinarith
    have hp_pos : (p : ℤ) ≠ 0 := by omega
    have : (p : ℤ) * (2 * (M : ℤ)) = (p : ℤ) * ((p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) + 2) := by
      calc (p : ℤ) * (2 * (M : ℤ)) = (2 : ℤ) * (p : ℤ) * (M : ℤ) := by ring
      _ = (p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) * (p : ℤ) + 2 * (p : ℤ) := h2
      _ = (p : ℤ) * ((p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) + 2) := by ring
    have h_final : 2 * (M : ℤ) = (p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) + 2 := by
      exact mul_left_cancel₀ hp_pos this
    have h_cast : ((p * (p * p - 4 * p + 3) + 2 : ℕ) : ℤ) = (p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) + 2 := by
      have hp4 : 4 * p ≤ p * p := by
        have : 4 * 5 ≤ p * p := by nlinarith
        nlinarith
      push_cast [Nat.cast_sub hp4]
      ring
    rw [← h_cast] at h_final
    have h_final2 : ((p * (p * p - 4 * p + 3) + 2 : ℕ) : ℤ) = ((2 * M : ℕ) : ℤ) := by
      push_cast
      exact h_final.symm
    exact_mod_cast h_final2
  · intro h
    have h_cast : ((p * (p * p - 4 * p + 3) + 2 : ℕ) : ℤ) = (p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) + 2 := by
      have hp4 : 4 * p ≤ p * p := by
        have : 4 * 5 ≤ p * p := by nlinarith
        nlinarith
      push_cast [Nat.cast_sub hp4]
      ring
    have h_final : (p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) + 2 = 2 * (M : ℤ) := by
      rw [← h_cast]
      exact_mod_cast h
    have : (2 : ℤ) * ((p * M : ℕ) : ℤ) = (2 : ℤ) * ((p * (p - 2) * (p * (p - 2) - 1) / 2 : ℕ) : ℤ) := by
      calc (2 : ℤ) * ((p * M : ℕ) : ℤ) = (p : ℤ) * (2 * (M : ℤ)) := by push_cast; ring
      _ = (p : ℤ) * ((p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) + 2) := by rw [← h_final]
      _ = (p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) * (p : ℤ) + 2 * (p : ℤ) := by ring
      _ = (2 : ℤ) * ((p * (p - 2) * (p * (p - 2) - 1) / 2 : ℕ) : ℤ) := H1.symm
    have : ((p * M : ℕ) : ℤ) = ((p * (p - 2) * (p * (p - 2) - 1) / 2 : ℕ) : ℤ) := by
      have h2 : (2 : ℤ) ≠ 0 := by decide
      exact mul_left_cancel₀ h2 this
    exact_mod_cast this.symm

lemma H_M_val_eq (p : ℕ) (hp : 5 ≤ p) (hp_prime : p.Prime) :
  let M := M_val p
  p * (p - 2) * (p * (p - 2) - 1) / 2 = p * M := by
  intro M
  have hM_ge : p ≤ M := by
    dsimp [M, M_val]
    have H : 2 ≤ (p - 1) * (p - 3) := by
      have : 4 ≤ p - 1 := by omega
      have : 2 ≤ p - 3 := by omega
      nlinarith
    have h_div : 1 ≤ (p - 1) * (p - 3) / 2 := by
      rw [Nat.le_div_iff_mul_le (by decide)]
      exact H
    nlinarith
  rw [hL1_val_eq p M hp hM_ge]
  dsimp [M, M_val]
  have H : p * (p * p - 4 * p + 3) + 2 = 2 * ((p - 1) * (p - 3) / 2 * p + 1) := by
    have hp_odd : Odd p := hp_prime.odd_of_ne_two (by omega)
    have H1 : 2 ∣ (p - 1) := by
      obtain ⟨k, hk⟩ := hp_odd
      use k
      omega
    have H1_mul : 2 ∣ (p - 1) * (p - 3) := dvd_mul_of_dvd_left H1 (p - 3)
    have H2 : 2 * ((p - 1) * (p - 3) / 2) = (p - 1) * (p - 3) := Nat.mul_div_cancel' H1_mul
    have H3 : 2 * ((p - 1) * (p - 3) / 2 * p + 1) = (p - 1) * (p - 3) * p + 2 := by
      calc 2 * ((p - 1) * (p - 3) / 2 * p + 1) = 2 * ((p - 1) * (p - 3) / 2 * p) + 2 * 1 := by ring
      _ = 2 * ((p - 1) * (p - 3) / 2) * p + 2 := by ring
      _ = (p - 1) * (p - 3) * p + 2 := by rw [H2]
    rw [H3]
    have H_cast : ((p * (p * p - 4 * p + 3) + 2 : ℕ) : ℤ) = (((p - 1) * (p - 3) * p + 2 : ℕ) : ℤ) := by
      have hp4 : 4 * p ≤ p * p := by
        have : 4 * 5 ≤ p * p := by nlinarith
        nlinarith
      have hp1 : 1 ≤ p := by omega
      have hp3 : 3 ≤ p := by omega
      push_cast [Nat.cast_sub hp4, Nat.cast_sub hp1, Nat.cast_sub hp3]
      ring
    exact_mod_cast H_cast
  exact H

lemma n_le_choose_two (n : ℕ) (hn : 3 ≤ n) : n ≤ n * (n - 1) / 2 := by
  have H : n * 2 ≤ n * (n - 1) := by
    have : 2 ≤ n - 1 := by omega
    nlinarith
  have H2 : (n * 2) / 2 ≤ (n * (n - 1)) / 2 := Nat.div_le_div_right H
  have H3 : (n * 2) / 2 = n := Nat.mul_div_cancel n (by decide)
  rw [H3] at H2
  exact H2

lemma sum_Icc_shift (p M n : ℕ) (f : ℕ → ℕ) :
  ∑ y ∈ Icc (p * M + 1) (p * M + n), f y = ∑ k ∈ Icc 1 n, f (p * M + k) := by
  have : Icc (p * M + 1) (p * M + n) = (Icc 1 n).image (fun k => p * M + k) := by
    ext x
    simp only [mem_image, mem_Icc]
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨x - p * M, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      omega
  rw [this, sum_image]
  intro a _ b _ hab
  dsimp at hab
  omega

theorem oeis_93456_conjecture_0 :
  Set.Finite {n : ℕ | n > 1 ∧ ¬ (a (n - 1) ∣ a n)} :=
by sorry


lemma padicValNat_le_padicValNat_of_dvd (p x y : ℕ) (hp : p.Prime) (hx : x ≠ 0) (hy : y ≠ 0) (hdvd : x ∣ y) : padicValNat p x ≤ padicValNat p y := by
  obtain ⟨c, hc⟩ := hdvd
  have hc_nz : c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc
    exact hy hc
  rw [hc]
  have fact_p : Fact p.Prime := ⟨hp⟩
  rw [padicValNat.mul hx hc_nz]
  omega

theorem oeis_93456_conjecture_0.disproof : ¬ (Set.Finite {n : ℕ | n > 1 ∧ ¬ (a (n - 1) ∣ a n)}) := by
  apply not_finite_of_unbounded
  intro B
  obtain ⟨p, hp_gt, hp_prime⟩ := Nat.exists_infinite_primes (max (B + 1) 5)
  have hp : 5 ≤ p := by omega
  have hB : B < p := by omega
  have fact_p : Fact p.Prime := ⟨hp_prime⟩
  
  let M := M_val p
  let n := p * (p - 2)
  use n
  
  have Hn_gt1 : 1 < n := by
    have H1 : 3 ≤ p - 2 := by omega
    have H2 : 15 ≤ p * (p - 2) := Nat.mul_le_mul hp H1
    omega
  have Hn_gtB : B < n := by
    have H1 : 3 ≤ p - 2 := by omega
    have H2 : p * 1 ≤ p * (p - 2) := Nat.mul_le_mul_left p (by omega)
    have H3 : p ≤ p * (p - 2) := by omega
    omega

  have hM_ge : p ≤ M := M_val_ge p hp
  have hM_mod : p ∣ M - 1 := M_val_mod p

  have hL1_val_eq : n * (n - 1) / 2 = p * M := by exact H_M_val_eq p hp hp_prime

  have h_a_n : a n = ∏ y ∈ (Icc (p * M + 1) (p * M + n)).filter (fun k => 1 < k ∧ ¬ k.Prime), y := by
    dsimp [a]
    have h_L2 : n.choose 2 + 1 = p * M + 1 := by
      rw [Nat.choose_two_right]
      rw [hL1_val_eq]
    have h_R2 : (n + 1).choose 2 = p * M + n := by
      have H_choose : (n + 1).choose 2 = (n + 1) * n / 2 := by
        have : n + 1 - 1 = n := by omega
        rw [Nat.choose_two_right, this]
      have H_z : (((n + 1) * n / 2 : ℕ) : ℤ) = (p * M + n : ℤ) := by
        have H_n : (((n + 1) * n / 2 : ℕ) : ℤ) = ((n * (n - 1) / 2 : ℕ) : ℤ) + n := by
          have h1 : (2:ℤ) * (((n+1)*n / 2 : ℕ):ℤ) = (n+1:ℤ)*n := by
            have H_div := n_choose_two_div (n+1) (by omega)
            have H_sub : (((n + 1 : ℕ) : ℤ) - 1) = (n : ℤ) := by omega
            rw [H_sub] at H_div
            exact H_div
          have h2 : (2:ℤ) * ((n * (n-1) / 2 : ℕ):ℤ) = (n:ℤ)*((n:ℤ)-1) := by
            have := n_choose_two_div n (by omega)
            exact this
          have H3 : (2:ℤ) * (((n + 1) * n / 2 : ℕ) : ℤ) = (2:ℤ) * (((n * (n - 1) / 2 : ℕ) : ℤ) + n) := by
            calc (2:ℤ) * (((n + 1) * n / 2 : ℕ) : ℤ) = (n+1:ℤ)*n := h1
            _ = (n:ℤ)*((n:ℤ)-1) + 2*(n:ℤ) := by ring
            _ = (2:ℤ) * ((n * (n-1) / 2 : ℕ):ℤ) + 2*(n:ℤ) := by rw [h2]
            _ = (2:ℤ) * (((n * (n - 1) / 2 : ℕ) : ℤ) + n) := by ring
          have h_two : (2:ℤ) ≠ 0 := by decide
          exact mul_left_cancel₀ h_two H3
        have H_M : ((n * (n - 1) / 2 : ℕ) : ℤ) = p * M := by exact_mod_cast hL1_val_eq
        rw [H_M] at H_n
        exact H_n
      rw [H_choose]
      exact_mod_cast H_z
    have : Icc ((n.choose 2) + 1) ((n + 1).choose 2) = Icc (p * M + 1) (p * M + n) := by
      rw [h_L2, h_R2]
    rw [this]
    rfl

  have h_a_n_minus_1 : a (n - 1) = ∏ y ∈ (Icc (p * M - n + 2) (p * M)).filter (fun k => 1 < k ∧ ¬ k.Prime), y := by
    dsimp [a]
    have h_L1_val : (n - 1).choose 2 + 1 = p * M - n + 2 := by
      have H_choose : (n - 1).choose 2 = (n - 1) * (n - 2) / 2 := Nat.choose_two_right (n - 1)
      have H_z : ((((n - 1) * (n - 2) / 2 : ℕ) : ℤ)) = (p * M : ℤ) - n + 1 := by
        have H1 : (2:ℤ) * (((n - 1) * (n - 2) / 2 : ℕ) : ℤ) = ((n - 1 : ℕ) : ℤ) * (((n - 1 : ℕ) : ℤ) - 1) := by
          have := n_choose_two_div (n - 1) (by omega)
          exact this
        have H2 : (2:ℤ) * (p * M : ℤ) = (n:ℤ)*(n-1) := by
          have H_M : ((p * M : ℕ) : ℤ) = ((n * (n - 1) / 2 : ℕ) : ℤ) := by exact_mod_cast hL1_val_eq.symm
          have H_n : (2:ℤ) * ((n * (n - 1) / 2 : ℕ) : ℤ) = (n:ℤ)*(n-1) := by
            have := n_choose_two_div n (by omega)
            exact this
          have H_PM_cast : (p * M : ℤ) = ((p * M : ℕ) : ℤ) := by push_cast; rfl
          rw [H_PM_cast, H_M, H_n]
        have hz1 : ((n-1:ℕ):ℤ) = n - 1 := by omega
        have hz2 : ((n-2:ℕ):ℤ) = n - 2 := by omega
        have H3 : (2:ℤ) * (((n - 1) * (n - 2) / 2 : ℕ) : ℤ) = (2:ℤ) * ((p * M : ℤ) - n + 1) := by
          calc (2:ℤ) * (((n - 1) * (n - 2) / 2 : ℕ) : ℤ) = ((n - 1 : ℕ) : ℤ) * (((n - 1 : ℕ) : ℤ) - 1) := H1
          _ = (n - 1 : ℤ) * (n - 2 : ℤ) := by rw [hz1]; ring
          _ = (n:ℤ)*(n-1) - 2*(n:ℤ) + 2 := by ring
          _ = (2:ℤ) * (p * M : ℤ) - 2*(n:ℤ) + 2 := by rw [← H2]
          _ = (2:ℤ) * ((p * M : ℤ) - n + 1) := by ring
        have h_two : (2:ℤ) ≠ 0 := by decide
        exact mul_left_cancel₀ h_two H3
      have hz2 : (((n - 1) * (n - 2) / 2 + 1 : ℕ) : ℤ) = ((p * M - n + 2 : ℕ) : ℤ) := by
        have hn_le : n ≤ p * M := by
          have hn_3 : 3 ≤ n := by
            have H1 : 3 ≤ p - 2 := by omega
            have H2 : 15 ≤ p * (p - 2) := Nat.mul_le_mul hp H1
            omega
          have H : n ≤ n * (n - 1) / 2 := n_le_choose_two n hn_3
          rw [hL1_val_eq] at H
          exact H
        have h_sub_cast : ((p * M - n + 2 : ℕ) : ℤ) = (p * M : ℤ) - n + 2 := by
          push_cast [Nat.cast_sub hn_le]
          rfl
        rw [h_sub_cast]
        have hlhs : (((n - 1) * (n - 2) / 2 + 1 : ℕ) : ℤ) = (((n - 1) * (n - 2) / 2 : ℕ) : ℤ) + 1 := by push_cast; rfl
        rw [hlhs]
        have : (((n - 1) * (n - 2) / 2 : ℕ) : ℤ) = (p * M : ℤ) - n + 1 := H_z
        linarith
      have hz3 : ((n - 1) * (n - 2) / 2 + 1) = p * M - n + 2 := by exact_mod_cast hz2
      rw [H_choose, hz3]
    have h_R1_val : n * (n - 1) / 2 = p * M := hL1_val_eq
    have h_R1_val2 : (n - 1 + 1).choose 2 = p * M := by
      have : n - 1 + 1 = n := by omega
      rw [this, Nat.choose_two_right, h_R1_val]
    have : Icc ((n - 1).choose 2 + 1) ((n - 1 + 1).choose 2) = Icc (p * M - n + 2) (p * M) := by
      rw [h_L1_val, h_R1_val2]
    rw [this]
    rfl
  have H_div1 : padicValNat p (a (n - 1)) = ∑ y ∈ (Icc (p * M - n + 2) (p * M)).filter (fun k => 1 < k ∧ ¬ k.Prime), padicValNat p y := by
    rw [h_a_n_minus_1]
    apply padicValNat_prod_of_coprime
    intro x hx
    have : x ∈ Icc (p * M - n + 2) (p * M) := mem_of_mem_filter x hx
    rw [mem_Icc] at this
    omega
  
  have H_div2 : padicValNat p (a n) = ∑ y ∈ (Icc (p * M + 1) (p * M + n)).filter (fun k => 1 < k ∧ ¬ k.Prime), padicValNat p y := by
    rw [h_a_n]
    apply padicValNat_prod_of_coprime
    intro x hx
    have : x ∈ Icc (p * M + 1) (p * M + n) := mem_of_mem_filter x hx
    rw [mem_Icc] at this
    omega
    
  have H_val1_ge : p - 1 ≤ padicValNat p (a (n - 1)) := by
    have hL : p * M - p * p + 2 * p + 2 ≤ p * (M - p + 3) := hL_ineq p M hp hM_ge
    have h_sub : (Icc (M - p + 3) M).image (fun x => p * x) ⊆ (Icc (p * M - n + 2) (p * M)).filter (fun k => 1 < k ∧ ¬ k.Prime) := I1_subset p hp M hM_ge hL
    have H_sum_le : ∑ x ∈ (Icc (M - p + 3) M).image (fun x => p * x), padicValNat p x ≤ ∑ y ∈ (Icc (p * M - n + 2) (p * M)).filter (fun k => 1 < k ∧ ¬ k.Prime), padicValNat p y := sum_subset_le _ _ _ h_sub
    have H_sum_eq : ∑ x ∈ (Icc (M - p + 3) M).image (fun x => p * x), padicValNat p x = ∑ x ∈ Icc (M - p + 3) M, padicValNat p (p * x) := by
      apply sum_image
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left (by omega) hab
    rw [H_div1]
    have H_sum_px : p - 1 ≤ ∑ x ∈ Icc (M - p + 3) M, padicValNat p (p * x) := sum_image_px p M hp hM_mod hM_ge
    rw [← H_sum_eq] at H_sum_px
    omega

  have H_val2_le : padicValNat p (a n) ≤ p - 2 := by
    have H_sub : (Icc (p * M + 1) (p * M + n)).filter (fun k => 1 < k ∧ ¬ k.Prime) ⊆ Icc (p * M + 1) (p * M + n) := filter_subset _ _
    have H_sum_le : ∑ y ∈ (Icc (p * M + 1) (p * M + n)).filter (fun k => 1 < k ∧ ¬ k.Prime), padicValNat p y ≤ ∑ y ∈ Icc (p * M + 1) (p * M + n), padicValNat p y := sum_subset_le _ _ _ H_sub
    have H_shift : ∑ y ∈ Icc (p * M + 1) (p * M + n), padicValNat p y = ∑ k ∈ Icc 1 n, padicValNat p (p * M + k) := sum_Icc_shift p M n (padicValNat p)
    have H_sum_eq : ∑ k ∈ Icc 1 n, padicValNat p (p * M + k) = p - 2 := sum_padicValNat_I2_full p M hp hM_mod (by omega)
    omega

  have H_not_dvd : ¬ (a (n - 1) ∣ a n) := by
    intro hdvd
    have h_a_n_ne_zero : a n ≠ 0 := by
      rw [h_a_n]
      apply prod_ne_zero_iff.mpr
      intro x hx
      have : x ∈ Icc (p * M + 1) (p * M + n) := mem_of_mem_filter x hx
      rw [mem_Icc] at this
      omega
    have h_a_n_minus_1_ne_zero : a (n - 1) ≠ 0 := by
      intro h
      have H_val : padicValNat p (a (n - 1)) = 0 := by rw [h, padicValNat.zero]
      omega
    have : padicValNat p (a (n - 1)) ≤ padicValNat p (a n) := padicValNat_le_padicValNat_of_dvd p (a (n - 1)) (a n) hp_prime h_a_n_minus_1_ne_zero h_a_n_ne_zero hdvd
    omega
  
  exact ⟨⟨Hn_gt1, H_not_dvd⟩, Hn_gtB⟩
