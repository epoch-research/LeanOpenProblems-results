import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A093456: Product of all composite numbers between $n(n-1)/2+1$ and $n(n+1)/2$ (including boundaries),
where $n(n-1)/2 = \binom{n}{2}$ and $n(n+1)/2 = \binom{n+1}{2}$.
-/
def a (n : ℕ) : ℕ :=
  let L := n.choose 2 + 1
  let R := (n + 1).choose 2

  -- A number k is composite if k > 1 and is not prime.
  let is_composite (k : ℕ) : Prop := 1 < k ∧ ¬ k.Prime

  (Icc L R).filter is_composite |>.prod id

lemma exists_prime_for_M (M : ℕ) (hM : 14 ≤ M) : ∃ p, Nat.Prime p ∧ 2 * M - 3 < p ∧ p ≤ (M * (M + 1)) / 4 := by
  have h_pos : 2 * M - 3 ≠ 0 := by omega
  rcases Nat.exists_prime_lt_and_le_two_mul (2 * M - 3) h_pos with ⟨p, hp, h1, h2⟩
  use p
  refine ⟨hp, h1, ?_⟩
  have h_bound : 2 * (2 * M - 3) ≤ (M * (M + 1)) / 4 := by
    rw [Nat.le_div_iff_mul_le (by decide)]
    have h_eq1 : M * (M + 1) = M * M + M := by ring
    have h_eq2 : 2 * (2 * M - 3) * 4 = 16 * M - 24 := by omega
    rw [h_eq1, h_eq2]
    rcases eq_or_lt_of_le hM with rfl | hM_gt
    · decide
    · have hM15 : 15 ≤ M := hM_gt
      have hM2 : 15 * M ≤ M * M := Nat.mul_le_mul_right M hM15
      omega
  exact h2.trans h_bound

lemma no_div_ineq {p n : ℕ} (hn10 : 10 ≤ n) (h_ge : 6 * p ≤ (n + 1) * (n + 2)) :
  n * (n - 1) ≥ 4 * p := by
  have hn2 : 10 * n ≤ n * n := Nat.mul_le_mul_right n hn10
  have h_exp1 : (n + 1) * (n + 2) = n * n + 3 * n + 2 := by ring
  have h_exp2 : n * (n - 1) = n * n - n := by
    rcases n with _ | n
    · omega
    · have h_sub : (n + 1) * (n + 1 - 1) = (n + 1) * n := rfl
      rw [h_sub]
      have : (n + 1) * (n + 1) = (n + 1) * n + (n + 1) := by ring
      omega
  have h_quad : 2 * (n * n + 3 * n + 2) ≤ 3 * (n * n - n) := by
    have h_eq : 3 * (n * n - n) = 3 * (n * n) - 3 * n := by
      rcases n with _ | n
      · omega
      · have : 3 * ((n + 1) * (n + 1) - (n + 1)) = 3 * ((n + 1) * (n + 1)) - 3 * (n + 1) := by
          omega
        rw [this]
    rw [h_eq]
    omega
  omega

lemma R_bound_of_p_verified {p n : ℕ} (hn10 : 10 ≤ n) (h_ge : (n + 1) * (n + 2) / 2 ≥ 3 * p) :
  n * (n - 1) / 2 ≥ 2 * p := by
  have h_ge_le : 3 * p ≤ (n + 1) * (n + 2) / 2 := h_ge
  have h_ge2 : 3 * p * 2 ≤ (n + 1) * (n + 2) := by
    rw [← Nat.le_div_iff_mul_le (by decide)]
    exact h_ge_le
  have h_ge3 : 6 * p ≤ (n + 1) * (n + 2) := by omega
  have h_mul := no_div_ineq hn10 h_ge3
  omega

lemma exists_R_ge_3p (p : ℕ) (hp : 19 ≤ p) : ∃ x, 3 * p ≤ x * (x + 1) / 2 := by
  use 3 * p
  rw [Nat.le_div_iff_mul_le (by decide)]
  have : 2 ≤ 3 * p + 1 := by omega
  nlinarith

lemma n_ge_10_of_p {p x : ℕ} (hp : 19 ≤ p) (hx : 3 * p ≤ x * (x + 1) / 2) :
  10 ≤ x - 1 := by
  have h_cases : x ≤ 10 ∨ 11 ≤ x := by omega
  rcases h_cases with hx10 | hx11
  · have : x * (x + 1) / 2 ≤ 55 := by
      have : x * (x + 1) ≤ 10 * 11 := by nlinarith
      omega
    omega
  · omega

lemma not_dvd_prod_of_not_dvd {ι : Type _} {s : Finset ι} {f : ι → ℕ} {p : ℕ} (hp : Nat.Prime p) (h : ∀ x ∈ s, ¬ (p ∣ f x)) : ¬ (p ∣ ∏ x ∈ s, f x) := by
  refine Finset.prod_induction f (fun x => ¬ (p ∣ x)) ?_ ?_ h
  · intro a b hpa hpb hpab
    rw [hp.dvd_mul] at hpab
    rcases hpab with ha | hb
    · exact hpa ha
    · exact hpb hb
  · intro hp1
    exact Nat.Prime.not_dvd_one hp hp1

lemma no_multiples_in_Icc {p n x : ℕ} (hn : n * (n - 1) / 2 ≥ 2 * p) (hn2 : (n + 1) * n / 2 < 3 * p) (hx : n * (n - 1) / 2 + 1 ≤ x ∧ x ≤ (n + 1) * n / 2) : ¬ (p ∣ x) := by
  intro hp_dvd
  rcases hp_dvd with ⟨k, rfl⟩
  rcases k with _ | k
  · omega
  · rcases k with _ | k
    · omega
    · rcases k with _ | k
      · omega
      · have h_mul : (k + 3) * p ≥ 3 * p := Nat.mul_le_mul_right p (by omega)
        have : p * (k + 1 + 1 + 1) = (k + 3) * p := by ring
        omega

lemma dvd_of_dvd_all {M : ℕ} (h : ∀ n ≥ M, a n ∣ a (n + 1)) (n : ℕ) (hn : M ≤ n) : a M ∣ a n := by
  induction' n, hn using Nat.le_induction with k hk ih
  · rfl
  · have h_step := h k hk
    exact Nat.dvd_trans ih h_step

lemma mono_ineq {n M' : ℕ} (hn_le : n ≤ M') : n * (n - 1) ≤ M' * (M' - 1) := by
  rcases n with _ | n
  · omega
  · rcases M' with _ | M'
    · omega
    · have h_n : (n + 1) * (n + 1 - 1) = (n + 1) * n := rfl
      have h_M' : (M' + 1) * (M' + 1 - 1) = (M' + 1) * M' := rfl
      rw [h_n, h_M']
      have : n ≤ M' := by omega
      nlinarith

lemma K_bound {p R : ℕ} (hp : p ≠ 0) (hR : 2 * p ≤ R) : 2 ≤ R / p := by
  rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hp)]
  omega

lemma K_spec {p R : ℕ} (hp : p ≠ 0) : (R / p + 1) * p > R := by
  have h_eq : (R / p + 1) * p = (R / p) * p + p := by ring
  rw [h_eq]
  have h_comm : (R / p) * p = p * (R / p) := Nat.mul_comm (R / p) p
  rw [h_comm]
  have h_mod := Nat.mod_lt R (Nat.pos_of_ne_zero hp)
  have h_div := Nat.div_add_mod R p
  omega

lemma helper_p_gt_M' (M' p : ℕ) (hM' : 15 ≤ M') (hp_gt : 2 * M' - 3 < p) : M' < 4 * p := by
  omega

lemma helper_MM_lt (M M' p : ℕ) (hM' : 15 ≤ M') (h_M'_ge_MM : M' ≥ M * M) (hp_gt : 2 * M' - 3 < p) : M * M < 4 * p := by
  have h4p : 4 * p > 8 * M' - 12 := by omega
  have : 8 * M' - 12 > M' := by omega
  omega

lemma helper_2p_gt (M p : ℕ) (h_MM_lt : M * M < 4 * p) : 2 * p > M * (M - 1) / 2 := by
  have h_le : M * (M - 1) ≤ M * M := Nat.mul_le_mul_left M (Nat.sub_le M 1)
  generalize h_A : M * (M - 1) = A at h_le
  generalize h_B : M * M = B at h_le h_MM_lt
  omega

lemma helper_My (M y p : ℕ) (hy_ge : 2 * p ≤ y * (y + 1) / 2) (h_2p_gt : 2 * p > M * (M - 1) / 2) (h_div_mono : y * (y + 1) / 2 ≤ M * (M - 1) / 2) : False := by
  generalize h_A : y * (y + 1) / 2 = A at hy_ge h_div_mono
  generalize h_B : M * (M - 1) / 2 = B at h_2p_gt h_div_mono
  omega

theorem oeis_93456_conjecture_0.disproof :
  ¬ Set.Finite {n : ℕ | n > 1 ∧ ¬ (a (n - 1) ∣ a n)} := by
  intro h_fin
  rcases h_fin.exists_le with ⟨M_old, hM_le_old⟩
  let M := max M_old 15
  have hM_le : ∀ i ∈ {n | n > 1 ∧ ¬a (n - 1) ∣ a n}, i ≤ M := by
    intro i hi
    have := hM_le_old i hi
    omega
  have hM_ge15 : M ≥ 15 := by omega
  let M' := max (M * M + 15) 15
  have hM' : 15 ≤ M' := by omega
  have hM'_14 : 14 ≤ M' := by omega
  have h_M'_ge_MM : M' ≥ M * M := by omega
  rcases exists_prime_for_M M' hM'_14 with ⟨p, hp, hp_gt, hp_le⟩
  have hp19 : 19 ≤ p := by omega
  have h_exists := exists_R_ge_3p p hp19
  let x := Nat.find h_exists
  have hx : 3 * p ≤ x * (x + 1) / 2 := Nat.find_spec h_exists
  have hx_pos : x ≠ 0 := by
    intro hx0
    rw [hx0] at hx
    omega
  let n := x - 1
  have hx_eq : x = n + 1 := (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hx_pos)).symm
  have hn_lt : n * (n + 1) / 2 < 3 * p := by
    have h_lt := Nat.find_min h_exists (by omega : n < x)
    omega
  have hn_ge : (n + 1) * (n + 2) / 2 ≥ 3 * p := by
    rw [hx_eq] at hx
    omega
  have hn10 : 10 ≤ n := n_ge_10_of_p hp19 hx
  have hn_ge2 := R_bound_of_p_verified hn10 hn_ge

  have h_p_gt_M' : M' < 4 * p := helper_p_gt_M' M' p hM' hp_gt
  have h_MM_lt : M * M < 4 * p := helper_MM_lt M M' p hM' h_M'_ge_MM hp_gt
  have h_2p_gt : 2 * p > M * (M - 1) / 2 := helper_2p_gt M p h_MM_lt

  -- Define y for the prime 2 * p
  have h_exists_y : ∃ y, 2 * p ≤ y * (y + 1) / 2 := by
    use 2 * p
    rw [Nat.le_div_iff_mul_le (by decide)]
    nlinarith
  let y := Nat.find h_exists_y
  have hy_ge : 2 * p ≤ y * (y + 1) / 2 := Nat.find_spec h_exists_y
  have hy_pos : y ≠ 0 := by
    intro hy0
    rw [hy0] at hy_ge
    omega
  have hy_lt : (y - 1) * y / 2 < 2 * p := by
    have h_lt := Nat.find_min h_exists_y (by omega : y - 1 < y)
    have h_eq : (y - 1) + 1 = y := by omega
    rw [h_eq] at h_lt
    omega

  have hn_ge2' : 2 * p ≤ (n - 1) * ((n - 1) + 1) / 2 := by
    have : (n - 1) * ((n - 1) + 1) = n * (n - 1) := by
      have : (n - 1) + 1 = n := by omega
      rw [this, Nat.mul_comm]
    rw [this]
    exact hn_ge2

  have hy_le_n1 : y ≤ n - 1 := Nat.find_min' h_exists_y hn_ge2'

  have h_My : M ≤ y := by
    by_contra h_lt
    push_neg at h_lt
    have h_mono := mono_ineq h_lt
    have h_div_mono : y * (y + 1) / 2 ≤ M * (M - 1) / 2 := by
      have : (y + 1) * (y + 1 - 1) = y * (y + 1) := by
        have : y + 1 - 1 = y := rfl
        rw [this, Nat.mul_comm]
      rw [this] at h_mono
      omega
    exact helper_My M y p hy_ge h_2p_gt h_div_mono

  have h_dvd_all : ∀ k ≥ M, a k ∣ a (k + 1) := by
    clear hp_le hp_gt hM' hM'_14 h_M'_ge_MM M' hp19 h_exists hx hx_pos n x hx_eq hn_lt hn_ge hn10 hn_ge2 h_p_gt_M' h_MM_lt h_2p_gt h_exists_y y hy_ge hy_pos hy_lt hn_ge2' hy_le_n1 h_My
    intro k hk
    have hk_gt : k + 1 > M := by omega
    have h_not_in_S : ¬ (k + 1 ∈ {n | n > 1 ∧ ¬ (a (n - 1) ∣ a n)}) := by
      intro h_in
      have := hM_le (k + 1) h_in
      omega
    simp only [Set.mem_setOf_eq] at h_not_in_S
    push_neg at h_not_in_S
    have hk_gt1 : k + 1 > 1 := by omega
    exact h_not_in_S hk_gt1

  have h_dvd_all_y : ∀ k ≥ y, a k ∣ a (k + 1) := by
    intro k hk
    exact h_dvd_all k (by omega)
  have h_ay_dvd_an1 := dvd_of_dvd_all h_dvd_all_y (n - 1) hy_le_n1

  have h_an1_dvd_an : a (n - 1) ∣ a n := by
    have := h_dvd_all (n - 1) (by omega)
    have h_eq : n - 1 + 1 = n := by omega
    rw [h_eq] at this
    exact this

  -- Now we show that p | a(y) and p ∤ a(n).
  -- First, p ∤ a(n).
  have hp_not_dvd_an : ¬ (p ∣ a n) := by
    unfold a
    have h_choose1 : n.choose 2 + 1 = n * (n - 1) / 2 + 1 := by rw [Nat.choose_two_right]
    have h_choose2 : (n + 1).choose 2 = (n + 1) * n / 2 := by
      rw [Nat.choose_two_right]
      have : n + 1 - 1 = n := by omega
      rw [this]
    refine not_dvd_prod_of_not_dvd hp ?_
    intro x hx
    change ¬ (p ∣ x)
    simp only [mem_filter, mem_Icc] at hx
    rw [h_choose1, h_choose2] at hx
    have hn_lt_comm : (n + 1) * n / 2 < 3 * p := by
      rw [Nat.mul_comm]
      exact hn_lt
    exact no_multiples_in_Icc hn_ge2 hn_lt_comm hx.1

  -- Now, p | a(y).
  have hp_dvd_ay : p ∣ a y := by
    unfold a
    have h_choose1 : y.choose 2 + 1 = y * (y - 1) / 2 + 1 := by rw [Nat.choose_two_right]
    have h_choose2 : (y + 1).choose 2 = (y + 1) * y / 2 := by
      rw [Nat.choose_two_right]
      have : y + 1 - 1 = y := by omega
      rw [this]
    have h_choose2_eq : (y + 1) * y / 2 = y * (y + 1) / 2 := by
      have : (y + 1) * y = y * (y + 1) := Nat.mul_comm (y + 1) y
      rw [this]
    -- We know 2p <= R_y is composite and lies in Icc L R.
    let C := 2 * p
    have hC_comp : 1 < C ∧ ¬ C.Prime := by
      refine ⟨by omega, ?_⟩
      intro hp_prime
      have := hp_prime.not_dvd_one
      have h2_dvd : 2 ∣ 2 * p := dvd_mul_right 2 p
      rcases hp_prime.eq_one_or_self_of_dvd 2 h2_dvd with h2_1 | h2_2p
      · omega
      · omega
    have hC_mem : C ∈ Icc (y * (y - 1) / 2 + 1) (y * (y + 1) / 2) := by
      rw [mem_Icc]
      refine ⟨?_, hy_ge⟩
      have h_comm : (y - 1) * y / 2 = y * (y - 1) / 2 := by rw [Nat.mul_comm]
      rw [← h_comm]
      omega
    have hC_filter : C ∈ filter (fun k => 1 < k ∧ ¬ k.Prime) (Icc (y * (y - 1) / 2 + 1) (y * (y + 1) / 2)) := by
      rw [mem_filter]
      exact ⟨hC_mem, hC_comp⟩
    have h_dvd : C ∣ ∏ x ∈ filter (fun k => 1 < k ∧ ¬ k.Prime) (Icc (y * (y - 1) / 2 + 1) (y * (y + 1) / 2)), x := by
      exact dvd_prod_of_mem id hC_filter
    have hp_dvd_C : p ∣ C := dvd_mul_left p 2
    rw [h_choose1, h_choose2, h_choose2_eq]
    exact Nat.dvd_trans hp_dvd_C h_dvd

  have hp_dvd_an : p ∣ a n := by
    have h1 := Nat.dvd_trans hp_dvd_ay h_ay_dvd_an1
    exact Nat.dvd_trans h1 h_an1_dvd_an
  exact hp_not_dvd_an hp_dvd_an
