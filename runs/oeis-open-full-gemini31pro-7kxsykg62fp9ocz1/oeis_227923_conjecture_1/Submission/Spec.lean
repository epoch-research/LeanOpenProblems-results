import FormalConjectures.Util.ProblemImports

open Nat Finset

def A227923 (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun x =>
    let y : ℕ := n - x
    if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime then 1 else 0

def SophieGermainPrimes : Set ℕ :=
  {p : ℕ | p.Prime ∧ (2 * p + 1).Prime}

def TwinPrimes : Set ℕ :=
  {p : ℕ | p.Prime ∧ (p + 2).Prime}

lemma factorial_gt_two_mul {N : ℕ} (h : 7 ≤ N) : (N + 1)! > 2 * N := by
  induction' h with k hk ih
  · exact by decide
  · have h1 : (k + 1 + 1)! = (k + 2) * (k + 1)! := rfl
    rw [h1]
    have h2 : 2 * (k + 1)! ≤ (k + 2) * (k + 1)! := Nat.mul_le_mul_right _ (by omega)
    have h3 : 2 * (2 * k) < 2 * (k + 1)! := Nat.mul_lt_mul_of_pos_left ih (by decide)
    have h_hk : 7 ≤ k := hk
    have h4 : 2 * (k + 1) < 2 * (2 * k) := by omega
    exact lt_of_lt_of_le (lt_trans h4 h3) h2

lemma hn_gt_1 {N : ℕ} (hN7 : 7 ≤ N) : 1 < (N + 1)! / 6 := by
  have hN8 : 8 ≤ N + 1 := by omega
  have hfac : 40320 ≤ (N + 1)! := by
    calc
      40320 = 8! := by rfl
      _ ≤ (N + 1)! := Nat.factorial_le hN8
  omega

lemma A227923_pos_implies_exists (n : ℕ) (h : A227923 n > 0) :
  ∃ x y, 1 ≤ x ∧ x < n ∧ y = n - x ∧
  (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime := by
  dsimp [A227923] at h
  have h_ne := h.ne'
  have h1 := Finset.exists_ne_zero_of_sum_ne_zero h_ne
  rcases h1 with ⟨x, hx1, hx2⟩
  rw [mem_Ico] at hx1
  use x, n - x
  refine ⟨hx1.1, hx1.2, rfl, ?_⟩
  by_cases h_cond : (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * (n - x) - 1).Prime ∧ (6 * (n - x) + 1).Prime
  · exact h_cond
  · rw [if_neg h_cond] at hx2
    contradiction

lemma contradiction_proof {N x y : ℕ}
  (hN7 : 7 ≤ N)
  (hx1 : 1 ≤ x)
  (hxy : x + y = (N + 1)! / 6)
  (hyp2 : (6 * y + 1).Prime)
  (h_le : 6 * x - 1 ≤ N) : False := by
  have hN8 : 8 ≤ N + 1 := by omega
  have h_div_6 : 6 ∣ (N + 1)! := by
    apply dvd_factorial (by decide) (by omega)
  have h_6_eq : 6 * (x + y) = (N + 1)! := by
    rw [hxy, Nat.mul_div_cancel' h_div_6]
  have h_k_ge : 5 ≤ 6 * x - 1 := by omega
  have h_k_div : (6 * x - 1) ∣ (N + 1)! := by
    apply dvd_factorial (by omega) (Nat.le_succ_of_le h_le)
  have h_6y1 : 6 * y + 1 = (N + 1)! - (6 * x - 1) := by
    omega
  have hk_div2 : (6 * x - 1) ∣ 6 * y + 1 := by
    rw [h_6y1]
    apply Nat.dvd_sub h_k_div (dvd_rfl)
  have h_eq : 6 * x - 1 = 6 * y + 1 := by
    rcases Prime.eq_one_or_self_of_dvd hyp2 _ hk_div2 with h | h
    · omega
    · exact h
  have h_2k : (N + 1)! = 2 * (6 * x - 1) := by
    omega
  have h_fac_gt : (N + 1)! > 2 * N := by
    exact factorial_gt_two_mul hN7
  omega

lemma contradiction_proof_2 {N x y : ℕ}
  (hN7 : 7 ≤ N)
  (hy1 : 1 ≤ y)
  (hxy : x + y = (N + 1)! / 6)
  (hyp2 : (6 * x - 1).Prime)
  (h_le : 6 * y + 1 ≤ N) : False := by
  have hN8 : 8 ≤ N + 1 := by omega
  have h_div_6 : 6 ∣ (N + 1)! := by
    apply dvd_factorial (by decide) (by omega)
  have h_6_eq : 6 * (x + y) = (N + 1)! := by
    rw [hxy, Nat.mul_div_cancel' h_div_6]
  have h_k_ge : 7 ≤ 6 * y + 1 := by omega
  have h_k_div : (6 * y + 1) ∣ (N + 1)! := by
    apply dvd_factorial (by omega) (Nat.le_succ_of_le h_le)
  have h_6x1 : 6 * x - 1 = (N + 1)! - (6 * y + 1) := by
    omega
  have hk_div2 : (6 * y + 1) ∣ 6 * x - 1 := by
    rw [h_6x1]
    apply Nat.dvd_sub h_k_div (dvd_rfl)
  have h_eq : 6 * y + 1 = 6 * x - 1 := by
    rcases Prime.eq_one_or_self_of_dvd hyp2 _ hk_div2 with h | h
    · omega
    · exact h
  have h_2k : (N + 1)! = 2 * (6 * y + 1) := by
    omega
  have h_fac_gt : (N + 1)! > 2 * N := by
    exact factorial_gt_two_mul hN7
  omega

lemma lem_sgp (h_conj : ∀ (n : ℕ), 1 < n → A227923 n > 0) : Set.Infinite SophieGermainPrimes := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  let N := max a 7
  let n := (N + 1)! / 6
  have hN7 : 7 ≤ N := le_max_right a 7
  have hNa : a ≤ N := le_max_left a 7
  have hn_gt : 1 < n := hn_gt_1 hN7
  have hpos := h_conj n hn_gt
  have hex := A227923_pos_implies_exists n hpos
  rcases hex with ⟨x, y, hx1, hxn, hy, hxp1, hxp2, hyp1, hyp2⟩
  use 6 * x - 1
  constructor
  · have h_eq : 2 * (6 * x - 1) + 1 = 12 * x - 1 := by omega
    exact ⟨hxp1, h_eq.symm ▸ hxp2⟩
  · by_contra h_not_lt
    push_neg at h_not_lt
    have h_le : 6 * x - 1 ≤ N := le_trans h_not_lt hNa
    have hxy : x + y = n := by omega
    exact contradiction_proof hN7 hx1 hxy hyp2 h_le

lemma lem_tp (h_conj : ∀ (n : ℕ), 1 < n → A227923 n > 0) : Set.Infinite TwinPrimes := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  let N := max (a + 2) 7
  let n := (N + 1)! / 6
  have hN7 : 7 ≤ N := le_max_right _ 7
  have hNa : a + 2 ≤ N := le_max_left _ 7
  have hn_gt : 1 < n := hn_gt_1 hN7
  have hpos := h_conj n hn_gt
  have hex := A227923_pos_implies_exists n hpos
  rcases hex with ⟨x, y, hx1, hxn, hy, hxp1, hxp2, hyp1, hyp2⟩
  use 6 * y - 1
  constructor
  · have h_eq : 6 * y - 1 + 2 = 6 * y + 1 := by omega
    exact ⟨hyp1, h_eq.symm ▸ hyp2⟩
  · by_contra h_not_lt
    push_neg at h_not_lt
    have h_le : 6 * y + 1 ≤ N := by omega
    have hy1 : 1 ≤ y := by omega
    have hxy : x + y = n := by omega
    exact contradiction_proof_2 hN7 hy1 hxy hxp1 h_le

theorem oeis_227923_conjecture_1 :
  (∀ (n : ℕ), 1 < n → A227923 n > 0) →
  (Set.Infinite SophieGermainPrimes ∧ Set.Infinite TwinPrimes) :=
by
  intro h
  exact ⟨lem_sgp h, lem_tp h⟩

theorem oeis_227923_conjecture_1.disproof : ¬ (type_of% @oeis_227923_conjecture_1) := sorry
