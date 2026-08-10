import FormalConjectures.Util.ProblemImports
open Nat

def D : ℕ → ℕ → ℕ → ℕ
  | N, 0, k => if k + 1 < N then 0 else k + 1
  | N, t+1, k => (D N t k + D N t (k+1)) / 2

lemma div2_mono {a b c d : ℕ} (h1 : a ≤ c) (h2 : b ≤ d) : (a+b)/2 ≤ (c+d)/2 := by
  exact Nat.div_le_div_right (Nat.add_le_add h1 h2)

lemma D_spatial_mono (N t k : ℕ) : D N t k ≤ D N t (k+1) := by
  induction t generalizing k with
  | zero =>
      by_cases h : k + 1 < N
      · by_cases hh : k + 1 + 1 < N <;> simp [D, h, hh]
      · have hh : ¬ k + 1 + 1 < N := by omega
        simp [D, h, hh]
  | succ t ih =>
      simp [D]
      exact div2_mono (ih k) (ih (k+1))

lemma D_bound (N t k : ℕ) : D N t k ≤ k+1 := by
  induction t generalizing k with
  | zero =>
      simp [D]
      split <;> omega
  | succ t ih =>
      simp [D]
      have h0 := ih k
      have h1 := ih (k+1)
      rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)]
      omega

lemma D_time_mono (N t k : ℕ) : D N t k ≤ D N (t+1) k := by
  simp [D]
  have h := D_spatial_mono N t k
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
  omega

lemma D_shift_same (N t k : ℕ) : D N t k ≤ D (N+1) t (k+1) := by
  induction t generalizing k with
  | zero =>
      by_cases h : k + 1 < N
      · have hR : k + 1 + 1 < N + 1 := by omega
        simp [D, h, hR]
      · have hR : ¬ k + 1 + 1 < N + 1 := by omega
        simp [D, h, hR]
  | succ t ih =>
      simp [D]
      exact div2_mono (ih k) (ih (k+1))

lemma D_lower_comp (N t k : ℕ) : D (N+1) (t+1) k ≤ D N t (k+1) := by
  induction t generalizing k with
  | zero =>
      by_cases h : k + 1 < N
      · have h1 : k + 1 < N + 1 := by omega
        have h2 : k + 1 + 1 < N + 1 := by omega
        simp [D, h, h1, h2]
      · have hR : ¬ k + 1 + 1 < N := by omega
        have rhs : D N 0 (k+1) = k+1+1 := by simp [D, hR]
        rw [rhs]
        simp [D]
        have hA : (if k < N then 0 else k + 1) ≤ k + 1 := by split <;> omega
        have hB : (if k + 1 < N then 0 else k + 1 + 1) ≤ k + 1 + 1 := by split <;> omega
        calc
          ((if k < N then 0 else k + 1) + if k + 1 < N then 0 else k + 1 + 1) / 2
              ≤ ((k+1) + (k+1+1)) / 2 := div2_mono hA hB
          _ ≤ k+1+1 := by
              rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)]
              omega
  | succ t ih =>
      simp [D]
      exact div2_mono (ih k) (ih (k+1))

lemma D0_le_one (N t : ℕ) : D N t 0 ≤ 1 := by simpa using D_bound N t 0

lemma D_lower_same (N t k : ℕ) : D (N+1) (t+1) k ≤ D N t k := by
  induction t generalizing k with
  | zero =>
      by_cases h : k + 1 < N
      · have h1 : k + 1 < N + 1 := by omega
        have h2 : k + 1 + 1 < N + 1 := by omega
        simp [D, h, h1, h2]
      · have rhs : D N 0 k = k+1 := by simp [D, h]
        rw [rhs]
        simp [D]
        have hA : (if k < N then 0 else k + 1) ≤ k + 1 := by split <;> omega
        have hB : (if k + 1 < N then 0 else k + 1 + 1) ≤ k + 1 + 1 := by split <;> omega
        calc
          ((if k < N then 0 else k + 1) + if k + 1 < N then 0 else k + 1 + 1) / 2
              ≤ ((k+1) + (k+1+1)) / 2 := div2_mono hA hB
          _ ≤ k+1 := by
              rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)]
              omega
  | succ t ih =>
      simp [D]
      exact div2_mono (ih k) (ih (k+1))


lemma D_gap_pos (N t k : ℕ) (h : 0 < D N t k) : D N t k + 1 ≤ D N t (k+1) := by
  induction t generalizing k with
  | zero =>
      simp [D] at h ⊢
      by_cases hk : k + 1 < N
      · simp [hk] at h
      · have hk2_or : k + 1 + 1 < N ∨ ¬ k + 1 + 1 < N := em _
        cases hk2_or with
        | inl hk2 => simp [hk, hk2]; omega
        | inr hk2 => simp [hk, hk2]
  | succ t ih =>
      simp [D] at h ⊢
      let a := D N t k
      let b := D N t (k+1)
      let c := D N t (k+2)
      have hmono_ab : a ≤ b := by exact D_spatial_mono N t k
      have hmono_bc : b ≤ c := by exact D_spatial_mono N t (k+1)
      by_cases ha : 0 < a
      · have hb : 0 < b := lt_of_lt_of_le ha hmono_ab
        have gab : a + 1 ≤ b := ih k ha
        have gbc : b + 1 ≤ c := ih (k+1) hb
        change (a + b) / 2 < (b + c) / 2
        rw [Nat.lt_iff_add_one_le]
        rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
        have hm : 2 * ((a + b) / 2) ≤ a + b := Nat.mul_div_le (a + b) 2
        omega
      · have ha0 : a = 0 := by omega
        have hb2 : 2 ≤ b := by
          have hsum : 2 ≤ a + b := by simpa [a, b] using h
          omega
        have hbpos : 0 < b := by omega
        have gbc : b + 1 ≤ c := ih (k+1) hbpos
        change (a + b) / 2 < (b + c) / 2
        rw [Nat.lt_iff_add_one_le]
        rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
        have hm : 2 * ((a + b) / 2) ≤ a + b := Nat.mul_div_le (a + b) 2
        omega

lemma D_pos_shift_two (N t k : ℕ) (h : 0 < D N t k) : D N t k + 2 ≤ D (N+1) t (k+2) := by
  induction t generalizing k with
  | zero =>
      simp [D] at h ⊢
      by_cases hk : k + 1 < N
      · simp [hk] at h
      · have hk2 : ¬ k + 2 < N := by omega
        simp [hk, hk2]
  | succ t ih =>
      simp [D] at h ⊢
      let a := D N t k
      let b := D N t (k+1)
      let y0 := D (N+1) t (k+2)
      let y1 := D (N+1) t (k+3)
      have hmono_ab : a ≤ b := D_spatial_mono N t k
      by_cases ha : 0 < a
      · have hb : 0 < b := lt_of_lt_of_le ha hmono_ab
        have hy0 : a + 2 ≤ y0 := ih k ha
        have hy1 : b + 2 ≤ y1 := ih (k+1) hb
        change (a + b) / 2 + 2 ≤ (y0 + y1) / 2
        rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
        have hm : 2 * ((a + b) / 2) ≤ a + b := Nat.mul_div_le (a + b) 2
        omega
      · have ha0 : a = 0 := by omega
        have hb2 : 2 ≤ b := by
          have hsum : 2 ≤ a + b := by simpa [a, b] using h
          omega
        have hbpos : 0 < b := by omega
        have hy0 : b ≤ y0 := D_shift_same N t (k+1)
        have hy1 : b + 2 ≤ y1 := ih (k+1) hbpos
        change (a + b) / 2 + 2 ≤ (y0 + y1) / 2
        rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
        have hm : 2 * ((a + b) / 2) ≤ a + b := Nat.mul_div_le (a + b) 2
        omega

lemma D_upper_pos (N t : ℕ) (h : 0 < D N t 0) : 0 < D (N+1) (t+2) 0 := by
  have h1 : D N t 0 ≤ D (N+1) t 1 := D_shift_same N t 0
  have h2 : D N t 0 + 2 ≤ D (N+1) t 2 := D_pos_shift_two N t 0 h
  simp [D]
  -- first show coordinate 1 after one step is at least 2
  have hz1 : 2 ≤ (D (N+1) t 1 + D (N+1) t 2) / 2 := by
    rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
    omega
  omega

lemma D_time_mono_le (N k : ℕ) : Monotone (fun t => D N t k) :=
  monotone_nat_of_le_succ (fun t => D_time_mono N t k)

noncomputable def T (N : ℕ) : ℕ := sInf {t : ℕ | 0 < D N t 0}

lemma T_set_nonempty (N : ℕ) : ({t : ℕ | 0 < D N t 0} : Set ℕ).Nonempty := by
  induction N with
  | zero =>
      refine ⟨0, ?_⟩
      simp [D]
  | succ N ih =>
      rcases ih with ⟨t, ht⟩
      refine ⟨t+2, ?_⟩
      simpa [Nat.succ_eq_add_one, add_assoc] using D_upper_pos N t ht

lemma T_mem (N : ℕ) : 0 < D N (T N) 0 := by
  exact Nat.sInf_mem (T_set_nonempty N)

lemma T_le_of_pos {N t : ℕ} (h : 0 < D N t 0) : T N ≤ t := by
  exact Nat.sInf_le h

lemma not_pos_before_T {N t : ℕ} (ht : t < T N) : D N t 0 = 0 := by
  by_contra h0
  have hp : 0 < D N t 0 := by omega
  have := T_le_of_pos (N := N) (t := t) hp
  omega

lemma T_succ_ge {N : ℕ} (hN : 1 ≤ N) : T N + 1 ≤ T (N+1) := by
  by_contra hnot
  have hle : T (N+1) ≤ T N := by omega
  have hp_at_s : 0 < D (N+1) (T N) 0 := by
    exact lt_of_lt_of_le (T_mem (N+1)) ((D_time_mono_le (N+1) 0) hle)
  cases hs : T N with
  | zero =>
      have hNle : N ≤ 1 := by
        have hpN := T_mem N
        rw [hs] at hpN
        by_contra hle
        have hgt : 1 < N := by omega
        simp [D, hgt] at hpN
      have hNeq : N = 1 := by omega
      rw [hs] at hp_at_s
      subst hNeq
      simp [D] at hp_at_s
  | succ s =>
      rw [hs] at hp_at_s
      have hprev : D N s 0 = 0 := by
        apply not_pos_before_T
        omega
      have hle0 : D (N+1) (s+1) 0 ≤ D N s 0 := D_lower_same N s 0
      omega

lemma T_succ_le (N : ℕ) : T (N+1) ≤ T N + 2 := by
  exact T_le_of_pos (D_upper_pos N (T N) (T_mem N))

lemma T_finite_difference {N : ℕ} (hN : 1 ≤ N) :
    T (N+1) = T N + 1 ∨ T (N+1) = T N + 2 := by
  have h1 := T_succ_ge (N := N) hN
  have h2 := T_succ_le N
  omega



