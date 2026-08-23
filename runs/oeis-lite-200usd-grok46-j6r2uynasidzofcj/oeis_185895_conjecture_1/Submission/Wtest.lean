import FormalConjectures.Util.ProblemImports

open Nat Finset

def W : ℕ → ℕ → ℕ
  | n, 0 => if n = 0 then 1 else 0
  | n, k + 1 =>
    if n < k + 1 then W n k
    else W n k + (k + 1).factorial * W (n - (k + 1)) k

lemma W_zero_left (k : ℕ) : W 0 k = 1 := by
  induction k with
  | zero => simp [W]
  | succ k ih => simp [W, ih]

lemma W_zero_right {n : ℕ} (hn : 0 < n) : W n 0 = 0 := by
  simp [W, hn.ne']

lemma W_succ_of_lt {n k : ℕ} (h : n < k + 1) : W n (k + 1) = W n k := by
  simp [W, h]

lemma W_succ_of_le {n k : ℕ} (h : k + 1 ≤ n) :
    W n (k + 1) = W n k + (k + 1).factorial * W (n - (k + 1)) k := by
  simp [W, Nat.not_lt.mpr h]

lemma W_eq_of_ge {n k : ℕ} (h : n ≤ k) : W n k = W n n := by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [W_succ_of_lt (by omega), ih]

lemma W_mono_right {n k₁ k₂ : ℕ} (h : k₁ ≤ k₂) : W n k₁ ≤ W n k₂ := by
  induction k₂, h using Nat.le_induction with
  | base => simp
  | succ k _ ih =>
    by_cases hlt : n < k + 1
    · rw [W_succ_of_lt hlt]; exact ih
    · rw [W_succ_of_le (Nat.le_of_not_lt hlt)]; omega

lemma W_eq_min (n k : ℕ) : W n k = W n (min n k) := by
  cases le_total n k with
  | inl h => rw [min_eq_left h, W_eq_of_ge h]
  | inr h => rw [min_eq_right h]

lemma Icc_succ_right' (a b : ℕ) (h : a ≤ b + 1) :
    Icc a (b + 1) = insert (b + 1) (Icc a b) := by
  ext x
  simp [mem_Icc, mem_insert]
  omega

lemma W_max_decomp :
    ∀ k n, W n k =
      (∑ j ∈ Icc 1 (min n k), j.factorial * W (n - j) (j - 1)) +
        if n = 0 then 1 else 0 := by
  intro k
  induction k with
  | zero =>
    intro n
    simp [W]
  | succ k ih =>
    intro n
    by_cases hlt : n < k + 1
    · rw [W_succ_of_lt hlt, ih]
      have hmin : min n (k + 1) = min n k := by omega
      rw [hmin]
    · have hle : k + 1 ≤ n := Nat.le_of_not_lt hlt
      rw [W_succ_of_le hle, ih n]
      have hmin : min n (k + 1) = k + 1 := by omega
      have hmin' : min n k = k := by omega
      rw [hmin, hmin']
      have ha : 1 ≤ k + 1 := by omega
      rw [Icc_succ_right' 1 k ha]
      have hnotin : k + 1 ∉ Icc 1 k := by simp [mem_Icc]
      rw [sum_insert hnotin]
      have : k + 1 - 1 = k := by omega
      rw [this]
      ac_rfl

lemma W_self (n : ℕ) (hn : 0 < n) :
    W n n = n.factorial + W n (n - 1) := by
  cases n with
  | zero => omega
  | succ n =>
    rw [W_succ_of_le (Nat.le_refl _)]
    simp [W_zero_left]
    ac_rfl

lemma W_pred_eq_sum (n : ℕ) (hn : 0 < n) :
    W n (n - 1) = ∑ j ∈ Icc 1 (n - 1), j.factorial * W (n - j) (j - 1) := by
  have := W_max_decomp (n - 1) n
  have hn0 : n ≠ 0 := hn.ne'
  simp only [hn0, ite_false] at this
  have hmin : min n (n - 1) = n - 1 := by omega
  rwa [hmin, add_zero] at this

lemma fpair_anti_left {n j : ℕ} (h1 : j + 1 ≤ n - j) :
    (j + 1).factorial * (n - (j + 1)).factorial ≤
      j.factorial * (n - j).factorial := by
  have hjn : j < n := by omega
  have hnj : n - (j + 1) + 1 = n - j := by omega
  -- (j+1)! (n-j-1)! * (n-j) = (j+1) j! * (n-j-1)! * (n-j)
  --                         = (j+1) j! * (n-j)!
  -- and (j+1) ≤ n-j so left * (n-j) ≤ right * (n-j)
  have hL :
      (j + 1).factorial * (n - (j + 1)).factorial * (n - j) =
        (j + 1) * (j.factorial * (n - j).factorial) := by
    rw [factorial_succ, mul_assoc, mul_comm (j + 1), mul_assoc]
    rw [show n - j = (n - (j + 1)) + 1 by omega, factorial_succ]
    ring
  have hpos : 0 < n - j := Nat.sub_pos_of_lt hjn
  have : (j + 1).factorial * (n - (j + 1)).factorial * (n - j) ≤
      j.factorial * (n - j).factorial * (n - j) := by
    rw [hL]
    have := Nat.mul_le_mul_right (j.factorial * (n - j).factorial) h1
    linarith
  exact Nat.le_of_mul_le_mul_right this hpos

lemma fpair_le_three_left (n j : ℕ) (h3 : 3 ≤ j) (hhalf : 2 * j ≤ n) :
    j.factorial * (n - j).factorial ≤ 6 * (n - 3).factorial := by
  induction j, h3 using Nat.le_induction with
  | base => simp [factorial]
  | succ j hj ih =>
    have hhalfj : 2 * j ≤ n := by omega
    have hanti : j + 1 ≤ n - j := by omega
    exact le_trans (fpair_anti_left hanti) (ih hhalfj)

lemma fpair_le_middle {n j : ℕ} (hn : 8 ≤ n) (hj1 : 3 ≤ j) (hj2 : j ≤ n - 3) :
    j.factorial * (n - j).factorial ≤ 6 * (n - 3).factorial := by
  cases le_total (2 * j) n with
  | inl hhalf =>
    exact fpair_le_three_left n j hj1 hhalf
  | inr hhalf =>
    have h3' : 3 ≤ n - j := by omega
    have hhalf' : 2 * (n - j) ≤ n := by omega
    have := fpair_le_three_left n (n - j) h3' hhalf'
    have hnj : n - (n - j) = j := by omega
    rwa [hnj, mul_comm] at this

lemma fact_pred (n : ℕ) (h : 1 ≤ n) : n.factorial = n * (n - 1).factorial := by
  cases n with
  | zero => omega
  | succ n => simp [factorial]

lemma Icc_endpoints (n : ℕ) (hn : 8 ≤ n) :
    Icc 1 (n - 1) = insert 1 (insert 2 (insert (n - 2) (insert (n - 1) (Icc 3 (n - 3))))) := by
  ext x
  simp only [mem_Icc, mem_insert]
  omega

lemma coeff_bound (n : ℕ) (hn : 8 ≤ n) :
    4 * (n - 2) + 6 * (n - 5) ≤ (n - 1) * (n - 2) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  subst n
  have h1 : 8 + m - 1 = 7 + m := by omega
  have h2 : 8 + m - 2 = 6 + m := by omega
  have h5 : 8 + m - 5 = 3 + m := by omega
  rw [h1, h2, h5]
  nlinarith

lemma sum_fact_pair_le (n : ℕ) (hn : 8 ≤ n) :
    ∑ j ∈ Icc 1 (n - 1), j.factorial * (n - j).factorial ≤ 3 * (n - 1).factorial := by
  have hset := Icc_endpoints n hn
  have hdis1 : 1 ∉ insert 2 (insert (n - 2) (insert (n - 1) (Icc 3 (n - 3)))) := by
    simp [mem_Icc, mem_insert]; omega
  have hdis2 : 2 ∉ insert (n - 2) (insert (n - 1) (Icc 3 (n - 3))) := by
    simp [mem_Icc, mem_insert]; omega
  have hdis3 : n - 2 ∉ insert (n - 1) (Icc 3 (n - 3)) := by
    simp [mem_Icc, mem_insert]; omega
  have hdis4 : n - 1 ∉ Icc 3 (n - 3) := by
    simp [mem_Icc]; omega
  rw [hset, sum_insert hdis1, sum_insert hdis2, sum_insert hdis3, sum_insert hdis4]
  have t1 : (1 : ℕ).factorial * (n - 1).factorial = (n - 1).factorial := by simp [factorial]
  have t2 : (2 : ℕ).factorial * (n - 2).factorial = 2 * (n - 2).factorial := by simp [factorial]
  have t3 : (n - 2).factorial * (n - (n - 2)).factorial = 2 * (n - 2).factorial := by
    rw [show n - (n - 2) = 2 by omega]; simp [factorial]; ring
  have t4 : (n - 1).factorial * (n - (n - 1)).factorial = (n - 1).factorial := by
    rw [show n - (n - 1) = 1 by omega]; simp [factorial]
  rw [t1, t2, t3, t4]
  set S := ∑ j ∈ Icc 3 (n - 3), j.factorial * (n - j).factorial
  have hmid_le : S ≤ ∑ j ∈ Icc 3 (n - 3), 6 * (n - 3).factorial := by
    apply sum_le_sum
    intro j hj
    simp [mem_Icc] at hj
    exact fpair_le_middle hn (by omega) (by omega)
  have hmid_eq : ∑ j ∈ Icc 3 (n - 3), 6 * (n - 3).factorial =
      #(Icc 3 (n - 3)) * (6 * (n - 3).factorial) := by
    simp [sum_const]
  have hcard : #(Icc 3 (n - 3)) = n - 5 := by
    rw [Nat.card_Icc]; omega
  have hmid : S ≤ (n - 5) * (6 * (n - 3).factorial) := by
    rw [hcard] at hmid_eq
    exact le_trans hmid_le (le_of_eq hmid_eq)
  have hn1 : (n - 1).factorial = (n - 1) * (n - 2) * (n - 3).factorial := by
    have h1 : (n - 1).factorial = (n - 1) * (n - 2).factorial := fact_pred (n - 1) (by omega)
    have h2 : (n - 2).factorial = (n - 2) * (n - 3).factorial := fact_pred (n - 2) (by omega)
    rw [h1, h2]; ring
  have hn2 : (n - 2).factorial = (n - 2) * (n - 3).factorial :=
    fact_pred (n - 2) (by omega)
  have hcoeff : 2 * ((n - 1) * (n - 2)) + 4 * (n - 2) + 6 * (n - 5) ≤
      3 * ((n - 1) * (n - 2)) := by
    have := coeff_bound n hn
    omega
  have hmain :
      2 * (n - 1).factorial + 4 * (n - 2).factorial + 6 * (n - 5) * (n - 3).factorial ≤
        3 * (n - 1).factorial := by
    rw [hn1, hn2]
    have := Nat.mul_le_mul_right (n - 3).factorial hcoeff
    convert this using 1 <;> ring
  -- The current expression is right-associated
  have hgoal :
      (n - 1).factorial + (2 * (n - 2).factorial + (2 * (n - 2).factorial +
        ((n - 1).factorial + S))) ≤ 3 * (n - 1).factorial := by
    have : (n - 1).factorial + (2 * (n - 2).factorial + (2 * (n - 2).factorial +
        ((n - 1).factorial + S))) =
        2 * (n - 1).factorial + 4 * (n - 2).factorial + S := by ring
    rw [this]
    have : 2 * (n - 1).factorial + 4 * (n - 2).factorial + S ≤
        2 * (n - 1).factorial + 4 * (n - 2).factorial +
          (n - 5) * (6 * (n - 3).factorial) := by gcongr
    refine le_trans this ?_
    have : (n - 5) * (6 * (n - 3).factorial) = 6 * (n - 5) * (n - 3).factorial := by ring
    rw [this]
    exact hmain
  exact hgoal

lemma W_le_two_small :
    (List.range 8).all (fun n =>
      (List.range 8).all (fun k => decide (W n k ≤ 2 * n.factorial))) = true := by
  native_decide

lemma W_le_two_of_le_seven (n k : ℕ) (hn : n ≤ 7) :
    W n k ≤ 2 * n.factorial := by
  have hall := List.all_eq_true.mp W_le_two_small
  have hn' : n ∈ List.range 8 := by simp [List.mem_range]; omega
  have hk' : min n k ∈ List.range 8 := by simp [List.mem_range]; omega
  have := List.all_eq_true.mp (hall n hn') (min n k) hk'
  have : W n (min n k) ≤ 2 * n.factorial := decide_eq_true_eq.mp this
  rwa [W_eq_min]

lemma W_le_two_factorial : ∀ n k, W n k ≤ 2 * n.factorial := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ihn =>
    intro k
    by_cases hn7 : n ≤ 7
    · exact W_le_two_of_le_seven n k hn7
    · have hn8 : 8 ≤ n := by omega
      have hn0 : 0 < n := by omega
      have hmono : W n k ≤ W n n := by
        cases le_total k n with
        | inl h => exact W_mono_right h
        | inr h => rw [W_eq_of_ge h]
      refine le_trans hmono ?_
      rw [W_self n hn0]
      have hsum : W n (n - 1) =
          ∑ j ∈ Icc 1 (n - 1), j.factorial * W (n - j) (j - 1) :=
        W_pred_eq_sum n hn0
      have hbound :
          ∑ j ∈ Icc 1 (n - 1), j.factorial * W (n - j) (j - 1) ≤
            ∑ j ∈ Icc 1 (n - 1), j.factorial * (2 * (n - j).factorial) := by
        apply sum_le_sum
        intro j hj
        simp [mem_Icc] at hj
        have hjt : n - j < n := Nat.sub_lt hn0 (by omega)
        exact Nat.mul_le_mul_left _ (ihn (n - j) hjt (j - 1))
      have hpair :
          ∑ j ∈ Icc 1 (n - 1), j.factorial * (2 * (n - j).factorial) =
            2 * ∑ j ∈ Icc 1 (n - 1), j.factorial * (n - j).factorial := by
        have : ∀ j, j.factorial * (2 * (n - j).factorial) =
            2 * (j.factorial * (n - j).factorial) := by intro; ring
        simp_rw [this, ← mul_sum]
      have h3 := sum_fact_pair_le n hn8
      have : W n (n - 1) ≤ 6 * (n - 1).factorial := by
        calc
          W n (n - 1) = ∑ j ∈ Icc 1 (n - 1), j.factorial * W (n - j) (j - 1) := hsum
          _ ≤ ∑ j ∈ Icc 1 (n - 1), j.factorial * (2 * (n - j).factorial) := hbound
          _ = 2 * ∑ j ∈ Icc 1 (n - 1), j.factorial * (n - j).factorial := hpair
          _ ≤ 2 * (3 * (n - 1).factorial) := Nat.mul_le_mul_left _ h3
          _ = 6 * (n - 1).factorial := by ring
      have : n.factorial + W n (n - 1) ≤ 2 * n.factorial := by
        have h6 : n.factorial + 6 * (n - 1).factorial ≤ 2 * n.factorial := by
          have hnfact : n.factorial = n * (n - 1).factorial := fact_pred n (by omega)
          rw [hnfact]
          have : 6 ≤ n := by omega
          have := Nat.mul_le_mul_right (n - 1).factorial this
          -- n * (n-1)! + 6*(n-1)! ≤ 2n*(n-1)!
          -- (n+6) ≤ 2n
          have : n * (n - 1).factorial + 6 * (n - 1).factorial =
              (n + 6) * (n - 1).factorial := by ring
          rw [this]
          have : 2 * (n * (n - 1).factorial) = (2 * n) * (n - 1).factorial := by ring
          rw [this]
          exact Nat.mul_le_mul_right _ (by omega)
        exact le_trans (Nat.add_le_add_left ‹_› _) h6
      exact this


def checkWsucc (M : ℕ) : Bool :=
  (List.range (M + 1)).all fun m =>
    decide (W (m + 1) m ≤ 2 * m.factorial)

lemma checkWsucc_150 : checkWsucc 150 = true := by native_decide

lemma W_succ_self_le_of_le_80 (m : ℕ) (hm : m ≤ 150) :
    W (m + 1) m ≤ 2 * m.factorial := by
  have hall := List.all_eq_true.mp checkWsucc_150
  have hm' : m ∈ List.range 151 := by simp [List.mem_range]; omega
  exact decide_eq_true_eq.mp (hall m hm')
