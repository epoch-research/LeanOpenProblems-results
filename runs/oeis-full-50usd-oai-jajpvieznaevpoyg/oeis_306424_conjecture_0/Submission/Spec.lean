import FormalConjectures.Util.ProblemImports

open List Finset Nat


/--
A306424: Numbers $k$ such that the base $b$ expansion of $k$ for each $b = 3..k-1$ never contains more than two distinct digits.
-/
def A306424_condition (k : ℕ) : Prop :=
  -- The bases $b$ range over $3 \le b \le k-1$, expressed as $3 \le b$ and $b < k$.
  ∀ b : ℕ, 3 ≤ b ∧ b < k → ((Nat.digits b k).toFinset.card) ≤ 2

/--
The sequence A306424: Numbers $k$ such that the base $b$ expansion of $k$ for each $b = 3..k-1$ never contains more than two distinct digits.
-/
noncomputable def a (n : ℕ) : ℕ := n.nth A306424_condition


set_option maxHeartbeats 1000000

lemma bad_digits_of_eq (b k r q : ℕ) (hb : 1 < b) (hr : r < b) (hq : q < b)
    (hk : k = r + b * (q + b)) (hrq : r ≠ q) (hr1 : r ≠ 1) (hq1 : q ≠ 1) :
    ¬ ((Nat.digits b k).toFinset.card ≤ 2) := by
  have hdigits : Nat.digits b k = [r, q, 1] := by
    rw [hk]
    rw [Nat.digits_add b hb r (q + b) hr (Or.inr (by omega))]
    have hqb : q + b = q + b * 1 := by omega
    rw [hqb]
    rw [Nat.digits_add b hb q 1 hq (Or.inr (by omega))]
    rw [Nat.digits_of_lt b 1 (by omega) hb]
  have hcard : ([r, q, 1] : List ℕ).toFinset.card = 3 := by
    simp [hrq, hr1, hq1]
  rw [hdigits, hcard]
  norm_num

lemma top3_calc (m : ℕ) (hm : 1 ≤ m) :
    (m+1)*(m+1) + (2*(m+1)-3) = 0 + m*(4+m) := by
  have hsub : (2*(m+1)-3) + 3 = 2*(m+1) := by omega
  nlinarith

lemma top2_calc (m : ℕ) (hm : 3 ≤ m) :
    (m+3)*(m+3) + (2*(m+3)-2) = 13 + m*(8+m) := by
  have hsub : (2*(m+3)-2) + 2 = 2*(m+3) := by omega
  nlinarith

lemma top1_calc (m : ℕ) (hm : 3 ≤ m) :
    (m+3)*(m+3) + (2*(m+3)-1) = 14 + m*(8+m) := by
  have hsub : (2*(m+3)-1) + 1 = 2*(m+3) := by omega
  nlinarith

lemma large_witness {k : ℕ} (hk400 : 400 ≤ k) :
    ∃ b : ℕ, 3 ≤ b ∧ b < k ∧ ¬ ((Nat.digits b k).toFinset.card ≤ 2) := by
  let n := Nat.sqrt k
  let x := k - n*n
  have hn_sq : n*n ≤ k := by simpa [n] using Nat.sqrt_le k
  have hk_eq : k = n*n + x := by omega
  have hlt_succ : k < (n+1)*(n+1) := by simpa [n] using Nat.lt_succ_sqrt k
  have hxle : x ≤ 2*n := by
    have h : n*n + x < (n+1)*(n+1) := by simpa [hk_eq] using hlt_succ
    nlinarith
  have hn20 : 20 ≤ n := by
    have h400' : 20*20 ≤ k := by norm_num at hk400 ⊢; exact hk400
    exact (Nat.le_sqrt).2 (by simpa [n] using h400')
  by_cases hx0 : x = 0
  · refine ⟨n-3, by omega, ?_, ?_⟩
    · have hb_le_n : n - 3 ≤ n := Nat.sub_le n 3
      have hn_lt_sq : n < n*n := by nlinarith [hn20]
      exact lt_of_lt_of_le (lt_of_le_of_lt hb_le_n hn_lt_sq) hn_sq
    · rw [hk_eq, hx0]
      exact (show ¬ ((Nat.digits (n-3) (n*n + 0)).toFinset.card ≤ 2) from by
        apply bad_digits_of_eq (b:=n-3) (r:=9) (q:=6)
        · omega
        · omega
        · omega
        · have hsub : n - 3 + 3 = n := by omega
          nlinarith
        · omega
        · omega
        · omega)
  by_cases hx1 : x = 1
  · refine ⟨n-2, by omega, ?_, ?_⟩
    · have hb_le_n : n - 2 ≤ n := Nat.sub_le n 2
      have hn_lt_sq : n < n*n := by nlinarith [hn20]
      exact lt_of_lt_of_le (lt_of_le_of_lt hb_le_n hn_lt_sq) hn_sq
    · rw [hk_eq, hx1]
      exact (show ¬ ((Nat.digits (n-2) (n*n + 1)).toFinset.card ≤ 2) from by
        apply bad_digits_of_eq (b:=n-2) (r:=5) (q:=4)
        · omega
        · omega
        · omega
        · have hsub : n - 2 + 2 = n := by omega
          nlinarith
        · omega
        · omega
        · omega)
  by_cases hxn_lt : x < n
  · refine ⟨n, by omega, ?_, ?_⟩
    · have hn_lt_sq : n < n*n := by nlinarith [hn20]
      exact lt_of_lt_of_le hn_lt_sq hn_sq
    · have hx2 : 2 ≤ x := by omega
      rw [hk_eq]
      apply bad_digits_of_eq (b:=n) (r:=x) (q:=0)
      · omega
      · omega
      · omega
      · ring
      · omega
      · omega
      · omega
  by_cases hxnp1 : x = n + 1
  · refine ⟨n-2, by omega, ?_, ?_⟩
    · have hb_le_n : n - 2 ≤ n := Nat.sub_le n 2
      have hn_lt_sq : n < n*n := by nlinarith [hn20]
      exact lt_of_lt_of_le (lt_of_le_of_lt hb_le_n hn_lt_sq) hn_sq
    · rw [hk_eq, hxnp1]
      apply bad_digits_of_eq (b:=n-2) (r:=7) (q:=5)
      · omega
      · omega
      · omega
      · have hsub : n - 2 + 2 = n := by omega
        nlinarith
      · omega
      · omega
      · omega
  by_cases hxhi : x ≤ 2*n - 4
  · refine ⟨n-1, by omega, ?_, ?_⟩
    · have hb_le_n : n - 1 ≤ n := Nat.sub_le n 1
      have hn_lt_sq : n < n*n := by nlinarith [hn20]
      exact lt_of_lt_of_le (lt_of_le_of_lt hb_le_n hn_lt_sq) hn_sq
    · rw [hk_eq]
      apply bad_digits_of_eq (b:=n-1) (r:=x - n + 2) (q:=3)
      · omega
      · omega
      · omega
      · have hn1 : n - 1 + 1 = n := by omega
        have hxlin : x - n + 2 + n = x + 2 := by omega
        nlinarith
      · omega
      · omega
      · omega
  by_cases hx_top3 : x = 2*n - 3
  · refine ⟨n-1, by omega, ?_, ?_⟩
    · have hb_le_n : n - 1 ≤ n := Nat.sub_le n 1
      have hn_lt_sq : n < n*n := by nlinarith [hn20]
      exact lt_of_lt_of_le (lt_of_le_of_lt hb_le_n hn_lt_sq) hn_sq
    · rw [hk_eq, hx_top3]
      apply bad_digits_of_eq (b:=n-1) (r:=0) (q:=4)
      · omega
      · omega
      · omega
      · let m := n - 1
        have hn1 : n = m + 1 := by omega
        rw [hn1]
        exact top3_calc m (by omega)
      · omega
      · omega
      · omega
  by_cases hx_top2 : x = 2*n - 2
  · refine ⟨n-3, by omega, ?_, ?_⟩
    · have hb_le_n : n - 3 ≤ n := Nat.sub_le n 3
      have hn_lt_sq : n < n*n := by nlinarith [hn20]
      exact lt_of_lt_of_le (lt_of_le_of_lt hb_le_n hn_lt_sq) hn_sq
    · rw [hk_eq, hx_top2]
      apply bad_digits_of_eq (b:=n-3) (r:=13) (q:=8)
      · omega
      · omega
      · omega
      · let m := n - 3
        have hn3 : n = m + 3 := by omega
        rw [hn3]
        exact top2_calc m (by omega)
      · omega
      · omega
      · omega
  by_cases hx_top1 : x = 2*n - 1
  · refine ⟨n-3, by omega, ?_, ?_⟩
    · have hb_le_n : n - 3 ≤ n := Nat.sub_le n 3
      have hn_lt_sq : n < n*n := by nlinarith [hn20]
      exact lt_of_lt_of_le (lt_of_le_of_lt hb_le_n hn_lt_sq) hn_sq
    · rw [hk_eq, hx_top1]
      apply bad_digits_of_eq (b:=n-3) (r:=14) (q:=8)
      · omega
      · omega
      · omega
      · let m := n - 3
        have hn3 : n = m + 3 := by omega
        rw [hn3]
        exact top1_calc m (by omega)
      · omega
      · omega
      · omega
  · have hx2n : x = 2*n := by omega
    refine ⟨n, by omega, ?_, ?_⟩
    · have hn_lt_sq : n < n*n := by nlinarith [hn20]
      exact lt_of_lt_of_le hn_lt_sq hn_sq
    · rw [hk_eq, hx2n]
      apply bad_digits_of_eq (b:=n) (r:=0) (q:=2)
      · omega
      · omega
      · omega
      · ring
      · omega
      · omega
      · omega

lemma not_condition_of_witness {k b : ℕ} (hb : 3 ≤ b ∧ b < k)
    (hbad : ¬ ((Nat.digits b k).toFinset.card ≤ 2)) : ¬ A306424_condition k := by
  intro hk
  exact hbad (hk b hb)

lemma condition_43 : A306424_condition 43 := by
  intro b hb
  have hlow : 3 ≤ b := hb.1
  have hhigh : b ≤ 42 := Nat.le_of_lt_succ hb.2
  interval_cases b <;> norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1]

lemma not_condition_of_gt_43 (k : ℕ) (hk43 : 43 < k) : ¬ A306424_condition k := by
  by_cases hk400 : 400 ≤ k
  · intro hcond
    obtain ⟨b, hb3, hbk, hbad⟩ := large_witness hk400
    exact hbad (hcond b ⟨hb3, hbk⟩)
  · have hk44 : 44 ≤ k := by omega
    have hk399 : k ≤ 399 := by omega
    interval_cases k
    · exact not_condition_of_witness (k:=44) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=45) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=46) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=47) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=48) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=49) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=50) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=51) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=52) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=53) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=54) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=55) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=56) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=57) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=58) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=59) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=60) (b:=6) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=61) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=62) (b:=6) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=63) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=64) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=65) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=66) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=67) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=68) (b:=6) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=69) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=70) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=71) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=72) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=73) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=74) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=75) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=76) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=77) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=78) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=79) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=80) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=81) (b:=6) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=82) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=83) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=84) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=85) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=86) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=87) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=88) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=89) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=90) (b:=6) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=91) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=92) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=93) (b:=7) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=94) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=95) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=96) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=97) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=98) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=99) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=100) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=101) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=102) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=103) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=104) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=105) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=106) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=107) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=108) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=109) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=110) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=111) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=112) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=113) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=114) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=115) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=116) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=117) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=118) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=119) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=120) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=121) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=122) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=123) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=124) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=125) (b:=6) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=126) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=127) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=128) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=129) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=130) (b:=9) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=131) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=132) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=133) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=134) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=135) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=136) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=137) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=138) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=139) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=140) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=141) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=142) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=143) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=144) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=145) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=146) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=147) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=148) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=149) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=150) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=151) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=152) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=153) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=154) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=155) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=156) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=157) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=158) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=159) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=160) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=161) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=162) (b:=6) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=163) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=164) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=165) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=166) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=167) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=168) (b:=8) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=169) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=170) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=171) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=172) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=173) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=174) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=175) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=176) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=177) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=178) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=179) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=180) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=181) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=182) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=183) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=184) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=185) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=186) (b:=6) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=187) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=188) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=189) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=190) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=191) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=192) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=193) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=194) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=195) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=196) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=197) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=198) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=199) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=200) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=201) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=202) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=203) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=204) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=205) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=206) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=207) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=208) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=209) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=210) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=211) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=212) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=213) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=214) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=215) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=216) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=217) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=218) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=219) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=220) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=221) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=222) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=223) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=224) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=225) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=226) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=227) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=228) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=229) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=230) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=231) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=232) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=233) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=234) (b:=6) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=235) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=236) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=237) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=238) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=239) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=240) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=241) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=242) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=243) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=244) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=245) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=246) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=247) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=248) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=249) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=250) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=251) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=252) (b:=7) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=253) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=254) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=255) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=256) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=257) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=258) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=259) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=260) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=261) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=262) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=263) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=264) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=265) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=266) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=267) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=268) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=269) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=270) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=271) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=272) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=273) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=274) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=275) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=276) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=277) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=278) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=279) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=280) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=281) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=282) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=283) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=284) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=285) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=286) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=287) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=288) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=289) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=290) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=291) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=292) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=293) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=294) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=295) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=296) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=297) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=298) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=299) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=300) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=301) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=302) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=303) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=304) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=305) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=306) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=307) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=308) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=309) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=310) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=311) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=312) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=313) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=314) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=315) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=316) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=317) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=318) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=319) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=320) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=321) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=322) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=323) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=324) (b:=6) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=325) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=326) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=327) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=328) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=329) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=330) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=331) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=332) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=333) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=334) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=335) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=336) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=337) (b:=6) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=338) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=339) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=340) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=341) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=342) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=343) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=344) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=345) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=346) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=347) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=348) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=349) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=350) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=351) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=352) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=353) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=354) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=355) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=356) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=357) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=358) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=359) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=360) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=361) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=362) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=363) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=364) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=365) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=366) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=367) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=368) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=369) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=370) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=371) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=372) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=373) (b:=5) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=374) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=375) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=376) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=377) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=378) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=379) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=380) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=381) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=382) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=383) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=384) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=385) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=386) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=387) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=388) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=389) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=390) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=391) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=392) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=393) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=394) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=395) (b:=4) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=396) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=397) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=398) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])
    · exact not_condition_of_witness (k:=399) (b:=3) (by norm_num) (by norm_num [Nat.digits, Nat.digitsAux, Nat.digitsAux0, Nat.digitsAux1])

/--
A306424 Conjecture: The sequence is finite, with 43 being the last term.
-/
theorem oeis_306424_conjecture_0 : A306424_condition 43 ∧ ∀ k : ℕ, 43 < k → ¬ A306424_condition k := by
  constructor
  · exact condition_43
  · exact not_condition_of_gt_43
