import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 1000000

open List Finset Nat

#check Nat.sqrt_le
#check Nat.lt_succ_sqrt
#check Nat.le_sqrt
#check Nat.sqrt_lt
#check Nat.digits_add
#check Nat.digits_of_lt

example : ¬ (((Nat.digits 4 44).toFinset.card) ≤ 2) := by
  native_decide

example : (Nat.digits 4 44) = [0,3,2] := by
  native_decide


def A306424_condition (k : ℕ) : Prop :=
  ∀ b : ℕ, 3 ≤ b ∧ b < k → ((Nat.digits b k).toFinset.card) ≤ 2

example : A306424_condition 43 := by
  intro b hb
  have hlow : 3 ≤ b := hb.1
  have hhigh : b ≤ 42 := Nat.le_of_lt_succ hb.2
  interval_cases b <;> native_decide



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
    simp [hrq, hr1, hq1, Ne.symm hrq, Ne.symm hr1, Ne.symm hq1]
  rw [hdigits, hcard]
  norm_num

example (n x : ℕ) (hn : 20 ≤ n) (hx0 : x = 0) :
    ¬ ((Nat.digits (n-3) (n*n + x)).toFinset.card ≤ 2) := by
  subst x
  apply bad_digits_of_eq (b:=n-3) (r:=9) (q:=6)
  · omega
  · omega
  · omega
  · have hsub : n - 3 + 3 = n := by omega
    nlinarith
  · omega
  · omega
  · omega


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


example (n x : ℕ) (hn : 20 ≤ n) (hx2 : 2 ≤ x) (hxn : x < n) :
    ¬ ((Nat.digits n (n*n + x)).toFinset.card ≤ 2) := by
  apply bad_digits_of_eq (b:=n) (r:=x) (q:=0)
  · omega
  · omega
  · omega
  · ring
  · omega
  · omega
  · omega

example (n x : ℕ) (hn : 20 ≤ n) (hxn : n ≤ x) (hxhi : x ≤ 2*n - 4) (hxne : x ≠ n + 1) :
    ¬ ((Nat.digits (n-1) (n*n + x)).toFinset.card ≤ 2) := by
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
    · have hb_le_n : n - 3 ≤ n := by omega
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
    · have hb_le_n : n - 2 ≤ n := by omega
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
    · nlinarith [hn20, show n*n ≤ k from hn_sq]
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
    · have hb_le_n : n - 2 ≤ n := by omega
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
    · have hb_le_n : n - 1 ≤ n := by omega
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
    · have hb_le_n : n - 1 ≤ n := by omega
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
  · refine ⟨n-3, ?_, ?_, ?_⟩
    · omega
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
  · refine ⟨n-3, ?_, ?_, ?_⟩
    · omega
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
