import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A306477: Number of ways to write $n$ as $\binom{w+2}{2} + \binom{x+3}{4} + \binom{y+5}{6} + \binom{z+7}{8}$
with $w,x,y,z$ nonnegative integers, where $\binom{m}{k}$ denotes the binomial coefficient $\frac{m!}{k!(m-k)!}$.
-/
def A306477 (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  R.sum (fun w =>
    R.sum (fun x =>
      R.sum (fun y =>
        R.sum (fun z =>
          if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0
        )
      )
    )
  )

/--
Conjecture: a(n) > 0 for all n > 0. In other words, any positive integer n can be written as
C(w,2) + C(x,4) + C(y,6) + C(z,8), where w,x,y,z are integers greater than one.
This is also known as "the 2-4-6-8 conjecture".
-/

private lemma choose2_ge_self (x : ℕ) : x ≤ (x + 2).choose 2 := by
  induction x with
  | zero => simp
  | succ x ih =>
      have hpos : 0 < (x + 2).choose 1 := Nat.choose_pos (by omega)
      calc
        x + 1 ≤ (x + 2).choose 2 + 1 := by omega
        _ ≤ (x + 2).choose 1 + (x + 2).choose 2 := by omega
        _ = (x + 3).choose 2 := by
            conv_rhs =>
              rw [show x + 3 = Nat.succ (x + 2) by omega]
              rw [show 2 = Nat.succ 1 by norm_num]
              rw [Nat.choose_succ_succ]
        _ = (x.succ + 2).choose 2 := by rw [show x.succ + 2 = x + 3 by omega]

private lemma choose4_ge_self (x : ℕ) : x ≤ (x + 3).choose 4 := by
  induction x with
  | zero => simp
  | succ x ih =>
      have hpos : 0 < (x + 3).choose 3 := Nat.choose_pos (by omega)
      calc
        x + 1 ≤ (x + 3).choose 4 + 1 := by omega
        _ ≤ (x + 3).choose 3 + (x + 3).choose 4 := by omega
        _ = (x + 4).choose 4 := by
            conv_rhs =>
              rw [show x + 4 = Nat.succ (x + 3) by omega]
              rw [show 4 = Nat.succ 3 by norm_num]
              rw [Nat.choose_succ_succ]
        _ = (x.succ + 3).choose 4 := by rw [show x.succ + 3 = x + 4 by omega]

private lemma choose6_ge_self (x : ℕ) : x ≤ (x + 5).choose 6 := by
  induction x with
  | zero => simp
  | succ x ih =>
      have hpos : 0 < (x + 5).choose 5 := Nat.choose_pos (by omega)
      calc
        x + 1 ≤ (x + 5).choose 6 + 1 := by omega
        _ ≤ (x + 5).choose 5 + (x + 5).choose 6 := by omega
        _ = (x + 6).choose 6 := by
            conv_rhs =>
              rw [show x + 6 = Nat.succ (x + 5) by omega]
              rw [show 6 = Nat.succ 5 by norm_num]
              rw [Nat.choose_succ_succ]
        _ = (x.succ + 5).choose 6 := by rw [show x.succ + 5 = x + 6 by omega]

private lemma choose8_ge_self (x : ℕ) : x ≤ (x + 7).choose 8 := by
  induction x with
  | zero => simp
  | succ x ih =>
      have hpos : 0 < (x + 7).choose 7 := Nat.choose_pos (by omega)
      calc
        x + 1 ≤ (x + 7).choose 8 + 1 := by omega
        _ ≤ (x + 7).choose 7 + (x + 7).choose 8 := by omega
        _ = (x + 8).choose 8 := by
            conv_rhs =>
              rw [show x + 8 = Nat.succ (x + 7) by omega]
              rw [show 8 = Nat.succ 7 by norm_num]
              rw [Nat.choose_succ_succ]
        _ = (x.succ + 7).choose 8 := by rw [show x.succ + 7 = x + 8 by omega]


private theorem two_four_six_eight_representation :
  ∀ n : ℕ, 0 < n →
    ∃ w x y z : ℕ,
      (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n := by
  intro n hn
  sorry


theorem oeis_306477_conjecture_1 : ∀ n : ℕ, 0 < n → 0 < A306477 n := by
  intro n hn
  obtain ⟨w, x, y, z, hsum⟩ := two_four_six_eight_representation n hn
  have hwle : w ≤ n := by
    by_contra h
    have hnltw : n < w := Nat.lt_of_not_ge h
    have hlt : n < (w + 2).choose 2 := lt_of_lt_of_le hnltw (choose2_ge_self w)
    have : n < n := by
      calc
        n < (w + 2).choose 2 := hlt
        _ ≤ (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 := by omega
        _ = n := hsum
    exact (Nat.lt_irrefl n) this
  have hxle : x ≤ n := by
    by_contra h
    have hnltx : n < x := Nat.lt_of_not_ge h
    have hxterm_le_sum : (x + 3).choose 4 ≤
        (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 := by omega
    have hxterm_le_n : (x + 3).choose 4 ≤ n := by simpa [hsum] using hxterm_le_sum
    have hx_gt_n : n < (x + 3).choose 4 := lt_of_lt_of_le hnltx (choose4_ge_self x)
    exact (not_lt_of_ge hxterm_le_n) hx_gt_n
  have hyle : y ≤ n := by
    by_contra h
    have hnlty : n < y := Nat.lt_of_not_ge h
    have hyterm_le_sum : (y + 5).choose 6 ≤
        (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 := by omega
    have hyterm_le_n : (y + 5).choose 6 ≤ n := by simpa [hsum] using hyterm_le_sum
    have hy_gt_n : n < (y + 5).choose 6 := lt_of_lt_of_le hnlty (choose6_ge_self y)
    exact (not_lt_of_ge hyterm_le_n) hy_gt_n
  have hzle : z ≤ n := by
    by_contra h
    have hnltz : n < z := Nat.lt_of_not_ge h
    have hzterm_le_sum : (z + 7).choose 8 ≤
        (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 := by omega
    have hzterm_le_n : (z + 7).choose 8 ≤ n := by simpa [hsum] using hzterm_le_sum
    have hz_gt_n : n < (z + 7).choose 8 := lt_of_lt_of_le hnltz (choose8_ge_self z)
    exact (not_lt_of_ge hzterm_le_n) hz_gt_n
  unfold A306477
  simp only
  let R := Finset.range (n + 1)
  have hwmem : w ∈ R := by simpa [R, Nat.lt_succ_iff] using hwle
  have hxmem : x ∈ R := by simpa [R, Nat.lt_succ_iff] using hxle
  have hymem : y ∈ R := by simpa [R, Nat.lt_succ_iff] using hyle
  have hzmem : z ∈ R := by simpa [R, Nat.lt_succ_iff] using hzle
  have hpos_inner : 0 < ∑ z' ∈ R,
      (if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z' + 7).choose 8 = n then 1 else 0) := by
    refine Finset.sum_pos' ?_ ?_
    · intro z' hz'
      split <;> omega
    · refine ⟨z, hzmem, ?_⟩
      simp [hsum]
  have hpos_y : 0 < ∑ y' ∈ R, ∑ z' ∈ R,
      (if (w + 2).choose 2 + (x + 3).choose 4 + (y' + 5).choose 6 + (z' + 7).choose 8 = n then 1 else 0) := by
    refine Finset.sum_pos' ?_ ?_
    · intro y' hy'
      exact Finset.sum_nonneg (by intro z' hz'; split <;> omega)
    · refine ⟨y, hymem, ?_⟩
      simpa using hpos_inner
  have hpos_x : 0 < ∑ x' ∈ R, ∑ y' ∈ R, ∑ z' ∈ R,
      (if (w + 2).choose 2 + (x' + 3).choose 4 + (y' + 5).choose 6 + (z' + 7).choose 8 = n then 1 else 0) := by
    refine Finset.sum_pos' ?_ ?_
    · intro x' hx'
      exact Finset.sum_nonneg (by intro y' hy'; exact Finset.sum_nonneg (by intro z' hz'; split <;> omega))
    · refine ⟨x, hxmem, ?_⟩
      simpa using hpos_y
  have hpos_w : 0 < ∑ w' ∈ R, ∑ x' ∈ R, ∑ y' ∈ R, ∑ z' ∈ R,
      (if (w' + 2).choose 2 + (x' + 3).choose 4 + (y' + 5).choose 6 + (z' + 7).choose 8 = n then 1 else 0) := by
    refine Finset.sum_pos' ?_ ?_
    · intro w' hw'
      exact Finset.sum_nonneg (by intro x' hx'; exact Finset.sum_nonneg (by intro y' hy'; exact Finset.sum_nonneg (by intro z' hz'; split <;> omega)))
    · refine ⟨w, hwmem, ?_⟩
      simpa using hpos_x
  simpa [R] using hpos_w
