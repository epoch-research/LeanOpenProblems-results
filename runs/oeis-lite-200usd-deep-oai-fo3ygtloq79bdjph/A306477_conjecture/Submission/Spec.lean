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
The 2-4-6-8 conjecture (oeis_306477_conjecture_5) states that $A306477(n) > 0$ for all $n > 0$.
In other words, any positive integer $n$ can be written as
$\binom{w}{2} + \binom{x}{4} + \binom{y}{6} + \binom{z}{8}$, where $w,x,y,z$ are integers greater than one.
Yaakov Baruch reported on March 12, 2019 that he had checked the 2-4-6-8 conjecture
for all $n = 1..2 \cdot 10^{12}$ with no counterexample found.
-/
private lemma A306477_le_choose_add_two (w : ℕ) : w ≤ (w + 2).choose 2 := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [show (w + 1 + 2).choose 2 = (w + 2).choose 2 + (w + 2).choose 1 by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.choose_succ_succ (w + 2) 1)]
    have hpos : 1 ≤ (w + 2).choose 1 := Nat.succ_le_of_lt (Nat.choose_pos (by omega))
    omega

private lemma A306477_le_choose_add_four (x : ℕ) : x ≤ (x + 3).choose 4 := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [show (x + 1 + 3).choose 4 = (x + 3).choose 4 + (x + 3).choose 3 by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.choose_succ_succ (x + 3) 3)]
    have hpos : 1 ≤ (x + 3).choose 3 := Nat.succ_le_of_lt (Nat.choose_pos (by omega))
    omega

private lemma A306477_le_choose_add_six (y : ℕ) : y ≤ (y + 5).choose 6 := by
  induction y with
  | zero => simp
  | succ y ih =>
    rw [show (y + 1 + 5).choose 6 = (y + 5).choose 6 + (y + 5).choose 5 by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.choose_succ_succ (y + 5) 5)]
    have hpos : 1 ≤ (y + 5).choose 5 := Nat.succ_le_of_lt (Nat.choose_pos (by omega))
    omega

private lemma A306477_le_choose_add_eight (z : ℕ) : z ≤ (z + 7).choose 8 := by
  induction z with
  | zero => simp
  | succ z ih =>
    rw [show (z + 1 + 7).choose 8 = (z + 7).choose 8 + (z + 7).choose 7 by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.choose_succ_succ (z + 7) 7)]
    have hpos : 1 ≤ (z + 7).choose 7 := Nat.succ_le_of_lt (Nat.choose_pos (by omega))
    omega

private lemma A306477_pos_of_rep {n w x y z : ℕ}
    (hrep : (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 +
      (z + 7).choose 8 = n) : A306477 n > 0 := by
  have hwterm : (w + 2).choose 2 ≤ n := by omega
  have hxterm : (x + 3).choose 4 ≤ n := by omega
  have hyterm : (y + 5).choose 6 ≤ n := by omega
  have hzterm : (z + 7).choose 8 ≤ n := by omega
  have hw : w ∈ Finset.range (n + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((A306477_le_choose_add_two w).trans hwterm)
  have hx : x ∈ Finset.range (n + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((A306477_le_choose_add_four x).trans hxterm)
  have hy : y ∈ Finset.range (n + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((A306477_le_choose_add_six y).trans hyterm)
  have hz : z ∈ Finset.range (n + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((A306477_le_choose_add_eight z).trans hzterm)
  simp only [A306477]
  apply Finset.sum_pos'
  · intro a ha
    positivity
  · refine ⟨w, hw, ?_⟩
    apply Finset.sum_pos'
    · intro a ha
      positivity
    · refine ⟨x, hx, ?_⟩
      apply Finset.sum_pos'
      · intro a ha
        positivity
      · refine ⟨y, hy, ?_⟩
        apply Finset.sum_pos'
        · intro a ha
          positivity
        · refine ⟨z, hz, ?_⟩
          simp [hrep]

theorem A306477_conjecture (n : ℕ) (hn : n > 0) : A306477 n > 0 := by
  sorry
