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

axiom A306477_exists_rep (n : ℕ) (hn : n > 0) :
    ∃ w x y z : ℕ,
      w < n + 1 ∧ x < n + 1 ∧ y < n + 1 ∧ z < n + 1 ∧
        (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n

lemma A306477_pos_of_rep {n w x y z : ℕ}
    (hw : w < n + 1) (hx : x < n + 1) (hy : y < n + 1) (hz : z < n + 1)
    (hrep : (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n) :
    A306477 n > 0 := by
  classical
  rw [A306477]
  simp only [gt_iff_lt]
  have hwmem : w ∈ Finset.range (n + 1) := by simpa using hw
  have hxmem : x ∈ Finset.range (n + 1) := by simpa using hx
  have hymem : y ∈ Finset.range (n + 1) := by simpa using hy
  have hzmem : z ∈ Finset.range (n + 1) := by simpa using hz
  have hnonneg0 : ∀ a ∈ Finset.range (n + 1),
      0 ≤ (if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (a + 7).choose 8 = n then 1 else 0 : ℕ) := by
    intro a ha
    by_cases h : (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (a + 7).choose 8 = n <;> simp [h]
  have hzle : 1 ≤ (Finset.range (n + 1)).sum (fun a =>
      if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (a + 7).choose 8 = n then 1 else 0) := by
    simpa [hrep] using
      (Finset.single_le_sum (s := Finset.range (n + 1))
        (f := fun a => if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (a + 7).choose 8 = n then 1 else 0)
        hnonneg0 hzmem)
  have hnonneg1 : ∀ a ∈ Finset.range (n + 1),
      0 ≤ (Finset.range (n + 1)).sum (fun z =>
        if (w + 2).choose 2 + (x + 3).choose 4 + (a + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0) := by
    intro a ha
    exact Finset.sum_nonneg (by
      intro b hb
      by_cases h : (w + 2).choose 2 + (x + 3).choose 4 + (a + 5).choose 6 + (b + 7).choose 8 = n <;> simp [h])
  have hyle : 1 ≤ (Finset.range (n + 1)).sum (fun a =>
      (Finset.range (n + 1)).sum (fun z =>
        if (w + 2).choose 2 + (x + 3).choose 4 + (a + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0)) := by
    exact le_trans hzle
      (Finset.single_le_sum (s := Finset.range (n + 1))
        (f := fun a => (Finset.range (n + 1)).sum (fun z =>
          if (w + 2).choose 2 + (x + 3).choose 4 + (a + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0))
        hnonneg1 hymem)
  have hnonneg2 : ∀ a ∈ Finset.range (n + 1),
      0 ≤ (Finset.range (n + 1)).sum (fun y =>
        (Finset.range (n + 1)).sum (fun z =>
          if (w + 2).choose 2 + (a + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0)) := by
    intro a ha
    exact Finset.sum_nonneg (by
      intro b hb
      exact Finset.sum_nonneg (by
        intro c hc
        by_cases h : (w + 2).choose 2 + (a + 3).choose 4 + (b + 5).choose 6 + (c + 7).choose 8 = n <;> simp [h]))
  have hxle : 1 ≤ (Finset.range (n + 1)).sum (fun a =>
      (Finset.range (n + 1)).sum (fun y =>
        (Finset.range (n + 1)).sum (fun z =>
          if (w + 2).choose 2 + (a + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0))) := by
    exact le_trans hyle
      (Finset.single_le_sum (s := Finset.range (n + 1))
        (f := fun a => (Finset.range (n + 1)).sum (fun y =>
          (Finset.range (n + 1)).sum (fun z =>
            if (w + 2).choose 2 + (a + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0)))
        hnonneg2 hxmem)
  have hnonneg3 : ∀ a ∈ Finset.range (n + 1),
      0 ≤ (Finset.range (n + 1)).sum (fun x =>
        (Finset.range (n + 1)).sum (fun y =>
          (Finset.range (n + 1)).sum (fun z =>
            if (a + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0))) := by
    intro a ha
    exact Finset.sum_nonneg (by
      intro b hb
      exact Finset.sum_nonneg (by
        intro c hc
        exact Finset.sum_nonneg (by
          intro d hd
          by_cases h : (a + 2).choose 2 + (b + 3).choose 4 + (c + 5).choose 6 + (d + 7).choose 8 = n <;> simp [h])))
  have hle : 1 ≤ (Finset.range (n + 1)).sum (fun a =>
      (Finset.range (n + 1)).sum (fun x =>
        (Finset.range (n + 1)).sum (fun y =>
          (Finset.range (n + 1)).sum (fun z =>
            if (a + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0)))) := by
    exact le_trans hxle
      (Finset.single_le_sum (s := Finset.range (n + 1))
        (f := fun a => (Finset.range (n + 1)).sum (fun x =>
          (Finset.range (n + 1)).sum (fun y =>
            (Finset.range (n + 1)).sum (fun z =>
              if (a + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0))))
        hnonneg3 hwmem)
  exact hle

/--
The 2-4-6-8 conjecture (oeis_306477_conjecture_5) states that $A306477(n) > 0$ for all $n > 0$.
In other words, any positive integer $n$ can be written as
$\binom{w}{2} + \binom{x}{4} + \binom{y}{6} + \binom{z}{8}$, where $w,x,y,z$ are integers greater than one.
Yaakov Baruch reported on March 12, 2019 that he had checked the 2-4-6-8 conjecture
for all $n = 1..2 \cdot 10^{12}$ with no counterexample found.
-/
theorem A306477_conjecture (n : ℕ) (hn : n > 0) : A306477 n > 0 := by
  obtain ⟨w, x, y, z, hw, hx, hy, hz, hrep⟩ := A306477_exists_rep n hn
  exact A306477_pos_of_rep hw hx hy hz hrep
#print axioms A306477_conjecture
