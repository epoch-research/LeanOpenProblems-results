import FormalConjectures.Util.ProblemImports

open Real

/--
A190363: $a(n) = n + \lfloor n \cdot r/t \rfloor + \lfloor n \cdot s/t \rfloor$; $r=1, s=\sqrt{5/4}, t=\sqrt{4/5}$.
The equivalent formula used in implementations is $a(n) = 2n + \lfloor n \cdot \sqrt{5/4} \rfloor + \lfloor n/4 \rfloor$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let n_R : ℝ := n
  let sqrt_expr : ℝ := sqrt (5 / 4)

  -- $\lfloor n \cdot \sqrt{5/4} \rfloor$
  let floor_term_sqrt : ℕ := (Int.floor (n_R * sqrt_expr)).toNat

  -- $\lfloor n/4 \rfloor$ (Natural number division is floor division)
  let floor_term_div : ℕ := n / 4

  2 * n + floor_term_sqrt + floor_term_div

open scoped BigOperators

/-- The set of coefficients $\tilde{c}_i$ for the linear recurrence relation of order 21.
The recurrence is $u(n+21) = \sum_{i=0}^{20} \tilde{c}_i u(n+i)$.
This corresponds to $a(n+21) = a(n+17) + a(n+4) - a(n)$.
The coefficients are $\tilde{c}_0 = -1, \tilde{c}_4 = 1, \tilde{c}_{17} = 1$, and 0 otherwise.
-/
noncomputable def A190363_coeffs : Fin 21 → ℤ :=
  fun i =>
    match i.val with
    | 0 => -1 -- coefficient for a(n)
    | 4 => 1  -- coefficient for a(n+4)
    | 17 => 1 -- coefficient for a(n+17)
    | _ => 0

/-- The linear recurrence structure for A190363 defined over $\mathbb{Z}$. -/
noncomputable def A190363_LR : LinearRecurrence ℤ :=
  LinearRecurrence.mk 21 A190363_coeffs

/-- If $4k^2 \le 5n^2 < 4(k+1)^2$ then $\lfloor n \sqrt{5/4} \rfloor = k$. -/
private lemma floor_sqrt54 (n k : ℕ) (h1 : 4 * k^2 ≤ 5 * n^2) (h2 : 5 * n^2 < 4 * (k+1)^2) :
    ⌊(n : ℝ) * Real.sqrt (5/4)⌋ = (k : ℤ) := by
  have hs : Real.sqrt (5/4) ^ 2 = 5/4 := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) ≤ Real.sqrt (5/4) := Real.sqrt_nonneg _
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have h1' : (4:ℝ) * (k:ℝ)^2 ≤ 5 * (n:ℝ)^2 := by exact_mod_cast h1
  have h2' : (5:ℝ) * (n:ℝ)^2 < 4 * ((k:ℝ)+1)^2 := by exact_mod_cast h2
  rw [Int.floor_eq_iff]
  constructor
  · push_cast
    nlinarith [sq_nonneg ((n:ℝ) * Real.sqrt (5/4) - (k:ℝ)),
      sq_nonneg ((n:ℝ) * Real.sqrt (5/4) + (k:ℝ)), mul_nonneg hn0 hs0]
  · push_cast
    nlinarith [sq_nonneg ((n:ℝ) * Real.sqrt (5/4) + (k:ℝ) + 1), mul_nonneg hn0 hs0]

/-- Explicit evaluation of `a n` given the value `k` of $\lfloor n \sqrt{5/4} \rfloor$. -/
private lemma a_val (n k : ℕ) (h1 : 4 * k^2 ≤ 5 * n^2) (h2 : 5 * n^2 < 4 * (k+1)^2) :
    a n = 2 * n + k + n / 4 := by
  have h := floor_sqrt54 n k h1 h2
  simp only [a, h, Int.toNat_natCast]

/--
The conjectured recurrence for A190363 is **false**: it fails at index $n = 144$
(i.e. at `n = 143` in the shifted sequence `fun n => a (n + 1)`), since
$a(165) = 555$ while $a(161) + a(148) - a(144) = 542 + 498 - 484 = 556$.
This comes from $161 \cdot \sqrt{5/4} = 180.0035\ldots$ being just above an integer
(related to the continued fraction convergent $161/72$ of $\sqrt{5}$).
-/
theorem oeis_190363_conjecture_0.disproof :
    ¬ A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by
  intro h
  have h143 := h 143
  simp only [A190363_LR] at h143
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, A190363_coeffs, Fin.val_zero,
    Fin.val_succ] at h143
  rw [a_val 165 184 (by norm_num) (by norm_num), a_val 144 160 (by norm_num) (by norm_num),
    a_val 148 165 (by norm_num) (by norm_num), a_val 161 180 (by norm_num) (by norm_num)] at h143
  norm_num at h143
