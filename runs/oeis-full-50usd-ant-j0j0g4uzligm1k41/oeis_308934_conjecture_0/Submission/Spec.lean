import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A308934: Number of ways to write $n$ as $(2^a 3^b)^2 + (2^c 3^d)^2 + x^2 + 2 y^2$,
where $a, b, c, d, x, y$ are nonnegative integers with $2^a 3^b \ge 2^c 3^d$.
-/
def A308934 (n : ℕ) : ℕ :=
  -- Note: Nat.log b n in Lean is $\lfloor \log_b n \rfloor$.
  -- Since $2^{2a} \le n$, $a \le \lfloor \log_2 n / 2 \rfloor$.
  let max_e2 := (Nat.log 2 n / 2) + 1
  let max_e3 := (Nat.log 3 n / 2) + 1

  -- Maximum value for y: $2y^2 \le n \implies y \le \sqrt{n/2}$.
  let max_y := Nat.sqrt (n / 2)

  -- Helper function for the base of the squares $2^k 3^l$.
  let r (k l : ℕ) : ℕ := (2^k * 3^l)

  -- The condition for $m$ to be a square is that its integer square root squared equals $m$.
  let is_square (m : ℕ) : Prop := (Nat.sqrt m) ^ 2 = m

  -- The overall count is a sum over all valid exponents a, b, c, d.
  Finset.sum (range max_e2) fun a =>
    Finset.sum (range max_e3) fun b =>
      let r_val := r a b

      Finset.sum (range max_e2) fun c =>
        Finset.sum (range max_e3) fun d =>
          let s_val := r c d

          -- Enforce the condition $2^a 3^b \geq 2^c 3^d$.
          if r_val < s_val then 0 else

          -- Pruning: if $r^2 + s^2 > n$.
          if r_val^2 + s_val^2 > n then 0 else

          -- Count the number of valid $y$'s.
          Finset.card $ Finset.filter (fun y =>
            let k := r_val^2 + s_val^2 + 2 * y^2

            -- Check $r^2 + s^2 + 2y^2 \le n$, and the remainder $n - k$ is a square $x^2$.
            k ≤ n ∧ is_square (n - k)
          ) (range (max_y + 1))

/-!
## Towards A308934 (Zhi-Wei Sun's conjecture)

The conjecture asserts `A308934 n > 0` for all `n > 1`, i.e. every `n > 1` admits a
representation `n = (2^a 3^b)^2 + (2^c 3^d)^2 + x^2 + 2 y^2`.

We formalise the reduction in rigorous, self-contained steps.

* `IsRepr n` packages the existence of such a representation.
* `repr_imp_pos` : a representation forces the counting function to be positive
  (all the index/range bounds in the definition are met).
* `reduction4`, `reduction9` : representability is preserved by multiplication by `4` and `9`
  (scale every base by `2` resp. `3`, and `x, y` by `2` resp. `3`).  Hence the problem reduces
  to *primitive* `n` (those with `4 ∤ n` and `9 ∤ n`).
* `isRepr_primitive` : every primitive `n ≥ 2` is representable — the arithmetic core.
-/

/-- There is a representation of `n` of the required shape. -/
def IsRepr (n : ℕ) : Prop :=
  ∃ a b c d x y : ℕ, 2^c * 3^d ≤ 2^a * 3^b ∧
    n = (2^a*3^b)^2 + (2^c*3^d)^2 + x^2 + 2*y^2

private lemma exp2_bound {n e : ℕ} (h : (2^e)^2 ≤ n) : e ≤ Nat.log 2 n / 2 := by
  rcases Nat.eq_zero_or_pos n with hz | hn
  · subst hz; have := pow_pos (by norm_num : (0:ℕ)<2) e
    simp only [Nat.le_zero] at h; nlinarith [h]
  · rw [Nat.le_div_iff_mul_le (by norm_num)]
    have : 2 ^ (e*2) ≤ n := by rw [pow_mul]; simpa [pow_mul] using h
    exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 this

private lemma exp3_bound {n e : ℕ} (h : (3^e)^2 ≤ n) : e ≤ Nat.log 3 n / 2 := by
  rcases Nat.eq_zero_or_pos n with hz | hn
  · subst hz; have := pow_pos (by norm_num : (0:ℕ)<3) e
    simp only [Nat.le_zero] at h; nlinarith [h]
  · rw [Nat.le_div_iff_mul_le (by norm_num)]
    have : 3 ^ (e*2) ≤ n := by rw [pow_mul]; simpa [pow_mul] using h
    exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 this

private lemma sub_le_prod_sq2 (a b : ℕ) : (2^a)^2 ≤ (2^a*3^b)^2 :=
  Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by positivity)) 2
private lemma sub_le_prod_sq3 (a b : ℕ) : (3^b)^2 ≤ (2^a*3^b)^2 :=
  Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (by positivity)) 2

/-- A representation of `n` witnesses positivity of the counting function `A308934 n`. -/
theorem repr_imp_pos {n : ℕ} (h : IsRepr n) : 0 < A308934 n := by
  obtain ⟨a, b, c, d, x, y, hle, he⟩ := h
  have hRle : (2^a*3^b)^2 ≤ n := by rw [he]; nlinarith [sq_nonneg x, sq_nonneg ((2:ℕ)^c*3^d)]
  have hSle : (2^c*3^d)^2 ≤ n := by rw [he]; nlinarith [sq_nonneg x]
  have ha : a ≤ Nat.log 2 n / 2 := exp2_bound (le_trans (sub_le_prod_sq2 a b) hRle)
  have hb : b ≤ Nat.log 3 n / 2 := exp3_bound (le_trans (sub_le_prod_sq3 a b) hRle)
  have hc : c ≤ Nat.log 2 n / 2 := exp2_bound (le_trans (sub_le_prod_sq2 c d) hSle)
  have hd : d ≤ Nat.log 3 n / 2 := exp3_bound (le_trans (sub_le_prod_sq3 c d) hSle)
  have hyle : y ≤ Nat.sqrt (n/2) := by
    rw [Nat.le_sqrt]
    have h1 : 2 * y^2 ≤ n := by
      rw [he]; nlinarith [sq_nonneg ((2:ℕ)^a*3^b), sq_nonneg ((2:ℕ)^c*3^d), sq_nonneg x]
    have h2 : y^2 ≤ n/2 := by rw [Nat.le_div_iff_mul_le (by norm_num)]; nlinarith [h1]
    nlinarith [h2, sq_nonneg y]
  set MY := Nat.sqrt (n/2) with hMY
  have hkle : (2^a*3^b)^2 + (2^c*3^d)^2 + 2 * y^2 ≤ n := by rw [he]; nlinarith [sq_nonneg x]
  have hsq : Nat.sqrt (n - ((2^a*3^b)^2 + (2^c*3^d)^2 + 2 * y^2)) ^ 2
      = n - ((2^a*3^b)^2 + (2^c*3^d)^2 + 2 * y^2) := by
    have : n - ((2^a*3^b)^2 + (2^c*3^d)^2 + 2 * y^2) = x^2 := by rw [he]; omega
    rw [this, Nat.sqrt_eq']
  have hymem : y ∈ Finset.filter (fun y =>
      ((2^a*3^b)^2 + (2^c*3^d)^2 + 2 * y^2) ≤ n ∧
      (Nat.sqrt (n - ((2^a*3^b)^2 + (2^c*3^d)^2 + 2 * y^2)))^2
        = n - ((2^a*3^b)^2 + (2^c*3^d)^2 + 2 * y^2))
      (range (MY + 1)) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hkle, hsq⟩
  have hRS : (2^a*3^b)^2 + (2^c*3^d)^2 ≤ n := by nlinarith [hkle, sq_nonneg y]
  show 0 < A308934 n
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _)
    ⟨a, mem_range.mpr (show a < Nat.log 2 n/2+1 by omega), ?_⟩
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _)
    ⟨b, mem_range.mpr (show b < Nat.log 3 n/2+1 by omega), ?_⟩
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _)
    ⟨c, mem_range.mpr (show c < Nat.log 2 n/2+1 by omega), ?_⟩
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _)
    ⟨d, mem_range.mpr (show d < Nat.log 3 n/2+1 by omega), ?_⟩
  simp only []
  rw [if_neg (by omega), if_neg (by omega)]
  exact Finset.card_pos.mpr ⟨y, hymem⟩

/-- Representability is preserved under multiplication by `4`
(scale each base by `2` and `x, y` by `2`). -/
theorem reduction4 {m : ℕ} (h : IsRepr m) : IsRepr (4*m) := by
  obtain ⟨a,b,c,d,x,y,hle,he⟩ := h
  exact ⟨a+1,b,c+1,d,2*x,2*y, by
    rw [show 2^(c+1)*3^d = 2*(2^c*3^d) by ring, show 2^(a+1)*3^b = 2*(2^a*3^b) by ring]
    exact Nat.mul_le_mul_left 2 hle, by subst he; ring⟩

/-- Representability is preserved under multiplication by `9`
(scale each base by `3` and `x, y` by `3`). -/
theorem reduction9 {m : ℕ} (h : IsRepr m) : IsRepr (9*m) := by
  obtain ⟨a,b,c,d,x,y,hle,he⟩ := h
  exact ⟨a,b+1,c,d+1,3*x,3*y, by
    rw [show 2^c*3^(d+1) = 3*(2^c*3^d) by ring, show 2^a*3^(b+1) = 3*(2^a*3^b) by ring]
    exact Nat.mul_le_mul_left 3 hle, by subst he; ring⟩

theorem isRepr_4 : IsRepr 4 := ⟨0,0,0,0,0,1, by norm_num, by norm_num⟩
theorem isRepr_9 : IsRepr 9 := ⟨1,0,1,0,1,0, by norm_num, by norm_num⟩

/-- **Arithmetic core.** Every primitive `n ≥ 2` (i.e. `4 ∤ n` and `9 ∤ n`) is representable. -/
theorem isRepr_primitive {n : ℕ} (hn : 2 ≤ n) (h4 : ¬ 4 ∣ n) (h9 : ¬ 9 ∣ n) : IsRepr n := by
  sorry

/-- Every `n ≥ 2` is representable, by strong induction using the `4`- and `9`-reductions. -/
theorem isRepr_all : ∀ n, 2 ≤ n → IsRepr n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn
    by_cases h4 : 4 ∣ n
    · obtain ⟨m, rfl⟩ := h4
      rcases Nat.lt_or_ge m 2 with hm | hm
      · interval_cases m
        · omega
        · simpa using isRepr_4
      · exact (by simpa using reduction4 (IH m (by omega) hm) : IsRepr (4*m))
    · by_cases h9 : 9 ∣ n
      · obtain ⟨m, rfl⟩ := h9
        rcases Nat.lt_or_ge m 2 with hm | hm
        · interval_cases m
          · omega
          · simpa using isRepr_9
        · exact (by simpa using reduction9 (IH m (by omega) hm) : IsRepr (9*m))
      · exact isRepr_primitive hn h4 h9

/-- A308934 Conjecture 1: a(n) > 0 for all n > 1. -/
theorem oeis_308934_conjecture_0 (n : ℕ) (hn : n > 1) : A308934 n > 0 :=
  repr_imp_pos (isRepr_all n hn)


