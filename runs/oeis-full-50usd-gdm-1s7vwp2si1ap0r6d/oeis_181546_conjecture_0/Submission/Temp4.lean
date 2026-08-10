import FormalConjectures.Util.ProblemImports

open Filter Asymptotics Real

def F (n L : ℕ) : ℕ :=
  Finset.sum (Finset.range (n / 2 + 1)) fun k => ((n-k).choose k) ^ L


noncomputable def limit_value (L : ℕ) : ℝ :=
  let fib_L : ℝ := Nat.fib L
  let lucas_L : ℝ := (lucasNumber L : ℤ)
  (fib_L * sqrt 5 + lucas_L) / 2

theorem F_one_eq_fib (n : ℕ) : F n 1 = Nat.fib (n + 1) := by
  -- F n 1 = ∑ k ∈ range (n / 2 + 1), (n-k).choose k
  have hF1 : F n 1 = ∑ k ∈ Finset.range (n / 2 + 1), (n-k).choose k := by
    simp [F]
  rw [hF1]
  rw [Nat.fib_succ_eq_sum_choose]
  -- Now we have ∑ k ∈ range (n / 2 + 1), (n-k).choose k = ∑ p ∈ antidiagonal n, p.1.choose p.2
  -- First, swap the antidiagonal
  have h_swap : ∑ p ∈ Finset.antidiagonal n, p.1.choose p.2 = ∑ p ∈ Finset.antidiagonal n, p.swap.1.choose p.swap.2 := by
    rw [← Finset.Nat.sum_antidiagonal_swap]
  rw [h_swap]
  -- Since p.swap.1 = p.2 and p.swap.2 = p.1
  have h_swap_eq : (fun p : ℕ × ℕ => p.swap.1.choose p.swap.2) = (fun p : ℕ × ℕ => p.2.choose p.1) := by
    ext p
    rfl
  rw [h_swap_eq]
  -- Now use Finset.Nat.sum_antidiagonal_eq_sum_range_succ
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => y.choose x) n]
  -- Now we have ∑ k ∈ Finset.range n.succ, (n-k).choose k
  -- Let's split the sum using Finset.sum_range_add
  have h_split_eq : n.succ = (n / 2 + 1) + (n - n / 2) := by omega
  -- We want to rewrite Finset.range n.succ as Finset.range ((n / 2 + 1) + (n - n / 2))
  have h_rw_range : Finset.range n.succ = Finset.range ((n / 2 + 1) + (n - n / 2)) := by rw [h_split_eq]
  rw [h_rw_range]
  rw [Finset.sum_range_add (fun k => (n-k).choose k) (n / 2 + 1) (n - n / 2)]
  -- We want to show the second term of the addition is 0
  have h_second_zero : ∑ x ∈ Finset.range (n - n / 2), (n - (n / 2 + 1 + x)).choose (n / 2 + 1 + x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    apply Nat.choose_eq_zero_of_lt
    omega
  rw [h_second_zero, add_zero]


lemma lucasNumber_recurrence (n : ℕ) : lucasNumber (n + 2) = lucasNumber (n + 1) + lucasNumber n := by
  simp [lucasNumber, LucasSequence.V]

lemma fib_recurrence (n : ℕ) : (Nat.fib (n + 2) : ℝ) = (Nat.fib (n + 1) : ℝ) + (Nat.fib n : ℝ) := by
  rw [Nat.fib_add_two]
  push_cast
  ring

lemma goldenRatio_recurrence (n : ℕ) : Real.goldenRatio ^ (n + 2) = Real.goldenRatio ^ (n + 1) + Real.goldenRatio ^ n := by
  have h_sq := Real.goldenRatio_sq
  calc Real.goldenRatio ^ (n + 2) = Real.goldenRatio ^ n * Real.goldenRatio ^ 2 := by ring
  _ = Real.goldenRatio ^ n * (Real.goldenRatio + 1) := by rw [h_sq]
  _ = Real.goldenRatio ^ (n + 1) + Real.goldenRatio ^ n := by ring

lemma limit_value_eq_goldenRatio_pow (L : ℕ) : limit_value L = Real.goldenRatio ^ L := by
  refine Nat.strong_induction_on L ?_
  intro L ih
  cases L with
  | zero =>
    simp [limit_value, lucasNumber, LucasSequence.V]
  | succ L =>
    cases L with
    | zero =>
      unfold limit_value Real.goldenRatio
      simp [lucasNumber, LucasSequence.V]
      ring
    | succ L =>
      have h_rec_lim : limit_value (L + 2) = limit_value (L + 1) + limit_value L := by
        unfold limit_value
        rw [fib_recurrence L, lucasNumber_recurrence L]
        push_cast
        ring
      rw [h_rec_lim]
      have ih1 := ih (L + 1) (by omega)
      have ih2 := ih L (by omega)
      rw [ih1, ih2]
      exact (goldenRatio_recurrence L).symm


open scoped goldenRatio

theorem oeis_181546_conjecture_0_one :
    Tendsto (fun n => (F (n+1) 1 : ℝ) / (F n 1 : ℝ)) atTop (nhds (limit_value 1)) := by
  have h_eq (n : ℕ) : ((F (n+1) 1 : ℝ) / (F n 1 : ℝ)) = (Nat.fib (n + 2) : ℝ) / (Nat.fib (n + 1) : ℝ) := by
    rw [F_one_eq_fib, F_one_eq_fib]
  simp_rw [h_eq]
  rw [limit_value_eq_goldenRatio_pow 1]
  simp only [pow_one]
  -- we want to use tendsto_fib_succ_div_fib_atTop
  -- which is Tendsto (fun n => (Nat.fib (n+1) / Nat.fib n : ℝ)) atTop (nhds Real.goldenRatio)
  have h_shift : Tendsto (fun n => (Nat.fib (n + 1 + 1) / Nat.fib (n + 1) : ℝ)) atTop (nhds Real.goldenRatio) := by
    exact (tendsto_add_atTop_iff_nat 1).mpr tendsto_fib_succ_div_fib_atTop
  -- since n + 1 + 1 = n + 2
  have h_subst : (fun n => (Nat.fib (n + 1 + 1) / Nat.fib (n + 1) : ℝ)) = (fun n => (Nat.fib (n + 2) : ℝ) / (Nat.fib (n + 1) : ℝ)) := by
    ext n
    have : n + 1 + 1 = n + 2 := by omega
    rw [this]
  rw [← h_subst]
  exact h_shift

