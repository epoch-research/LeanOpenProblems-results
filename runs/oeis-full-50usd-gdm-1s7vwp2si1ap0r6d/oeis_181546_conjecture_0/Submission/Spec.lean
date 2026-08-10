import FormalConjectures.Util.ProblemImports

/--
A181546: $a(n) = \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n-k}{k}^4$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n / 2 + 1)) fun k => ((n-k).choose k) ^ 4

-- The general function F(n, L) mentioned in the conjecture.
def F (n L : ℕ) : ℕ :=
  Finset.sum (Finset.range (n / 2 + 1)) fun k => ((n-k).choose k) ^ L

open Filter Asymptotics Real

noncomputable def limit_value (L : ℕ) : ℝ :=
  let fib_L : ℝ := Nat.fib L
  let lucas_L : ℝ := (lucasNumber L : ℤ)
  (fib_L * sqrt 5 + lucas_L) / 2

lemma add_pow_le_custom (a b L : ℕ) (hL : 1 ≤ L) : a^L + b^L ≤ (a + b)^L := by
  induction L with
  | zero => omega
  | succ L ih =>
    cases L with
    | zero => simp
    | succ L =>
      have h1 : a^(L+2) = a^(L+1) * a := by ring
      have h2 : b^(L+2) = b^(L+1) * b := by ring
      rw [h1, h2]
      have ha : a ≤ a + b := by omega
      have hb : b ≤ a + b := by omega
      have h3 : a^(L+1) * a ≤ a^(L+1) * (a + b) := Nat.mul_le_mul_left (a^(L+1)) ha
      have h4 : b^(L+1) * b ≤ b^(L+1) * (a + b) := Nat.mul_le_mul_left (b^(L+1)) hb
      have h5 : a^(L+2) + b^(L+2) ≤ a^(L+1) * (a + b) + b^(L+1) * (a + b) := by
        rw [h1, h2]
        omega
      have h6 : a^(L+1) * (a + b) + b^(L+1) * (a + b) = (a^(L+1) + b^(L+1)) * (a + b) := by ring
      have ih_spec := ih (by omega)
      have h7 : (a^(L+1) + b^(L+1)) * (a + b) ≤ (a + b)^(L+1) * (a + b) := Nat.mul_le_mul_right (a + b) ih_spec
      have h8 : (a + b)^(L+1) * (a + b) = (a + b)^(L+2) := by ring
      calc
        a^(L+2) + b^(L+2) ≤ a^(L+1) * (a + b) + b^(L+1) * (a + b) := h5
        _ = (a^(L+1) + b^(L+1)) * (a + b) := h6
        _ ≤ (a + b)^(L+1) * (a + b) := h7
        _ = (a + b)^(L+2) := h8

lemma sum_pow_le_sum_pow {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) (L : ℕ) (hL : 1 ≤ L) :
    (∑ k ∈ s, f k ^ L) ≤ (∑ k ∈ s, f k) ^ L := by
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    have : 0^L = 0 := Nat.zero_pow (by omega)
    rw [this]
  · intro x s hx ih
    simp only [Finset.sum_insert hx]
    have h_ih : f x ^ L + (∑ k ∈ s, f k ^ L) ≤ f x ^ L + (∑ k ∈ s, f k) ^ L := by omega
    have h_add := add_pow_le_custom (f x) (∑ k ∈ s, f k) L hL
    omega

theorem F_zero_eq (n : ℕ) : F n 0 = n / 2 + 1 := by
  simp [F]

lemma nat_div_two_le_succ_div_two (n : ℕ) : n / 2 ≤ (n + 1) / 2 := by
  apply Nat.div_le_div_right
  omega

lemma succ_div_two_le_nat_div_two_add_one (n : ℕ) : (n + 1) / 2 ≤ n / 2 + 1 := by
  omega

lemma real_nat_div_two_le_succ_div_two (n : ℕ) : (↑(n / 2) : ℝ) ≤ (↑((n + 1) / 2) : ℝ) := by
  exact (Nat.cast_le (α := ℝ)).mpr (nat_div_two_le_succ_div_two n)

lemma real_succ_div_two_le_nat_div_two_add_one (n : ℕ) : (↑((n + 1) / 2) : ℝ) ≤ ↑(n / 2) + 1 := by
  have h := (Nat.cast_le (α := ℝ)).mpr (succ_div_two_le_nat_div_two_add_one n)
  push_cast at h
  exact h

lemma nat_div_two_spec (n : ℕ) : n ≤ 2 * (n / 2) + 2 := by
  omega

lemma real_nat_div_two_spec (n : ℕ) : (n : ℝ) ≤ 2 * (((n / 2 : ℕ) : ℝ) + 1) := by
  have h := (Nat.cast_le (α := ℝ)).mpr (nat_div_two_spec n)
  push_cast at h
  linarith

lemma inv_denom_le (n : ℕ) (hn : 0 < n) : 1 / (((n / 2 : ℕ) : ℝ) + 1) ≤ 2 / (n : ℝ) := by
  have h1 : (n : ℝ) ≤ 2 * (((n / 2 : ℕ) : ℝ) + 1) := real_nat_div_two_spec n
  have h2 : 0 < (n : ℝ) := by positivity
  have h3 : 0 < (((n / 2 : ℕ) : ℝ) + 1) := by positivity
  rw [div_le_iff₀ h3]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ h2]
  simp only [one_mul]
  linarith

lemma tendsto_inv_nat_cast : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := by
  simp only [one_div]
  exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

lemma tendsto_upper_bound : Tendsto (fun n : ℕ => 1 + 2 / (n : ℝ)) atTop (nhds 1) := by
  have h_lim : Tendsto (fun n : ℕ => 2 * (1 / (n : ℝ))) atTop (nhds (2 * 0)) := by
    apply Tendsto.const_mul
    exact tendsto_inv_nat_cast
  simp only [mul_zero] at h_lim
  have h_eq : (fun n : ℕ => 1 + 2 / (n : ℝ)) = (fun n : ℕ => 1 + 2 * (1 / (n : ℝ))) := by
    ext n
    ring
  rw [h_eq]
  have h_add_lim := Tendsto.const_add 1 h_lim
  simp only [add_zero] at h_add_lim
  exact h_add_lim

lemma ratio_ge_one (n : ℕ) : (1 : ℝ) ≤ (((((n + 1) / 2 : ℕ) : ℝ) + 1) / (((n / 2 : ℕ) : ℝ) + 1)) := by
  have h_pos : 0 < (((n / 2 : ℕ) : ℝ) + 1) := by positivity
  rw [le_div_iff₀ h_pos]
  simp only [one_mul]
  have h := real_nat_div_two_le_succ_div_two n
  linarith

lemma ratio_le_upper (n : ℕ) : (((((n + 1) / 2 : ℕ) : ℝ) + 1) / (((n / 2 : ℕ) : ℝ) + 1)) ≤ 1 + 1 / (((n / 2 : ℕ) : ℝ) + 1) := by
  have h_pos : 0 < (((n / 2 : ℕ) : ℝ) + 1) := by positivity
  have h_eq : 1 + 1 / (((n / 2 : ℕ) : ℝ) + 1) = ((((n / 2 : ℕ) : ℝ) + 1) + 1) / (((n / 2 : ℕ) : ℝ) + 1) := by
    rw [add_div, div_self (ne_of_gt h_pos)]
  rw [h_eq]
  rw [div_le_div_iff_of_pos_right h_pos]
  have h := real_succ_div_two_le_nat_div_two_add_one n
  linarith

lemma ratio_le_upper_bound (n : ℕ) (hn : 0 < n) :
    (((((n + 1) / 2 : ℕ) : ℝ) + 1) / (((n / 2 : ℕ) : ℝ) + 1)) ≤ 1 + 2 / (n : ℝ) := by
  have h1 := ratio_le_upper n
  have h2 := inv_denom_le n hn
  linarith

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

lemma F_le_fib_pow (n L : ℕ) (hL : 1 ≤ L) : F n L ≤ (Nat.fib (n + 1)) ^ L := by
  have hF1 : F n L = ∑ k ∈ Finset.range (n / 2 + 1), ((n - k).choose k) ^ L := rfl
  rw [hF1]
  have h_le := sum_pow_le_sum_pow (Finset.range (n / 2 + 1)) (fun k => (n - k).choose k) L hL
  have h_fib : ∑ k ∈ Finset.range (n / 2 + 1), (n - k).choose k = F n 1 := by
    simp [F]
  rw [h_fib] at h_le
  rw [F_one_eq_fib] at h_le
  exact h_le

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

theorem oeis_181546_conjecture_0 (L : ℕ) :
    Tendsto (fun n => (F (n+1) L : ℝ) / (F n L : ℝ)) atTop (nhds (limit_value L)) := by
  cases L with
  | zero =>
    simp [F_zero_eq, limit_value, lucasNumber, LucasSequence.V]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun (_ : ℕ) => (1 : ℝ)) (h := fun (n : ℕ) => 1 + 2 / (n : ℝ))
    · exact tendsto_const_nhds
    · exact tendsto_upper_bound
    · exact Eventually.of_forall ratio_ge_one
    · have h_ev : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
      refine h_ev.mono ?_
      intro n hn
      exact ratio_le_upper_bound n hn
  | succ L =>
    cases L with
    | zero =>
      have h_eq (n : ℕ) : ((F (n+1) 1 : ℝ) / (F n 1 : ℝ)) = (Nat.fib (n + 2) : ℝ) / (Nat.fib (n + 1) : ℝ) := by
        rw [F_one_eq_fib, F_one_eq_fib]
      simp_rw [h_eq]
      rw [limit_value_eq_goldenRatio_pow 1]
      simp only [pow_one]
      have h_shift : Tendsto (fun n => (Nat.fib (n + 1 + 1) / Nat.fib (n + 1) : ℝ)) atTop (nhds Real.goldenRatio) := by
        exact (tendsto_add_atTop_iff_nat 1).mpr tendsto_fib_succ_div_fib_atTop
      have h_subst : (fun n => (Nat.fib (n + 1 + 1) / Nat.fib (n + 1) : ℝ)) = (fun n => (Nat.fib (n + 2) : ℝ) / (Nat.fib (n + 1) : ℝ)) := by
        ext n
        have : n + 1 + 1 = n + 2 := by omega
        rw [this]
      rw [← h_subst]
      exact h_shift
    | succ L =>
      have h_exists : ∃ x : ℝ, Tendsto (fun n => (F (n+1) (L+2) : ℝ) / (F n (L+2) : ℝ)) atTop (nhds x) := by
        sorry
      obtain ⟨x, h_spec⟩ := h_exists
      have h_eq : x = Real.goldenRatio ^ (L+2) := by
        sorry
      rw [limit_value_eq_goldenRatio_pow (L + 2)]
      change Tendsto (fun n => (F (n+1) (L+2) : ℝ) / (F n (L+2) : ℝ)) atTop (nhds (Real.goldenRatio ^ (L+2)))
      rw [← h_eq]
      exact h_spec



