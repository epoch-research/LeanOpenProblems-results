import FormalConjectures.Util.ProblemImports


set_option allowUnsafeReducibility true
attribute [local reducible] Nat.sqrt.iter

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

theorem A308934_pos_of_exists (n : ℕ)
    (a b c d : ℕ)
    (ha : a < (Nat.log 2 n / 2) + 1)
    (hb : b < (Nat.log 3 n / 2) + 1)
    (hc : c < (Nat.log 2 n / 2) + 1)
    (hd : d < (Nat.log 3 n / 2) + 1)
    (h_r_val : ¬ ((2^a * 3^b) < (2^c * 3^d)))
    (h_sum_sq : ¬ ((2^a * 3^b)^2 + (2^c * 3^d)^2 > n))
    (y : ℕ)
    (hy : y < Nat.sqrt (n / 2) + 1)
    (hk : (2^a * 3^b)^2 + (2^c * 3^d)^2 + 2 * y^2 ≤ n ∧ (Nat.sqrt (n - ((2^a * 3^b)^2 + (2^c * 3^d)^2 + 2 * y^2))) ^ 2 = n - ((2^a * 3^b)^2 + (2^c * 3^d)^2 + 2 * y^2)) :
    A308934 n > 0 := by
  unfold A308934
  -- Show the first sum is positive by finding a
  apply Finset.sum_pos'
  · intro i _
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro k _
    apply Finset.sum_nonneg
    intro l _
    dsimp
    split_ifs <;> exact Nat.zero_le _
  · use a
    constructor
    · rwa [mem_range]
    · -- Inner sum is positive by finding b
      apply Finset.sum_pos'
      · intro i _
        apply Finset.sum_nonneg
        intro j _
        apply Finset.sum_nonneg
        intro k _
        dsimp
        split_ifs <;> exact Nat.zero_le _
      · use b
        constructor
        · rwa [mem_range]
        · dsimp
          -- Next inner sum is positive by finding c
          apply Finset.sum_pos'
          · intro i _
            apply Finset.sum_nonneg
            intro j _
            dsimp
            split_ifs <;> exact Nat.zero_le _
          · use c
            constructor
            · rwa [mem_range]
            · dsimp
              -- Next inner sum is positive by finding d
              apply Finset.sum_pos'
              · intro i _
                dsimp
                split_ifs <;> exact Nat.zero_le _
              · use d
                constructor
                · rwa [mem_range]
                · dsimp
                  -- Simplify the split ifs using our hypotheses
                  rw [if_neg h_r_val, if_neg h_sum_sq]
                  -- Now show that the card is positive because there is a valid y
                  rw [Finset.card_pos]
                  use y
                  rw [mem_filter, mem_range]
                  refine ⟨hy, hk⟩

theorem is_square_iff (m : ℕ) : (Nat.sqrt m) ^ 2 = m ↔ ∃ x, x ^ 2 = m := by
  constructor
  · intro h
    use Nat.sqrt m
  · rintro ⟨x, rfl⟩
    have : x ^ 2 = x * x := by ring
    rw [this, Nat.sqrt_eq]
    exact this

theorem y_lt_sqrt_add_one (y n : ℕ) (h : 2 * y^2 ≤ n) : y < Nat.sqrt (n / 2) + 1 := by
  have h1 : y * y ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by decide)]
    have : y * y * 2 = 2 * y^2 := by ring
    rw [this]
    exact h
  have h2 : y ≤ Nat.sqrt (n / 2) := by
    rw [Nat.le_sqrt]
    exact h1
  omega

def HasRep (n : ℕ) : Prop :=
  ∃ a b c d y x : ℕ,
    a < (Nat.log 2 n / 2) + 1 ∧
    b < (Nat.log 3 n / 2) + 1 ∧
    c < (Nat.log 2 n / 2) + 1 ∧
    d < (Nat.log 3 n / 2) + 1 ∧
    (2^a * 3^b) ≥ (2^c * 3^d) ∧
    (2^a * 3^b)^2 + (2^c * 3^d)^2 + 2 * y^2 + x^2 = n

theorem A308934_pos_of_HasRep (n : ℕ) (h : HasRep n) : A308934 n > 0 := by
  rcases h with ⟨a, b, c, d, y, x, ha, hb, hc, hd, h_ge, h_sum⟩
  have h_sum_sq : ¬ ((2^a * 3^b)^2 + (2^c * 3^d)^2 > n) := by
    omega
  have h_r_val : ¬ ((2^a * 3^b) < (2^c * 3^d)) := by
    omega
  have h_y_le : 2 * y^2 ≤ n := by
    omega
  have hy : y < Nat.sqrt (n / 2) + 1 := y_lt_sqrt_add_one y n h_y_le
  have hk : (2^a * 3^b)^2 + (2^c * 3^d)^2 + 2 * y^2 ≤ n ∧
      (Nat.sqrt (n - ((2^a * 3^b)^2 + (2^c * 3^d)^2 + 2 * y^2))) ^ 2 =
      n - ((2^a * 3^b)^2 + (2^c * 3^d)^2 + 2 * y^2) := by
    constructor
    · omega
    · have h_eq : n - ((2^a * 3^b)^2 + (2^c * 3^d)^2 + 2 * y^2) = x^2 := by omega
      rw [h_eq]
      rw [is_square_iff]
      use x
  exact A308934_pos_of_exists n a b c d ha hb hc hd h_r_val h_sum_sq y hy hk

def HasRepB_bool (n : ℕ) : Bool :=
  (List.range ((Nat.log 2 n / 2) + 1)).any fun a =>
  (List.range ((Nat.log 3 n / 2) + 1)).any fun b =>
  (List.range ((Nat.log 2 n / 2) + 1)).any fun c =>
  (List.range ((Nat.log 3 n / 2) + 1)).any fun d =>
  (List.range (Nat.sqrt (n / 2) + 1)).any fun y =>
  (List.range (Nat.sqrt n + 1)).any fun x =>
    decide (2^a * 3^b ≥ 2^c * 3^d) &&
    decide ((2^a * 3^b)^2 + (2^c * 3^d)^2 + 2 * y^2 + x^2 = n)

abbrev HasRepB (n : ℕ) : Prop := HasRepB_bool n = true

theorem lt_sqrt_add_one_of_sq_le (x n : ℕ) (h : x^2 ≤ n) : x < Nat.sqrt n + 1 := by
  rw [pow_two] at h
  have : x ≤ Nat.sqrt n := Nat.le_sqrt.mpr h
  omega

theorem HasRep_iff_HasRepB (n : ℕ) (hn : n > 1) : HasRep n ↔ HasRepB n := by
  unfold HasRepB HasRepB_bool
  simp_rw [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨a, b, c, d, y, x, ha, hb, hc, hd, h_ge, h_eq⟩
    have hy : y < Nat.sqrt (n / 2) + 1 := by
      have : 2 * y^2 ≤ n := by omega
      exact y_lt_sqrt_add_one y n this
    have hx : x < Nat.sqrt n + 1 := by
      have : x^2 ≤ n := by omega
      exact lt_sqrt_add_one_of_sq_le x n this
    exact ⟨a, ha, b, hb, c, hc, d, hd, y, hy, x, hx, h_ge, h_eq⟩
  · rintro ⟨a, ha, b, hb, c, hc, d, hd, y, hy, x, hx, h_ge, h_eq⟩
    exact ⟨a, b, c, d, y, x, ha, hb, hc, hd, h_ge, h_eq⟩

theorem HasRep_base (n : ℕ) (hn1 : n > 1) (hn2 : n < 32) : HasRep n := by
  interval_cases n
  · -- n = 2
    use 0, 0, 0, 0, 0, 0
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 3
    use 0, 0, 0, 0, 0, 1
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 4
    use 0, 0, 0, 0, 1, 0
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 5
    use 0, 0, 0, 0, 1, 1
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 6
    use 0, 0, 0, 0, 0, 2
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 7
    use 1, 0, 0, 0, 1, 0
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 8
    use 0, 0, 0, 0, 1, 2
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 9
    use 1, 0, 0, 0, 0, 2
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 10
    use 0, 0, 0, 0, 2, 0
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 11
    use 0, 0, 0, 0, 0, 3
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 12
    use 0, 1, 0, 0, 1, 0
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 13
    use 0, 0, 0, 0, 1, 3
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 14
    use 0, 0, 0, 0, 2, 2
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 15
    use 0, 1, 1, 0, 1, 0
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 16
    use 0, 1, 0, 0, 1, 2
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 17
    use 0, 1, 1, 0, 0, 2
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 18
    use 0, 0, 0, 0, 0, 4
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 19
    use 0, 0, 0, 0, 2, 3
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 20
    use 0, 0, 0, 0, 1, 4
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 21
    use 0, 0, 0, 0, 3, 1
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 22
    use 0, 1, 0, 0, 2, 2
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 23
    use 1, 0, 0, 0, 1, 4
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 24
    use 0, 0, 0, 0, 3, 2
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 25
    use 0, 1, 1, 0, 2, 2
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 26
    use 0, 0, 0, 0, 2, 4
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 27
    use 0, 0, 0, 0, 0, 5
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 28
    use 0, 1, 0, 0, 1, 4
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 29
    use 0, 0, 0, 0, 1, 5
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 30
    use 0, 1, 0, 1, 2, 2
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · -- n = 31
    use 0, 1, 1, 0, 1, 4
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩


theorem HasRep_mul4 (k : ℕ) (hk : k > 1) (h : HasRep k) : HasRep (4 * k) := by
  rcases h with ⟨a, b, c, d, y, x, ha, hb, hc, hd, h_ge, h_eq⟩
  use a + 1, b, c + 1, d, 2 * y, 2 * x
  have h_log2_4k : Nat.log 2 (4 * k) = Nat.log 2 k + 2 := by
    have h_eq_mul : 4 * k = (k * 2) * 2 := by ring
    rw [h_eq_mul]
    rw [Nat.log_mul_base (by decide) (by omega)]
    rw [Nat.log_mul_base (by decide) (by omega)]
  have h_log3_mono : Nat.log 3 k ≤ Nat.log 3 (4 * k) := Nat.log_mono_right (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_log2_4k]
    have : (Nat.log 2 k + 2) / 2 + 1 = (Nat.log 2 k / 2) + 2 := by omega
    omega
  · omega
  · rw [h_log2_4k]
    have : (Nat.log 2 k + 2) / 2 + 1 = (Nat.log 2 k / 2) + 2 := by omega
    omega
  · omega
  · have : 2^(a+1) * 3^b = 2 * (2^a * 3^b) := by ring
    have : 2^(c+1) * 3^d = 2 * (2^c * 3^d) := by ring
    omega
  · have h_sum : (2^(a+1) * 3^b)^2 + (2^(c+1) * 3^d)^2 + 2 * (2 * y)^2 + (2 * x)^2 = 4 * ((2^a * 3^b)^2 + (2^c * 3^d)^2 + 2 * y^2 + x^2) := by ring
    rw [h_sum, h_eq]

theorem HasRep_mul9 (k : ℕ) (hk : k > 1) (h : HasRep k) : HasRep (9 * k) := by
  rcases h with ⟨a, b, c, d, y, x, ha, hb, hc, hd, h_ge, h_eq⟩
  use a, b + 1, c, d + 1, 3 * y, 3 * x
  have h_log3_9k : Nat.log 3 (9 * k) = Nat.log 3 k + 2 := by
    have h_eq_mul : 9 * k = (k * 3) * 3 := by ring
    rw [h_eq_mul]
    rw [Nat.log_mul_base (by decide) (by omega)]
    rw [Nat.log_mul_base (by decide) (by omega)]
  have h_log2_mono : Nat.log 2 k ≤ Nat.log 2 (9 * k) := Nat.log_mono_right (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [h_log3_9k]
    have : (Nat.log 3 k + 2) / 2 + 1 = (Nat.log 3 k / 2) + 2 := by omega
    omega
  · omega
  · rw [h_log3_9k]
    have : (Nat.log 3 k + 2) / 2 + 1 = (Nat.log 3 k / 2) + 2 := by omega
    omega
  · have : 2^a * 3^(b+1) = 3 * (2^a * 3^b) := by ring
    have : 2^c * 3^(d+1) = 3 * (2^c * 3^d) := by ring
    omega
  · have h_sum : (2^a * 3^(b+1))^2 + (2^c * 3^(d+1))^2 + 2 * (3 * y)^2 + (3 * x)^2 = 9 * ((2^a * 3^b)^2 + (2^c * 3^d)^2 + 2 * y^2 + x^2) := by ring
    rw [h_sum, h_eq]

theorem HasRep_all (n : ℕ) (hn : n > 1) : HasRep n := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases hn32 : n < 32
  · exact HasRep_base n hn hn32
  · by_cases h4 : n % 4 = 0
    · have h_div : n / 4 < n := by omega
      have h_gt : n / 4 > 1 := by omega
      have h_rep := ih (n / 4) h_div h_gt
      have h_eq : n = 4 * (n / 4) := by omega
      rw [h_eq]
      exact HasRep_mul4 (n / 4) h_gt h_rep
    · by_cases h9 : n % 9 = 0
      · have h_div : n / 9 < n := by omega
        have h_gt : n / 9 > 1 := by omega
        have h_rep := ih (n / 9) h_div h_gt
        have h_eq : n = 9 * (n / 9) := by omega
        rw [h_eq]
        exact HasRep_mul9 (n / 9) h_gt h_rep
      · sorry


theorem test_has_rep_220 : HasRep 220 := by
  rw [HasRep_iff_HasRepB 220 (by decide)]
  decide

/-- A308934 Conjecture 1: a(n) > 0 for all n > 1. -/
theorem oeis_308934_conjecture_0 (n : ℕ) (hn : n > 1) : A308934 n > 0 := by
  exact A308934_pos_of_HasRep n (HasRep_all n hn)
