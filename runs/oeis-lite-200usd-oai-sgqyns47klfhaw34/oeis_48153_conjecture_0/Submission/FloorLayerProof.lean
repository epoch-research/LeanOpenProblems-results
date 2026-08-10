import FormalConjectures.Util.ProblemImports
open Finset

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

lemma mod_sum_floor_identity (n : ℕ) :
    A048153 n + n * (∑ k ∈ Finset.range n, (k ^ 2 / n)) = ∑ k ∈ Finset.range n, k ^ 2 := by
  unfold A048153
  rw [← Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact Nat.mod_add_div (k^2) n

lemma ceil_linear_sum_bound (n : ℕ) :
    3 * (∑ i ∈ Finset.range (n - 2), (2 * (i + 1) + n + 2) / 3)
      ≤ (n - 2) * (2 * n + 1) := by
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero => simp
      | succ t =>
        -- n is t+2
        simp
        calc
          3 * (∑ i ∈ Finset.range t, (2 * (i + 1) + (t + 1 + 1) + 2) / 3)
              = ∑ i ∈ Finset.range t, 3 * ((2 * (i + 1) + (t + 1 + 1) + 2) / 3) := by
                rw [Finset.mul_sum]
          _ ≤ ∑ i ∈ Finset.range t, (2 * (i + 1) + (t + 1 + 1) + 2) := by
                apply Finset.sum_le_sum
                intro i hi
                exact Nat.mul_div_le (2 * (i + 1) + (t + 1 + 1) + 2) 3
          _ ≤ t * (2 * (t + 1 + 1) + 1) := by
                simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_range]
                rw [← Finset.mul_sum]
                rw [Finset.sum_range_id]
                cases t with
                | zero => norm_num
                | succ u =>
                    simp only [Nat.succ_eq_add_one, add_tsub_cancel_right]
                    have hdiv : ((u + 1) * u / 2) * 2 ≤ (u + 1) * u := by
                      exact Nat.div_mul_le_self _ _
                    nlinarith [hdiv]

lemma q_le_div_of_threshold {n i k : ℕ} (hi : i ∈ Finset.range (n - 2))
    (hk : (2 * (i + 1) + n + 2) / 3 ≤ k) :
    i + 1 ≤ k ^ 2 / n := by
  have hnpos : 0 < n := by
    have : i < n - 2 := by simpa using hi
    omega
  rw [Nat.le_div_iff_mul_le hnpos]
  let q := i + 1
  let c := (2 * q + n + 2) / 3
  have hceil : 2 * q + n ≤ 3 * c := by
    dsimp [c]
    omega
  have hkc : c ≤ k := by simpa [q, c] using hk
  have h3 : 3 * c ≤ 3 * k := Nat.mul_le_mul_left 3 hkc
  have hagm : 9 * q * n ≤ (2 * q + n) ^ 2 := by
    have hz : (0 : ℤ) ≤ ((n : ℤ) - 2 * (q : ℤ)) ^ 2 := sq_nonneg _
    have hz' : (9 * q * n : ℤ) ≤ ((2 * q + n : ℕ) : ℤ) ^ 2 := by
      push_cast
      ring_nf at hz ⊢
      nlinarith
    exact_mod_cast hz'
  have hmain : 9 * q * n ≤ (3 * k) ^ 2 := by
    nlinarith
  have hfinal : q * n ≤ k ^ 2 := by
    nlinarith
  simpa [q, pow_two, mul_assoc, mul_comm, mul_left_comm] using hfinal

lemma card_filter_threshold_le (n k : ℕ) :
    ((Finset.range (n - 2)).filter (fun i => (2 * (i + 1) + n + 2) / 3 ≤ k)).card ≤ k ^ 2 / n := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  have hq := q_le_div_of_threshold (n := n) (i := i) (k := k) (by simpa using hi.1) hi.2
  omega

lemma filter_range_ge_eq_Ico (n c : ℕ) :
    (Finset.range n).filter (fun k => c ≤ k) = Finset.Ico c n := by
  ext k
  simp [and_comm]

lemma sum_indicator_ge (n c : ℕ) :
    (∑ k ∈ Finset.range n, (if c ≤ k then 1 else 0 : ℕ)) = n - c := by
  rw [← Finset.card_eq_sum_ones ((Finset.range n).filter (fun k => c ≤ k))]
  rw [filter_range_ge_eq_Ico]
  simp

lemma floor_sum_lower_triple (n : ℕ) :
    (n - 2) * (n - 1) ≤ 3 * (∑ k ∈ Finset.range n, k ^ 2 / n) := by
  let c : ℕ → ℕ := fun i => (2 * (i + 1) + n + 2) / 3
  have hcard_sum :
      (∑ k ∈ Finset.range n, ((Finset.range (n - 2)).filter (fun i => c i ≤ k)).card)
        = ∑ i ∈ Finset.range (n - 2), (n - c i) := by
    calc
      (∑ k ∈ Finset.range n, ((Finset.range (n - 2)).filter (fun i => c i ≤ k)).card)
          = ∑ k ∈ Finset.range n, ∑ i ∈ Finset.range (n - 2), (if c i ≤ k then 1 else 0 : ℕ) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [← Finset.card_eq_sum_ones ((Finset.range (n - 2)).filter (fun i => c i ≤ k))]
              rfl
      _ = ∑ i ∈ Finset.range (n - 2), ∑ k ∈ Finset.range n, (if c i ≤ k then 1 else 0 : ℕ) := by
              rw [Finset.sum_comm]
      _ = ∑ i ∈ Finset.range (n - 2), (n - c i) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact sum_indicator_ge n (c i)
  have hle :
      (∑ k ∈ Finset.range n, ((Finset.range (n - 2)).filter (fun i => c i ≤ k)).card)
        ≤ ∑ k ∈ Finset.range n, k ^ 2 / n := by
    apply Finset.sum_le_sum
    intro k hk
    exact card_filter_threshold_le n k
  have h3le :
      3 * (∑ i ∈ Finset.range (n - 2), c i) ≤ (n - 2) * (2 * n + 1) := by
    simpa [c] using ceil_linear_sum_bound n
  have hmain : 3 * (∑ i ∈ Finset.range (n - 2), (n - c i)) ≤ 3 * (∑ k ∈ Finset.range n, k ^ 2 / n) := by
    rw [← hcard_sum]
    exact Nat.mul_le_mul_left 3 hle
  have hsumc_le : 3 * (∑ i ∈ Finset.range (n - 2), c i) ≤ (n - 2) * (2 * n + 1) := h3le
  -- Need algebra: (n-2)(n-1) ≤ 3 sum(n-c)
  have halg : (n - 2) * (n - 1) ≤ 3 * (∑ i ∈ Finset.range (n - 2), (n - c i)) := by
    -- expand sum (n-c) via sum_sub? use omega with inequalities maybe
    have hcn (i : ℕ) (hi : i ∈ Finset.range (n - 2)) : c i ≤ n := by
      have : i < n - 2 := by simpa using hi
      dsimp [c]
      omega
    have hsum_sub : (∑ i ∈ Finset.range (n - 2), (n - c i)) = (n - 2) * n - ∑ i ∈ Finset.range (n - 2), c i := by
      rw [← Finset.sum_sub_distrib]
      · simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      · intro i hi; exact hcn i hi
    rw [hsum_sub]
    have hmul : 3 * ((n - 2) * n - ∑ i ∈ Finset.range (n - 2), c i)
          = 3 * ((n - 2) * n) - 3 * (∑ i ∈ Finset.range (n - 2), c i) := by
      have hle' : ∑ i ∈ Finset.range (n - 2), c i ≤ (n - 2) * n := by
        rw [← Finset.sum_const (b := n)]
        simp only [nsmul_eq_mul, Finset.card_range]
        exact Finset.sum_le_sum hcn
      omega
    rw [hmul]
    omega
  exact halg.trans hmain

lemma sum_range_sq_nat (n : ℕ) :
    6 * (∑ k ∈ Finset.range n, k ^ 2) = n * (n - 1) * (2 * n - 1) := by
  -- Try known theorem?
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have : 6 * (∑ x ∈ Finset.range n, x ^ 2 + n ^ 2) = 6 * (∑ x ∈ Finset.range n, x ^ 2) + 6 * n ^ 2 := by ring
    rw [this, ih]
    -- natural subtraction pain; use omega/nlinarith after cases?
    nlinarith [Nat.zero_le n]

example (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  have hid := mod_sum_floor_identity n
  have hfloor := floor_sum_lower_triple n
  have hsumsq := sum_range_sq_nat n
  -- combine in integers
  have hnpos : 0 < n := by omega
  -- move to integers to avoid nat sub/div
  have hidz : (A048153 n : ℤ) + (n : ℤ) * (∑ k ∈ Finset.range n, k ^ 2 / n : ℕ) = (∑ k ∈ Finset.range n, k ^ 2 : ℕ) := by exact_mod_cast hid
  have hfloorz : ((n - 2) * (n - 1) : ℕ) ≤ 3 * (∑ k ∈ Finset.range n, k ^ 2 / n) := hfloor
  have hsumsqz : (6 : ℤ) * (∑ k ∈ Finset.range n, k ^ 2 : ℕ) = (n : ℤ) * (n - 1 : ℕ) * (2 * n - 1 : ℕ) := by exact_mod_cast hsumsq
  -- prove 2*A ≤ n^2-1 maybe equivalent to A≤/2? For Nat, use Nat.le_div_iff_mul_le? Need parity? If 2A≤n²-1 then A≤(...)/2.
  apply Nat.le_div_iff_mul_le (by decide : 0 < 2) |>.mpr
  have goalz : (2 : ℤ) * (A048153 n : ℤ) ≤ (n ^ 2 - 1 : ℕ) := by
    -- derive using hfloorz * 2n? Let's let nlinarith with cast of hfloorz
    have hfz : ((n - 2 : ℕ) * (n - 1 : ℕ) : ℤ) ≤ 3 * (∑ k ∈ Finset.range n, k ^ 2 / n : ℕ) := by exact_mod_cast hfloorz
    have hn2 : (2 : ℤ) * (n : ℤ) * ((n - 2 : ℕ) * (n - 1 : ℕ) : ℤ) ≤ (2 : ℤ) * (n : ℤ) * (3 * (∑ k ∈ Finset.range n, k ^ 2 / n : ℕ)) := by
      nlinarith [show (0:ℤ) ≤ (n:ℤ) by exact_mod_cast Nat.zero_le n, hfz]
    -- nlinarith with identities; need cast n-2 relation h
    have hnsub1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have hnsub2_nonneg : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 ∨ n = 1 := by omega
    rcases hnsub2_nonneg with hnsub2 | hn1
    · nlinarith [hidz, hsumsqz, hn2]
    · subst n
      norm_num [A048153]
  exact_mod_cast goalz
