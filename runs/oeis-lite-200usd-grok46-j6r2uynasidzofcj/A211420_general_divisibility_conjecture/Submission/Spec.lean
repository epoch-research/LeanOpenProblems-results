import FormalConjectures.Util.ProblemImports

open Nat

/--
A211420: $a(n) = \frac{(8n)! n!}{(4n)! (3n)! (2n)!}$
Since the OEIS entry states that this ratio is always an integer, we define it directly as a natural number.
The division in Lean's `Nat` type is integer division, which is exact here.
-/
def A211420 (n : ℕ) : ℕ :=
  (8 * n).factorial * n.factorial / ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial)

/-- The Bober step function is nonnegative on residues: `⌊8s/m⌋ ≥ ⌊4s/m⌋ + ⌊3s/m⌋ + ⌊2s/m⌋` for `s < m`. -/
lemma bober_psi_residue_nonneg (s m : ℕ) (hsm : s < m) :
    (4 * s) / m + (3 * s) / m + (2 * s) / m ≤ (8 * s) / m := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le s) hsm
  by_cases h2 : 2 * s < m
  · -- 2s < m ⇒ ⌊2s/m⌋ = 0
    have d2 : (2 * s) / m = 0 := Nat.div_eq_of_lt h2
    by_cases h3 : 3 * s < m
    · -- 3s < m ⇒ ⌊3s/m⌋ = 0
      have d3 : (3 * s) / m = 0 := Nat.div_eq_of_lt h3
      by_cases h4 : 4 * s < m
      · -- all zero on LHS
        have d4 : (4 * s) / m = 0 := Nat.div_eq_of_lt h4
        simp [d2, d3, d4]
      · -- m ≤ 4s and 3s < m ⇒ ⌊4s/m⌋ = 1, ⌊8s/m⌋ = 2
        have d4 : (4 * s) / m = 1 := by
          refine Nat.div_eq_of_lt_le ?_ ?_
          · omega
          · omega
        have d8 : (8 * s) / m = 2 := by
          refine Nat.div_eq_of_lt_le ?_ ?_
          · omega
          · omega
        omega
    · -- m ≤ 3s and 2s < m ⇒ ⌊3s/m⌋ = 1, ⌊4s/m⌋ = 1, ⌊8s/m⌋ ≥ 2
      have d3 : (3 * s) / m = 1 := by
        refine Nat.div_eq_of_lt_le ?_ ?_
        · omega
        · omega
      have d4 : (4 * s) / m = 1 := by
        refine Nat.div_eq_of_lt_le ?_ ?_
        · omega
        · omega
      have d8 : 2 ≤ (8 * s) / m := by
        rw [Nat.le_div_iff_mul_le hm]
        omega
      omega
  · -- m ≤ 2s (and s < m ⇒ 2s < 2m) ⇒ ⌊2s/m⌋ = 1
    have d2 : (2 * s) / m = 1 := by
      refine Nat.div_eq_of_lt_le ?_ ?_
      · omega
      · omega
    by_cases h3 : 3 * s < 2 * m
    · -- s < 2m/3, s ≥ m/2 ⇒ ⌊4s/m⌋ = 2, ⌊3s/m⌋ = 1, ⌊8s/m⌋ ≥ 4
      have d3 : (3 * s) / m = 1 := by
        refine Nat.div_eq_of_lt_le ?_ ?_
        · omega
        · omega
      have d4 : (4 * s) / m = 2 := by
        refine Nat.div_eq_of_lt_le ?_ ?_
        · omega
        · omega
      have d8 : 4 ≤ (8 * s) / m := by
        rw [Nat.le_div_iff_mul_le hm]
        omega
      omega
    · -- 2m ≤ 3s
      have d3 : (3 * s) / m = 2 := by
        refine Nat.div_eq_of_lt_le ?_ ?_
        · omega
        · omega
      by_cases h4 : 4 * s < 3 * m
      · -- ⌊4s/m⌋ = 2, ⌊8s/m⌋ = 5
        have d4 : (4 * s) / m = 2 := by
          refine Nat.div_eq_of_lt_le ?_ ?_
          · omega
          · omega
        have d8 : (8 * s) / m = 5 := by
          refine Nat.div_eq_of_lt_le ?_ ?_
          · omega
          · omega
        omega
      · -- 3m ≤ 4s ⇒ ⌊4s/m⌋ = 3, ⌊8s/m⌋ ≥ 6
        have d4 : (4 * s) / m = 3 := by
          refine Nat.div_eq_of_lt_le ?_ ?_
          · omega
          · omega
        have d8 : 6 ≤ (8 * s) / m := by
          rw [Nat.le_div_iff_mul_le hm]
          omega
        omega

lemma mul_div_add_mod_div (c n m : ℕ) (hm : 0 < m) :
    (c * n) / m = c * (n / m) + (c * (n % m)) / m := by
  have hn : n = m * (n / m) + n % m := (Nat.div_add_mod n m).symm
  calc (c * n) / m
      = (c * (m * (n / m) + n % m)) / m := by rw [← hn]
    _ = (c * m * (n / m) + c * (n % m)) / m := by
          rw [Nat.mul_add, Nat.mul_assoc]
    _ = (m * (c * (n / m)) + c * (n % m)) / m := by
          rw [Nat.mul_comm c m, Nat.mul_assoc]
    _ = (c * (n % m) + m * (c * (n / m))) / m := by
          rw [Nat.add_comm]
    _ = (c * (n % m)) / m + c * (n / m) := Nat.add_mul_div_left _ _ hm
    _ = c * (n / m) + (c * (n % m)) / m := Nat.add_comm _ _

lemma bober_psi_nonneg (n m : ℕ) (hm : 0 < m) :
    (4 * n) / m + (3 * n) / m + (2 * n) / m ≤ (8 * n) / m + n / m := by
  have hs : n % m < m := Nat.mod_lt n hm
  rw [mul_div_add_mod_div 4 n m hm, mul_div_add_mod_div 3 n m hm,
      mul_div_add_mod_div 2 n m hm, mul_div_add_mod_div 8 n m hm]
  have hmod0 : (n % m) / m = 0 := Nat.div_eq_of_lt hs
  have := bober_psi_residue_nonneg (n % m) m hs
  omega

/-- `(a + b) / m ≤ a / m + b / m + 1`. -/
lemma add_div_le_add_div_add_one (a b m : ℕ) (hm : 0 < m) :
    (a + b) / m ≤ a / m + b / m + 1 := by
  rw [Nat.add_div hm]
  split_ifs <;> omega

/-- If `r < m`, then `(a + r) / m` is `a / m` or `a / m + 1`, and equals `a / m + 1`
iff `m ≤ a % m + r`. -/
lemma add_lt_div_eq (a r m : ℕ) (hm : 0 < m) (hr : r < m) :
    (a + r) / m = a / m + if m ≤ a % m + r then 1 else 0 := by
  have : r % m = r := Nat.mod_eq_of_lt hr
  rw [Nat.add_div hm, Nat.div_eq_of_lt hr, Nat.add_zero, this]

/-- When `k ∈ {1,2,3}`, `8r ≤ m` and wrapping occurs, the residue step function is at least 1. -/
lemma bober_psi_residue_ge_one (k r s m : ℕ)
    (hk : k = 1 ∨ k = 2 ∨ k = 3) (hr : 1 ≤ r) (hsm : s < m) (hmr : 8 * r ≤ m)
    (hwrap : m ≤ (k * s) % m + r) :
    (4 * s) / m + (3 * s) / m + (2 * s) / m + 1 ≤ (8 * s) / m := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le s) hsm
  have hr_lt : r < m := by omega
  have hr_le : r ≤ m := le_of_lt hr_lt
  rcases hk with rfl | rfl | rfl
  · -- k = 1: wrap means m ≤ s + r (since (1*s)%m = s)
    have hs_mod : (1 * s) % m = s := by
      rw [Nat.one_mul, Nat.mod_eq_of_lt hsm]
    rw [hs_mod] at hwrap
    -- 8s ≥ 8(m - r) ≥ 7m
    have h8 : 7 * m ≤ 8 * s := by omega
    have d8 : 7 ≤ (8 * s) / m := by
      rw [Nat.le_div_iff_mul_le hm]; exact h8
    -- s < m ⇒ ⌊4s/m⌋ ≤ 3, ⌊3s/m⌋ ≤ 2, ⌊2s/m⌋ ≤ 1
    have d4 : (4 * s) / m ≤ 3 := by
      rw [Nat.div_le_iff_le_mul hm]; omega
    have d3 : (3 * s) / m ≤ 2 := by
      rw [Nat.div_le_iff_le_mul hm]; omega
    have d2 : (2 * s) / m ≤ 1 := by
      rw [Nat.div_le_iff_le_mul hm]; omega
    omega
  · -- k = 2
    have h2s : 2 * s < 2 * m := by omega
    by_cases ht : 2 * s < m
    · -- (2s)%m = 2s, wrap: m ≤ 2s + r
      have hmod : (2 * s) % m = 2 * s := Nat.mod_eq_of_lt ht
      rw [hmod] at hwrap
      -- 2s ≥ m - r, 8s ≥ 4m - 4r ≥ 4m - m/2 = 7m/2, and 8s < 4m so ⌊8s/m⌋ = 3
      have d8 : (8 * s) / m = 3 := by
        refine Nat.div_eq_of_lt_le ?_ ?_
        · omega
        · omega
      have d4 : (4 * s) / m = 1 := by
        refine Nat.div_eq_of_lt_le ?_ ?_
        · omega
        · omega
      have d3 : (3 * s) / m = 1 := by
        refine Nat.div_eq_of_lt_le ?_ ?_
        · omega
        · omega
      have d2 : (2 * s) / m = 0 := Nat.div_eq_of_lt ht
      omega
    · -- m ≤ 2s < 2m, (2s)%m = 2s - m, wrap: m ≤ 2s - m + r i.e. 2m ≤ 2s + r
      have hmod : (2 * s) % m = 2 * s - m := by
        have := Nat.mod_eq_sub_mod (le_of_not_gt ht)
        rwa [Nat.mod_eq_of_lt (by omega : 2 * s - m < m)] at this
      rw [hmod] at hwrap
      -- 2s ≥ 2m - r, 8s ≥ 8m - 4r ≥ 7.5m so ⌊8s/m⌋ = 7
      have d8 : (8 * s) / m = 7 := by
        refine Nat.div_eq_of_lt_le ?_ ?_
        · omega
        · omega
      have d4 : (4 * s) / m = 3 := by
        refine Nat.div_eq_of_lt_le ?_ ?_
        · omega
        · omega
      have d3 : (3 * s) / m = 2 := by
        refine Nat.div_eq_of_lt_le ?_ ?_
        · omega
        · omega
      have d2 : (2 * s) / m = 1 := by
        refine Nat.div_eq_of_lt_le ?_ ?_
        · omega
        · omega
      omega
  · -- k = 3
    rcases lt_trichotomy (3 * s) m with ht0 | ht0 | ht0
    · -- 3s < m, (3s)%m = 3s, wrap: m ≤ 3s + r
      have hmod : (3 * s) % m = 3 * s := Nat.mod_eq_of_lt ht0
      rw [hmod] at hwrap
      have d8 : (8 * s) / m = 2 := by
        refine Nat.div_eq_of_lt_le ?_ ?_
        · omega
        · omega
      have d4 : (4 * s) / m = 1 := by
        refine Nat.div_eq_of_lt_le ?_ ?_
        · omega
        · omega
      have d3 : (3 * s) / m = 0 := Nat.div_eq_of_lt ht0
      have d2 : (2 * s) / m = 0 := Nat.div_eq_of_lt (by omega)
      omega
    · -- 3s = m, (3s)%m = 0, wrap: m ≤ 0 + r i.e. m ≤ r, contradicts r < m
      rw [ht0, Nat.mod_self] at hwrap
      omega
    · -- m < 3s
      by_cases ht2 : 3 * s < 2 * m
      · -- m < 3s < 2m, (3s)%m = 3s - m, wrap: m ≤ 3s - m + r i.e. 2m ≤ 3s + r
        have hmod : (3 * s) % m = 3 * s - m := by
          have := Nat.mod_eq_sub_mod (le_of_lt ht0)
          rwa [Nat.mod_eq_of_lt (by omega : 3 * s - m < m)] at this
        rw [hmod] at hwrap
        have d8 : (8 * s) / m = 5 := by
          refine Nat.div_eq_of_lt_le ?_ ?_
          · omega
          · omega
        have d4 : (4 * s) / m = 2 := by
          refine Nat.div_eq_of_lt_le ?_ ?_
          · omega
          · omega
        have d3 : (3 * s) / m = 1 := by
          refine Nat.div_eq_of_lt_le ?_ ?_
          · omega
          · omega
        have d2 : (2 * s) / m = 1 := by
          refine Nat.div_eq_of_lt_le ?_ ?_
          · omega
          · omega
        omega
      · -- 2m ≤ 3s < 3m (s < m), (3s)%m = 3s - 2m, wrap: m ≤ 3s - 2m + r
        have h3s_lt : 3 * s < 3 * m := by omega
        have hmod : (3 * s) % m = 3 * s - 2 * m := by
          have h1 : (3 * s) % m = (3 * s - m) % m := Nat.mod_eq_sub_mod (le_of_lt ht0)
          have h2 : 3 * s - m ≥ m := by omega
          have h3 : 3 * s - m - m = 3 * s - 2 * m := by omega
          have h4 : 3 * s - 2 * m < m := by omega
          rw [h1, Nat.mod_eq_sub_mod h2, h3, Nat.mod_eq_of_lt h4]
        rw [hmod] at hwrap
        have d8 : (8 * s) / m = 7 := by
          refine Nat.div_eq_of_lt_le ?_ ?_
          · omega
          · omega
        have d4 : (4 * s) / m = 3 := by
          refine Nat.div_eq_of_lt_le ?_ ?_
          · omega
          · omega
        have d3 : (3 * s) / m = 2 := by
          refine Nat.div_eq_of_lt_le ?_ ?_
          · omega
          · omega
        have d2 : (2 * s) / m = 1 := by
          refine Nat.div_eq_of_lt_le ?_ ?_
          · omega
          · omega
        omega

/-- Reduce the step function to the residue. -/
lemma bober_psi_eq_residue (n m : ℕ) (hm : 0 < m) :
    (8 * n) / m + n / m + (4 * (n % m)) / m + (3 * (n % m)) / m + (2 * (n % m)) / m =
    (4 * n) / m + (3 * n) / m + (2 * n) / m + (8 * (n % m)) / m := by
  rw [mul_div_add_mod_div 4 n m hm, mul_div_add_mod_div 3 n m hm,
      mul_div_add_mod_div 2 n m hm, mul_div_add_mod_div 8 n m hm]
  have : (n % m) / m = 0 := Nat.div_eq_of_lt (Nat.mod_lt n hm)
  omega

/-- For `k ∈ {1,2,3}` and `m ≥ 8r`, we have
`⌊(kn+r)/m⌋ + ⌊4n/m⌋ + ⌊3n/m⌋ + ⌊2n/m⌋ ≤ ⌊kn/m⌋ + ⌊8n/m⌋ + ⌊n/m⌋`. -/
lemma large_power_alpha_le_psi (k r n m : ℕ)
    (hk : k = 1 ∨ k = 2 ∨ k = 3) (hr : 1 ≤ r) (hmr : 8 * r ≤ m) :
    (k * n + r) / m + (4 * n) / m + (3 * n) / m + (2 * n) / m ≤
      (k * n) / m + (8 * n) / m + n / m := by
  have hm : 0 < m := by omega
  have hr_lt : r < m := by omega
  have hs : n % m < m := Nat.mod_lt n hm
  -- Decompose kn
  have hkn : (k * n) / m = k * (n / m) + (k * (n % m)) / m :=
    mul_div_add_mod_div k n m hm
  -- Decompose kn + r
  have hknr : (k * n + r) / m = k * (n / m) + (k * (n % m) + r) / m := by
    have hn : k * n + r = m * (k * (n / m)) + (k * (n % m) + r) := by
      have := Nat.div_add_mod n m
      zify at this ⊢
      nlinarith
    rw [hn, Nat.add_comm (m * (k * (n / m))), Nat.add_mul_div_left _ _ hm, Nat.add_comm]
  rw [hkn, hknr]
  -- Reduce to residues: need (k*s + r)/m + floors(s) ≤ (k*s)/m + floor(8s/m)
  -- Use add_lt_div_eq
  rw [add_lt_div_eq (k * (n % m)) r m hm hr_lt]
  have hks_div : (k * (n % m)) / m = (k * (n % m)) % m / m + (k * (n % m)) / m := by
    simp
  -- Split on wrap
  by_cases hwrap : m ≤ (k * (n % m)) % m + r
  · simp only [hwrap, ↓reduceIte]
    have hge := bober_psi_residue_ge_one k r (n % m) m hk hr hs hmr hwrap
    have hpsi := bober_psi_eq_residue n m hm
    -- (k*(n%m))/m + 1 + (4n)/m + (3n)/m + (2n)/m ≤ (k*(n%m))/m + (8n)/m + n/m
    -- iff 1 + (4n)/m + (3n)/m + (2n)/m ≤ (8n)/m + n/m
    -- and residue ge_one says 1 + (4s)/m+(3s)/m+(2s)/m ≤ (8s)/m
    -- combined with bober_psi_eq_residue
    have : (4 * n) / m + (3 * n) / m + (2 * n) / m + 1 ≤ (8 * n) / m + n / m := by
      have hres := bober_psi_residue_nonneg (n % m) m hs
      -- from hge: (4s)/m+(3s)/m+(2s)/m+1 ≤ (8s)/m
      -- from eq: (8n)/m + n/m + (4s)/m+(3s)/m+(2s)/m = (4n)/m+(3n)/m+(2n)/m + (8s)/m
      -- so (8n)/m + n/m ≥ (4n)/m+(3n)/m+(2n)/m + 1
      omega
    omega
  · simp only [hwrap, ↓reduceIte, Nat.add_zero]
    have := bober_psi_nonneg n m hm
    omega

/-- In all cases, `⌊(kn+r)/m⌋ ≤ ⌊kn/m⌋ + ⌊r/m⌋ + 1`. -/
lemma alpha_le_succ (k n r m : ℕ) (hm : 0 < m) :
    (k * n + r) / m ≤ (k * n) / m + r / m + 1 :=
  add_div_le_add_div_add_one (k * n) r m hm

/-- Combining the two regimes. -/
lemma alpha_le_psi_add_bound (k r n m : ℕ)
    (hk : k = 1 ∨ k = 2 ∨ k = 3) (hr : 1 ≤ r) (hm : 0 < m) :
    (k * n + r) / m + (4 * n) / m + (3 * n) / m + (2 * n) / m ≤
      (k * n) / m + (8 * n) / m + n / m + (if m < 8 * r then r + 1 else 0) := by
  by_cases h : m < 8 * r
  · simp only [h, ↓reduceIte]
    have hα := alpha_le_succ k n r m hm
    have hψ := bober_psi_nonneg n m hm
    have : r / m ≤ r := Nat.div_le_self r m
    omega
  · simp only [h, ↓reduceIte, Nat.add_zero]
    have hmr : 8 * r ≤ m := Nat.le_of_not_gt h
    exact large_power_alpha_le_psi k r n m hk hr hmr

/-- The numerator of `A211420 n`. -/
def A211420_num (n : ℕ) : ℕ := (8 * n).factorial * n.factorial

/-- The denominator of `A211420 n`. -/
def A211420_den (n : ℕ) : ℕ :=
  (4 * n).factorial * (3 * n).factorial * (2 * n).factorial

lemma A211420_den_pos (n : ℕ) : 0 < A211420_den n := by
  unfold A211420_den
  exact Nat.mul_pos (Nat.mul_pos (factorial_pos _) (factorial_pos _)) (factorial_pos _)

lemma A211420_num_pos (n : ℕ) : 0 < A211420_num n := by
  unfold A211420_num
  exact Nat.mul_pos (factorial_pos _) (factorial_pos _)

lemma A211420_den_ne_zero (n : ℕ) : A211420_den n ≠ 0 :=
  (A211420_den_pos n).ne'

lemma A211420_num_ne_zero (n : ℕ) : A211420_num n ≠ 0 :=
  (A211420_num_pos n).ne'

/-- `A211420` is an integer: the denominator divides the numerator. -/
lemma A211420_den_dvd_num (n : ℕ) : A211420_den n ∣ A211420_num n := by
  refine (Nat.factorization_le_iff_dvd (A211420_den_ne_zero n) (A211420_num_ne_zero n)).mp ?_
  intro p
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    unfold A211420_den A211420_num
    have hpos4 : (4 * n).factorial ≠ 0 := factorial_ne_zero _
    have hpos3 : (3 * n).factorial ≠ 0 := factorial_ne_zero _
    have hpos2 : (2 * n).factorial ≠ 0 := factorial_ne_zero _
    have hpos8 : (8 * n).factorial ≠ 0 := factorial_ne_zero _
    have hposn : n.factorial ≠ 0 := factorial_ne_zero _
    rw [padicValNat.mul (mul_ne_zero hpos4 hpos3) hpos2,
        padicValNat.mul hpos4 hpos3,
        padicValNat.mul hpos8 hposn]
    -- Use Legendre with a common bound
    let b := Nat.log p (8 * n) + 1
    have hb8 : Nat.log p (8 * n) < b := Nat.lt_succ_self _
    have hb4 : Nat.log p (4 * n) < b :=
      (Nat.log_mono_right (Nat.mul_le_mul_right n (by norm_num : 4 ≤ 8))).trans_lt hb8
    have hb3 : Nat.log p (3 * n) < b :=
      (Nat.log_mono_right (Nat.mul_le_mul_right n (by norm_num : 3 ≤ 8))).trans_lt hb8
    have hb2 : Nat.log p (2 * n) < b :=
      (Nat.log_mono_right (Nat.mul_le_mul_right n (by norm_num : 2 ≤ 8))).trans_lt hb8
    have hbn : Nat.log p n < b :=
      (Nat.log_mono_right (Nat.le_mul_of_pos_left n (by norm_num : 0 < 8))).trans_lt hb8
    rw [padicValNat_factorial hb8, padicValNat_factorial hbn,
        padicValNat_factorial hb4, padicValNat_factorial hb3, padicValNat_factorial hb2]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro j hj
    exact bober_psi_nonneg n (p ^ j) (pow_pos hp.pos _)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

lemma A211420_eq_div (n : ℕ) :
    A211420 n = A211420_num n / A211420_den n := rfl

lemma A211420_mul_den (n : ℕ) :
    A211420 n * A211420_den n = A211420_num n := by
  rw [A211420_eq_div, Nat.div_mul_cancel (A211420_den_dvd_num n)]

lemma A211420_pos (n : ℕ) : 0 < A211420 n := by
  have h := A211420_mul_den n
  have hn := A211420_num_ne_zero n
  rw [← h] at hn
  exact Nat.pos_of_ne_zero (fun hz => hn (by simp [hz]))

lemma A211420_ne_zero (n : ℕ) : A211420 n ≠ 0 := (A211420_pos n).ne'

lemma padicValNat_A211420 (p n : ℕ) (hp : p.Prime) :
    padicValNat p (A211420 n) =
      padicValNat p (A211420_num n) - padicValNat p (A211420_den n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [A211420_eq_div, padicValNat.div_of_dvd (A211420_den_dvd_num n)]



lemma log_lt_of_le_of_log_lt {p a c b : ℕ} (h : a ≤ c) (hb : Nat.log p c < b) :
    Nat.log p a < b :=
  (Nat.log_mono_right h).trans_lt hb

lemma extra_sum_le (p r b : ℕ) (hp : 1 < p) :
    ∑ j ∈ Finset.Ico 1 b, (if p ^ j < 8 * r then r + 1 else 0) ≤ 8 * r * (r + 1) := by
  have hpt : ∀ j ∈ Finset.Ico 1 b,
      (if p ^ j < 8 * r then r + 1 else 0) ≤
        (if j ∈ Finset.range (8 * r) then r + 1 else 0) := by
    intro j hj
    by_cases hpr : p ^ j < 8 * r
    · have hjlt : j < p ^ j := Nat.lt_pow_self hp
      have hj8 : j < 8 * r := lt_trans hjlt hpr
      have : j ∈ Finset.range (8 * r) := Finset.mem_range.mpr hj8
      simp [hpr, this]
    · simp [hpr]
  have hle := Finset.sum_le_sum hpt
  have heq :
      ∑ j ∈ Finset.Ico 1 b, (if j ∈ Finset.range (8 * r) then r + 1 else 0) =
        ∑ j ∈ (Finset.Ico 1 b).filter (· ∈ Finset.range (8 * r)), (r + 1) :=
    (Finset.sum_filter (s := Finset.Ico 1 b) (p := fun j => j ∈ Finset.range (8 * r))
      (f := fun _ => r + 1)).symm
  rw [heq] at hle
  have hsub : (Finset.Ico 1 b).filter (· ∈ Finset.range (8 * r)) ⊆ Finset.range (8 * r) := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have hle3 :
      ∑ j ∈ (Finset.Ico 1 b).filter (· ∈ Finset.range (8 * r)), (r + 1) ≤
        ∑ j ∈ Finset.range (8 * r), (r + 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  have hcard : ∑ j ∈ Finset.range (8 * r), (r + 1) = 8 * r * (r + 1) := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

/-- Valuation comparison: `v_p(P_n) + v_p(den) ≤ v_p(num) + extra`. -/
lemma padicValNat_asc_add_den_le (k r n p : ℕ)
    (hk : k = 1 ∨ k = 2 ∨ k = 3) (hr : 1 ≤ r) (hp : p.Prime) :
    padicValNat p (Nat.ascFactorial (k * n + 1) r) + padicValNat p (A211420_den n) ≤
      padicValNat p (A211420_num n) +
        ∑ j ∈ Finset.Ico 1 (Nat.log p (8 * n + k * n + r) + 1),
          (if p ^ j < 8 * r then r + 1 else 0) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let N := 8 * n + k * n + r
  let b := Nat.log p N + 1
  have hbN : Nat.log p N < b := Nat.lt_succ_self _
  have h8_le : 8 * n ≤ N := by unfold N; omega
  have hknr_le : k * n + r ≤ N := by unfold N; omega
  have hkn_le : k * n ≤ N := by unfold N; omega
  have h4_le : 4 * n ≤ N := by unfold N; omega
  have h3_le : 3 * n ≤ N := by unfold N; omega
  have h2_le : 2 * n ≤ N := by unfold N; omega
  have hn_le : n ≤ N := by unfold N; omega
  have hb8 := log_lt_of_le_of_log_lt h8_le hbN
  have hbr := log_lt_of_le_of_log_lt hknr_le hbN
  have hbn0 := log_lt_of_le_of_log_lt hkn_le hbN
  have hb4 := log_lt_of_le_of_log_lt h4_le hbN
  have hb3 := log_lt_of_le_of_log_lt h3_le hbN
  have hb2 := log_lt_of_le_of_log_lt h2_le hbN
  have hbn := log_lt_of_le_of_log_lt hn_le hbN
  have hpos4 : (4 * n).factorial ≠ 0 := factorial_ne_zero _
  have hpos3 : (3 * n).factorial ≠ 0 := factorial_ne_zero _
  have hpos2 : (2 * n).factorial ≠ 0 := factorial_ne_zero _
  have hpos8 : (8 * n).factorial ≠ 0 := factorial_ne_zero _
  have hposn : n.factorial ≠ 0 := factorial_ne_zero _
  have hmul := Nat.factorial_mul_ascFactorial (k * n) r
  have hAsc : Nat.ascFactorial (k * n + 1) r ≠ 0 := by
    intro hz
    rw [hz, Nat.mul_zero] at hmul
    exact (factorial_ne_zero _) hmul.symm
  have hPeq : padicValNat p (Nat.ascFactorial (k * n + 1) r) +
        padicValNat p (k * n).factorial =
        padicValNat p (k * n + r).factorial := by
    have := padicValNat.mul (p := p) (factorial_ne_zero (k * n)) hAsc
    rw [hmul] at this
    omega
  unfold A211420_num A211420_den
  rw [padicValNat.mul hpos8 hposn,
      padicValNat.mul (mul_ne_zero hpos4 hpos3) hpos2,
      padicValNat.mul hpos4 hpos3]
  rw [padicValNat_factorial hbr, padicValNat_factorial hbn0] at hPeq
  rw [padicValNat_factorial hb8, padicValNat_factorial hbn,
      padicValNat_factorial hb4, padicValNat_factorial hb3, padicValNat_factorial hb2]
  have hpt : ∀ j ∈ Finset.Ico 1 b,
      (k * n + r) / p ^ j + (4 * n) / p ^ j + (3 * n) / p ^ j + (2 * n) / p ^ j ≤
        (k * n) / p ^ j + (8 * n) / p ^ j + n / p ^ j +
          (if p ^ j < 8 * r then r + 1 else 0) := by
    intro j hj
    exact alpha_le_psi_add_bound k r n (p ^ j) hk hr (pow_pos hp.pos _)
  have hsum := Finset.sum_le_sum hpt
  simp only [Finset.sum_add_distrib] at hsum hPeq
  -- hPeq : vP + ∑ kn/p^j = ∑ (kn+r)/p^j
  -- hsum : ∑(kn+r) + ∑4 + ∑3 + ∑2 ≤ ∑kn + ∑8 + ∑n + ∑extra
  change
    padicValNat p ((k * n + 1).ascFactorial r) +
      (∑ i ∈ Finset.Ico 1 b, (4 * n) / p ^ i +
        ∑ i ∈ Finset.Ico 1 b, (3 * n) / p ^ i +
          ∑ i ∈ Finset.Ico 1 b, (2 * n) / p ^ i) ≤
    (∑ i ∈ Finset.Ico 1 b, (8 * n) / p ^ i +
      ∑ i ∈ Finset.Ico 1 b, n / p ^ i) +
      ∑ j ∈ Finset.Ico 1 (log p (8 * n + k * n + r) + 1),
        if p ^ j < 8 * r then r + 1 else 0
  -- b = log p N + 1 and N = 8n+kn+r
  have hbdef : b = Nat.log p (8 * n + k * n + r) + 1 := rfl
  rw [← hbdef]
  omega

lemma padicValNat_asc_le_A211420_add (k r n p : ℕ)
    (hk : k = 1 ∨ k = 2 ∨ k = 3) (hr : 1 ≤ r) (hp : p.Prime) :
    padicValNat p (Nat.ascFactorial (k * n + 1) r) ≤
      padicValNat p (A211420 n) + 8 * r * (r + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := padicValNat_asc_add_den_le k r n p hk hr hp
  have hextra := extra_sum_le p r (Nat.log p (8 * n + k * n + r) + 1) hp.one_lt
  rw [padicValNat_A211420 p n hp]
  have hden_le : padicValNat p (A211420_den n) ≤ padicValNat p (A211420_num n) := by
    have hdvd := A211420_den_dvd_num n
    have := padicValNat.div_of_dvd (p := p) hdvd
    have : padicValNat p (A211420_num n / A211420_den n) + padicValNat p (A211420_den n) =
        padicValNat p (A211420_num n) := by
      have hpos : A211420_num n / A211420_den n ≠ 0 := by
        rw [← A211420_eq_div]
        exact A211420_ne_zero n
      have := padicValNat.mul (p := p) hpos (A211420_den_ne_zero n)
      rw [Nat.div_mul_cancel hdvd] at this
      omega
    omega
  omega

lemma padicValNat_asc_le_A211420 (k r n p : ℕ)
    (hk : k = 1 ∨ k = 2 ∨ k = 3) (hr : 1 ≤ r) (hp : p.Prime)
    (hpr : 8 * r ≤ p) :
    padicValNat p (Nat.ascFactorial (k * n + 1) r) ≤ padicValNat p (A211420 n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := padicValNat_asc_add_den_le k r n p hk hr hp
  have hextra0 :
      ∑ j ∈ Finset.Ico 1 (Nat.log p (8 * n + k * n + r) + 1),
        (if p ^ j < 8 * r then r + 1 else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hpj : p ≤ p ^ j := Nat.le_self_pow (Nat.one_le_iff_ne_zero.mp hj1) p
    have : ¬ p ^ j < 8 * r := by omega
    simp [this]
  rw [hextra0, Nat.add_zero] at h
  rw [padicValNat_A211420 p n hp]
  have hden_le : padicValNat p (A211420_den n) ≤ padicValNat p (A211420_num n) := by
    have hdvd := A211420_den_dvd_num n
    have hpos : A211420_num n / A211420_den n ≠ 0 := by
      rw [← A211420_eq_div]
      exact A211420_ne_zero n
    have := padicValNat.mul (p := p) hpos (A211420_den_ne_zero n)
    rw [Nat.div_mul_cancel hdvd] at this
    omega
  omega

/-- The constant `C(k,r)`: a power of `(8r)!` large enough to cover all small primes. -/
def A211420_C (r : ℕ) : ℕ := ((8 * r).factorial) ^ (8 * r * (r + 1))

lemma A211420_C_ne_zero (r : ℕ) : A211420_C r ≠ 0 := by
  unfold A211420_C
  exact pow_ne_zero _ (factorial_ne_zero _)

lemma padicValNat_C_of_lt (p r : ℕ) (hp : p.Prime) (hpr : p < 8 * r) :
    8 * r * (r + 1) ≤ padicValNat p (A211420_C r) := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold A211420_C
  rw [padicValNat.pow _ (factorial_ne_zero _)]
  have hdiv : p ∣ (8 * r).factorial := by
    rw [hp.dvd_factorial]
    exact le_of_lt hpr
  have hge : 1 ≤ padicValNat p (8 * r).factorial :=
    one_le_padicValNat_of_dvd (factorial_ne_zero _) hdiv
  exact Nat.le_mul_of_pos_right _ hge

lemma padicValNat_C_of_ge (p r : ℕ) (hp : p.Prime) (hpr : 8 * r ≤ p) :
    padicValNat p (A211420_C r) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold A211420_C
  rw [padicValNat.pow _ (factorial_ne_zero _)]
  have hne : p ≠ 8 * r := by
    intro heq
    have hnp : ¬ (8 * r).Prime := by
      have hmul : 8 * r = 2 * (4 * r) := by ring
      rw [hmul]
      exact Nat.not_prime_mul (by norm_num) (by omega)
    rw [heq] at hp
    exact hnp hp
  have hnd : ¬ p ∣ (8 * r).factorial := by
    rw [hp.dvd_factorial]
    omega
  simp [padicValNat.eq_zero_of_not_dvd hnd]

/--
General Conjecture:
There are constants $C(k, r)$, for $k \in \{1, 2, 3\}$ and $r \ge 1$,
such that $a(n) \cdot C(k, r) / ((k \cdot n + 1)(k \cdot n + 2)\cdots(k \cdot n + r))$ is an integer for all $n$.
The denominator product $\prod_{i=1}^r (k \cdot n + i)$ is formalized using Nat.ascFactorial,
where $\text{ascFactorial } x r = x(x+1)\cdots(x+r-1)$.
Letting $x = k \cdot n + 1$ gives the desired product.
-/
theorem A211420_general_divisibility_conjecture :
  ∀ (k : ℕ) (r : ℕ), (k = 1 ∨ k = 2 ∨ k = 3) → (r ≥ 1) → ∃ C : ℕ, ∀ n : ℕ,
    Nat.ascFactorial (k * n + 1) r ∣ C * (A211420 n) := by
  intro k r hk hr
  refine ⟨A211420_C r, ?_⟩
  intro n
  have hPpos : Nat.ascFactorial (k * n + 1) r ≠ 0 := by
    have hmul := Nat.factorial_mul_ascFactorial (k * n) r
    intro hz
    rw [hz, Nat.mul_zero] at hmul
    exact (factorial_ne_zero _) hmul.symm
  have hCApos : A211420_C r * A211420 n ≠ 0 :=
    mul_ne_zero (A211420_C_ne_zero r) (A211420_ne_zero n)
  refine (Nat.factorization_prime_le_iff_dvd hPpos hCApos).mp ?_
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
      padicValNat.mul (A211420_C_ne_zero r) (A211420_ne_zero n)]
  by_cases hpr : p < 8 * r
  · have hC := padicValNat_C_of_lt p r hp hpr
    have hmain := padicValNat_asc_le_A211420_add k r n p hk hr hp
    omega
  · have hC : padicValNat p (A211420_C r) = 0 :=
      padicValNat_C_of_ge p r hp (Nat.le_of_not_gt hpr)
    have hmain := padicValNat_asc_le_A211420 k r n p hk hr hp (Nat.le_of_not_gt hpr)
    omega
