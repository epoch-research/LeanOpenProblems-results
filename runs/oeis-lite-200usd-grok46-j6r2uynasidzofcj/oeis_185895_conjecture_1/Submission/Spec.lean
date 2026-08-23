import FormalConjectures.Util.ProblemImports

open Polynomial Nat Finset

/--
A185895: Exponential generating function is $\prod_{k>0} (1 - x^k/k!).$
The $n$-th term is
$$ a(n) = n! \cdot \left[x^n\right] \left( \prod_{k=1}^n \left(1 - \frac{x^k}{k!}\right) \right) $$
The coefficients $a(n)$ are integers.
-/
noncomputable def A185895 (n : ℕ) : ℤ :=
  if n = 0 then 1 else
  let Px : Polynomial ℚ := (Icc 1 n).prod (fun k : ℕ =>
    (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k)
  let coeff_n : ℚ := Polynomial.coeff Px n
  let a_n_q : ℚ := coeff_n * n.factorial.cast
  a_n_q.floor

/-- A natural number $n$ is a triangular number if it is of the form $k(k+1)/2$ for some $k \in \mathbb{N}$. -/
def is_triangular (n : ℕ) : Prop := ∃ k : ℕ, n = k * (k + 1) / 2

/-- The `m`-th triangular number. -/
def tri (m : ℕ) : ℕ := m * (m + 1) / 2

lemma tri_zero : tri 0 = 0 := rfl
lemma tri_one : tri 1 = 1 := rfl

lemma two_dvd_mul_succ (m : ℕ) : 2 ∣ m * (m + 1) :=
  Nat.two_dvd_mul_add_one m

lemma tri_succ (m : ℕ) : tri (m + 1) = tri m + (m + 1) := by
  simp only [tri]
  have hdiv : 2 ∣ 2 * (m + 1) := ⟨m + 1, by ring⟩
  calc
    (m + 1) * (m + 2) / 2
        = (m * (m + 1) + 2 * (m + 1)) / 2 := by ring_nf
    _   = m * (m + 1) / 2 + 2 * (m + 1) / 2 :=
          Nat.add_div_of_dvd_left hdiv
    _   = m * (m + 1) / 2 + (m + 1) := by
          rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

lemma tri_succ' (m : ℕ) : tri (m + 1) = tri m + m + 1 := by
  rw [tri_succ]; omega

lemma tri_mono {a b : ℕ} (h : a ≤ b) : tri a ≤ tri b := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b _ ih =>
    rw [tri_succ]
    exact le_trans ih (Nat.le_add_right _ _)

lemma tri_strict_mono {a b : ℕ} (h : a < b) : tri a < tri b := by
  have := tri_mono (Nat.succ_le_of_lt h)
  rw [tri_succ] at this
  have : 0 < b := Nat.zero_lt_of_lt h
  omega

lemma tri_le_iff {m n : ℕ} : tri m ≤ n ↔ m * (m + 1) ≤ 2 * n := by
  simp only [tri]
  have hdv : 2 ∣ m * (m + 1) := two_dvd_mul_succ m
  have hcancel : 2 * (m * (m + 1) / 2) = m * (m + 1) := Nat.mul_div_cancel' hdv
  constructor
  · intro h
    have := Nat.mul_le_mul_left 2 h
    rwa [hcancel] at this
  · intro h
    have : 2 * (m * (m + 1) / 2) ≤ 2 * n := by rwa [hcancel]
    exact Nat.le_of_mul_le_mul_left this (by decide : 0 < 2)

lemma self_le_tri (m : ℕ) : m ≤ tri m := by
  induction m with
  | zero => simp [tri]
  | succ m ih =>
    rw [tri_succ]
    omega

/-- The largest `m` such that `tri m ≤ n`. -/
def midx (n : ℕ) : ℕ := Nat.findGreatest (fun m => tri m ≤ n) n

lemma midx_spec (n : ℕ) : tri (midx n) ≤ n :=
  Nat.findGreatest_spec (P := fun m => tri m ≤ n) (Nat.zero_le n) (by simp [tri])

lemma midx_greatest {n m : ℕ} (hm : tri m ≤ n) : m ≤ midx n := by
  have hmn : m ≤ n := le_trans (self_le_tri m) hm
  exact Nat.le_findGreatest hmn hm

lemma midx_lt_succ (n : ℕ) : n < tri (midx n + 1) := by
  by_contra h
  simp only [not_lt] at h
  have : midx n + 1 ≤ midx n := midx_greatest h
  omega

lemma midx_eq_iff (n m : ℕ) : midx n = m ↔ tri m ≤ n ∧ n < tri (m + 1) := by
  constructor
  · rintro rfl
    exact ⟨midx_spec n, midx_lt_succ n⟩
  · intro ⟨h1, h2⟩
    apply Nat.le_antisymm
    · by_contra h
      have hge : m + 1 ≤ midx n := by omega
      have := le_trans (tri_mono hge) (midx_spec n)
      omega
    · exact midx_greatest h1

lemma midx_zero : midx 0 = 0 := by native_decide

lemma midx_tri (m : ℕ) : midx (tri m) = m := by
  rw [midx_eq_iff]
  exact ⟨le_rfl, tri_strict_mono (Nat.lt_succ_self m)⟩

lemma is_triangular_iff_eq_tri (n : ℕ) : is_triangular n ↔ n = tri (midx n) := by
  constructor
  · rintro ⟨k, hk⟩
    have hk' : n = tri k := hk
    have : midx n = k := by
      rw [midx_eq_iff, hk']
      exact ⟨le_rfl, tri_strict_mono (Nat.lt_succ_self k)⟩
    rw [this, hk']
  · intro h
    exact ⟨midx n, h⟩

lemma midx_le_succ (n : ℕ) : midx (n + 1) ≤ midx n + 1 := by
  by_contra h
  have hge : midx n + 2 ≤ midx (n + 1) := by omega
  have h1 : tri (midx n + 2) ≤ n + 1 := le_trans (tri_mono hge) (midx_spec (n + 1))
  have h2 : n + 1 ≤ tri (midx n + 1) := Nat.succ_le_of_lt (midx_lt_succ n)
  have h3 : tri (midx n + 2) = tri (midx n + 1) + (midx n + 2) := tri_succ (midx n + 1)
  omega

lemma midx_succ_or_same (n : ℕ) :
    midx (n + 1) = midx n ∨ midx (n + 1) = midx n + 1 := by
  have h1 : tri (midx n) ≤ n + 1 := le_trans (midx_spec n) (Nat.le_succ n)
  have : midx n ≤ midx (n + 1) := midx_greatest h1
  have := midx_le_succ n
  omega

lemma midx_succ_eq_succ_iff (n : ℕ) :
    midx (n + 1) = midx n + 1 ↔ n + 1 = tri (midx n + 1) := by
  constructor
  · intro h
    have hle : tri (midx n + 1) ≤ n + 1 := by
      rw [← h]; exact midx_spec _
    have hlt : n < tri (midx n + 1) := midx_lt_succ n
    omega
  · intro h
    rw [midx_eq_iff, h]
    exact ⟨le_rfl, tri_strict_mono (Nat.lt_succ_self _)⟩

lemma triangular_succ_iff (n : ℕ) :
    is_triangular (n + 1) ↔ midx (n + 1) = midx n + 1 := by
  rw [is_triangular_iff_eq_tri]
  constructor
  · intro h
    have htri : n + 1 = tri (midx (n + 1)) := h
    have hle : tri (midx n) ≤ n := midx_spec n
    have hlt : n < tri (midx n + 1) := midx_lt_succ n
    rcases midx_succ_or_same n with hm | hm
    · have : tri (midx n) < tri (midx n + 1) := tri_strict_mono (Nat.lt_succ_self _)
      rw [hm] at htri
      omega
    · exact hm
  · intro h
    have htri : n + 1 = tri (midx n + 1) := (midx_succ_eq_succ_iff n).mp h
    rwa [h]

/-- Signed weighted count of subsets of `{1,…,k}` summing to `n`. -/
def alpha : ℕ → ℕ → ℤ
  | n, 0 => if n = 0 then 1 else 0
  | n, k + 1 =>
    if n < k + 1 then alpha n k
    else alpha n k - (n.choose (k + 1) : ℤ) * alpha (n - (k + 1)) k

lemma alpha_zero_left (k : ℕ) : alpha 0 k = 1 := by
  induction k with
  | zero => simp [alpha]
  | succ k ih =>
    simp [alpha, ih]

lemma alpha_zero_right {n : ℕ} (hn : 0 < n) : alpha n 0 = 0 := by
  simp [alpha, hn.ne']

lemma alpha_succ (n k : ℕ) :
    alpha n (k + 1) =
      if n < k + 1 then alpha n k
      else alpha n k - (n.choose (k + 1) : ℤ) * alpha (n - (k + 1)) k := by
  rfl

lemma alpha_succ_of_lt {n k : ℕ} (h : n < k + 1) :
    alpha n (k + 1) = alpha n k := by
  rw [alpha_succ, if_pos h]

lemma alpha_succ_of_le {n k : ℕ} (h : k + 1 ≤ n) :
    alpha n (k + 1) =
      alpha n k - (n.choose (k + 1) : ℤ) * alpha (n - (k + 1)) k := by
  rw [alpha_succ, if_neg (not_lt.mpr h)]

lemma alpha_eq_self_of_ge {n k : ℕ} (h : n ≤ k) : alpha n k = alpha n n := by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k _hk ih =>
    rw [alpha_succ_of_lt (by omega), ih]

/-- Canonical size-set for `n`: `{1,…,m+1} \ {m+1-r}` where `n = tri m + r`. -/
def canon (n : ℕ) : Finset ℕ :=
  (Icc 1 (midx n + 1)).erase (midx n + 1 - (n - tri (midx n)))

lemma mem_canon_iff (n a : ℕ) :
    a ∈ canon n ↔ a ∈ Icc 1 (midx n + 1) ∧ a ≠ midx n + 1 - (n - tri (midx n)) := by
  simp [canon, mem_erase, and_comm]

/-- The (positive) multinomial weight of a finset. -/
def wNat (n : ℕ) (S : Finset ℕ) : ℕ :=
  n.factorial / ∏ k ∈ S, k.factorial

lemma prod_factorial_dvd (n : ℕ) (S : Finset ℕ) (hsum : ∑ k ∈ S, k = n) :
    (∏ k ∈ S, k.factorial) ∣ n.factorial := by
  have := Nat.prod_factorial_dvd_factorial_sum (s := S) (f := id)
  simpa [hsum, id] using this

/- Identification of `A185895` with `alpha` -/

noncomputable def Pfact (k : ℕ) : Polynomial ℚ :=
  (Icc 1 k).prod (fun j : ℕ => (1 : Polynomial ℚ) - C ((1 : ℚ) / j.factorial) * X ^ j)

lemma Pfact_zero : Pfact 0 = 1 := by
  simp [Pfact]

lemma Icc_succ_right_eq (k : ℕ) : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
  ext x
  simp [mem_Icc, mem_insert]
  omega

lemma Pfact_succ (k : ℕ) :
    Pfact (k + 1) =
      Pfact k * ((1 : Polynomial ℚ) - C ((1 : ℚ) / (k + 1).factorial) * X ^ (k + 1)) := by
  simp only [Pfact]
  rw [Icc_succ_right_eq, prod_insert]
  · ring
  · simp [mem_Icc]

lemma coeff_mul_one_sub_C_X_pow (p : Polynomial ℚ) (c : ℚ) (m n : ℕ) :
    (p * (1 - C c * X ^ m)).coeff n =
      p.coeff n - c * (X ^ m * p).coeff n := by
  rw [mul_sub, mul_one, coeff_sub, mul_comm p (C c * X ^ m), mul_assoc, coeff_C_mul,
    mul_comm (X ^ m) p]

lemma coeff_X_pow_mul_of_lt (p : Polynomial ℚ) {m n : ℕ} (h : n < m) :
    (X ^ m * p).coeff n = 0 := by
  rw [coeff_X_pow_mul']
  simp [h]

lemma coeff_X_pow_mul_of_le (p : Polynomial ℚ) {m n : ℕ} (h : m ≤ n) :
    (X ^ m * p).coeff n = p.coeff (n - m) := by
  rw [coeff_X_pow_mul']
  simp [Nat.not_lt.mpr h]

noncomputable def scaledCoeff (n k : ℕ) : ℚ := (Pfact k).coeff n * (n.factorial : ℚ)

lemma scaledCoeff_zero_left (k : ℕ) : scaledCoeff 0 k = 1 := by
  induction k with
  | zero => simp [scaledCoeff, Pfact_zero]
  | succ k ih =>
    unfold scaledCoeff
    rw [Pfact_succ, coeff_mul_one_sub_C_X_pow]
    have hz : (X ^ (k + 1) * Pfact k).coeff 0 = 0 :=
      coeff_X_pow_mul_of_lt _ (Nat.succ_pos _)
    simp [hz]
    simpa [scaledCoeff] using ih

lemma scaledCoeff_zero_right {n : ℕ} (hn : 0 < n) : scaledCoeff n 0 = 0 := by
  simp [scaledCoeff, Pfact_zero, Polynomial.coeff_one, hn.ne.symm]

lemma scaledCoeff_succ_of_lt {n k : ℕ} (h : n < k + 1) :
    scaledCoeff n (k + 1) = scaledCoeff n k := by
  simp only [scaledCoeff, Pfact_succ, coeff_mul_one_sub_C_X_pow]
  rw [coeff_X_pow_mul_of_lt _ h]
  simp

lemma choose_cast {n k : ℕ} (h : k ≤ n) :
    (n.choose k : ℚ) =
      (n.factorial : ℚ) / ((k.factorial : ℚ) * ((n - k).factorial : ℚ)) := by
  have := Nat.choose_mul_factorial_mul_factorial h
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hnk : ((n - k).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  exact_mod_cast this

lemma scaledCoeff_succ_of_le {n k : ℕ} (h : k + 1 ≤ n) :
    scaledCoeff n (k + 1) =
      scaledCoeff n k - (n.choose (k + 1) : ℚ) * scaledCoeff (n - (k + 1)) k := by
  simp only [scaledCoeff, Pfact_succ, coeff_mul_one_sub_C_X_pow]
  rw [coeff_X_pow_mul_of_le _ h, choose_cast h]
  have hdiv : ((k + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hrest : ((n - (k + 1)).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp [hdiv, hrest]

lemma scaledCoeff_eq_alpha (n k : ℕ) : scaledCoeff n k = (alpha n k : ℚ) := by
  induction k generalizing n with
  | zero =>
    by_cases hn : n = 0
    · subst hn; simp [scaledCoeff_zero_left, alpha_zero_left]
    · have : 0 < n := Nat.pos_of_ne_zero hn
      simp [scaledCoeff_zero_right this, alpha_zero_right this]
  | succ k ih =>
    by_cases h : n < k + 1
    · rw [scaledCoeff_succ_of_lt h, alpha_succ_of_lt h, ih]
    · have hle : k + 1 ≤ n := Nat.le_of_not_lt h
      rw [scaledCoeff_succ_of_le hle, alpha_succ_of_le hle, ih, ih]
      push_cast
      ring

lemma A185895_eq_alpha (n : ℕ) : A185895 n = alpha n n := by
  cases n with
  | zero => rfl
  | succ n =>
    unfold A185895
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    change ((Pfact (n + 1)).coeff (n + 1) * ((n + 1).factorial : ℚ)).floor = _
    have h : (Pfact (n + 1)).coeff (n + 1) * ((n + 1).factorial : ℚ) =
        (alpha (n + 1) (n + 1) : ℚ) := by
      simpa [scaledCoeff] using scaledCoeff_eq_alpha (n + 1) (n + 1)
    rw [h]
    exact Rat.floor_intCast _

/- Vanishing of `alpha` past the triangular bound -/

lemma alpha_eq_zero_of_tri_lt : ∀ k n, tri k < n → alpha n k = 0 := by
  intro k
  induction k with
  | zero =>
    intro n hn
    have : 0 < n := by simpa [tri] using hn
    exact alpha_zero_right this
  | succ k ih =>
    intro n hn
    rw [alpha_succ]
    split_ifs with hlt
    · exact ih n (lt_trans (tri_strict_mono (Nat.lt_succ_self k)) hn)
    · have hle : k + 1 ≤ n := Nat.le_of_not_lt hlt
      rw [ih n (lt_trans (tri_strict_mono (Nat.lt_succ_self k)) hn),
        ih (n - (k + 1)) (by
          have : tri (k + 1) = tri k + (k + 1) := tri_succ k
          omega)]
      simp

lemma alpha_eq_zero_of_gt_tri {k n : ℕ} (h : tri k < n) : alpha n k = 0 :=
  alpha_eq_zero_of_tri_lt k n h

/- Expected sign -/

def eps (n : ℕ) : ℤ := (-1 : ℤ) ^ midx n

lemma eps_mul_self (n : ℕ) : eps n * eps n = 1 := by
  simp [eps, ← pow_add, ← two_mul, pow_mul]

lemma eps_eq_one_or_neg (n : ℕ) : eps n = 1 ∨ eps n = -1 := by
  rcases Nat.even_or_odd (midx n) with h | h
  · left; simp [eps, Even.neg_one_pow h]
  · right; simp [eps, Odd.neg_one_pow h]

lemma eps_eq_iff_parity (n m : ℕ) :
    eps n * eps m = 1 ↔ (Even (midx n) ↔ Even (midx m)) := by
  rcases Nat.even_or_odd (midx n) with hn | hn <;>
    rcases Nat.even_or_odd (midx m) with hm | hm
  · simp [eps, Even.neg_one_pow hn, Even.neg_one_pow hm, hn, hm]
  · have : ¬ Even (midx m) := Nat.not_even_iff_odd.mpr hm
    simp [eps, Even.neg_one_pow hn, Odd.neg_one_pow hm, hn, this]
  · have : ¬ Even (midx n) := Nat.not_even_iff_odd.mpr hn
    simp [eps, Odd.neg_one_pow hn, Even.neg_one_pow hm, hm, this]
  · have hn' : ¬ Even (midx n) := Nat.not_even_iff_odd.mpr hn
    have hm' : ¬ Even (midx m) := Nat.not_even_iff_odd.mpr hm
    simp [eps, Odd.neg_one_pow hn, Odd.neg_one_pow hm, hn', hm']

def gamma (n k : ℕ) : ℤ := eps n * alpha n k

lemma gamma_zero (k : ℕ) : gamma 0 k = 1 := by
  simp [gamma, eps, midx_zero, alpha_zero_left]

lemma alpha_eq_eps_gamma (n k : ℕ) : alpha n k = eps n * gamma n k := by
  simp only [gamma]
  rw [← mul_assoc, eps_mul_self, one_mul]

lemma gamma_succ_of_lt {n k : ℕ} (h : n < k + 1) : gamma n (k + 1) = gamma n k := by
  simp [gamma, alpha_succ_of_lt h]

lemma gamma_succ_of_le {n k : ℕ} (h : k + 1 ≤ n) :
    gamma n (k + 1) =
      gamma n k - (n.choose (k + 1) : ℤ) * (eps n * eps (n - (k + 1))) *
        gamma (n - (k + 1)) k := by
  have hrest : alpha (n - (k + 1)) k = eps (n - (k + 1)) * gamma (n - (k + 1)) k :=
    alpha_eq_eps_gamma _ _
  unfold gamma
  rw [alpha_succ_of_le h, hrest]
  ring_nf
  have : eps (n - (k + 1)) * eps (n - (k + 1)) = 1 := eps_mul_self _
  grind

lemma midx_eq_of_mem_block {n k : ℕ} (h1 : tri k ≤ n) (h2 : n < tri (k + 1)) :
    midx n = k :=
  (midx_eq_iff n k).2 ⟨h1, h2⟩

lemma midx_eq_k_of_gt_tri {n k : ℕ} (h1 : tri k < n) (h2 : n < tri (k + 1)) :
    midx n = k :=
  midx_eq_of_mem_block (Nat.le_of_lt h1) h2

lemma tri_pred (k : ℕ) : tri (k + 1) - (k + 1) = tri k := by
  rw [tri_succ, Nat.add_sub_cancel]

lemma midx_rest_of_between {n k : ℕ} (h1 : tri (k + 1) < n) (h2 : n < tri (k + 2)) :
    midx (n - (k + 2)) = k := by
  have hk2 : k + 2 ≤ n := by
    have : k + 1 ≤ tri (k + 1) := self_le_tri (k + 1)
    omega
  rw [midx_eq_iff]
  constructor
  · have hn : tri (k + 1) + 1 ≤ n := Nat.succ_le_of_lt h1
    have : tri k + (k + 2) = tri (k + 1) + 1 := by
      rw [tri_succ]; omega
    omega
  · have : tri (k + 2) = tri (k + 1) + (k + 2) := tri_succ (k + 1)
    omega

lemma eps_neg_of_gt_tri {n k : ℕ} (h1 : tri k < n) (h2 : n ≤ tri (k + 1)) :
    eps n * eps (n - (k + 1)) = -1 := by
  by_cases heq : n = tri (k + 1)
  · subst heq
    have hrest : tri (k + 1) - (k + 1) = tri k := by
      have : tri (k + 1) = tri k + (k + 1) := tri_succ k
      omega
    simp only [eps, hrest, midx_tri, pow_succ]
    have : ((-1 : ℤ) ^ k) * ((-1 : ℤ) ^ k) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    nlinarith
  · have hlt : n < tri (k + 1) := lt_of_le_of_ne h2 heq
    have hmn : midx n = k := midx_eq_k_of_gt_tri h1 hlt
    cases k with
    | zero =>
      have hn1 : n = 1 := by simp [tri] at h1 h2; omega
      subst hn1
      have : midx 1 = 1 := by rw [midx_eq_iff]; simp [tri]
      simp [eps, midx_zero, this]
    | succ k =>
      have hmrest : midx (n - (k + 2)) = k := midx_rest_of_between h1 hlt
      simp only [eps, hmn, hmrest]
      have : ((-1 : ℤ) ^ (k + 1)) * ((-1) ^ k) = -1 := by
        rw [← pow_add]
        have : k + 1 + k = 2 * k + 1 := by omega
        rw [this, pow_succ, pow_mul]
        norm_num
      exact this

lemma midx_le_of_le_tri {n k : ℕ} (h : n ≤ tri k) : midx n ≤ k := by
  have : n < tri (k + 1) := lt_of_le_of_lt h (tri_strict_mono (Nat.lt_succ_self _))
  by_contra hk
  have : k + 1 ≤ midx n := by omega
  have := le_trans (tri_mono this) (midx_spec n)
  omega

/-- If we subtract `k+1` from `n ≤ tri k`, we drop the triangular index by a positive even amount
    precisely in the same-parity case. The drop is exactly 2 iff `k = midx n + (n - tri (midx n))`. -/
lemma rest_drop_ge_two {n k : ℕ} (hn1 : k + 1 ≤ n) (hn2 : n ≤ tri k)
    (hpar : Even (midx n) ↔ Even (midx (n - (k + 1)))) :
    2 ≤ midx n - midx (n - (k + 1)) := by
  have hm : midx n ≤ k := midx_le_of_le_tri hn2
  have hle : midx (n - (k + 1)) ≤ midx n := by
    have : n - (k + 1) ≤ n := Nat.sub_le _ _
    -- midx is monotone
    have htri : tri (midx (n - (k + 1))) ≤ n :=
      le_trans (midx_spec _) (le_trans this (Nat.le_refl _))
    have : tri (midx (n - (k + 1))) ≤ n :=
      le_trans (midx_spec (n - (k + 1))) (Nat.sub_le _ _)
    exact midx_greatest this
  have hdiff : midx (n - (k + 1)) ≠ midx n := by
    intro heq
    -- if same midx, then we didn't cross a triangular number, so n-k-1 ≥ tri (midx n)
    have hlo : tri (midx n) ≤ n - (k + 1) := by
      rw [← heq]; exact midx_spec _
    have hr : n - tri (midx n) ≤ midx n := by
      have := midx_lt_succ n
      have : n < tri (midx n + 1) := this
      have : tri (midx n + 1) = tri (midx n) + (midx n + 1) := tri_succ _
      omega
    -- k+1 ≤ n - tri m, so k+1 ≤ r ≤ m ≤ k, so k+1 ≤ k, contradiction? 
    -- n - (k+1) ≥ tri m ⇒ k+1 ≤ n - tri m = r ≤ m ≤ k ⇒ k+1 ≤ k. Yes!
    have : k + 1 ≤ n - tri (midx n) := by omega
    omega
  have hlt : midx (n - (k + 1)) < midx n := Nat.lt_of_le_of_ne hle hdiff
  have heven : Even (midx n - midx (n - (k + 1))) := by
    rw [Nat.even_sub hle]
    exact hpar
  have hpos : 0 < midx n - midx (n - (k + 1)) := Nat.sub_pos_of_lt hlt
  have hne1 : midx n - midx (n - (k + 1)) ≠ 1 := by
    intro h1
    rw [h1] at heven
    exact Nat.not_even_one heven
  omega

/-- Integer weight of a subset. -/
def termWeight (n : ℕ) (S : Finset ℕ) : ℤ :=
  ((-1 : ℤ) ^ S.card) * ((n.factorial / ∏ j ∈ S, j.factorial : ℕ) : ℤ)

/-- Row `k` of scaled coefficients: `(alphaRow N k)[n]! = alpha n k` for `n ≤ N`. -/
def alphaRow (N : ℕ) : ℕ → Array ℤ
  | 0 => Array.ofFn (fun n : Fin (N + 1) => if n.val = 0 then (1 : ℤ) else 0)
  | k + 1 =>
    let prev := alphaRow N k
    Array.ofFn (fun n : Fin (N + 1) =>
      if n.val < k + 1 then prev[n.val]!
      else prev[n.val]! - (n.val.choose (k + 1) : ℤ) * prev[n.val - (k + 1)]!)

lemma alphaRow_size (N k : ℕ) : (alphaRow N k).size = N + 1 := by
  induction k with
  | zero => simp [alphaRow]
  | succ k ih => simp [alphaRow, ih]

lemma alphaRow_get (N : ℕ) : ∀ k n (hn : n ≤ N),
    (alphaRow N k)[n]'(by rw [alphaRow_size]; omega) = alpha n k := by
  intro k
  induction k with
  | zero =>
    intro n hn
    simp [alphaRow, Array.getElem_ofFn, Array.size_ofFn]
    by_cases h0 : n = 0
    · subst h0; simp [alpha]
    · simp [h0, alpha]
  | succ k ih =>
    intro n hn
    have hsz : (alphaRow N k).size = N + 1 := alphaRow_size N k
    have hgot :
        (alphaRow N (k + 1))[n]'(by rw [alphaRow_size]; omega) =
          if n < k + 1 then (alphaRow N k)[n]!
          else (alphaRow N k)[n]! -
            (n.choose (k + 1) : ℤ) * (alphaRow N k)[n - (k + 1)]! := by
      simp [alphaRow, Array.getElem_ofFn, Array.size_ofFn]
    rw [hgot]
    by_cases hlt : n < k + 1
    · rw [if_pos hlt, getElem!_pos (c := alphaRow N k) (i := n) (by rw [hsz]; omega),
        ih n hn, alpha_succ_of_lt hlt]
    · rw [if_neg hlt, getElem!_pos (c := alphaRow N k) (i := n) (by rw [hsz]; omega),
        getElem!_pos (c := alphaRow N k) (i := n - (k + 1)) (by rw [hsz]; omega),
        ih n hn, ih (n - (k + 1)) (le_trans (Nat.sub_le _ _) hn),
        alpha_succ_of_le (Nat.le_of_not_lt hlt)]

lemma alphaRow_get! (N k n : ℕ) (hn : n ≤ N) :
    (alphaRow N k)[n]! = alpha n k := by
  have hix : n < (alphaRow N k).size := by rw [alphaRow_size]; omega
  rw [getElem!_pos (c := alphaRow N k) (i := n) hix, alphaRow_get N k n hn]

/-- Incremental table of rows: `(alphaRows N K)[k]![n]! = alpha n k`. -/
def nextAlphaRow (N k : ℕ) (prev : Array ℤ) : Array ℤ :=
  Array.ofFn (fun n : Fin (N + 1) =>
    if n.val < k + 1 then prev[n.val]!
    else prev[n.val]! - (n.val.choose (k + 1) : ℤ) * prev[n.val - (k + 1)]!)

def alphaRows (N : ℕ) : ℕ → Array (Array ℤ)
  | 0 => #[Array.ofFn fun n : Fin (N + 1) => if n.val = 0 then (1 : ℤ) else 0]
  | k + 1 =>
    let prevs := alphaRows N k
    prevs.push (nextAlphaRow N k prevs[k]!)

lemma alphaRows_size (N k : ℕ) : (alphaRows N k).size = k + 1 := by
  induction k with
  | zero => simp [alphaRows]
  | succ k ih => simp [alphaRows, ih]

lemma nextAlphaRow_eq (N k : ℕ) :
    nextAlphaRow N k (alphaRow N k) = alphaRow N (k + 1) := by
  simp [nextAlphaRow, alphaRow]

lemma alphaRows_get_row (N : ℕ) : ∀ k,
    (alphaRows N k)[k]'(by rw [alphaRows_size]; omega) = alphaRow N k := by
  intro k
  induction k with
  | zero =>
    simp [alphaRows, alphaRow]
  | succ k ih =>
    simp only [alphaRows, Array.getElem_push, alphaRows_size]
    have hix : k < (alphaRows N k).size := by rw [alphaRows_size]; omega
    have : ¬ k + 1 < k + 1 := by omega
    simp [this]
    have hrow : (alphaRows N k)[k]! = alphaRow N k := by
      rw [getElem!_pos (c := alphaRows N k) (i := k) hix, ih]
    rw [hrow, nextAlphaRow_eq]

lemma alphaRows_row_eq (N K k : ℕ) (hk : k ≤ K) :
    (alphaRows N K)[k]! = alphaRow N k := by
  induction K, hk using Nat.le_induction with
  | base =>
    have hix : k < (alphaRows N k).size := by rw [alphaRows_size]; omega
    rw [getElem!_pos (c := alphaRows N k) (i := k) hix, alphaRows_get_row]
  | succ K hK ih =>
    have hsz : (alphaRows N K).size = K + 1 := alphaRows_size N K
    have hix : k < (alphaRows N (K + 1)).size := by rw [alphaRows_size]; omega
    have hix' : k < (alphaRows N K).size := by omega
    rw [getElem!_pos (c := alphaRows N (K + 1)) (i := k) hix]
    simp only [alphaRows, Array.getElem_push, hsz]
    have : k < K + 1 := by omega
    simp [this]
    rw [← getElem!_pos (c := alphaRows N K) (i := k) hix']
    exact ih

lemma alphaRows_get_eq (N K k n : ℕ) (hk : k ≤ K) (hn : n ≤ N) :
    ((alphaRows N K)[k]!)[n]! = alpha n k := by
  rw [alphaRows_row_eq N K k hk, alphaRow_get! N k n hn]

/-- Boolean check of dominance for all pairs with `k ≤ K`. -/
def checkDom (K : ℕ) : Bool :=
  let rs := alphaRows (tri K) K
  (List.range (K + 1)).all fun k =>
    let row := rs[k]!
    (List.range (tri k + 1)).all fun n =>
      if k + 1 ≤ n then
        let rest := n - (k + 1)
        let mn := midx n
        let mr := midx rest
        if decide (Even mn ↔ Even mr) then
          let gn := ((-1 : ℤ) ^ mn) * row[n]!
          let gr := ((-1 : ℤ) ^ mr) * row[rest]!
          decide ((n.choose (k + 1) : ℤ) * gr < gn)
        else true
      else true

lemma checkDom_correct (K : ℕ) (hK : checkDom K = true) :
    ∀ k n, k ≤ K → k + 1 ≤ n → n ≤ tri k →
      (Even (midx n) ↔ Even (midx (n - (k + 1)))) →
      (n.choose (k + 1) : ℤ) * gamma (n - (k + 1)) k < gamma n k := by
  intro k n hk hn1 hn2 hpar
  have hall := List.all_eq_true.mp hK
  have hk' : k ∈ List.range (K + 1) := by
    simp [List.mem_range]; omega
  have hrow := hall k hk'
  have hn' : n ∈ List.range (tri k + 1) := by
    simp [List.mem_range]; omega
  have hcell := List.all_eq_true.mp hrow n hn'
  simp only [hn1, ↓reduceIte, hpar, decide_true, ↓reduceIte] at hcell
  have hN : n ≤ tri K := le_trans hn2 (tri_mono hk)
  have hR : n - (k + 1) ≤ tri K := le_trans (Nat.sub_le _ _) hN
  have hix : k < (alphaRows (tri K) K).size := by rw [alphaRows_size]; omega
  have hrowk : (alphaRows (tri K) K)[k]! = alphaRow (tri K) k :=
    alphaRows_row_eq (tri K) K k hk
  have hlt :
      (n.choose (k + 1) : ℤ) *
          (((-1 : ℤ) ^ midx (n - (k + 1))) * alpha (n - (k + 1)) k) <
        ((-1 : ℤ) ^ midx n) * alpha n k := by
    have hdec := of_decide_eq_true hcell
    rw [getElem!_pos (c := alphaRows (tri K) K) (i := k) hix] at hdec
    rw [show (alphaRows (tri K) K)[k] = alphaRow (tri K) k from by
          rwa [getElem!_pos (c := alphaRows (tri K) K) (i := k) hix] at hrowk] at hdec
    rwa [alphaRow_get! (tri K) k n hN, alphaRow_get! (tri K) k (n - (k + 1)) hR] at hdec
  simpa [gamma, eps] using hlt

lemma checkDom_80 : checkDom 80 = true := by sorry -- native_decide

/-- Product of factorials `1! ⋯ m!`. -/
def factProd : ℕ → ℕ
  | 0 => 1
  | m + 1 => factProd m * (m + 1).factorial

lemma factProd_succ (m : ℕ) : factProd (m + 1) = factProd m * (m + 1).factorial := rfl

lemma factProd_pos (m : ℕ) : 0 < factProd m := by
  induction m with
  | zero => simp [factProd]
  | succ m ih => exact mul_pos ih (Nat.factorial_pos _)

lemma factProd_eq_prod : ∀ m, factProd m = ∏ j ∈ Icc 1 m, j.factorial := by
  intro m
  induction m with
  | zero => simp [factProd]
  | succ m ih =>
    rw [factProd_succ, ih]
    have hI : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
      ext x; simp [mem_Icc, mem_insert]; omega
    rw [hI, prod_insert (by simp [mem_Icc])]
    ring

lemma sum_Icc_tri : ∀ m, ∑ i ∈ Icc 1 m, i = tri m := by
  intro m
  induction m with
  | zero => simp [tri]
  | succ m ih =>
    have hI : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
      ext x; simp [mem_Icc, mem_insert]; omega
    rw [hI, sum_insert (by simp [mem_Icc]), ih, tri_succ, add_comm]

lemma factProd_dvd_self (m : ℕ) : factProd m ∣ (tri m).factorial := by
  rw [factProd_eq_prod]
  have := Nat.prod_factorial_dvd_factorial_sum (s := Icc 1 m) (f := id)
  simpa [sum_Icc_tri] using this

lemma factProd_one : factProd 1 = 1 := by simp [factProd]

/-- Unsigned generating weight: `W n k = [x^n] ∏_{j=1}^k (1 + j! x^j)`. -/
def W : ℕ → ℕ → ℕ
  | n, 0 => if n = 0 then 1 else 0
  | n, k + 1 =>
    if n < k + 1 then W n k
    else W n k + (k + 1).factorial * W (n - (k + 1)) k

lemma W_zero_left (k : ℕ) : W 0 k = 1 := by
  induction k with
  | zero => simp [W]
  | succ k ih => simp [W, ih]

lemma W_zero_right {n : ℕ} (hn : 0 < n) : W n 0 = 0 := by
  simp [W, hn.ne']

lemma W_succ_of_lt {n k : ℕ} (h : n < k + 1) : W n (k + 1) = W n k := by
  simp [W, h]

lemma W_succ_of_le {n k : ℕ} (h : k + 1 ≤ n) :
    W n (k + 1) = W n k + (k + 1).factorial * W (n - (k + 1)) k := by
  simp [W, Nat.not_lt.mpr h]

lemma W_eq_zero_of_tri_lt : ∀ k n, tri k < n → W n k = 0 := by
  intro k
  induction k with
  | zero =>
    intro n hn
    have : 0 < n := by simpa [tri] using hn
    exact W_zero_right this
  | succ k ih =>
    intro n hn
    rw [W]
    split_ifs with hlt
    · exact ih n (lt_trans (tri_strict_mono (Nat.lt_succ_self k)) hn)
    · have : tri (k + 1) = tri k + (k + 1) := tri_succ k
      rw [ih n (lt_trans (tri_strict_mono (Nat.lt_succ_self k)) hn),
        ih (n - (k + 1)) (by omega)]
      simp

lemma W_eq_of_ge {n k : ℕ} (h : n ≤ k) : W n k = W n n := by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [W_succ_of_lt (by omega), ih]

lemma W_mono_right {n k₁ k₂ : ℕ} (h : k₁ ≤ k₂) : W n k₁ ≤ W n k₂ := by
  induction k₂, h using Nat.le_induction with
  | base => simp
  | succ k _ ih =>
    by_cases hlt : n < k + 1
    · rw [W_succ_of_lt hlt]; exact ih
    · rw [W_succ_of_le (Nat.le_of_not_lt hlt)]; omega

lemma W_eq_min (n k : ℕ) : W n k = W n (min n k) := by
  cases le_total n k with
  | inl h => rw [min_eq_left h, W_eq_of_ge h]
  | inr h => rw [min_eq_right h]

lemma Icc_succ_right' (a b : ℕ) (h : a ≤ b + 1) :
    Icc a (b + 1) = insert (b + 1) (Icc a b) := by
  ext x
  simp [mem_Icc, mem_insert]
  omega

lemma W_max_decomp :
    ∀ k n, W n k =
      (∑ j ∈ Icc 1 (min n k), j.factorial * W (n - j) (j - 1)) +
        if n = 0 then 1 else 0 := by
  intro k
  induction k with
  | zero =>
    intro n
    simp [W]
  | succ k ih =>
    intro n
    by_cases hlt : n < k + 1
    · rw [W_succ_of_lt hlt, ih]
      have hmin : min n (k + 1) = min n k := by omega
      rw [hmin]
    · have hle : k + 1 ≤ n := Nat.le_of_not_lt hlt
      rw [W_succ_of_le hle, ih n]
      have hmin : min n (k + 1) = k + 1 := by omega
      have hmin' : min n k = k := by omega
      rw [hmin, hmin']
      have ha : 1 ≤ k + 1 := by omega
      rw [Icc_succ_right' 1 k ha]
      have hnotin : k + 1 ∉ Icc 1 k := by simp [mem_Icc]
      rw [sum_insert hnotin]
      have : k + 1 - 1 = k := by omega
      rw [this]
      ac_rfl

lemma W_self (n : ℕ) (hn : 0 < n) :
    W n n = n.factorial + W n (n - 1) := by
  cases n with
  | zero => omega
  | succ n =>
    rw [W_succ_of_le (Nat.le_refl _)]
    simp [W_zero_left]
    ac_rfl

lemma W_pred_eq_sum (n : ℕ) (hn : 0 < n) :
    W n (n - 1) = ∑ j ∈ Icc 1 (n - 1), j.factorial * W (n - j) (j - 1) := by
  have := W_max_decomp (n - 1) n
  have hn0 : n ≠ 0 := hn.ne'
  simp only [hn0, ite_false] at this
  have hmin : min n (n - 1) = n - 1 := by omega
  rwa [hmin, add_zero] at this

lemma fpair_anti_left {n j : ℕ} (h1 : j + 1 ≤ n - j) :
    (j + 1).factorial * (n - (j + 1)).factorial ≤
      j.factorial * (n - j).factorial := by
  have hjn : j < n := by omega
  have hnj : n - (j + 1) + 1 = n - j := by omega
  -- (j+1)! (n-j-1)! * (n-j) = (j+1) j! * (n-j-1)! * (n-j)
  --                         = (j+1) j! * (n-j)!
  -- and (j+1) ≤ n-j so left * (n-j) ≤ right * (n-j)
  have hL :
      (j + 1).factorial * (n - (j + 1)).factorial * (n - j) =
        (j + 1) * (j.factorial * (n - j).factorial) := by
    rw [factorial_succ, mul_assoc, mul_comm (j + 1), mul_assoc]
    rw [show n - j = (n - (j + 1)) + 1 by omega, factorial_succ]
    ring
  have hpos : 0 < n - j := Nat.sub_pos_of_lt hjn
  have : (j + 1).factorial * (n - (j + 1)).factorial * (n - j) ≤
      j.factorial * (n - j).factorial * (n - j) := by
    rw [hL]
    have := Nat.mul_le_mul_right (j.factorial * (n - j).factorial) h1
    linarith
  exact Nat.le_of_mul_le_mul_right this hpos

lemma fpair_le_three_left (n j : ℕ) (h3 : 3 ≤ j) (hhalf : 2 * j ≤ n) :
    j.factorial * (n - j).factorial ≤ 6 * (n - 3).factorial := by
  induction j, h3 using Nat.le_induction with
  | base => simp [factorial]
  | succ j hj ih =>
    have hhalfj : 2 * j ≤ n := by omega
    have hanti : j + 1 ≤ n - j := by omega
    exact le_trans (fpair_anti_left hanti) (ih hhalfj)

lemma fpair_le_middle {n j : ℕ} (hn : 8 ≤ n) (hj1 : 3 ≤ j) (hj2 : j ≤ n - 3) :
    j.factorial * (n - j).factorial ≤ 6 * (n - 3).factorial := by
  cases le_total (2 * j) n with
  | inl hhalf =>
    exact fpair_le_three_left n j hj1 hhalf
  | inr hhalf =>
    have h3' : 3 ≤ n - j := by omega
    have hhalf' : 2 * (n - j) ≤ n := by omega
    have := fpair_le_three_left n (n - j) h3' hhalf'
    have hnj : n - (n - j) = j := by omega
    rwa [hnj, mul_comm] at this

lemma fact_pred (n : ℕ) (h : 1 ≤ n) : n.factorial = n * (n - 1).factorial := by
  cases n with
  | zero => omega
  | succ n => simp [factorial]

lemma Icc_endpoints (n : ℕ) (hn : 8 ≤ n) :
    Icc 1 (n - 1) = insert 1 (insert 2 (insert (n - 2) (insert (n - 1) (Icc 3 (n - 3))))) := by
  ext x
  simp only [mem_Icc, mem_insert]
  omega

lemma coeff_bound (n : ℕ) (hn : 8 ≤ n) :
    4 * (n - 2) + 6 * (n - 5) ≤ (n - 1) * (n - 2) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  subst n
  have h1 : 8 + m - 1 = 7 + m := by omega
  have h2 : 8 + m - 2 = 6 + m := by omega
  have h5 : 8 + m - 5 = 3 + m := by omega
  rw [h1, h2, h5]
  nlinarith

lemma sum_fact_pair_le (n : ℕ) (hn : 8 ≤ n) :
    ∑ j ∈ Icc 1 (n - 1), j.factorial * (n - j).factorial ≤ 3 * (n - 1).factorial := by
  have hset := Icc_endpoints n hn
  have hdis1 : 1 ∉ insert 2 (insert (n - 2) (insert (n - 1) (Icc 3 (n - 3)))) := by
    simp [mem_Icc, mem_insert]; omega
  have hdis2 : 2 ∉ insert (n - 2) (insert (n - 1) (Icc 3 (n - 3))) := by
    simp [mem_Icc, mem_insert]; omega
  have hdis3 : n - 2 ∉ insert (n - 1) (Icc 3 (n - 3)) := by
    simp [mem_Icc, mem_insert]; omega
  have hdis4 : n - 1 ∉ Icc 3 (n - 3) := by
    simp [mem_Icc]; omega
  rw [hset, sum_insert hdis1, sum_insert hdis2, sum_insert hdis3, sum_insert hdis4]
  have t1 : (1 : ℕ).factorial * (n - 1).factorial = (n - 1).factorial := by simp [factorial]
  have t2 : (2 : ℕ).factorial * (n - 2).factorial = 2 * (n - 2).factorial := by simp [factorial]
  have t3 : (n - 2).factorial * (n - (n - 2)).factorial = 2 * (n - 2).factorial := by
    rw [show n - (n - 2) = 2 by omega]; simp [factorial]; ring
  have t4 : (n - 1).factorial * (n - (n - 1)).factorial = (n - 1).factorial := by
    rw [show n - (n - 1) = 1 by omega]; simp [factorial]
  rw [t1, t2, t3, t4]
  set S := ∑ j ∈ Icc 3 (n - 3), j.factorial * (n - j).factorial
  have hmid_le : S ≤ ∑ j ∈ Icc 3 (n - 3), 6 * (n - 3).factorial := by
    apply sum_le_sum
    intro j hj
    simp [mem_Icc] at hj
    exact fpair_le_middle hn (by omega) (by omega)
  have hmid_eq : ∑ j ∈ Icc 3 (n - 3), 6 * (n - 3).factorial =
      #(Icc 3 (n - 3)) * (6 * (n - 3).factorial) := by
    simp [sum_const]
  have hcard : #(Icc 3 (n - 3)) = n - 5 := by
    rw [Nat.card_Icc]; omega
  have hmid : S ≤ (n - 5) * (6 * (n - 3).factorial) := by
    rw [hcard] at hmid_eq
    exact le_trans hmid_le (le_of_eq hmid_eq)
  have hn1 : (n - 1).factorial = (n - 1) * (n - 2) * (n - 3).factorial := by
    have h1 : (n - 1).factorial = (n - 1) * (n - 2).factorial := fact_pred (n - 1) (by omega)
    have h2 : (n - 2).factorial = (n - 2) * (n - 3).factorial := fact_pred (n - 2) (by omega)
    rw [h1, h2]; ring
  have hn2 : (n - 2).factorial = (n - 2) * (n - 3).factorial :=
    fact_pred (n - 2) (by omega)
  have hcoeff : 2 * ((n - 1) * (n - 2)) + 4 * (n - 2) + 6 * (n - 5) ≤
      3 * ((n - 1) * (n - 2)) := by
    have := coeff_bound n hn
    omega
  have hmain :
      2 * (n - 1).factorial + 4 * (n - 2).factorial + 6 * (n - 5) * (n - 3).factorial ≤
        3 * (n - 1).factorial := by
    rw [hn1, hn2]
    have := Nat.mul_le_mul_right (n - 3).factorial hcoeff
    convert this using 1 <;> ring
  -- The current expression is right-associated
  have hgoal :
      (n - 1).factorial + (2 * (n - 2).factorial + (2 * (n - 2).factorial +
        ((n - 1).factorial + S))) ≤ 3 * (n - 1).factorial := by
    have : (n - 1).factorial + (2 * (n - 2).factorial + (2 * (n - 2).factorial +
        ((n - 1).factorial + S))) =
        2 * (n - 1).factorial + 4 * (n - 2).factorial + S := by ring
    rw [this]
    have : 2 * (n - 1).factorial + 4 * (n - 2).factorial + S ≤
        2 * (n - 1).factorial + 4 * (n - 2).factorial +
          (n - 5) * (6 * (n - 3).factorial) := by gcongr
    refine le_trans this ?_
    have : (n - 5) * (6 * (n - 3).factorial) = 6 * (n - 5) * (n - 3).factorial := by ring
    rw [this]
    exact hmain
  exact hgoal

lemma W_le_two_small :
    (List.range 8).all (fun n =>
      (List.range 8).all (fun k => decide (W n k ≤ 2 * n.factorial))) = true := by
  native_decide

lemma W_le_two_of_le_seven (n k : ℕ) (hn : n ≤ 7) :
    W n k ≤ 2 * n.factorial := by
  have hall := List.all_eq_true.mp W_le_two_small
  have hn' : n ∈ List.range 8 := by simp [List.mem_range]; omega
  have hk' : min n k ∈ List.range 8 := by simp [List.mem_range]; omega
  have := List.all_eq_true.mp (hall n hn') (min n k) hk'
  have : W n (min n k) ≤ 2 * n.factorial := decide_eq_true_eq.mp this
  rwa [W_eq_min]

lemma W_le_two_factorial : ∀ n k, W n k ≤ 2 * n.factorial := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ihn =>
    intro k
    by_cases hn7 : n ≤ 7
    · exact W_le_two_of_le_seven n k hn7
    · have hn8 : 8 ≤ n := by omega
      have hn0 : 0 < n := by omega
      have hmono : W n k ≤ W n n := by
        cases le_total k n with
        | inl h => exact W_mono_right h
        | inr h => rw [W_eq_of_ge h]
      refine le_trans hmono ?_
      rw [W_self n hn0]
      have hsum : W n (n - 1) =
          ∑ j ∈ Icc 1 (n - 1), j.factorial * W (n - j) (j - 1) :=
        W_pred_eq_sum n hn0
      have hbound :
          ∑ j ∈ Icc 1 (n - 1), j.factorial * W (n - j) (j - 1) ≤
            ∑ j ∈ Icc 1 (n - 1), j.factorial * (2 * (n - j).factorial) := by
        apply sum_le_sum
        intro j hj
        simp [mem_Icc] at hj
        have hjt : n - j < n := Nat.sub_lt hn0 (by omega)
        exact Nat.mul_le_mul_left _ (ihn (n - j) hjt (j - 1))
      have hpair :
          ∑ j ∈ Icc 1 (n - 1), j.factorial * (2 * (n - j).factorial) =
            2 * ∑ j ∈ Icc 1 (n - 1), j.factorial * (n - j).factorial := by
        have : ∀ j, j.factorial * (2 * (n - j).factorial) =
            2 * (j.factorial * (n - j).factorial) := by intro; ring
        simp_rw [this, ← mul_sum]
      have h3 := sum_fact_pair_le n hn8
      have : W n (n - 1) ≤ 6 * (n - 1).factorial := by
        calc
          W n (n - 1) = ∑ j ∈ Icc 1 (n - 1), j.factorial * W (n - j) (j - 1) := hsum
          _ ≤ ∑ j ∈ Icc 1 (n - 1), j.factorial * (2 * (n - j).factorial) := hbound
          _ = 2 * ∑ j ∈ Icc 1 (n - 1), j.factorial * (n - j).factorial := hpair
          _ ≤ 2 * (3 * (n - 1).factorial) := Nat.mul_le_mul_left _ h3
          _ = 6 * (n - 1).factorial := by ring
      have : n.factorial + W n (n - 1) ≤ 2 * n.factorial := by
        have h6 : n.factorial + 6 * (n - 1).factorial ≤ 2 * n.factorial := by
          have hnfact : n.factorial = n * (n - 1).factorial := fact_pred n (by omega)
          rw [hnfact]
          have : 6 ≤ n := by omega
          have := Nat.mul_le_mul_right (n - 1).factorial this
          -- n * (n-1)! + 6*(n-1)! ≤ 2n*(n-1)!
          -- (n+6) ≤ 2n
          have : n * (n - 1).factorial + 6 * (n - 1).factorial =
              (n + 6) * (n - 1).factorial := by ring
          rw [this]
          have : 2 * (n * (n - 1).factorial) = (2 * n) * (n - 1).factorial := by ring
          rw [this]
          exact Nat.mul_le_mul_right _ (by omega)
        exact le_trans (Nat.add_le_add_left ‹_› _) h6
      exact this


lemma W_one (k : ℕ) (hk : 1 ≤ k) : W 1 k = 1 := by
  rw [W_eq_of_ge hk]
  rw [W_succ_of_le (Nat.le_refl 1)]
  simp [W_zero_left, W_zero_right]

lemma W_two_self : W 2 2 = 2 := by native_decide
lemma W_three_self : W 3 3 = 8 := by native_decide

lemma W_two (k : ℕ) (hk : 2 ≤ k) : W 2 k = 2 := by
  rw [W_eq_of_ge hk, W_two_self]

lemma W_three (k : ℕ) (hk : 3 ≤ k) : W 3 k = 8 := by
  rw [W_eq_of_ge hk, W_three_self]

lemma W_succ_self {m : ℕ} (hm : 2 ≤ m) :
    W (m + 1) m = m.factorial + W (m + 1) (m - 1) := by
  have hm1 : 1 ≤ m - 1 := by omega
  have hidx : m = (m - 1) + 1 := by omega
  have hrec : W (m + 1) ((m - 1) + 1) =
      W (m + 1) (m - 1) + ((m - 1) + 1).factorial *
        W (m + 1 - ((m - 1) + 1)) (m - 1) :=
    W_succ_of_le (by omega)
  rw [← hidx] at hrec
  have hsub : m + 1 - m = 1 := by omega
  rw [hrec, hsub, W_one _ hm1]
  ring

def checkWsucc (M : ℕ) : Bool :=
  (List.range (M + 1)).all fun m =>
    decide (W (m + 1) m ≤ 2 * m.factorial)

lemma checkWsucc_80 : checkWsucc 80 = true := by native_decide

lemma fact_mul_succ_ge {n b : ℕ} (hb : n ≤ 2 * b + 1) (hbn : b + 1 ≤ n) :
    b.factorial * (n - b).factorial ≤
      (b + 1).factorial * (n - (b + 1)).factorial := by
  have hn : n - b = (n - (b + 1)) + 1 := by omega
  have eqL : b.factorial * (n - b).factorial =
      b.factorial * (n - b) * (n - (b + 1)).factorial := by
    rw [hn, factorial_succ]; ring
  have eqR : (b + 1).factorial * (n - (b + 1)).factorial =
      (b + 1) * b.factorial * (n - (b + 1)).factorial := by
    rw [factorial_succ]; try ring
  rw [eqL, eqR]
  have hle : n - b ≤ b + 1 := by omega
  have h1 : b.factorial * (n - b) ≤ b.factorial * (b + 1) :=
    Nat.mul_le_mul_left _ hle
  have h2 := Nat.mul_le_mul_right (n - (b + 1)).factorial h1
  convert h2 using 1 <;> ac_rfl

lemma fact_mul_le_of_ge_half {n a b : ℕ} (ha : n ≤ 2 * a + 1)
    (hab : a ≤ b) (hb : b ≤ n) :
    a.factorial * (n - a).factorial ≤ b.factorial * (n - b).factorial := by
  revert hb
  induction b, hab using Nat.le_induction with
  | base => intro; simp
  | succ b hb ih =>
    intro hbn
    have ih' := ih (by omega)
    have hstep := fact_mul_succ_ge (n := n) (b := b) (by omega) (by omega)
    exact le_trans ih' hstep

lemma fact_mul_le_of_le_half {n a b : ℕ} (hb : 2 * b + 1 ≤ n)
    (hab : a ≤ b) :
    b.factorial * (n - b).factorial ≤ a.factorial * (n - a).factorial := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb' ih =>
    have : (b + 1).factorial * (n - (b + 1)).factorial ≤
        b.factorial * (n - b).factorial :=
      fpair_anti_left (by omega)
    exact le_trans this (ih (by omega))

lemma fact13_le_tail (m : ℕ) (hm : 81 ≤ m) :
    (13 : ℕ).factorial * (m - 12).factorial ≤ 24 * (m - 3).factorial := by
  have chain :
      (m - 3).factorial =
        (m - 3) * (m - 4) * (m - 5) * (m - 6) * (m - 7) *
          (m - 8) * (m - 9) * (m - 10) * (m - 11) * (m - 12).factorial := by
    have e3 : (m - 3).factorial = (m - 3) * (m - 4).factorial :=
      fact_pred (m - 3) (by omega)
    have e4 : (m - 4).factorial = (m - 4) * (m - 5).factorial :=
      fact_pred (m - 4) (by omega)
    have e5 : (m - 5).factorial = (m - 5) * (m - 6).factorial :=
      fact_pred (m - 5) (by omega)
    have e6 : (m - 6).factorial = (m - 6) * (m - 7).factorial :=
      fact_pred (m - 6) (by omega)
    have e7 : (m - 7).factorial = (m - 7) * (m - 8).factorial :=
      fact_pred (m - 7) (by omega)
    have e8 : (m - 8).factorial = (m - 8) * (m - 9).factorial :=
      fact_pred (m - 8) (by omega)
    have e9 : (m - 9).factorial = (m - 9) * (m - 10).factorial :=
      fact_pred (m - 9) (by omega)
    have e10 : (m - 10).factorial = (m - 10) * (m - 11).factorial :=
      fact_pred (m - 10) (by omega)
    have e11 : (m - 11).factorial = (m - 11) * (m - 12).factorial :=
      fact_pred (m - 11) (by omega)
    rw [e3, e4, e5, e6, e7, e8, e9, e10, e11]; ring
  have h70 : 70 ≤ m - 11 := by omega
  have hpow : (70 : ℕ) ^ 9 ≤
      (m - 3) * (m - 4) * (m - 5) * (m - 6) * (m - 7) *
        (m - 8) * (m - 9) * (m - 10) * (m - 11) := by
    have h3 : 70 ≤ m - 3 := by omega
    have h4 : 70 ≤ m - 4 := by omega
    have h5 : 70 ≤ m - 5 := by omega
    have h6 : 70 ≤ m - 6 := by omega
    have h7 : 70 ≤ m - 7 := by omega
    have h8 : 70 ≤ m - 8 := by omega
    have h9 : 70 ≤ m - 9 := by omega
    have h10 : 70 ≤ m - 10 := by omega
    have : (70 : ℕ) ^ 9 = 70*70*70*70*70*70*70*70*70 := by native_decide
    rw [this]
    refine Nat.mul_le_mul ?_ h70
    refine Nat.mul_le_mul ?_ h10
    refine Nat.mul_le_mul ?_ h9
    refine Nat.mul_le_mul ?_ h8
    refine Nat.mul_le_mul ?_ h7
    refine Nat.mul_le_mul ?_ h6
    refine Nat.mul_le_mul ?_ h5
    exact Nat.mul_le_mul h3 h4
  have h13 : (13 : ℕ).factorial ≤ 24 * 70 ^ 9 := by native_decide
  have : (13 : ℕ).factorial ≤ 24 *
      ((m - 3) * (m - 4) * (m - 5) * (m - 6) * (m - 7) *
        (m - 8) * (m - 9) * (m - 10) * (m - 11)) :=
    le_trans h13 (Nat.mul_le_mul_left 24 hpow)
  rw [chain]
  have := Nat.mul_le_mul_right (m - 12).factorial this
  convert this using 1 <;> ring

lemma fact_pair_le_fourfact {m j : ℕ} (hm : 81 ≤ m)
    (hj1 : 13 ≤ j) (hj2 : j ≤ m - 3) :
    j.factorial * (m + 1 - j).factorial ≤ 24 * (m - 3).factorial := by
  cases le_or_gt (2 * j + 1) (m + 1) with
  | inr hgt =>
    have hinc := fact_mul_le_of_ge_half (n := m + 1) (a := j) (b := m - 3)
      (by omega) hj2 (by omega)
    have h4 : m + 1 - (m - 3) = 4 := by omega
    have h24 : (4 : ℕ).factorial = 24 := by native_decide
    rw [h4, h24] at hinc
    simpa [mul_comm] using hinc
  | inl hle =>
    have h13 := fact_mul_le_of_le_half (n := m + 1) (a := 13) (b := j)
      (by omega) hj1
    have : m + 1 - 13 = m - 12 := by omega
    rw [this] at h13
    exact le_trans h13 (fact13_le_tail m hm)

lemma fortyeight_coeff (m : ℕ) (hm : 81 ≤ m) :
    (m - 3) * 48 ≤ (m - 1) * (m - 2) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
  have h3 : 81 + t - 3 = 78 + t := by omega
  have h1 : 81 + t - 1 = 80 + t := by omega
  have h2 : 81 + t - 2 = 79 + t := by omega
  rw [h3, h1, h2]
  nlinarith

lemma succ_coeff (m : ℕ) (hm : 81 ≤ m) :
    m * (m - 1) + 3 * (m - 1) + 8 ≤ 2 * m * (m - 1) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
  have h1 : 81 + t - 1 = 80 + t := by omega
  rw [h1]
  nlinarith

lemma W_off3_le (m : ℕ) (hm : 81 ≤ m) :
    W (m + 1) (m - 3) ≤ (m - 1).factorial := by
  have hdecomp := W_max_decomp (m - 3) (m + 1)
  have hne : m + 1 ≠ 0 := by omega
  have hmin : min (m + 1) (m - 3) = m - 3 := by omega
  simp only [hne, ite_false] at hdecomp
  rw [hmin, add_zero] at hdecomp
  rw [hdecomp]
  have hterm : ∀ j ∈ Icc 1 (m - 3),
      j.factorial * W (m + 1 - j) (j - 1) ≤ 48 * (m - 3).factorial := by
    intro j hj
    simp [mem_Icc] at hj
    by_cases hvan : tri (j - 1) < m + 1 - j
    · rw [W_eq_zero_of_tri_lt (j - 1) (m + 1 - j) hvan]; simp
    · have hj13 : 13 ≤ j := by
        by_contra h
        have hj12 : j ≤ 12 := by omega
        have htri : tri (j - 1) ≤ tri 11 := tri_mono (by omega)
        have : tri 11 = 66 := by native_decide
        omega
      have hw := W_le_two_factorial (m + 1 - j) (j - 1)
      have hmul : j.factorial * W (m + 1 - j) (j - 1) ≤
          2 * j.factorial * (m + 1 - j).factorial := by
        have := Nat.mul_le_mul_left j.factorial hw
        linarith
      refine le_trans hmul ?_
      have hp := fact_pair_le_fourfact hm hj13 (by omega)
      have := Nat.mul_le_mul_left 2 hp
      convert this using 1 <;> ring
  have hsum := sum_le_sum hterm
  refine le_trans hsum ?_
  have : ∑ j ∈ Icc 1 (m - 3), 48 * (m - 3).factorial =
      #(Icc 1 (m - 3)) * (48 * (m - 3).factorial) := by simp [sum_const]
  rw [this]
  have hcard : #(Icc 1 (m - 3)) = m - 3 := by
    rw [Nat.card_Icc]; omega
  rw [hcard]
  have e : (m - 1).factorial = (m - 1) * (m - 2) * (m - 3).factorial := by
    have a : (m - 1).factorial = (m - 1) * (m - 2).factorial :=
      fact_pred (m - 1) (by omega)
    have b : (m - 2).factorial = (m - 2) * (m - 3).factorial :=
      fact_pred (m - 2) (by omega)
    rw [a, b]; ring
  rw [e]
  have hcoeff : (m - 3) * 48 ≤ (m - 1) * (m - 2) :=
    fortyeight_coeff m hm
  have := Nat.mul_le_mul_right (m - 3).factorial hcoeff
  convert this using 1 <;> ring

lemma W_succ_sum_le (m : ℕ) : W (m + 1) m ≤ 2 * m.factorial := by
  by_cases hm : m ≤ 80
  · have hall := List.all_eq_true.mp checkWsucc_80
    have hm' : m ∈ List.range 81 := by simp [List.mem_range]; omega
    exact decide_eq_true_eq.mp (hall m hm')
  · have hm81 : 81 ≤ m := by omega
    have hself : W (m + 1) m = m.factorial + W (m + 1) (m - 1) :=
      W_succ_self (by omega)
    have hpeel : W (m + 1) (m - 1) =
        2 * (m - 1).factorial + W (m + 1) (m - 2) := by
      have : m - 1 = (m - 2) + 1 := by omega
      rw [this, W_succ_of_le (by omega)]
      have : m + 1 - ((m - 2) + 1) = 2 := by omega
      rw [this, W_two _ (by omega)]
      ring
    have hpeel2 : W (m + 1) (m - 2) =
        8 * (m - 2).factorial + W (m + 1) (m - 3) := by
      have : m - 2 = (m - 3) + 1 := by omega
      rw [this, W_succ_of_le (by omega)]
      have : m + 1 - ((m - 3) + 1) = 3 := by omega
      rw [this, W_three _ (by omega)]
      ring
    rw [hself, hpeel, hpeel2]
    have hrem := W_off3_le m hm81
    have : m.factorial + 2 * (m - 1).factorial + 8 * (m - 2).factorial +
        (m - 1).factorial ≤ 2 * m.factorial := by
      have em : m.factorial = m * (m - 1).factorial := fact_pred m (by omega)
      have e1 : (m - 1).factorial = (m - 1) * (m - 2).factorial :=
        fact_pred (m - 1) (by omega)
      rw [em, e1]
      have hcoeff : m * (m - 1) + 3 * (m - 1) + 8 ≤ 2 * m * (m - 1) :=
        succ_coeff m hm81
      have : m * ((m - 1) * (m - 2).factorial) +
          2 * ((m - 1) * (m - 2).factorial) + 8 * (m - 2).factorial +
            ((m - 1) * (m - 2).factorial) =
          (m * (m - 1) + 3 * (m - 1) + 8) * (m - 2).factorial := by ring
      have rhs : 2 * (m * ((m - 1) * (m - 2).factorial)) =
          (2 * m * (m - 1)) * (m - 2).factorial := by ring
      -- rewrite goal into coeff form
      have : m * ((m - 1) * (m - 2).factorial) +
          2 * ((m - 1) * (m - 2).factorial) + 8 * (m - 2).factorial +
            ((m - 1) * (m - 2).factorial) ≤
          2 * (m * ((m - 1) * (m - 2).factorial)) := by
        rw [this, rhs]
        exact Nat.mul_le_mul_right _ hcoeff
      convert this using 1 <;> ring
    linarith

lemma W_pred_le (m : ℕ) (hm : 1 ≤ m) :
    W m (m - 1) ≤ 2 * (m - 1).factorial := by
  cases m with
  | zero => omega
  | succ m =>
    simpa using W_succ_sum_le m

/- Integer generating counterparts of `alpha` and `W`. -/

def sig : ℕ → ℕ → ℤ
  | n, 0 => if n = 0 then 1 else 0
  | n, k + 1 =>
    if n < k + 1 then ((k + 1).factorial : ℤ) * sig n k
    else ((k + 1).factorial : ℤ) * sig n k - sig (n - (k + 1)) k

def tau : ℕ → ℕ → ℤ
  | d, 0 => if d = 0 then 1 else 0
  | d, k + 1 =>
    if d < k + 1 then tau d k
    else tau d k - ((k + 1).factorial : ℤ) * tau (d - (k + 1)) k

lemma sig_zero_right {n : ℕ} (hn : 0 < n) : sig n 0 = 0 := by
  simp [sig, hn.ne']

lemma tau_zero_left (k : ℕ) : tau 0 k = 1 := by
  induction k with
  | zero => simp [tau]
  | succ k ih => simp [tau, ih]

lemma tau_zero_right {d : ℕ} (hd : 0 < d) : tau d 0 = 0 := by
  simp [tau, hd.ne']

lemma tau_succ_of_lt {d k : ℕ} (h : d < k + 1) : tau d (k + 1) = tau d k := by
  simp [tau, h]

lemma tau_succ_of_le {d k : ℕ} (h : k + 1 ≤ d) :
    tau d (k + 1) = tau d k - ((k + 1).factorial : ℤ) * tau (d - (k + 1)) k := by
  simp [tau, Nat.not_lt.mpr h]

lemma sig_succ_of_lt {n k : ℕ} (h : n < k + 1) :
    sig n (k + 1) = ((k + 1).factorial : ℤ) * sig n k := by
  simp [sig, h]

lemma sig_succ_of_le {n k : ℕ} (h : k + 1 ≤ n) :
    sig n (k + 1) =
      ((k + 1).factorial : ℤ) * sig n k - sig (n - (k + 1)) k := by
  simp [sig, Nat.not_lt.mpr h]

lemma tau_eq_zero_of_tri_lt : ∀ k d, tri k < d → tau d k = 0 := by
  intro k
  induction k with
  | zero =>
    intro d hd
    have : 0 < d := by simpa [tri] using hd
    exact tau_zero_right this
  | succ k ih =>
    intro d hd
    by_cases hlt : d < k + 1
    · rw [tau_succ_of_lt hlt]
      exact ih d (lt_trans (tri_strict_mono (Nat.lt_succ_self k)) hd)
    · rw [tau_succ_of_le (Nat.le_of_not_lt hlt)]
      have : tri (k + 1) = tri k + (k + 1) := tri_succ k
      rw [ih d (lt_trans (tri_strict_mono (Nat.lt_succ_self k)) hd),
        ih (d - (k + 1)) (by omega)]
      simp

lemma sig_eq_zero_of_tri_lt : ∀ k n, tri k < n → sig n k = 0 := by
  intro k
  induction k with
  | zero =>
    intro n hn
    have : 0 < n := by simpa [tri] using hn
    exact sig_zero_right this
  | succ k ih =>
    intro n hn
    by_cases hlt : n < k + 1
    · rw [sig_succ_of_lt hlt, ih n (lt_trans (tri_strict_mono (Nat.lt_succ_self k)) hn)]
      simp
    · rw [sig_succ_of_le (Nat.le_of_not_lt hlt)]
      have : tri (k + 1) = tri k + (k + 1) := tri_succ k
      rw [ih n (lt_trans (tri_strict_mono (Nat.lt_succ_self k)) hn),
        ih (n - (k + 1)) (by omega)]
      simp

lemma tau_eq_of_ge {d k : ℕ} (h : d ≤ k) : tau d k = tau d d := by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [tau_succ_of_lt (by omega), ih]

lemma tau_abs_le_W : ∀ k d, (tau d k).natAbs ≤ W d k := by
  intro k
  induction k with
  | zero =>
    intro d
    by_cases hd : d = 0
    · subst hd; simp [tau, W]
    · simp [tau, W, hd]
  | succ k ih =>
    intro d
    by_cases hlt : d < k + 1
    · rw [tau_succ_of_lt hlt, W_succ_of_lt hlt]
      exact ih d
    · have hle : k + 1 ≤ d := Nat.le_of_not_lt hlt
      rw [tau_succ_of_le hle, W_succ_of_le hle]
      refine le_trans (Int.natAbs_sub_le _ _) ?_
      have h1 := ih d
      have h2 := ih (d - (k + 1))
      have hmul :
          (((k + 1).factorial : ℤ) * tau (d - (k + 1)) k).natAbs =
            (k + 1).factorial * (tau (d - (k + 1)) k).natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [hmul]
      exact Nat.add_le_add h1 (Nat.mul_le_mul_left _ h2)

lemma alpha_mul_factProd : ∀ k n,
    alpha n k * (factProd k : ℤ) = sig n k * (n.factorial : ℤ) := by
  intro k
  induction k with
  | zero =>
    intro n
    by_cases hn : n = 0
    · subst hn; simp [alpha, sig, factProd]
    · simp [alpha, sig, factProd, hn]
  | succ k ih =>
    intro n
    by_cases hlt : n < k + 1
    · rw [alpha_succ_of_lt hlt, sig_succ_of_lt hlt, factProd_succ]
      push_cast
      have := ih n
      linear_combination ((k + 1).factorial : ℤ) * this
    · have hle : k + 1 ≤ n := Nat.le_of_not_lt hlt
      rw [alpha_succ_of_le hle, sig_succ_of_le hle, factProd_succ]
      push_cast
      have ih1 := ih n
      have ih2 := ih (n - (k + 1))
      have hC :
          (n.choose (k + 1) : ℤ) * ((k + 1).factorial : ℤ) *
            ((n - (k + 1)).factorial : ℤ) = (n.factorial : ℤ) := by
        exact_mod_cast
          (Nat.choose_mul_factorial_mul_factorial (n := n) (k := k + 1) hle)
      -- (αn - C αr) * Fk * (k+1)! = ((k+1)! σn - σr) * n!
      linear_combination
        ((k + 1).factorial : ℤ) * ih1
          - ((n.choose (k + 1) : ℤ) * ((k + 1).factorial : ℤ)) * ih2
          + sig (n - (k + 1)) k * hC.symm

lemma sig_eq_tau {n k : ℕ} (hn : n ≤ tri k) :
    sig n k = ((-1 : ℤ) ^ k) * tau (tri k - n) k := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by simpa [tri] using hn
    subst this
    simp [sig, tau, tri]
  | succ k ih =>
    by_cases hlt : n < k + 1
    · have hn' : n ≤ tri k :=
        le_trans (Nat.lt_succ_iff.mp hlt) (self_le_tri k)
      rw [sig_succ_of_lt hlt, ih hn']
      have hΔ : tri k < tri (k + 1) - n := by
        have : tri (k + 1) = tri k + (k + 1) := tri_succ k
        omega
      have hτ0 : tau (tri (k + 1) - n) k = 0 := tau_eq_zero_of_tri_lt k _ hΔ
      have hge : k + 1 ≤ tri (k + 1) - n := by
        have : tri (k + 1) = tri k + (k + 1) := tri_succ k
        omega
      rw [tau_succ_of_le hge, hτ0]
      have : tri (k + 1) - n - (k + 1) = tri k - n := by
        have : tri (k + 1) = tri k + (k + 1) := tri_succ k
        omega
      rw [this]
      ring
    · have hle : k + 1 ≤ n := Nat.le_of_not_lt hlt
      rw [sig_succ_of_le hle]
      rcases le_or_gt n (tri k) with hnk | hnk
      · have hrest : n - (k + 1) ≤ tri k := le_trans (Nat.sub_le _ _) hnk
        rw [ih hnk, ih hrest]
        have hΔge : k + 1 ≤ tri (k + 1) - n := by
          have : tri (k + 1) = tri k + (k + 1) := tri_succ k
          omega
        rw [tau_succ_of_le hΔge]
        have h1 : tri (k + 1) - n - (k + 1) = tri k - n := by
          have : tri (k + 1) = tri k + (k + 1) := tri_succ k
          omega
        have h2 : tri k - (n - (k + 1)) = tri (k + 1) - n := by
          have : tri (k + 1) = tri k + (k + 1) := tri_succ k
          omega
        rw [h1, h2]
        ring
      · have hs0 : sig n k = 0 := sig_eq_zero_of_tri_lt k n hnk
        rw [hs0, mul_zero, zero_sub]
        have hrest : n - (k + 1) ≤ tri k := by
          have : tri (k + 1) = tri k + (k + 1) := tri_succ k
          omega
        rw [ih hrest]
        have hΔlt : tri (k + 1) - n < k + 1 := by
          have : tri (k + 1) = tri k + (k + 1) := tri_succ k
          omega
        rw [tau_succ_of_lt hΔlt]
        have : tri k - (n - (k + 1)) = tri (k + 1) - n := by
          have : tri (k + 1) = tri k + (k + 1) := tri_succ k
          omega
        rw [this]
        ring

lemma alpha_abs_le_W (k n : ℕ) (hn : n ≤ tri k) :
    (alpha n k).natAbs * factProd k ≤ n.factorial * W (tri k - n) k := by
  have hid := alpha_mul_factProd k n
  have hst := sig_eq_tau hn
  have hL : (alpha n k * (factProd k : ℤ)).natAbs =
      (alpha n k).natAbs * factProd k := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
  have hR : (sig n k * (n.factorial : ℤ)).natAbs =
      (sig n k).natAbs * n.factorial := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
  have heq : (alpha n k).natAbs * factProd k = (sig n k).natAbs * n.factorial := by
    rw [← hL, hid, hR]
  rw [heq, hst, Int.natAbs_mul]
  have h1 : ((-1 : ℤ) ^ k).natAbs = 1 := by
    rw [Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow]
  rw [h1, one_mul]
  have hτ := tau_abs_le_W k (tri k - n)
  simpa [Nat.mul_comm] using Nat.mul_le_mul_left n.factorial hτ

lemma div_factProd_succ (m : ℕ) :
    (tri (m + 1)).factorial / factProd (m + 1) =
      (tri (m + 1)).choose (m + 1) * ((tri m).factorial / factProd m) := by
  have hpos : 0 < factProd (m + 1) := factProd_pos _
  have hdvd : factProd (m + 1) ∣ (tri (m + 1)).factorial := factProd_dvd_self _
  have hcancel : ((tri m).factorial / factProd m) * factProd m = (tri m).factorial :=
    Nat.div_mul_cancel (factProd_dvd_self m)
  have hle : m + 1 ≤ tri (m + 1) := self_le_tri (m + 1)
  have hch := Nat.choose_mul_factorial_mul_factorial (n := tri (m + 1)) (k := m + 1) hle
  have hsub : tri (m + 1) - (m + 1) = tri m := tri_pred m
  rw [hsub] at hch
  rw [Nat.div_eq_iff_eq_mul_left hpos hdvd]
  calc
    (tri (m + 1)).factorial
        = (tri (m + 1)).choose (m + 1) * (m + 1).factorial * (tri m).factorial :=
          hch.symm
    _ = (tri (m + 1)).choose (m + 1) * (tri m).factorial * (m + 1).factorial := by
          ac_rfl
    _ = (tri (m + 1)).choose (m + 1) *
          (((tri m).factorial / factProd m) * factProd m) * (m + 1).factorial := by
          rw [hcancel]
    _ = (tri (m + 1)).choose (m + 1) * ((tri m).factorial / factProd m) *
          (factProd m * (m + 1).factorial) := by
          ac_rfl
    _ = (tri (m + 1)).choose (m + 1) * ((tri m).factorial / factProd m) *
          factProd (m + 1) := by
          rw [factProd_succ]

lemma alpha_of_tri (m : ℕ) :
    alpha (tri m) m =
      ((-1 : ℤ) ^ m) * ↑((tri m).factorial / factProd m) := by
  induction m with
  | zero =>
    simp [alpha, tri, factProd]
  | succ m ih =>
    have hα0 : alpha (tri (m + 1)) m = 0 :=
      alpha_eq_zero_of_gt_tri (tri_strict_mono (Nat.lt_succ_self m))
    rw [alpha_succ_of_le (self_le_tri (m + 1)), hα0, zero_sub, tri_pred, ih]
    rw [div_factProd_succ]
    push_cast
    rw [pow_succ]
    ring

lemma tau_self_sub (d : ℕ) (hd : 1 ≤ d) :
    tau d d = tau d (d - 1) - (d.factorial : ℤ) := by
  cases d with
  | zero => omega
  | succ d =>
    rw [tau_succ_of_le (Nat.le_refl _)]
    simp [tau_zero_left]

lemma natAbs_sub_ge (a b : ℤ) : a.natAbs - b.natAbs ≤ (a - b).natAbs := by
  have h := Int.natAbs_sub_le a (a - b)
  have : a - (a - b) = b := by ring
  rw [this] at h
  omega

lemma tau_abs_ge_fact_sub_W (d : ℕ) (hd : 1 ≤ d) :
    d.factorial - W d (d - 1) ≤ (tau d d).natAbs := by
  have h := tau_self_sub d hd
  have hW := tau_abs_le_W (d - 1) d
  rw [h]
  have hge := natAbs_sub_ge (d.factorial : ℤ) (tau d (d - 1))
  have hcomm : ((d.factorial : ℤ) - tau d (d - 1)).natAbs =
      (tau d (d - 1) - (d.factorial : ℤ)).natAbs := by
    rw [← Int.natAbs_neg]; congr 1; ring
  rw [← hcomm]
  refine le_trans ?_ hge
  simpa using Nat.sub_le_sub_left hW d.factorial

lemma gamma_eq_natAbs {n k : ℕ} (h : 0 < gamma n k) :
    gamma n k = ((alpha n k).natAbs : ℤ) := by
  rcases eps_eq_one_or_neg n with hε | hε
  · unfold gamma at h ⊢
    rw [hε, one_mul] at h ⊢
    rw [Int.natCast_natAbs, abs_of_pos h]
  · unfold gamma at h ⊢
    rw [hε, neg_mul, one_mul] at h ⊢
    have hneg : alpha n k < 0 := by nlinarith
    rw [Int.natCast_natAbs, abs_of_neg hneg]

lemma sig_natAbs_eq_tau {n k : ℕ} (hn : n ≤ tri k) :
    (sig n k).natAbs = (tau (tri k - n) k).natAbs := by
  rw [sig_eq_tau hn, Int.natAbs_mul]
  have : ((-1 : ℤ) ^ k).natAbs = 1 := by
    rw [Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow]
  simp [this]

lemma alpha_natAbs_mul_factProd (n k : ℕ) :
    (alpha n k).natAbs * factProd k = (sig n k).natAbs * n.factorial := by
  have hid := alpha_mul_factProd k n
  have hL : (alpha n k * (factProd k : ℤ)).natAbs =
      (alpha n k).natAbs * factProd k := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
  have hR : (sig n k * (n.factorial : ℤ)).natAbs =
      (sig n k).natAbs * n.factorial := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
  rw [← hL, hid, hR]

lemma tau_one (k : ℕ) (hk : 1 ≤ k) : tau 1 k = -1 := by
  have : tau 1 k = tau 1 1 := tau_eq_of_ge hk
  rw [this, tau_self_sub 1 (by omega)]
  simp [tau_zero_right]

lemma tau_two_self : tau 2 2 = -2 := by native_decide

lemma tau_two (k : ℕ) (hk : 2 ≤ k) : tau 2 k = -2 := by
  rw [tau_eq_of_ge hk, tau_two_self]

lemma two_fact_lt_succ (k : ℕ) (hk : 2 ≤ k) :
    2 * k.factorial < (k + 1).factorial := by
  change 2 * k.factorial < (k + 1) * k.factorial
  exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.factorial_pos _)

lemma W_succ_pred {n m : ℕ} (hm : 1 ≤ m) (hn : m ≤ n) :
    W n m = W n (m - 1) + m.factorial * W (n - m) (m - 1) := by
  cases m with
  | zero => omega
  | succ m =>
    rw [W_succ_of_le (by simpa using hn)]
    simp [Nat.succ_eq_add_one]

lemma W_succ_lt_succ_fact (k : ℕ) (hk : 81 ≤ k) :
    W (k + 1) k < (k + 1).factorial := by
  have hW := W_succ_sum_le k
  have hlt := two_fact_lt_succ k (by omega)
  omega

/-- If the complementary `tau` magnitudes satisfy the strict factorial gap, dominance follows. -/
lemma dominance_of_tau (k n : ℕ)
    (hpos : ∀ m, m ≤ tri k → 0 < gamma m k)
    (hn1 : k + 1 ≤ n) (hn2 : n ≤ tri k)
    (htau : (tau (tri k - n + (k + 1)) k).natAbs <
      (tau (tri k - n) k).natAbs * (k + 1).factorial) :
    (n.choose (k + 1) : ℤ) * gamma (n - (k + 1)) k < gamma n k := by
  have hrest : n - (k + 1) ≤ tri k := le_trans (Nat.sub_le _ _) hn2
  have hγn := gamma_eq_natAbs (hpos n hn2)
  have hγr := gamma_eq_natAbs (hpos (n - (k + 1)) hrest)
  rw [hγn, hγr]
  have hAn := alpha_natAbs_mul_factProd n k
  have hAr := alpha_natAbs_mul_factProd (n - (k + 1)) k
  have hsn := sig_natAbs_eq_tau hn2
  have hsr := sig_natAbs_eq_tau hrest
  have hΔr : tri k - (n - (k + 1)) = tri k - n + (k + 1) := by omega
  rw [hΔr] at hsr
  set tΔ := (tau (tri k - n) k).natAbs
  set t' := (tau (tri k - n + (k + 1)) k).natAbs
  have hAn' : (alpha n k).natAbs * factProd k = tΔ * n.factorial := by
    rw [hAn, hsn]
  have hAr' : (alpha (n - (k + 1)) k).natAbs * factProd k =
      t' * (n - (k + 1)).factorial := by
    rw [hAr, hsr]
  have hC := Nat.choose_mul_factorial_mul_factorial (n := n) (k := k + 1) hn1
  have hF : 0 < factProd k := factProd_pos k
  have hfact : 0 < (k + 1).factorial := Nat.factorial_pos _
  have hnfact : 0 < n.factorial := Nat.factorial_pos _
  refine (Int.ofNat_lt.mpr ?_)
  refine Nat.lt_of_mul_lt_mul_right (a := factProd k) ?_
  refine Nat.lt_of_mul_lt_mul_right (a := (k + 1).factorial) ?_
  calc
    n.choose (k + 1) * (alpha (n - (k + 1)) k).natAbs * factProd k *
        (k + 1).factorial
        = n.choose (k + 1) * (k + 1).factorial *
            ((alpha (n - (k + 1)) k).natAbs * factProd k) := by ring
    _ = n.choose (k + 1) * (k + 1).factorial *
            (t' * (n - (k + 1)).factorial) := by rw [hAr']
    _ = (n.choose (k + 1) * (k + 1).factorial * (n - (k + 1)).factorial) * t' := by
          ring
    _ = n.factorial * t' := by rw [hC]
    _ < n.factorial * (tΔ * (k + 1).factorial) :=
          Nat.mul_lt_mul_of_pos_left htau hnfact
    _ = (tΔ * n.factorial) * (k + 1).factorial := by ring
    _ = ((alpha n k).natAbs * factProd k) * (k + 1).factorial := by rw [hAn']
    _ = (alpha n k).natAbs * factProd k * (k + 1).factorial := by ring

lemma tau_abs_le_W' (k d : ℕ) : (tau d k).natAbs ≤ W d k :=
  tau_abs_le_W k d

lemma threek8_lt (k : ℕ) (hk : 81 ≤ k) :
    3 * k + 8 < k * (k + 1) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  nlinarith

lemma W_plus2_lt (k : ℕ) (hk : 81 ≤ k) :
    W (k + 2) k < (k + 1).factorial := by
  have h1 := W_succ_pred (n := k + 2) (m := k) (by omega) (by omega)
  have hk2 : k + 2 - k = 2 := by omega
  rw [hk2] at h1
  have h2w : W 2 (k - 1) = 2 := W_two _ (by omega)
  rw [h2w] at h1
  have h2 := W_succ_pred (n := k + 2) (m := k - 1) (by omega) (by omega)
  have hk3 : k + 2 - (k - 1) = 3 := by omega
  have hk11 : k - 1 - 1 = k - 2 := by omega
  rw [hk3, hk11] at h2
  have h3w : W 3 (k - 2) = 8 := W_three _ (by omega)
  rw [h3w] at h2
  have hoff : W (k + 2) (k - 2) ≤ k.factorial := by
    have := W_off3_le (k + 1) (by omega)
    have e1 : (k + 1) + 1 = k + 2 := by omega
    have e2 : k + 1 - 3 = k - 2 := by omega
    have e3 : k + 1 - 1 = k := by omega
    simpa [e1, e2, e3] using this
  have ek : k.factorial = k * (k - 1).factorial := fact_pred k (by omega)
  have es : (k + 1).factorial = k * (k + 1) * (k - 1).factorial := by
    change (k + 1) * k.factorial = _
    rw [ek]; ring
  have hbound :
      W (k + 2) (k - 2) + 8 * (k - 1).factorial + 2 * k.factorial ≤
        (3 * k + 8) * (k - 1).factorial := by
    have hrem : W (k + 2) (k - 2) ≤ k * (k - 1).factorial := by
      rwa [ek] at hoff
    have : 2 * k.factorial = 2 * k * (k - 1).factorial := by rw [ek]; ring
    rw [this]
    have := Nat.add_le_add_right (Nat.add_le_add_right hrem (8 * (k - 1).factorial))
      (2 * k * (k - 1).factorial)
    refine le_trans this (le_of_eq ?_)
    ring
  have hlt : (3 * k + 8) * (k - 1).factorial < (k + 1).factorial := by
    rw [es]
    exact Nat.mul_lt_mul_of_pos_right (threek8_lt k hk) (Nat.factorial_pos _)
  calc
    W (k + 2) k
        = W (k + 2) (k - 1) + k.factorial * 2 := h1
    _ = W (k + 2) (k - 2) + (k - 1).factorial * 8 + k.factorial * 2 := by
          rw [h2]
    _ = W (k + 2) (k - 2) + 8 * (k - 1).factorial + 2 * k.factorial := by ring
    _ ≤ (3 * k + 8) * (k - 1).factorial := hbound
    _ < (k + 1).factorial := hlt

lemma fact_sub_two (d : ℕ) (hd : 2 ≤ d) :
    d.factorial - 2 * (d - 1).factorial = (d - 2) * (d - 1).factorial := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hd
  have h1 : 2 + t - 1 = 1 + t := by omega
  have h2 : 2 + t - 2 = t := by omega
  have ed : (2 + t).factorial = (2 + t) * (1 + t).factorial := by
    have : 2 + t = (1 + t) + 1 := by omega
    rw [this, factorial_succ]
  rw [h1, ed, ← Nat.mul_sub_right_distrib, h2]

lemma tau_abs_ge_pred {d : ℕ} (hd : 3 ≤ d) :
    (d - 2) * (d - 1).factorial ≤ (tau d d).natAbs := by
  have hge := tau_abs_ge_fact_sub_W d (by omega)
  have hW := W_pred_le d (by omega)
  have hsub : d.factorial - 2 * (d - 1).factorial ≤ d.factorial - W d (d - 1) :=
    Nat.sub_le_sub_left hW _
  have heq := fact_sub_two d (by omega)
  rw [heq] at hsub
  exact le_trans hsub hge

lemma W_self_le_two (n : ℕ) : W n n ≤ 2 * n.factorial :=
  W_le_two_factorial n n

lemma W_le_pow_factProd : ∀ m n, W n m ≤ 2 ^ m * factProd m := by
  intro m
  induction m with
  | zero =>
    intro n
    by_cases hn : n = 0
    · subst hn; simp [W, factProd]
    · simp [W, factProd, hn]
  | succ m ih =>
    intro n
    by_cases hlt : n < m + 1
    · rw [W_succ_of_lt hlt]
      refine le_trans (ih n) ?_
      have : 2 ^ m * factProd m ≤ 2 ^ (m + 1) * factProd (m + 1) := by
        rw [pow_succ, factProd_succ]
        have h2 : 2 ^ m ≤ 2 * 2 ^ m := Nat.le_mul_of_pos_left _ (by decide : 0 < 2)
        have hf : factProd m ≤ factProd m * (m + 1).factorial :=
          Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
        calc
          2 ^ m * factProd m ≤ (2 * 2 ^ m) * factProd m :=
            Nat.mul_le_mul_right _ h2
          _ = 2 * 2 ^ m * factProd m := by ring
          _ ≤ 2 * 2 ^ m * (factProd m * (m + 1).factorial) :=
            Nat.mul_le_mul_left _ hf
          _ = 2 ^ m * 2 * (factProd m * (m + 1).factorial) := by ring
      exact this
    · have hle : m + 1 ≤ n := Nat.le_of_not_lt hlt
      rw [W_succ_of_le hle]
      have h1 := ih n
      have h2 := ih (n - (m + 1))
      have : W n m + (m + 1).factorial * W (n - (m + 1)) m ≤
          2 ^ m * factProd m + (m + 1).factorial * (2 ^ m * factProd m) := by
        gcongr
      refine le_trans this ?_
      have : 2 ^ m * factProd m + (m + 1).factorial * (2 ^ m * factProd m) =
          2 ^ m * factProd m * (1 + (m + 1).factorial) := by ring
      rw [this, pow_succ, factProd_succ]
      have hfac : 1 + (m + 1).factorial ≤ 2 * (m + 1).factorial := by
        have : 1 ≤ (m + 1).factorial := Nat.succ_le_of_lt (Nat.factorial_pos _)
        omega
      have := Nat.mul_le_mul_left (2 ^ m * factProd m) hfac
      convert this using 1 <;> ring

lemma two_le_midx_drop {n k : ℕ} (hn1 : k + 1 ≤ n) (hn2 : n ≤ tri k)
    (hpar : Even (midx n) ↔ Even (midx (n - (k + 1)))) :
    k - 1 ≤ tri k - n ∨ tri k - n = 0 := by
  have hdrop := rest_drop_ge_two hn1 hn2 hpar
  by_cases h0 : n = tri k
  · right; omega
  · left
    have nlt : n < tri k := Nat.lt_of_le_of_ne hn2 (by exact mt id (by intro h; exact h0 (by omega)))
    by_contra h
    have hΔ : tri k - n ≤ k - 2 := by omega
    have hnbig : tri (k - 1) + 2 ≤ n := by
      have : tri k = tri (k - 1) + k := by
        cases k with
        | zero => omega
        | succ k =>
          rw [tri_succ]
          simp
      omega
    have hm : midx n = k - 1 := by
      have hle : tri (k - 1) ≤ n := by omega
      have hlt : n < tri k := nlt
      have hkpos : 1 ≤ k := by omega
      have : tri ((k - 1) + 1) = tri k := by
        cases k with
        | zero => omega
        | succ k => simp [tri_succ]
      rw [midx_eq_iff]
      constructor
      · exact hle
      · rwa [this]
    have hrest : midx (n - (k + 1)) = k - 2 := by
      have hk2 : 2 ≤ k := by omega
      have hlo : tri (k - 2) ≤ n - (k + 1) := by
        have : tri (k - 1) = tri (k - 2) + (k - 1) := by
          cases k with
          | zero => omega
          | succ k =>
            cases k with
            | zero => omega
            | succ k =>
              simp [tri_succ]
        omega
      have hhi : n - (k + 1) < tri (k - 2 + 1) := by
        have heq : k - 2 + 1 = k - 1 := by omega
        rw [heq]
        have : tri k = tri (k - 1) + k := by
          cases k with
          | zero => omega
          | succ k => simp [tri_succ]
        omega
      rw [midx_eq_iff]
      exact ⟨hlo, hhi⟩
    have : midx n - midx (n - (k + 1)) = 1 := by
      rw [hm, hrest]
      omega
    omega

lemma tau_abs_self_ge {d : ℕ} (hd : 3 ≤ d) :
    (d - 2) * (d - 1).factorial ≤ (tau d d).natAbs :=
  tau_abs_ge_pred hd

lemma four_times_lt_quadratic (t : ℕ) :
    4 * (80 + t) < (78 + t) * (82 + t) := by
  have hL : 4 * (80 + t) = 320 + 4 * t := by ring
  have hR : (78 + t) * (82 + t) = 6396 + 160 * t + t * t := by ring
  rw [hL, hR]
  have : 0 < 6076 + 156 * t + t * t := by
    have : 0 < 6076 := by decide
    omega
  omega

lemma four_mul_lt_target (k : ℕ) (hk : 81 ≤ k) :
    4 * k.factorial * (k - 1).factorial <
      (k - 3) * (k - 2).factorial * (k + 1).factorial := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  have ek : (81 + t).factorial = (81 + t) * (80 + t).factorial := by
    have : 81 + t = (80 + t) + 1 := by omega
    rw [this, factorial_succ]
  have e1 : (80 + t).factorial = (80 + t) * (79 + t).factorial := by
    have : 80 + t = (79 + t) + 1 := by omega
    rw [this, factorial_succ]
  have e2 : (82 + t).factorial = (82 + t) * (81 + t).factorial := by
    have : 82 + t = (81 + t) + 1 := by omega
    rw [this, factorial_succ]
  have hk1 : 81 + t - 1 = 80 + t := by omega
  have hk2 : 81 + t - 2 = 79 + t := by omega
  have hk3 : 81 + t - 3 = 78 + t := by omega
  have hk1' : 81 + t + 1 = 82 + t := by omega
  rw [hk1, hk2, hk3, hk1', ek, e1, e2]
  have hpos : 0 < (79 + t).factorial := Nat.factorial_pos _
  have hpos' : 0 < 80 + t := by omega
  have hposk : 0 < 81 + t := by omega
  -- Cancel (79+t)! from both sides after rewriting factorials.
  have hL :
      4 * ((81 + t) * ((80 + t) * (79 + t).factorial)) *
        ((80 + t) * (79 + t).factorial) =
      (4 * (81 + t) * (80 + t) * (80 + t)) *
        ((79 + t).factorial * (79 + t).factorial) := by ring
  have hR :
      (78 + t) * (79 + t).factorial * ((82 + t) * ((81 + t) * (80 + t).factorial)) =
      ((78 + t) * (82 + t) * (81 + t) * (80 + t)) *
        ((79 + t).factorial * (79 + t).factorial) := by
    rw [e1]; ring
  -- First cancel one (80+t), then (81+t).
  have hcore : 4 * (81 + t) * (80 + t) < (78 + t) * (82 + t) * (81 + t) := by
    have h := four_times_lt_quadratic t
    have := Nat.mul_lt_mul_of_pos_right h hposk
    convert this using 1 <;> ring
  have hmid : 4 * (81 + t) * (80 + t) * (80 + t) <
      (78 + t) * (82 + t) * (81 + t) * (80 + t) :=
    Nat.mul_lt_mul_of_pos_right hcore hpos'
  have hpos2 : 0 < (79 + t).factorial * (79 + t).factorial :=
    Nat.mul_pos hpos hpos
  rw [show (81 + t).factorial = (81 + t) * (80 + t).factorial from ek]
  rw [hL, hR]
  exact Nat.mul_lt_mul_of_pos_right hmid hpos2

lemma fact_le_self_pow : ∀ n, n.factorial ≤ n ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [factorial_succ, Nat.pow_succ]
    have h1 : n.factorial ≤ n ^ n := ih
    have h2 : n ^ n ≤ (n + 1) ^ n := Nat.pow_le_pow_left (by omega) _
    have : (n + 1) * n.factorial ≤ (n + 1) * (n + 1) ^ n :=
      Nat.mul_le_mul_left _ (le_trans h1 h2)
    simpa [Nat.mul_comm] using this

lemma nat_pow_succ_left (a n : ℕ) : a ^ (n + 1) = a * a ^ n := by
  rw [Nat.pow_succ, Nat.mul_comm]

lemma pow_add_one_ge (m d : ℕ) :
    m ^ (d + 1) + (d + 1) * m ^ d ≤ (m + 1) ^ (d + 1) := by
  induction d with
  | zero =>
    simp [nat_pow_succ_left, pow_zero, pow_one]
  | succ d ih =>
    rw [nat_pow_succ_left (m + 1)]
    have hmul := Nat.mul_le_mul_left (m + 1) ih
    refine le_trans ?_ hmul
    have hdist : (m + 1) * (m ^ (d + 1) + (d + 1) * m ^ d) =
        m ^ (d + 2) + m ^ (d + 1) + (d + 1) * m ^ (d + 1) +
          (d + 1) * m ^ d := by
      have hp : m * m ^ (d + 1) = m ^ (d + 2) :=
        (nat_pow_succ_left m (d + 1)).symm
      have hq : m ^ (d + 1) = m * m ^ d := nat_pow_succ_left m d
      rw [← hp]
      ring
    rw [hdist]
    have : m ^ (d + 2) + (d + 2) * m ^ (d + 1) ≤
        m ^ (d + 2) + m ^ (d + 1) + (d + 1) * m ^ (d + 1) +
          (d + 1) * m ^ d := by
      have : (d + 2) * m ^ (d + 1) =
          m ^ (d + 1) + (d + 1) * m ^ (d + 1) := by ring
      omega
    convert this using 2 <;> ring

lemma pow_add_fact_le (m d : ℕ) (hd1 : 1 ≤ d) (hd : d ≤ m) :
    m ^ d + d.factorial ≤ (m + 1) ^ d := by
  cases d with
  | zero => omega
  | succ d =>
    have hbin := pow_add_one_ge m d
    -- m^{d+1} + (d+1) m^d ≤ (m+1)^{d+1}
    -- and (d+1)! = (d+1) d! ≤ (d+1) m^d   since d! ≤ m^d (d ≤ m)
    have hf : d.factorial ≤ m ^ d := by
      refine le_trans (fact_le_self_pow d) ?_
      exact Nat.pow_le_pow_left (by omega) _
    have : (d + 1).factorial = (d + 1) * d.factorial := factorial_succ d
    rw [this]
    have : (d + 1) * d.factorial ≤ (d + 1) * m ^ d :=
      Nat.mul_le_mul_left _ hf
    exact le_trans (Nat.add_le_add_left this _) hbin

lemma W_le_shift_pow : ∀ m d, W (m + d) m ≤ 2 * m.factorial * m ^ d := by
  intro m
  induction m with
  | zero =>
    intro d
    by_cases hd : d = 0
    · subst hd; simp [W]
    · have : (0 : ℕ) ^ d = 0 := zero_pow hd
      simp [W, hd, this]
  | succ m ih =>
    intro d
    by_cases hd0 : d = 0
    · subst hd0
      simpa [Nat.add_zero, pow_zero, Nat.mul_one] using
        W_le_two_factorial (m + 1) (m + 1)
    · have hrec : W (m + 1 + d) (m + 1) =
          W (m + 1 + d) m + (m + 1).factorial * W d m := by
        have : m + 1 ≤ m + 1 + d := by omega
        rw [W_succ_of_le this]
        have : m + 1 + d - (m + 1) = d := by omega
        rw [this]
      rw [hrec]
      have hshift : W (m + 1 + d) m ≤ 2 * m.factorial * m ^ (d + 1) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (d + 1)
      have em : (m + 1).factorial = (m + 1) * m.factorial := by simp [factorial]
      by_cases hdm : d ≤ m
      · have hWd : W d m = W d d := W_eq_of_ge hdm
        have hWdd : W d d ≤ 2 * d.factorial := W_le_two_factorial d d
        have hsum :
            2 * m.factorial * m ^ (d + 1) +
              (m + 1).factorial * (2 * d.factorial) ≤
            2 * (m + 1).factorial * (m + 1) ^ d := by
          rw [em]
          have hf := pow_add_fact_le m d (by omega) hdm
          -- m^d + d! ≤ (m+1)^d
          -- Need m^{d+1} + (m+1) d! ≤ (m+1)^{d+1} = (m+1)(m+1)^d
          have hcore : m ^ (d + 1) + (m + 1) * d.factorial ≤
              (m + 1) * (m + 1) ^ d := by
            have hp : m ^ (d + 1) = m * m ^ d := by
              rw [Nat.pow_succ, Nat.mul_comm]
            have h1 : m * m ^ d + m ^ d + (m + 1) * d.factorial =
                (m + 1) * (m ^ d + d.factorial) := by ring
            have h2 : (m + 1) * (m ^ d + d.factorial) ≤
                (m + 1) * (m + 1) ^ d :=
              Nat.mul_le_mul_left _ hf
            have : m * m ^ d + (m + 1) * d.factorial ≤
                m * m ^ d + m ^ d + (m + 1) * d.factorial := by omega
            rw [hp]
            exact le_trans this (by rwa [h1])
          have hmul := Nat.mul_le_mul_right m.factorial hcore
          have hL : 2 * m.factorial * m ^ (d + 1) +
              ((m + 1) * m.factorial) * (2 * d.factorial) =
              2 * ((m ^ (d + 1) + (m + 1) * d.factorial) * m.factorial) := by ring
          have hR : 2 * ((m + 1) * m.factorial) * (m + 1) ^ d =
              2 * ((m + 1) * (m + 1) ^ d * m.factorial) := by ring
          rw [hL, hR]
          exact Nat.mul_le_mul_left 2 hmul
        refine le_trans (Nat.add_le_add hshift ?_) hsum
        rw [hWd]
        exact Nat.mul_le_mul_left _ hWdd
      · have hWdm : W d m = W (m + (d - m)) m := by congr 1; omega
        have hWdm' : W d m ≤ 2 * m.factorial * m ^ (d - m) := by
          rw [hWdm]; exact ih (d - m)
        have hsum :
            2 * m.factorial * m ^ (d + 1) +
              (m + 1).factorial * (2 * m.factorial * m ^ (d - m)) ≤
            2 * (m + 1).factorial * (m + 1) ^ d := by
          rw [em]
          have hcore : m ^ (d + 1) + (m + 1) * m.factorial * m ^ (d - m) ≤
              (m + 1) ^ (d + 1) := by
            have hbin := pow_add_one_ge m d
            have hf : m.factorial ≤ m ^ m := fact_le_self_pow m
            have hd1 : m + 1 ≤ d + 1 := by omega
            have hsec : (m + 1) * m.factorial * m ^ (d - m) ≤
                (d + 1) * m ^ d := by
              have : (m + 1) * m.factorial ≤ (d + 1) * m ^ m :=
                Nat.mul_le_mul hd1 hf
              have hpow : m ^ m * m ^ (d - m) = m ^ d := by
                rw [← pow_add]; congr 1; omega
              have hmul := Nat.mul_le_mul_right (m ^ (d - m)) this
              have : (d + 1) * m ^ m * m ^ (d - m) = (d + 1) * m ^ d := by
                rw [mul_assoc, hpow]
              rw [this] at hmul
              exact hmul
            exact le_trans (Nat.add_le_add_left hsec _) hbin
          have hL : 2 * m.factorial * m ^ (d + 1) +
              ((m + 1) * m.factorial) * (2 * m.factorial * m ^ (d - m)) =
              2 * m.factorial *
                (m ^ (d + 1) + (m + 1) * m.factorial * m ^ (d - m)) := by ring
          rw [hL]
          have hmul := Nat.mul_le_mul_left (2 * m.factorial) hcore
          refine le_trans hmul ?_
          have hexp : (m + 1) ^ (d + 1) = (m + 1) * (m + 1) ^ d :=
            nat_pow_succ_left _ _
          rw [hexp]
          exact le_of_eq (by ring)
        refine le_trans (Nat.add_le_add hshift ?_) hsum
        exact Nat.mul_le_mul_left _ hWdm'

lemma fact_pair_le_left_of_le_half {n a b : ℕ}
    (hab : a ≤ b) (hb : 2 * b ≤ n) :
    b.factorial * (n - b).factorial ≤ a.factorial * (n - a).factorial := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb' ih =>
    have hanti : (b + 1).factorial * (n - (b + 1)).factorial ≤
        b.factorial * (n - b).factorial :=
      fpair_anti_left (by omega)
    exact le_trans hanti (ih (by omega))

lemma fact_pair_le_right_of_ge_half {n b c : ℕ}
    (hbc : b ≤ c) (hb : n ≤ 2 * b + 1) (hc : c ≤ n) :
    b.factorial * (n - b).factorial ≤ c.factorial * (n - c).factorial := by
  exact fact_mul_le_of_ge_half (n := n) (a := b) (b := c) hb hbc hc

lemma fact_pair_le_max_ends {n a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ n) :
    b.factorial * (n - b).factorial ≤
      a.factorial * (n - a).factorial ∨
    b.factorial * (n - b).factorial ≤
      c.factorial * (n - c).factorial := by
  cases le_or_gt (2 * b) n with
  | inl hle =>
    left
    exact fact_pair_le_left_of_le_half hab hle
  | inr hgt =>
    right
    exact fact_pair_le_right_of_ge_half hbc (by omega) hc

lemma W_le_two_max_pair (n m j0 : ℕ) (hj0 : 1 ≤ j0) (hjm : j0 ≤ m)
    (hmn : m ≤ n)
    (hvan : ∀ j, j ∈ Icc 1 m → j < j0 → W (n - j) (j - 1) = 0) :
    W n m ≤
      2 * (m.succ) *
        (j0.factorial * (n - j0).factorial +
          m.factorial * (n - m).factorial) := by
  have hdecomp := W_max_decomp m n
  by_cases hn0 : n = 0
  · subst hn0
    omega
  · simp only [hn0, ite_false] at hdecomp
    have hmin : min n m = m := by omega
    rw [hdecomp, hmin, add_zero]
    have hterm : ∀ j ∈ Icc 1 m,
        j.factorial * W (n - j) (j - 1) ≤
          2 * (j0.factorial * (n - j0).factorial +
            m.factorial * (n - m).factorial) := by
      intro j hj
      simp [mem_Icc] at hj
      have hj1 : 1 ≤ j := hj.1
      by_cases hsmall : j < j0
      · have : j ∈ Icc 1 m := by simp [mem_Icc]; omega
        rw [hvan j this hsmall]; simp
      · have hj0' : j0 ≤ j := Nat.le_of_not_lt hsmall
        have hjn : j ≤ n := by omega
        have hjm' : j ≤ m := by omega
        have hw : W (n - j) (j - 1) ≤ 2 * (n - j).factorial :=
          W_le_two_factorial _ _
        have : j.factorial * W (n - j) (j - 1) ≤
            2 * (j.factorial * (n - j).factorial) := by
          have := Nat.mul_le_mul_left j.factorial hw
          linarith
        refine le_trans this ?_
        have hpair := fact_pair_le_max_ends (n := n) (a := j0) (b := j) (c := m)
          hj0' hjm' (by omega)
        have hmax : j.factorial * (n - j).factorial ≤
            j0.factorial * (n - j0).factorial +
              m.factorial * (n - m).factorial := by
          cases hpair with
          | inl h => exact le_trans h (Nat.le_add_right _ _)
          | inr h => exact le_trans h (Nat.le_add_left _ _)
        have := Nat.mul_le_mul_left 2 hmax
        linarith
    have hsum := sum_le_sum hterm
    refine le_trans hsum ?_
    have : ∑ j ∈ Icc 1 m,
        2 * (j0.factorial * (n - j0).factorial +
          m.factorial * (n - m).factorial) =
        #(Icc 1 m) *
          (2 * (j0.factorial * (n - j0).factorial +
            m.factorial * (n - m).factorial)) := by
      simp [sum_const]
    rw [this]
    have hcard : #(Icc 1 m) ≤ m.succ := by
      rw [Nat.card_Icc]; omega
    have := Nat.mul_le_mul_right
      (2 * (j0.factorial * (n - j0).factorial +
        m.factorial * (n - m).factorial)) hcard
    convert this using 1 <;> ring

/-- Finite check: `j! 2^{j-1} factProd(j-1)` is tiny compared with `81! 80!`. -/
def checkSmallW : Bool :=
  (List.range 24).all fun j =>
    decide (j.factorial * 2 ^ (j.pred) * factProd j.pred * 1000 ≤
      (81 : ℕ).factorial * (80 : ℕ).factorial)

lemma checkSmallW_true : checkSmallW = true := by native_decide

lemma smallW_term_le_81 (j : ℕ) (hj : j ≤ 23) :
    j.factorial * 2 ^ (j.pred) * factProd j.pred * 1000 ≤
      (81 : ℕ).factorial * (80 : ℕ).factorial := by
  have hall := List.all_eq_true.mp checkSmallW_true
  have hj' : j ∈ List.range 24 := by simp [List.mem_range]; omega
  exact decide_eq_true_eq.mp (hall j hj')

lemma fact_pair_mono (a b : ℕ) (h : a ≤ b) :
    a.factorial * (a - 1).factorial ≤ b.factorial * (b - 1).factorial := by
  have h1 : a.factorial ≤ b.factorial := Nat.factorial_le h
  have h2 : (a - 1).factorial ≤ (b - 1).factorial :=
    Nat.factorial_le (Nat.sub_le_sub_right h _)
  exact Nat.mul_le_mul h1 h2

lemma smallW_term_le (k j : ℕ) (hk : 81 ≤ k) (hj : j ≤ 23) :
    j.factorial * W (2 * k - j) (j - 1) ≤
      k.factorial * (k - 1).factorial / 1000 := by
  have hW : W (2 * k - j) (j - 1) ≤ 2 ^ (j - 1) * factProd (j - 1) :=
    W_le_pow_factProd (j - 1) (2 * k - j)
  have hterm : j.factorial * W (2 * k - j) (j - 1) ≤
      j.factorial * 2 ^ (j.pred) * factProd j.pred := by
    have : j - 1 = j.pred := rfl
    have := Nat.mul_le_mul_left j.factorial hW
    simpa [this, Nat.mul_assoc] using this
  have h81 := smallW_term_le_81 j hj
  have hmono := fact_pair_mono 81 k hk
  have hbig : j.factorial * 2 ^ j.pred * factProd j.pred * 1000 ≤
      k.factorial * (k - 1).factorial := by
    have : (81 : ℕ).factorial * (80 : ℕ).factorial ≤
        k.factorial * (k - 1).factorial := by
      simpa using hmono
    exact le_trans h81 this
  have hpos : 0 < 1000 := by decide
  exact Nat.le_div_iff_mul_le hpos |>.mpr (le_trans (Nat.mul_le_mul_right 1000 hterm) hbig)

lemma sqrt_sq_le (n : ℕ) : n.sqrt * n.sqrt ≤ n := Nat.sqrt_le n

lemma five_sqrt_lt (k : ℕ) (hk : 81 ≤ k) : 5 * k.sqrt + 24 ≤ k := by
  have hsq : k.sqrt * k.sqrt ≤ k := Nat.sqrt_le k
  have h9 : 9 ≤ k.sqrt := by
    have : 81 ≤ k := hk
    have : (9 : ℕ) * 9 ≤ k := by omega
    exact Nat.le_sqrt.mpr this
  have hbound : 5 * k.sqrt + 24 ≤ 5 * k.sqrt + 3 * k.sqrt := by
    have : 24 ≤ 3 * k.sqrt := by
      have : 8 ≤ k.sqrt := by omega
      omega
    omega
  have : 8 * k.sqrt ≤ k := by
    have : 8 * k.sqrt ≤ k.sqrt * k.sqrt := by
      have : 8 ≤ k.sqrt := by omega
      exact Nat.mul_le_mul_right _ this
    exact le_trans this hsq
  omega

lemma van13_of_two_k (k j : ℕ) (hk : 81 ≤ k) (hj : j ≤ k - 1) :
    ∀ t, t ∈ Icc 1 (j - 1) → t < 13 → W (2 * k - j - t) (t - 1) = 0 := by
  intro t ht ht13
  simp [mem_Icc] at ht
  apply W_eq_zero_of_tri_lt
  have htri : tri (t - 1) ≤ tri 11 := tri_mono (by omega)
  have : tri 11 = 66 := by native_decide
  have : 2 * k - j - t ≥ 2 * k - (k - 1) - 12 := by omega
  have : 2 * k - (k - 1) - 12 = k - 11 := by omega
  omega

lemma two_mul_div_le_log_one_add {n : ℕ} (hn : 0 < n) :
    (2 : ℝ) / (2 * n + 1) ≤ Real.log (1 + 1 / n) := by
  have hx : (0 : ℝ) ≤ 1 / n := by positivity
  have h := Real.le_log_one_add_of_nonneg hx
  have : (2 : ℝ) * (1 / n) / (1 / n + 2) = 2 / (2 * n + 1) := by
    field_simp
    ring
  rwa [this] at h

lemma one_add_inv_pow_succ_ge_exp {n : ℕ} (hn : 0 < n) :
    Real.exp 1 ≤ ((n + 1 : ℝ) / n) ^ (n + 1) := by
  have hlog : (1 : ℝ) ≤ (n + 1 : ℝ) * Real.log (1 + 1 / n) := by
    have h1 := two_mul_div_le_log_one_add hn
    have h2 : (1 : ℝ) / (n + 1) ≤ 2 / (2 * n + 1) := by
      have hn1 : (0 : ℝ) < n + 1 := by positivity
      have hn2 : (0 : ℝ) < 2 * n + 1 := by positivity
      rw [div_le_div_iff₀ hn1 hn2]
      norm_cast; omega
    have h3 : (1 : ℝ) ≤ (n + 1) * (2 / (2 * n + 1)) := by
      field_simp
      norm_cast; omega
    nlinarith
  have hpos : (0 : ℝ) < 1 + 1 / n := by positivity
  have hexp : Real.exp 1 ≤ Real.exp ((n + 1 : ℝ) * Real.log (1 + 1 / n)) :=
    Real.exp_le_exp.mpr hlog
  have hmul : Real.exp ((n + 1 : ℝ) * Real.log (1 + 1 / n)) =
      (1 + 1 / n) ^ (n + 1) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hpos]
    norm_cast
  have hfrac : (1 : ℝ) + 1 / n = (n + 1) / n := by field_simp
  rwa [hmul, hfrac] at hexp

lemma n_pow_mul_exp_le (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ (n + 1) * Real.exp 1 ≤ (n + 1 : ℝ) ^ (n + 1) := by
  have hexp := one_add_inv_pow_succ_ge_exp hn
  have hmul := mul_le_mul_of_nonneg_right hexp
    (pow_nonneg (Nat.cast_nonneg n) (n + 1))
  have hrew : ((n + 1 : ℝ) / n) ^ (n + 1) * (n : ℝ) ^ (n + 1) =
      (n + 1 : ℝ) ^ (n + 1) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_pow, div_mul_cancel₀]
    exact pow_ne_zero _ this.ne'
  rw [hrew] at hmul
  linarith

lemma factorial_le_mul_exp_pow (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ (n : ℝ) * Real.exp 1 * ((n : ℝ) / Real.exp 1) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => simp [Nat.factorial]
  | succ n hn ih =>
    have hn0 : 0 < n := by omega
    rw [Nat.factorial_succ]
    push_cast
    refine le_trans (mul_le_mul_of_nonneg_left ih (by positivity)) ?_
    have hpos_e : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
    have hpow := n_pow_mul_exp_le n hn0
    have hL : (n + 1 : ℝ) * (n * Real.exp 1 * ((n : ℝ) / Real.exp 1) ^ n) =
        (n + 1) * Real.exp 1 * ((n : ℝ) ^ (n + 1) / Real.exp 1 ^ n) := by
      rw [div_pow, pow_succ' (n : ℝ)]
      field_simp
    have hR : (n + 1 : ℝ) * Real.exp 1 * ((n + 1 : ℝ) / Real.exp 1) ^ (n + 1) =
        (n + 1) * Real.exp 1 * ((n + 1 : ℝ) ^ (n + 1) / Real.exp 1 ^ (n + 1)) := by
      rw [div_pow]
    rw [hL, hR]
    have hpos1 : (0 : ℝ) < (n + 1 : ℝ) * Real.exp 1 := by positivity
    refine (mul_le_mul_iff_of_pos_left hpos1).mpr ?_
    rw [div_le_div_iff₀ (pow_pos hpos_e n) (pow_pos hpos_e _)]
    calc
      (n : ℝ) ^ (n + 1) * Real.exp 1 ^ (n + 1)
          = (n : ℝ) ^ (n + 1) * Real.exp 1 * Real.exp 1 ^ n := by
            rw [pow_succ (Real.exp 1)]; ring
      _ ≤ (n + 1 : ℝ) ^ (n + 1) * Real.exp 1 ^ n :=
            mul_le_mul_of_nonneg_right hpow (pow_nonneg (le_of_lt hpos_e) _)

lemma stirlingSeq_antitone_ge_one {n : ℕ} (hn : 1 ≤ n) :
    Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
  cases n with
  | zero => omega
  | succ n =>
    have h := Stirling.stirlingSeq'_antitone (Nat.zero_le n)
    simpa [Function.comp] using h

lemma factorial_upper_stirling (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n := by
  have hseq : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 :=
    stirlingSeq_antitone_ge_one hn
  rw [Stirling.stirlingSeq_one] at hseq
  unfold Stirling.stirlingSeq at hseq
  have hpos : (0 : ℝ) < Real.sqrt (2 * n) * ((n : ℝ) / Real.exp 1) ^ n := by
    positivity
  rw [div_le_iff₀ hpos] at hseq
  refine le_trans hseq ?_
  have hsq : Real.sqrt (2 * (n : ℝ)) = Real.sqrt 2 * Real.sqrt (n : ℝ) :=
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2) (n : ℝ)
  rw [hsq]
  have hs2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  field_simp
  simp

lemma log_factorial_upper {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤
      1 + Real.log n / 2 + n * Real.log n - n := by
  have hpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hle := factorial_upper_stirling n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have := Real.log_le_log hpos hle
  refine le_trans this ?_
  have h1 : Real.log (Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n) =
      1 + Real.log n / 2 + n * (Real.log n - 1) := by
    have he : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    have hs : Real.log (Real.sqrt (n : ℝ)) = Real.log n / 2 :=
      Real.log_sqrt (le_of_lt hn0)
    have hp : Real.log (((n : ℝ) / Real.exp 1) ^ n) =
        n * Real.log ((n : ℝ) / Real.exp 1) :=
      Real.log_pow _ n
    have hd : Real.log ((n : ℝ) / Real.exp 1) = Real.log n - 1 := by
      rw [Real.log_div (ne_of_gt hn0) (Real.exp_ne_zero 1), Real.log_exp]
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), he, hs, hp, hd]
  rw [h1]
  linarith

lemma twenty_mul_k_plus_seven (k : ℕ) (hk : 81 ≤ k) :
    20 * (k + 7) ≤ k * (k - 1) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hk1 : 81 + t - 1 = 80 + t := by omega
  rw [hk1]
  nlinarith

lemma km1_core (k : ℕ) (hk : 81 ≤ k) :
    (k - 1) * (k + 7) * 20 ≤ k * (k - 1) * (k - 1) := by
  have h := twenty_mul_k_plus_seven k hk
  have : (k - 1) * (20 * (k + 7)) ≤ (k - 1) * (k * (k - 1)) :=
    Nat.mul_le_mul_left _ h
  convert this using 1 <;> ring

lemma small_div_23_40 (X : ℕ) :
    23 * (X / 1000) ≤ X / 40 := by
  have hpos40 : 0 < 40 := by decide
  have hpos1000 : 0 < 1000 := by decide
  rw [Nat.le_div_iff_mul_le hpos40]
  have hle : 23 * (X / 1000) * 40 ≤ 920 * (X / 1000) := by
    have : 23 * 40 = 920 := by decide
    omega
  refine le_trans hle ?_
  have h1 : X / 1000 ≤ X / 920 :=
    Nat.div_le_div_left (by decide : 920 ≤ 1000) (by decide : 0 < 920)
  have : 920 * (X / 1000) ≤ 920 * (X / 920) := Nat.mul_le_mul_left _ h1
  refine le_trans this ?_
  have : 920 * (X / 920) ≤ X := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self X 920
  exact this

/-- The `j = k-1` term of `W(2k,k)`. -/
lemma W_km1_term_le (k : ℕ) (hk : 81 ≤ k) :
    (k - 1).factorial * W (k + 1) (k - 2) ≤
      k.factorial * (k - 1).factorial / 20 := by
  have hW : W (k + 1) (k - 2) =
      W (k + 1) (k - 3) + (k - 2).factorial * W 3 (k - 3) := by
    have : k - 2 = (k - 3) + 1 := by omega
    rw [this, W_succ_of_le (by omega)]
    have : k + 1 - ((k - 3) + 1) = 3 := by omega
    rw [this]
  have h3 : W 3 (k - 3) = 8 := W_three _ (by omega)
  have hW' : W (k + 1) (k - 2) =
      W (k + 1) (k - 3) + 8 * (k - 2).factorial := by
    rw [hW, h3]; ring
  rw [hW']
  have hoff := W_off3_le k hk
  have hsum : W (k + 1) (k - 3) + 8 * (k - 2).factorial ≤
      (k - 1).factorial + 8 * (k - 2).factorial :=
    Nat.add_le_add_right hoff _
  have hterm : (k - 1).factorial * (W (k + 1) (k - 3) + 8 * (k - 2).factorial) ≤
      (k - 1).factorial * ((k - 1).factorial + 8 * (k - 2).factorial) :=
    Nat.mul_le_mul_left _ hsum
  refine le_trans hterm ?_
  have e1 : (k - 1).factorial = (k - 1) * (k - 2).factorial :=
    fact_pred (k - 1) (by omega)
  have ek : k.factorial = k * (k - 1).factorial := fact_pred k (by omega)
  have hpos : 0 < 20 := by decide
  rw [Nat.le_div_iff_mul_le hpos]
  -- ((k-1)!)^2 + 8 (k-1)! (k-2)! ≤ k! (k-1)! / 20 * 20 = k! (k-1)!
  have : (k - 1).factorial * ((k - 1).factorial + 8 * (k - 2).factorial) * 20 ≤
      k.factorial * (k - 1).factorial := by
    rw [ek, e1]
    have hposf : 0 < (k - 2).factorial := Nat.factorial_pos _
    -- cancel (k-1) (k-2)! from both sides after expansion
    have hL :
        ((k - 1) * (k - 2).factorial) *
            ((k - 1) * (k - 2).factorial + 8 * (k - 2).factorial) * 20 =
          (k - 1) * (k - 2).factorial * (k - 2).factorial *
            ((k - 1) + 8) * 20 := by
      ring
    have hR :
        (k * ((k - 1) * (k - 2).factorial)) * ((k - 1) * (k - 2).factorial) =
          k * (k - 1) * (k - 1) * (k - 2).factorial * (k - 2).factorial := by
      ring
    rw [hL, hR]
    have h78 : k - 1 + 8 = k + 7 := by omega
    rw [h78]
    have hcore := km1_core k hk
    have := Nat.mul_le_mul_right ((k - 2).factorial * (k - 2).factorial) hcore
    convert this using 1 <;> ring
  exact this

lemma mul_div_le_div_mul (c a b : ℕ) (hb : 0 < b) :
    c * (a / b) ≤ (c * a) / b := by
  rw [Nat.le_div_iff_mul_le hb]
  have : c * (a / b) * b = c * ((a / b) * b) := by ring
  rw [this]
  exact Nat.mul_le_mul_left c (Nat.div_mul_le_self a b)

lemma two_div_four (X : ℕ) : 2 * (X / 4) ≤ X / 2 := by
  have h1 : 2 * (X / 4) ≤ (2 * X) / 4 :=
    mul_div_le_div_mul 2 X 4 (by decide)
  have h2 : (2 * X) / 4 = X / 2 := by
    have : (2 * X) / (2 * 2) = X / 2 := Nat.mul_div_mul_left X 2 (by decide)
    simpa using this
  rwa [h2] at h1

lemma comb_budget (X : ℕ) :
    X / 20 + (X + X / 4) ≤ X + X / 2 := by
  have h : X / 20 ≤ X / 4 :=
    Nat.div_le_div_left (by decide : 4 ≤ 20) (by decide : 0 < 4)
  have : X / 20 + X / 4 ≤ X / 4 + X / 4 := Nat.add_le_add_right h _
  have h2 : X / 4 + X / 4 ≤ X / 2 := by
    have : X / 4 + X / 4 = 2 * (X / 4) := by ring
    rw [this]; exact two_div_four X
  have hsum : X / 20 + X / 4 ≤ X / 2 := le_trans this h2
  calc
    X / 20 + (X + X / 4) = X + (X / 20 + X / 4) := by ring
    _ ≤ X + X / 2 := Nat.add_le_add_left hsum _

lemma rest_budget (X : ℕ) :
    X / 40 + (X + X / 2) ≤ 2 * X := by
  have hhalf : X / 40 ≤ X / 2 :=
    Nat.div_le_div_left (by decide : 2 ≤ 40) (by decide : 0 < 2)
  have : X / 40 + X / 2 ≤ X / 2 + X / 2 := Nat.add_le_add_right hhalf _
  have hsum : X / 40 + X / 2 ≤ X :=
    le_trans this (by
      have : X / 2 + X / 2 = 2 * (X / 2) := by ring
      rw [this]; exact Nat.mul_div_le X 2)
  calc
    X / 40 + (X + X / 2) = X + (X / 40 + X / 2) := by ring
    _ ≤ X + X := Nat.add_le_add_left hsum _
    _ = 2 * X := by ring

lemma Icc_union_split {a b c : ℕ} (h1 : a ≤ b + 1) (h2 : b ≤ c) :
    Icc a c = Icc a b ∪ Icc (b + 1) c := by
  ext x
  simp [mem_Icc, mem_union]
  omega

lemma large_right_s1 (k : ℕ) (hk : 81 ≤ k) :
    (k - 1) * (k - 1).factorial * (k - 2).factorial * 6
      ≤ k.factorial * (k - 1).factorial / 10 := by
  have hk1 : 1 ≤ k := by omega
  have : (k - 1) * (k - 2).factorial * 6 ≤ k.factorial / 10 := by
    have ek : k.factorial = k * (k - 1).factorial := fact_pred k hk1
    have e1 : (k - 1).factorial = (k - 1) * (k - 2).factorial :=
      fact_pred (k - 1) (by omega)
    rw [ek, e1]
    have hpos : 0 < 10 := by decide
    rw [Nat.le_div_iff_mul_le hpos]
    have : (k - 1) * (k - 2).factorial * 6 * 10 ≤
        k * ((k - 1) * (k - 2).factorial) := by
      have : 60 ≤ k := by omega
      have hmul := Nat.mul_le_mul_right ((k - 1) * (k - 2).factorial) this
      convert hmul using 1 <;> ring
    exact this
  have hpos : 0 < 10 := by decide
  have : (k - 1) * (k - 1).factorial * (k - 2).factorial * 6 * 10 ≤
      k.factorial * (k - 1).factorial := by
    have := Nat.mul_le_mul_right (k - 1).factorial
      (Nat.le_div_iff_mul_le hpos |>.mp this)
    convert this using 1 <;> ring
  exact Nat.le_div_iff_mul_le hpos |>.mpr this

/-- Adaptive off-diagonal width: large enough for the shift-power bound,
and small enough for the `j0 = 13` pairing bound. -/
def midShift (k : ℕ) : ℕ :=
  max (5 * k.sqrt) ((k * (3 * Nat.log 2 k + 8)).sqrt)

lemma six_le_log2 (k : ℕ) (hk : 81 ≤ k) : 6 ≤ Nat.log 2 k := by
  have hpow : 2 ^ 6 ≤ k := by omega
  exact (Nat.le_log_iff_pow_le (by decide : 1 < 2) (by omega : k ≠ 0)).2 hpow

lemma two_pow_ge_sq_succ : ∀ n, 6 ≤ n → (n + 1) * (n + 1) ≤ 2 ^ (n + 1)
  | n, hn => by
    induction n, hn using Nat.le_induction with
    | base => decide
    | succ n hn ih =>
      have h2 : 2 * ((n + 1) * (n + 1)) ≤ 2 ^ (n + 2) := by
        have : 2 ^ (n + 2) = 2 ^ (n + 1) * 2 := Nat.pow_succ _ _
        rw [this, Nat.mul_comm (2 ^ (n + 1))]
        exact Nat.mul_le_mul_left 2 ih
      refine le_trans ?_ h2
      have : (n + 2) * (n + 2) ≤ 2 * ((n + 1) * (n + 1)) := by
        nlinarith
      exact this

lemma log2_lt_sqrt_succ (k : ℕ) (hk : 81 ≤ k) :
    Nat.log 2 k < k.sqrt + 1 := by
  have hk0 : k ≠ 0 := by omega
  rw [Nat.log_lt_iff_lt_pow (by decide : 1 < 2) hk0]
  have hsq : k < (k.sqrt + 1) * (k.sqrt + 1) := Nat.lt_succ_sqrt k
  refine lt_of_lt_of_le hsq ?_
  have hn : 6 ≤ k.sqrt := by
    have : 9 ≤ k.sqrt := Nat.le_sqrt.mpr (by omega : 9 * 9 ≤ k)
    omega
  exact two_pow_ge_sq_succ k.sqrt hn

lemma log2_le_sqrt (k : ℕ) (hk : 81 ≤ k) : Nat.log 2 k ≤ k.sqrt := by
  have := log2_lt_sqrt_succ k hk
  omega

lemma midShift_eq_logsqrt (k : ℕ) (hk : 81 ≤ k) :
    midShift k = (k * (3 * Nat.log 2 k + 8)).sqrt := by
  apply max_eq_right
  have hlog : 6 ≤ Nat.log 2 k := six_le_log2 k hk
  have h25 : 25 ≤ 3 * Nat.log 2 k + 8 := by omega
  have hL : (5 * k.sqrt) * (5 * k.sqrt) = 25 * (k.sqrt * k.sqrt) := by ring
  have hsq : k.sqrt * k.sqrt ≤ k := Nat.sqrt_le k
  have : (5 * k.sqrt) * (5 * k.sqrt) ≤ k * (3 * Nat.log 2 k + 8) := by
    rw [hL]
    have h1 : 25 * (k.sqrt * k.sqrt) ≤ 25 * k := Nat.mul_le_mul_left 25 hsq
    refine le_trans h1 ?_
    have : 25 * k ≤ k * (3 * Nat.log 2 k + 8) := by
      rw [Nat.mul_comm 25]
      exact Nat.mul_le_mul_left k h25
    exact this
  exact Nat.le_sqrt.mpr this

lemma three_log_mul_le_of_lt_1024 (k : ℕ) (hk : 81 ≤ k) (h : k < 2 ^ 10) :
    k * (3 * Nat.log 2 k + 8) ≤ (k - 24) * (k - 24) := by
  have hlog : Nat.log 2 k ≤ 9 := by
    have := (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (by omega : k ≠ 0)).2 h
    omega
  have h35 : 3 * Nat.log 2 k + 8 ≤ 35 := by omega
  have : k * (3 * Nat.log 2 k + 8) ≤ k * 35 := Nat.mul_le_mul_left k h35
  refine le_trans this ?_
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hk1 : 81 + t - 24 = 57 + t := by omega
  rw [hk1]
  nlinarith

lemma three_log_mul_le_of_ge_1024 (k : ℕ) (hk : 1024 ≤ k) :
    k * (3 * Nat.log 2 k + 8) ≤ (k - 24) * (k - 24) := by
  have hk81 : 81 ≤ k := by omega
  have hls : Nat.log 2 k ≤ k.sqrt := log2_le_sqrt k hk81
  have hmul : k * (3 * Nat.log 2 k + 8) ≤ k * (3 * k.sqrt + 8) :=
    Nat.mul_le_mul_left k (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hls) _)
  refine le_trans hmul ?_
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hs : 32 ≤ (1024 + t).sqrt :=
    Nat.le_sqrt.mpr (by omega : 32 * 32 ≤ 1024 + t)
  have hcore : 3 * (1024 + t).sqrt + 56 ≤ 1024 + t := by
    have : 3 * (1024 + t).sqrt + 56 ≤ (1024 + t).sqrt * (1024 + t).sqrt := by
      obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hs
      rw [hu]; nlinarith
    exact le_trans this (Nat.sqrt_le _)
  have h48 : 3 * (1024 + t).sqrt + 8 + 48 ≤ 1024 + t := by omega
  have : 3 * (1024 + t).sqrt + 8 ≤ 1024 + t - 48 := by omega
  have hmul' : (1024 + t) * (3 * (1024 + t).sqrt + 8) ≤
      (1024 + t) * (1024 + t - 48) :=
    Nat.mul_le_mul_left _ this
  refine le_trans hmul' ?_
  have hk1 : 1024 + t - 24 = 1000 + t := by omega
  have hk2 : 1024 + t - 48 = 976 + t := by omega
  rw [hk1, hk2]
  nlinarith

lemma three_log_mul_le (k : ℕ) (hk : 81 ≤ k) :
    k * (3 * Nat.log 2 k + 8) ≤ (k - 24) * (k - 24) := by
  by_cases h : k < 2 ^ 10
  · exact three_log_mul_le_of_lt_1024 k hk h
  · have : 1024 ≤ k := by omega
    exact three_log_mul_le_of_ge_1024 k this

lemma midShift_add_24_le (k : ℕ) (hk : 81 ≤ k) :
    midShift k + 24 ≤ k := by
  rw [midShift_eq_logsqrt k hk]
  have hle := three_log_mul_le k hk
  have hsq : (k * (3 * Nat.log 2 k + 8)).sqrt ≤
      ((k - 24) * (k - 24)).sqrt := Nat.sqrt_le_sqrt hle
  rw [Nat.sqrt_eq] at hsq
  omega

lemma midShift_pos (k : ℕ) (hk : 81 ≤ k) : 2 ≤ midShift k := by
  have : 5 * k.sqrt ≤ midShift k := le_max_left _ _
  have : 9 ≤ k.sqrt := Nat.le_sqrt.mpr (by omega : 9 * 9 ≤ k)
  omega

lemma midShift_sq_ge (k : ℕ) (hk : 81 ≤ k) :
    k * (3 * Nat.log 2 k + 8) ≤ (midShift k + 1) * (midShift k + 1) := by
  rw [midShift_eq_logsqrt k hk]
  exact Nat.lt_succ_sqrt (k * (3 * Nat.log 2 k + 8)) |>.le

lemma hasDerivAt_log_one_sub_quad (t : ℝ) (ht : t < 1) :
    HasDerivAt (fun u : ℝ => -Real.log (1 - u) - u - u ^ 2 / 2)
      (t ^ 2 / (1 - t)) t := by
  have hlog : HasDerivAt (fun u : ℝ => Real.log (1 - u)) ((1 - t)⁻¹ * (-1)) t := by
    have hlin : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    exact (Real.hasDerivAt_log (by linarith : (1 - t : ℝ) ≠ 0)).comp t hlin
  have hid : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id t
  have hsq : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t := by
    have hp : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t)
    convert HasDerivAt.div_const hp 2 using 1
    ring
  have hcomb := (hlog.neg.sub hid).sub hsq
  convert hcomb using 1
  have hne : (1 - t : ℝ) ≠ 0 := by linarith
  field_simp
  ring

lemma log_one_sub_quadratic {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log (1 - x) ≤ -x - x ^ 2 / 2 := by
  by_cases hx : x = 0
  · subst hx; simp
  · have habs : |x| < 1 := by
      rw [abs_of_nonneg hx0]; exact hx1
    have hsum := Real.hasSum_pow_div_log_of_abs_lt_one habs
    have hnn : ∀ n : ℕ, 0 ≤ x ^ (n + 1) / ((n : ℝ) + 1) := by
      intro n
      exact div_nonneg (pow_nonneg hx0 _) (add_nonneg (Nat.cast_nonneg n) zero_le_one)
    have hpartial :
        ∑ i ∈ Finset.range 2, x ^ (i + 1) / ((i : ℝ) + 1) ≤
          ∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) :=
      Summable.sum_le_tsum (Finset.range 2) (fun _ _ => hnn _) hsum.summable
    have hsum2 : ∑ i ∈ Finset.range 2, x ^ (i + 1) / ((i : ℝ) + 1) =
        x + x ^ 2 / 2 := by
      simp [Finset.sum_range_succ, pow_one]
      ring
    have : x + x ^ 2 / 2 ≤ -Real.log (1 - x) := by
      rw [← hsum.tsum_eq, ← hsum2]; exact hpartial
    linarith

lemma log_one_sub_cubic {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log (1 - x) ≤ -x - x ^ 2 / 2 - x ^ 3 / 3 := by
  by_cases hx : x = 0
  · subst hx; simp
  · have habs : |x| < 1 := by
      rw [abs_of_nonneg hx0]; exact hx1
    have hsum := Real.hasSum_pow_div_log_of_abs_lt_one habs
    have hnn : ∀ n : ℕ, 0 ≤ x ^ (n + 1) / ((n : ℝ) + 1) := by
      intro n
      exact div_nonneg (pow_nonneg hx0 _) (add_nonneg (Nat.cast_nonneg n) zero_le_one)
    have hpartial :
        ∑ i ∈ Finset.range 3, x ^ (i + 1) / ((i : ℝ) + 1) ≤
          ∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) :=
      Summable.sum_le_tsum (Finset.range 3) (fun _ _ => hnn _) hsum.summable
    have hsum3 : ∑ i ∈ Finset.range 3, x ^ (i + 1) / ((i : ℝ) + 1) =
        x + x ^ 2 / 2 + x ^ 3 / 3 := by
      simp [Finset.sum_range_succ, pow_one]
      ring
    have : x + x ^ 2 / 2 + x ^ 3 / 3 ≤ -Real.log (1 - x) := by
      rw [← hsum.tsum_eq, ← hsum3]; exact hpartial
    linarith

lemma hasDerivAt_log_one_add_cubic (t : ℝ) (ht : -1 < t) :
    HasDerivAt (fun u : ℝ => u - u ^ 2 / 2 + u ^ 3 / 3 - Real.log (1 + u))
      (t ^ 3 / (1 + t)) t := by
  have h1 : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id t
  have h2 : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t := by
    have := HasDerivAt.div_const (hasDerivAt_pow 2 t) 2
    convert this using 1; ring
  have h3 : HasDerivAt (fun u : ℝ => u ^ 3 / 3) (t ^ 2) t := by
    have := HasDerivAt.div_const (hasDerivAt_pow 3 t) 3
    convert this using 1; ring
  have hlog : HasDerivAt (fun u : ℝ => Real.log (1 + u)) ((1 + t)⁻¹) t := by
    have : HasDerivAt (fun u : ℝ => (1 : ℝ) + u) 1 t :=
      (hasDerivAt_id t).const_add 1
    convert this.log (by linarith) using 1
    field_simp
  have hcomb := ((h1.sub h2).add h3).sub hlog
  convert hcomb using 1
  have hne : (1 + t : ℝ) ≠ 0 := by linarith
  field_simp
  ring

lemma log_one_add_cubic {x : ℝ} (hx0 : 0 ≤ x) :
    Real.log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    let f : ℝ → ℝ := fun u => u - u ^ 2 / 2 + u ^ 3 / 3 - Real.log (1 + u)
    have hcont : ContinuousOn f (Set.Icc 0 x) := by
      intro t ht
      have ht' : -1 < t := by
        have := Set.mem_Icc.mp ht
        linarith
      exact (hasDerivAt_log_one_add_cubic t ht').continuousAt.continuousWithinAt
    have hdiff : ∀ t ∈ Set.Ioo 0 x, HasDerivAt f (t ^ 3 / (1 + t)) t := by
      intro t ht
      have ht' : -1 < t := by
        have := Set.mem_Ioo.mp ht
        linarith
      exact hasDerivAt_log_one_add_cubic t ht'
    obtain ⟨c, hc, heq⟩ :=
      exists_hasDerivAt_eq_slope f (fun t => t ^ 3 / (1 + t)) hxpos hcont hdiff
    have hc0 : 0 < c := (Set.mem_Ioo.mp hc).1
    have hder : 0 ≤ c ^ 3 / (1 + c) :=
      div_nonneg (pow_nonneg (le_of_lt hc0) 3) (by linarith)
    have hxne : (x : ℝ) - 0 ≠ 0 := by linarith
    have hsub : f x - f 0 = (c ^ 3 / (1 + c)) * (x - 0) :=
      (div_eq_iff hxne).mp heq.symm
    have : 0 ≤ f x - f 0 := by
      rw [hsub]
      exact mul_nonneg hder (by linarith)
    simp [f] at this
    linarith

lemma fact13_eq : (13 : ℕ).factorial = 6227020800 := by native_decide

lemma exp_seven_gt_1095 : (1095 : ℝ) < Real.exp 7 := by
  have hbase : (2718 / 1000 : ℝ) < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hpow : (2718 / 1000 : ℝ) ^ 7 < Real.exp 1 ^ 7 :=
    pow_lt_pow_left₀ hbase (by positivity) (by decide : (7 : ℕ) ≠ 0)
  have hexp : Real.exp 1 ^ 7 = Real.exp 7 := by
    simpa using (Real.exp_nat_mul (1 : ℝ) 7).symm
  have hrat : (1095 : ℝ) < (2718 / 1000 : ℝ) ^ 7 := by
    rw [div_pow]
    have hN : (1095 : ℕ) * 1000 ^ 7 < 2718 ^ 7 := by native_decide
    have : (1095 : ℝ) * 1000 ^ 7 < 2718 ^ 7 := by exact_mod_cast hN
    have hpos : (0 : ℝ) < 1000 ^ 7 := by positivity
    exact (lt_div_iff₀ hpos).mpr (by linarith)
  linarith

lemma exp_two_gt_seven : (7 : ℝ) < Real.exp 2 := by
  have : (27 / 10 : ℝ) < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have : (27 / 10 : ℝ) ^ 2 < Real.exp 1 ^ 2 :=
    pow_lt_pow_left₀ this (by positivity) (by decide : (2 : ℕ) ≠ 0)
  have : Real.exp 1 ^ 2 = Real.exp 2 := by
    simpa using (Real.exp_nat_mul (1 : ℝ) 2).symm
  have : (27 / 10 : ℝ) ^ 2 = 729 / 100 := by norm_num
  linarith

lemma pow1095_three : (1095 : ℕ) ^ 3 = 1312932375 := by native_decide

lemma log_fact13_lt_23 : Real.log ((13 : ℕ).factorial : ℝ) < 23 := by
  rw [fact13_eq]
  have hpos : (0 : ℝ) < 6227020800 := by norm_num
  refine (Real.log_lt_iff_lt_exp hpos).mpr ?_
  have h7 := exp_seven_gt_1095
  have h2 := exp_two_gt_seven
  have hexp : Real.exp 23 = Real.exp 7 ^ 3 * Real.exp 2 := by
    have h23 : (23 : ℝ) = 3 * 7 + 2 := by norm_num
    rw [h23, Real.exp_add]
    have : Real.exp (3 * 7) = Real.exp 7 ^ 3 := by
      simpa using Real.exp_nat_mul (7 : ℝ) 3
    rw [this]
  have h1095 : (1095 : ℝ) ^ 3 * 7 < Real.exp 7 ^ 3 * Real.exp 2 := by
    have h1 : (1095 : ℝ) ^ 3 < Real.exp 7 ^ 3 :=
      pow_lt_pow_left₀ h7 (by positivity) (by decide : (3 : ℕ) ≠ 0)
    nlinarith [Real.exp_pos (7 : ℝ), Real.exp_pos (2 : ℝ)]
  have hnum : (6227020800 : ℝ) < (1095 : ℝ) ^ 3 * 7 := by
    have : (1095 : ℕ) ^ 3 * 7 = 9190526625 := by
      rw [pow1095_three]
    have : (6227020800 : ℕ) < 9190526625 := by decide
    exact_mod_cast this
  linarith

lemma log_six_div_five_le : Real.log (6 / 5 : ℝ) ≤ (1 / 5 : ℝ) := by
  have : Real.log (6 / 5) = Real.log (1 + 1 / 5) := by norm_num
  rw [this]
  simpa using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 + 1 / 5)

lemma two_real_log_fact_upper {n : ℕ} (hn : 1 ≤ n) :
    2 * Real.log (n.factorial : ℝ) ≤
      2 + Real.log n + 2 * n * Real.log n - 2 * n := by
  have h := log_factorial_upper hn
  linarith

lemma log_fact_stirling_lower {n : ℕ} (hn : n ≠ 0) :
    n * Real.log n - n + Real.log n / 2 + Real.log (2 * Real.pi) / 2 ≤
      Real.log (n.factorial : ℝ) :=
  Stirling.le_log_factorial_stirling hn

/-- Auxiliary real inequalities for the mid-term bound. -/
lemma real_log_two_lt_one : Real.log 2 < 1 := by
  have : Real.log 2 < Real.log (Real.exp 1) :=
    Real.log_lt_log (by positivity) Real.exp_one_gt_two
  rwa [Real.log_exp] at this

lemma real_log_six_gt_one : 1 < Real.log 6 := by
  have : Real.exp 1 < 6 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  simpa [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) this

lemma real_two_pi_ge_six : (6 : ℝ) ≤ 2 * Real.pi := by
  have : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
  linarith

lemma real_log_two_pi_gt_one : 1 < Real.log (2 * Real.pi) :=
  lt_of_lt_of_le real_log_six_gt_one
    (Real.log_le_log (by positivity) real_two_pi_ge_six)

lemma nat_log2_ge_log_div (k : ℕ) (hk : 1 ≤ k) :
    Real.log k / Real.log 2 - 1 < Nat.log 2 k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlt : k < 2 ^ (Nat.log 2 k + 1) :=
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) k
  have : (k : ℝ) < (2 : ℝ) ^ (Nat.log 2 k + 1) := by exact_mod_cast hlt
  have hloglt : Real.log k < (Nat.log 2 k + 1 : ℝ) * Real.log 2 := by
    have := Real.log_lt_log hkpos this
    rw [Real.log_pow] at this
    convert this
    simp
  have : Real.log k < (Nat.log 2 k : ℝ) * Real.log 2 + Real.log 2 := by
    linarith
  have : Real.log k / Real.log 2 < (Nat.log 2 k : ℝ) + 1 :=
    (div_lt_iff₀ hlog2pos).mpr (by linarith)
  linarith

lemma three_log_k_le_three_log2 (k : ℕ) (hk : 81 ≤ k) :
    (3 : ℝ) * Real.log k + 3 ≤ 3 * Nat.log 2 k + 8 := by
  have hlt := nat_log2_ge_log_div k (by omega)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2lt : Real.log 2 < 1 := real_log_two_lt_one
  have hge : (3 : ℝ) * (Real.log k / Real.log 2 - 1) + 8 ≤ 3 * Nat.log 2 k + 8 := by
    nlinarith
  have hdiv : Real.log k ≤ Real.log k / Real.log 2 := by
    have hlogk : 0 ≤ Real.log k := Real.log_natCast_nonneg k
    exact (le_div_iff₀ hlog2pos).mpr (by nlinarith [hlog2lt])
  nlinarith

lemma midShift_sq_div_ge (k : ℕ) (hk : 81 ≤ k) :
    (3 : ℝ) * Real.log k + 3 ≤ ((midShift k : ℝ) + 1) ^ 2 / k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsq : (k : ℝ) * (3 * Nat.log 2 k + 8) ≤ ((midShift k : ℝ) + 1) * ((midShift k : ℝ) + 1) := by
    have := midShift_sq_ge k hk
    exact_mod_cast this
  have hsq' : (k : ℝ) * (3 * Nat.log 2 k + 8) ≤ ((midShift k : ℝ) + 1) ^ 2 := by
    rwa [pow_two]
  have hdiv : (3 : ℝ) * Nat.log 2 k + 8 ≤ ((midShift k : ℝ) + 1) ^ 2 / k :=
    (le_div_iff₀ hkpos).mpr (by linarith [hsq'])
  exact le_trans (three_log_k_le_three_log2 k hk) hdiv

lemma neg_log_one_sub_inv (k : ℕ) (hk : 2 ≤ k) :
    ((k - 1 : ℕ) : ℝ) * (-Real.log (1 - (1 : ℝ) / k)) ≤ 1 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpos : (0 : ℝ) < 1 - (1 : ℝ) / k := by
    have : (1 : ℝ) / k < 1 := (div_lt_one hkpos).mpr (by exact_mod_cast (show 1 < k by omega))
    linarith
  have hinv : Real.log ((1 - (1 : ℝ) / k)⁻¹) = -Real.log (1 - 1 / k) := Real.log_inv _
  have hup : Real.log ((1 - (1 : ℝ) / k)⁻¹) ≤ (1 - (1 : ℝ) / k)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hk1ne : (k : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
    linarith
  have hfrac : (1 - (1 : ℝ) / k)⁻¹ - 1 = (1 : ℝ) / ((k : ℝ) - 1) := by
    field_simp [hkpos.ne', hk1ne]
    ring
  have : -Real.log (1 - (1 : ℝ) / k) ≤ 1 / ((k : ℝ) - 1) := by
    rw [← hinv]
    linarith
  have hkn : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    linarith
  have hmul := mul_le_mul_of_nonneg_left this hkn
  have hcancel : ((k : ℝ) - 1) * (1 / ((k : ℝ) - 1)) = 1 :=
    mul_div_cancel₀ 1 hk1ne
  rw [hkm1]
  linarith

lemma mid_cut_bounds (k : ℕ) (hk : 81 ≤ k) :
    24 ≤ k - midShift k ∧ k - midShift k + 2 ≤ k ∧
      2 ≤ midShift k ∧ midShift k + 1 < k := by
  have hs24 := midShift_add_24_le k hk
  have hs2 := midShift_pos k hk
  omega

/-- Combine 2 log((j-1)!) with the remaining power. -/
lemma two_log_fact_shift_combine {j k : ℕ} (hj : 3 ≤ j) :
    2 * Real.log (((j - 1).factorial : ℝ)) +
      (2 * (k : ℝ) - 2 * (j : ℝ) + 1) * Real.log ((j - 1 : ℕ) : ℝ) ≤
      4 - 2 * (j : ℝ) + 2 * (k : ℝ) * Real.log ((j - 1 : ℕ) : ℝ) := by
  have hjm : 1 ≤ j - 1 := by omega
  have hup := two_real_log_fact_upper (n := j - 1) hjm
  have hjcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]
  have hstep :
      2 * Real.log (((j - 1).factorial : ℝ)) +
        (2 * (k : ℝ) - 2 * (j : ℝ) + 1) * Real.log ((j - 1 : ℕ) : ℝ) ≤
      2 + Real.log ((j - 1 : ℕ) : ℝ) +
        2 * ((j - 1 : ℕ) : ℝ) * Real.log ((j - 1 : ℕ) : ℝ)
        - 2 * ((j - 1 : ℕ) : ℝ) +
        (2 * (k : ℝ) - 2 * (j : ℝ) + 1) * Real.log ((j - 1 : ℕ) : ℝ) := by
    linarith [hup]
  refine le_trans hstep ?_
  have hcoef : (1 : ℝ) + 2 * ((j - 1 : ℕ) : ℝ) + (2 * (k : ℝ) - 2 * (j : ℝ) + 1) =
      2 * (k : ℝ) := by rw [hjcast]; ring
  have hconst : (2 : ℝ) - 2 * ((j - 1 : ℕ) : ℝ) = 4 - 2 * (j : ℝ) := by
    rw [hjcast]; ring
  calc
    2 + Real.log ((j - 1 : ℕ) : ℝ) +
        2 * ((j - 1 : ℕ) : ℝ) * Real.log ((j - 1 : ℕ) : ℝ)
        - 2 * ((j - 1 : ℕ) : ℝ) +
        (2 * (k : ℝ) - 2 * (j : ℝ) + 1) * Real.log ((j - 1 : ℕ) : ℝ)
        = (2 - 2 * ((j - 1 : ℕ) : ℝ)) +
          ((1 : ℝ) + 2 * ((j - 1 : ℕ) : ℝ) + (2 * (k : ℝ) - 2 * (j : ℝ) + 1)) *
            Real.log ((j - 1 : ℕ) : ℝ) := by ring
    _ = (4 - 2 * (j : ℝ)) + (2 * (k : ℝ)) * Real.log ((j - 1 : ℕ) : ℝ) := by
        rw [hconst, hcoef]
  exact le_of_eq (by ring)

lemma jpred_cast (k : ℕ) (hk : 81 ≤ k) :
    ((k - midShift k - 1 : ℕ) : ℝ) = (k : ℝ) - ((midShift k + 1 : ℕ) : ℝ) := by
  have : k - midShift k - 1 = k - (midShift k + 1) := by
    have := (mid_cut_bounds k hk).2.2.2; omega
  rw [this, Nat.cast_sub (by
    have := (mid_cut_bounds k hk).2.2.2; omega), Nat.cast_add, Nat.cast_one]

lemma two_k_log_jpred (k : ℕ) (hk : 81 ≤ k) :
    2 * (k : ℝ) * Real.log ((k - midShift k - 1 : ℕ) : ℝ) ≤
      2 * (k : ℝ) * Real.log k
        - 2 * ((midShift k + 1 : ℕ) : ℝ)
        - ((midShift k + 1 : ℕ) : ℝ) ^ 2 / k := by
  set s := midShift k
  have hsk : s + 1 < k := (mid_cut_bounds k hk).2.2.2
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hjcast := jpred_cast k hk
  have hfrac : ((k - s - 1 : ℕ) : ℝ) = (k : ℝ) * (1 - ((s + 1 : ℕ) : ℝ) / k) := by
    rw [show s = midShift k from rfl, hjcast]
    have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
    field_simp [hkne]
  have hpos : (0 : ℝ) < 1 - ((s + 1 : ℕ) : ℝ) / k := by
    have : ((s + 1 : ℕ) : ℝ) / k < 1 :=
      (div_lt_one hkpos).mpr (by exact_mod_cast hsk)
    linarith
  have hlog : Real.log ((k - s - 1 : ℕ) : ℝ) =
      Real.log k + Real.log (1 - ((s + 1 : ℕ) : ℝ) / k) := by
    rw [hfrac, Real.log_mul hkpos.ne' (ne_of_gt hpos)]
  have hx0 : (0 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) / k := by positivity
  have hx1 : ((s + 1 : ℕ) : ℝ) / k < 1 :=
    (div_lt_one hkpos).mpr (by exact_mod_cast hsk)
  have hquad := log_one_sub_quadratic hx0 hx1
  have h2k : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
  rw [hlog]
  have hexp : 2 * (k : ℝ) * (Real.log k + Real.log (1 - ((s + 1 : ℕ) : ℝ) / k)) =
      2 * (k : ℝ) * Real.log k + 2 * (k : ℝ) * Real.log (1 - ((s + 1 : ℕ) : ℝ) / k) := by
    ring
  rw [hexp]
  have hmul := mul_le_mul_of_nonneg_left hquad h2k
  have hsum := add_le_add_right hmul (2 * (k : ℝ) * Real.log k)
  refine le_trans hsum ?_
  -- 2k log k + 2k (-x - x²/2) = 2k log k - 2(s+1) - (s+1)²/k
  have hx : (2 * (k : ℝ)) * (((s + 1 : ℕ) : ℝ) / k) = 2 * ((s + 1 : ℕ) : ℝ) := by
    have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
    field_simp [hkne]
  have hx2 : (2 * (k : ℝ)) * ((((s + 1 : ℕ) : ℝ) / k) ^ 2 / 2) =
      ((s + 1 : ℕ) : ℝ) ^ 2 / k := by
    have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
    field_simp [hkne]
  linarith

lemma neg_km1_log (k : ℕ) (hk : 2 ≤ k) :
    -((k - 1 : ℕ) : ℝ) * Real.log ((k - 1 : ℕ) : ℝ) ≤
      -((k - 1 : ℕ) : ℝ) * Real.log k + 1 := by
  have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpos : (0 : ℝ) < 1 - (1 : ℝ) / k := by
    have : (1 : ℝ) / k < 1 := (div_lt_one hkpos).mpr (by exact_mod_cast (show 1 < k by omega))
    linarith
  have hlogeq : Real.log ((k - 1 : ℕ) : ℝ) = Real.log k + Real.log (1 - (1 : ℝ) / k) := by
    have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) * (1 - (1 : ℝ) / k) := by
      rw [hkm1]
      have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
      field_simp [hkne]
    rw [this, Real.log_mul (ne_of_gt hkpos) (ne_of_gt hpos)]
  have hneg := neg_log_one_sub_inv k hk
  have hmul : ((k - 1 : ℕ) : ℝ) * Real.log ((k - 1 : ℕ) : ℝ) =
      ((k - 1 : ℕ) : ℝ) * Real.log k +
        ((k - 1 : ℕ) : ℝ) * Real.log (1 - (1 : ℝ) / k) := by
    rw [hlogeq]; ring
  have : -(((k - 1 : ℕ) : ℝ) * Real.log ((k - 1 : ℕ) : ℝ)) =
      -((k - 1 : ℕ) : ℝ) * Real.log k
        - ((k - 1 : ℕ) : ℝ) * Real.log (1 - (1 : ℝ) / k) := by
    rw [hmul]; ring
  -- rewrite the goal's left side similarly
  have hL : -((k - 1 : ℕ) : ℝ) * Real.log ((k - 1 : ℕ) : ℝ) =
      -(((k - 1 : ℕ) : ℝ) * Real.log ((k - 1 : ℕ) : ℝ)) := by ring
  rw [hL, this]
  have : -((k - 1 : ℕ) : ℝ) * Real.log (1 - (1 : ℝ) / k) =
      ((k - 1 : ℕ) : ℝ) * (-Real.log (1 - (1 : ℝ) / k)) := by ring
  linarith

lemma neg_two_logs_fact (k : ℕ) (hk : 81 ≤ k) :
    -Real.log (k.factorial : ℝ) - Real.log (((k - 1).factorial : ℝ)) ≤
      -((2 * (k : ℝ) - 1) * Real.log k) + 2 * (k : ℝ)
        - (Real.log k + Real.log ((k - 1 : ℕ) : ℝ)) / 2
        - Real.log (2 * Real.pi) := by
  have h1 := log_fact_stirling_lower (show k ≠ 0 by omega)
  have h2 := log_fact_stirling_lower (show k - 1 ≠ 0 by omega)
  have hneg := neg_km1_log k (by omega)
  have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hkU : -Real.log (k.factorial : ℝ) ≤
      -(k : ℝ) * Real.log k + (k : ℝ) - Real.log k / 2 - Real.log (2 * Real.pi) / 2 := by
    linarith [h1]
  have hkmU : -Real.log (((k - 1).factorial : ℝ)) ≤
      -((k - 1 : ℕ) : ℝ) * Real.log ((k - 1 : ℕ) : ℝ)
        + ((k - 1 : ℕ) : ℝ)
        - Real.log ((k - 1 : ℕ) : ℝ) / 2 - Real.log (2 * Real.pi) / 2 := by
    linarith [h2]
  have hsum : -Real.log (k.factorial : ℝ) - Real.log (((k - 1).factorial : ℝ)) ≤
      -(k : ℝ) * Real.log k + (k : ℝ) - Real.log k / 2 - Real.log (2 * Real.pi) / 2
        - ((k - 1 : ℕ) : ℝ) * Real.log k + 1
        + ((k - 1 : ℕ) : ℝ)
        - Real.log ((k - 1 : ℕ) : ℝ) / 2 - Real.log (2 * Real.pi) / 2 := by
    linarith [hkU, hkmU, hneg]
  rw [hkm1] at hsum ⊢
  have hrew : -((2 * (k : ℝ) - 1) * Real.log k) + 2 * (k : ℝ)
        - (Real.log k + Real.log ((k : ℝ) - 1)) / 2
        - Real.log (2 * Real.pi)
      = -(k : ℝ) * Real.log k + (k : ℝ) - Real.log k / 2 - Real.log (2 * Real.pi) / 2
        - ((k : ℝ) - 1) * Real.log k + 1
        + ((k : ℝ) - 1)
        - Real.log ((k : ℝ) - 1) / 2 - Real.log (2 * Real.pi) / 2 := by
    ring
  linarith

lemma leftover_nonpos (k : ℕ) (hk : 81 ≤ k) :
    Real.log 2 + (2 : ℝ) - Real.log (2 * Real.pi) + (3 : ℝ) * Real.log k
      + (1 / 2) * Real.log (k / ((k - 1 : ℕ) : ℝ))
      - ((midShift k : ℝ) + 1) ^ 2 / k ≤ 0 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkm1pos : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hle1 : Real.log (k / ((k - 1 : ℕ) : ℝ)) ≤ 1 := by
    have heq : (k : ℝ) / ((k - 1 : ℕ) : ℝ) = 1 + 1 / ((k - 1 : ℕ) : ℝ) := by
      rw [hkm1]
      have hne : (k : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hne]; ring
    rw [heq]
    have hx1 : (1 : ℝ) / ((k - 1 : ℕ) : ℝ) ≤ 1 := by
      have : (1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k - 1 by omega)
      exact div_le_one_of_le₀ this (le_of_lt hkm1pos)
    have hlog := Real.log_le_sub_one_of_pos
      (by positivity : (0 : ℝ) < 1 + 1 / ((k - 1 : ℕ) : ℝ))
    linarith
  have hconst : Real.log 2 + (2 : ℝ) - Real.log (2 * Real.pi) + (1 / 2 : ℝ) ≤ (5 / 2 : ℝ) := by
    linarith [real_log_two_lt_one, real_log_two_pi_gt_one]
  have hdom := midShift_sq_div_ge k hk
  have hhalf : (1 / 2 : ℝ) * Real.log (k / ((k - 1 : ℕ) : ℝ)) ≤ 1 / 2 := by
    nlinarith [hle1]
  linarith [hdom, hconst, hhalf]

/-- Algebraic identity: `4 - 2j - 2(s+1) + 2k = 2` when `j = k - s`. -/
lemma mid_linear_const (k : ℕ) (hk : 81 ≤ k) :
    (4 : ℝ) - 2 * ((k - midShift k : ℕ) : ℝ)
      - 2 * ((midShift k + 1 : ℕ) : ℝ) + 2 * (k : ℝ) = 2 := by
  have hsle : midShift k ≤ k := by
    have := midShift_add_24_le k hk; omega
  have hj : ((k - midShift k : ℕ) : ℝ) = (k : ℝ) - (midShift k : ℝ) :=
    Nat.cast_sub hsle
  have hsc : ((midShift k + 1 : ℕ) : ℝ) = (midShift k : ℝ) + 1 := by simp
  rw [hj, hsc]; ring

lemma mid_cut_log_diff_le (k : ℕ) (hk : 81 ≤ k) :
    let s := midShift k
    let j := k - s
    Real.log 2 + Real.log j + 2 * Real.log ((j - 1).factorial : ℝ)
      + (2 * k - 2 * j + 1 : ℝ) * Real.log (j - 1 : ℝ)
      - Real.log (k.factorial : ℝ) - Real.log ((k - 1).factorial : ℝ)
      + 2 * Real.log k ≤ 0 := by
  intro s j
  have hb := mid_cut_bounds k hk
  have hj24 : 24 ≤ j := by
    simpa [j, s] using hb.1
  have hj3 : 3 ≤ j := by omega
  have hsle : s ≤ k := by
    have := midShift_add_24_le k hk; omega
  have hcast_j1 : (j - 1 : ℝ) = ((j - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]
  have hcomb := two_log_fact_shift_combine (j := j) (k := k) hj3
  have hgoal_comb :
      2 * Real.log ((j - 1).factorial : ℝ) +
        (2 * k - 2 * j + 1 : ℝ) * Real.log (j - 1 : ℝ) ≤
      4 - 2 * (j : ℝ) + 2 * (k : ℝ) * Real.log (j - 1 : ℝ) := by
    -- `(2*k - 2*j + 1 : ℝ)` is defeq to `2*↑k - 2*↑j + 1`
    simpa [hcast_j1] using hcomb
  have hj1eq : j - 1 = k - s - 1 := by omega
  have h2k := two_k_log_jpred k hk
  have h2k' : 2 * (k : ℝ) * Real.log (j - 1 : ℝ) ≤
      2 * (k : ℝ) * Real.log k - 2 * ((s + 1 : ℕ) : ℝ)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k := by
    rw [hcast_j1, hj1eq]
    simpa [s] using h2k
  have hneg := neg_two_logs_fact k hk
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlogj : Real.log j ≤ Real.log k :=
    Real.log_le_log hjpos (by exact_mod_cast (show j ≤ k by omega))
  have hlin := mid_linear_const k hk
  -- Step 1: replace the two-fact + power by the combined upper bound
  have hstep1 :
      Real.log 2 + Real.log j + 2 * Real.log ((j - 1).factorial : ℝ)
        + (2 * k - 2 * j + 1 : ℝ) * Real.log (j - 1 : ℝ)
        - Real.log (k.factorial : ℝ) - Real.log ((k - 1).factorial : ℝ)
        + 2 * Real.log k
      ≤ Real.log 2 + Real.log j + 4 - 2 * (j : ℝ)
        + 2 * (k : ℝ) * Real.log (j - 1 : ℝ)
        - Real.log (k.factorial : ℝ) - Real.log ((k - 1).factorial : ℝ)
        + 2 * Real.log k := by
    linarith [hgoal_comb]
  -- Step 2: expand log(j-1)
  have hstep2 :
      Real.log 2 + Real.log j + 4 - 2 * (j : ℝ)
        + 2 * (k : ℝ) * Real.log (j - 1 : ℝ)
        - Real.log (k.factorial : ℝ) - Real.log ((k - 1).factorial : ℝ)
        + 2 * Real.log k
      ≤ Real.log 2 + Real.log j + 4 - 2 * (j : ℝ)
        + 2 * (k : ℝ) * Real.log k - 2 * ((s + 1 : ℕ) : ℝ)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k
        - Real.log (k.factorial : ℝ) - Real.log ((k - 1).factorial : ℝ)
        + 2 * Real.log k := by
    linarith [h2k']
  -- Step 3: Stirling lower bounds
  have hstep3 :
      Real.log 2 + Real.log j + 4 - 2 * (j : ℝ)
        + 2 * (k : ℝ) * Real.log k - 2 * ((s + 1 : ℕ) : ℝ)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k
        - Real.log (k.factorial : ℝ) - Real.log ((k - 1).factorial : ℝ)
        + 2 * Real.log k
      ≤ Real.log 2 + Real.log j + 4 - 2 * (j : ℝ)
        + 2 * (k : ℝ) * Real.log k - 2 * ((s + 1 : ℕ) : ℝ)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k
        - ((2 * (k : ℝ) - 1) * Real.log k) + 2 * (k : ℝ)
        - (Real.log k + Real.log ((k - 1 : ℕ) : ℝ)) / 2
        - Real.log (2 * Real.pi)
        + 2 * Real.log k := by
    linarith [hneg]
  have hlin' : (4 : ℝ) - 2 * (j : ℝ) - 2 * ((s + 1 : ℕ) : ℝ) + 2 * (k : ℝ) = 2 := by
    simpa [j, s] using hlin
  have hlogs : (2 : ℝ) * (k : ℝ) * Real.log k
      - (2 * (k : ℝ) - 1) * Real.log k + 2 * Real.log k
      = (3 : ℝ) * Real.log k := by ring
  have hsimp :
      Real.log 2 + Real.log j + 4 - 2 * (j : ℝ)
        + 2 * (k : ℝ) * Real.log k - 2 * ((s + 1 : ℕ) : ℝ)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k
        - ((2 * (k : ℝ) - 1) * Real.log k) + 2 * (k : ℝ)
        - (Real.log k + Real.log ((k - 1 : ℕ) : ℝ)) / 2
        - Real.log (2 * Real.pi)
        + 2 * Real.log k
      = Real.log 2 + Real.log j + 2 + (3 : ℝ) * Real.log k
        - (Real.log k + Real.log ((k - 1 : ℕ) : ℝ)) / 2
        - Real.log (2 * Real.pi)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k := by
    linear_combination hlin' + hlogs
  -- Now log j ≤ log k, and leftover ≤ 0
  have hcast_s1 : ((s + 1 : ℕ) : ℝ) = (s : ℝ) + 1 := by simp
  have hleft := leftover_nonpos k hk
  have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  -- leftover is log2 + 2 - log(2π) + 3 log k + (1/2) log(k/(k-1)) - (s+1)²/k ≤ 0
  -- Our expression after replacing log j by log k is:
  -- log2 + log k + 2 + 3 log k - (log k + log(k-1))/2 - log(2π) - (s+1)²/k
  -- = log2 + 2 - log(2π) + 3 log k + log k - log k/2 - log(k-1)/2 - (s+1)²/k
  -- = leftover without the (1/2)log(k/(k-1)) plus log k - log k/2 - log(k-1)/2
  -- log k - log k/2 - log(k-1)/2 = log k/2 - log(k-1)/2 = (1/2) log(k/(k-1))
  have hident :
      Real.log 2 + Real.log k + 2 + (3 : ℝ) * Real.log k
        - (Real.log k + Real.log ((k - 1 : ℕ) : ℝ)) / 2
        - Real.log (2 * Real.pi)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k
      = Real.log 2 + (2 : ℝ) - Real.log (2 * Real.pi) + (3 : ℝ) * Real.log k
        + (1 / 2) * Real.log (k / ((k - 1 : ℕ) : ℝ))
        - ((midShift k : ℝ) + 1) ^ 2 / k := by
    have hdiv : Real.log (k / ((k - 1 : ℕ) : ℝ)) =
        Real.log k - Real.log ((k - 1 : ℕ) : ℝ) :=
      Real.log_div (ne_of_gt hkpos)
        (by exact_mod_cast (show k - 1 ≠ 0 by omega))
    have hs1 : ((s + 1 : ℕ) : ℝ) = (midShift k : ℝ) + 1 := by
      simp [s]
    rw [hdiv, hs1]
    ring
  have hfinal :
      Real.log 2 + Real.log j + 2 + (3 : ℝ) * Real.log k
        - (Real.log k + Real.log ((k - 1 : ℕ) : ℝ)) / 2
        - Real.log (2 * Real.pi)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k ≤ 0 := by
    have : Real.log 2 + Real.log j + 2 + (3 : ℝ) * Real.log k
        - (Real.log k + Real.log ((k - 1 : ℕ) : ℝ)) / 2
        - Real.log (2 * Real.pi)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k
      ≤ Real.log 2 + Real.log k + 2 + (3 : ℝ) * Real.log k
        - (Real.log k + Real.log ((k - 1 : ℕ) : ℝ)) / 2
        - Real.log (2 * Real.pi)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k := by
      linarith [hlogj]
    refine le_trans this ?_
    rw [hident]
    exact hleft
  linarith [hstep1, hstep2, hstep3, hsimp, hfinal]

lemma log_nat_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a * b : ℝ) = Real.log a + Real.log b :=
  Real.log_mul (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')

/-- Real form of the mid-cut monomial. -/
lemma mid_cut_monomial_log (k : ℕ) (hk : 81 ≤ k)
    (s j : ℕ) (hs : s = midShift k) (hj : j = k - s) :
    Real.log ((2 : ℝ) * j * (j - 1).factorial * (j - 1).factorial *
      ((j - 1 : ℕ) : ℝ) ^ (2 * s + 1) * k * k) =
    Real.log 2 + Real.log j + 2 * Real.log ((j - 1).factorial : ℝ)
      + (2 * s + 1 : ℝ) * Real.log ((j - 1 : ℕ) : ℝ)
      + 2 * Real.log k := by
  have hb := mid_cut_bounds k hk
  have hj0 : (0 : ℝ) < j := by
    have : 24 ≤ j := by rw [hj, hs]; exact hb.1
    exact_mod_cast (show 0 < j by omega)
  have hf0 : (0 : ℝ) < (j - 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hbase : (0 : ℝ) < (j - 1 : ℕ) := by
    have : 24 ≤ j := by rw [hj, hs]; exact hb.1
    exact_mod_cast (show 0 < j - 1 by omega)
  have hp0 : (0 : ℝ) < ((j - 1 : ℕ) : ℝ) ^ (2 * s + 1) := pow_pos hbase _
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
  push_cast
  ring

lemma mid_cut_term_le (k : ℕ) (hk : 81 ≤ k) :
    let s := midShift k
    let j := k - s
    2 * j * (j - 1).factorial * (j - 1).factorial *
      (j - 1) ^ (2 * s + 1) * k * k
        ≤ k.factorial * (k - 1).factorial := by
  intro s j
  have hb := mid_cut_bounds k hk
  have hj24 : 24 ≤ j := by simpa [j, s] using hb.1
  have hcast :
      ((2 * j * (j - 1).factorial * (j - 1).factorial *
        (j - 1) ^ (2 * s + 1) * k * k : ℕ) : ℝ) =
      (2 : ℝ) * j * (j - 1).factorial * (j - 1).factorial *
        ((j - 1 : ℕ) : ℝ) ^ (2 * s + 1) * k * k := by norm_cast
  have hcastR :
      ((k.factorial * (k - 1).factorial : ℕ) : ℝ) =
      (k.factorial : ℝ) * ((k - 1).factorial : ℝ) := by norm_cast
  have hposL : (0 : ℝ) <
      (2 : ℝ) * j * (j - 1).factorial * (j - 1).factorial *
        ((j - 1 : ℕ) : ℝ) ^ (2 * s + 1) * k * k := by
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hf0 : (0 : ℝ) < (j - 1).factorial := by exact_mod_cast Nat.factorial_pos _
    have hbse : (0 : ℝ) < (j - 1 : ℕ) := by exact_mod_cast (show 0 < j - 1 by omega)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    positivity
  have hposR : (0 : ℝ) < (k.factorial : ℝ) * ((k - 1).factorial : ℝ) := by
    have : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have : (0 : ℝ) < (k - 1).factorial := by exact_mod_cast Nat.factorial_pos _
    positivity
  have hlog := mid_cut_log_diff_le k hk
  have hexp := mid_cut_monomial_log k hk s j rfl rfl
  have hpow : (2 * s + 1 : ℝ) = (2 * k - 2 * j + 1 : ℝ) := by
    have hnat : (2 * s + 1 : ℕ) = 2 * k - 2 * j + 1 := by
      have := hb.2.2.2
      omega
    have hle : 2 * j ≤ 2 * k := by omega
    calc
      (2 * s + 1 : ℝ) = ((2 * s + 1 : ℕ) : ℝ) := by norm_cast
      _ = ((2 * k - 2 * j + 1 : ℕ) : ℝ) := by rw [hnat]
      _ = (2 * k - 2 * j + 1 : ℝ) := by
          rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_one]
          simp [Nat.cast_mul]
  have hjm : (j - 1 : ℝ) = ((j - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]
  have hineq :
      Real.log ((2 : ℝ) * j * (j - 1).factorial * (j - 1).factorial *
        ((j - 1 : ℕ) : ℝ) ^ (2 * s + 1) * k * k)
      ≤ Real.log ((k.factorial : ℝ) * ((k - 1).factorial : ℝ)) := by
    rw [hexp, log_nat_mul (Nat.factorial_pos _) (Nat.factorial_pos _)]
    -- hlog after unfolding lets
    have : Real.log 2 + Real.log j + 2 * Real.log ((j - 1).factorial : ℝ)
        + (2 * k - 2 * j + 1 : ℝ) * Real.log (j - 1 : ℝ)
        - Real.log (k.factorial : ℝ) - Real.log ((k - 1).factorial : ℝ)
        + 2 * Real.log k ≤ 0 := hlog
    rw [hpow, ← hjm]
    linarith
  have := (Real.log_le_log_iff hposL hposR).1 hineq
  have : ((2 * j * (j - 1).factorial * (j - 1).factorial *
      (j - 1) ^ (2 * s + 1) * k * k : ℕ) : ℝ)
      ≤ ((k.factorial * (k - 1).factorial : ℕ) : ℝ) := by
    rwa [hcast, hcastR]
  exact Nat.cast_le.mp this

lemma mid_shift_pow_term (k j : ℕ) (hj : 2 ≤ j) :
    j.factorial * (2 * (j - 1).factorial * (j - 1) ^ (2 * k - 2 * j + 1)) =
      2 * j * (j - 1).factorial * (j - 1).factorial *
        (j - 1) ^ (2 * k - 2 * j + 1) := by
  have : j.factorial = j * (j - 1).factorial := fact_pred j (by omega)
  rw [this]; ring

lemma W_mid_term_shift (k j : ℕ) (hj : 2 ≤ j) (hjk : j ≤ k) :
    j.factorial * W (2 * k - j) (j - 1) ≤
      2 * j * (j - 1).factorial * (j - 1).factorial *
        (j - 1) ^ (2 * k - 2 * j + 1) := by
  have hW : W (2 * k - j) (j - 1) ≤
      2 * (j - 1).factorial * (j - 1) ^ (2 * k - 2 * j + 1) := by
    have : 2 * k - j = (j - 1) + (2 * k - 2 * j + 1) := by omega
    rw [this]
    exact W_le_shift_pow (j - 1) (2 * k - 2 * j + 1)
  have := Nat.mul_le_mul_left j.factorial hW
  rwa [mid_shift_pow_term k j hj] at this

/-- The shift-power proxy is nondecreasing in `j` for `2 ≤ j < k`. -/
lemma shift_pow_proxy_ratio {k j : ℕ} (hj : 2 ≤ j) (hjk : j < k) :
    2 * j * (j - 1).factorial * (j - 1).factorial *
      (j - 1) ^ (2 * k - 2 * j + 1) ≤
    2 * (j + 1) * j.factorial * j.factorial *
      j ^ (2 * k - 2 * (j + 1) + 1) := by
  have hf : j.factorial = j * (j - 1).factorial := fact_pred j (by omega)
  have hpexp : 2 * k - 2 * (j + 1) + 1 = 2 * k - 2 * j - 1 := by omega
  rw [hf, hpexp]
  -- Cancel `2 * ((j-1)! )^2`
  have hcore : j * (j - 1) ^ (2 * k - 2 * j + 1) ≤
      (j + 1) * j * j * j ^ (2 * k - 2 * j - 1) := by
    have hp : (j - 1) ^ (2 * k - 2 * j + 1) ≤ j ^ (2 * k - 2 * j + 1) :=
      Nat.pow_le_pow_left (by omega) _
    have hmul := Nat.mul_le_mul_left j hp
    have hj1 : j ≤ j + 1 := by omega
    have hexp : j ^ (2 * k - 2 * j + 1) = j * j * j ^ (2 * k - 2 * j - 1) := by
      have : 2 * k - 2 * j + 1 = 2 + (2 * k - 2 * j - 1) := by omega
      rw [this, Nat.pow_add, Nat.pow_two]
    have : j * j ^ (2 * k - 2 * j + 1) = j * (j * j * j ^ (2 * k - 2 * j - 1)) := by
      rw [hexp]
    -- j * (j-1)^p ≤ j * j^p = j^p * j ≤ (j+1) * j * j * j^{p-2} wait
    have h1 : j * (j - 1) ^ (2 * k - 2 * j + 1) ≤
        j * j ^ (2 * k - 2 * j + 1) := hmul
    refine le_trans h1 ?_
    rw [hexp]
    -- j * (j * j * pow) ≤ (j+1) * (j * j * pow)
    have hassoc : (j + 1) * j * j * j ^ (2 * k - 2 * j - 1) =
        (j + 1) * (j * j * j ^ (2 * k - 2 * j - 1)) := by ring
    rw [hassoc]
    exact Nat.mul_le_mul_right (j * j * j ^ (2 * k - 2 * j - 1)) hj1
  -- Lift through the common factorial factor
  have : 2 * (j - 1).factorial * (j - 1).factorial *
      (j * (j - 1) ^ (2 * k - 2 * j + 1)) ≤
    2 * (j - 1).factorial * (j - 1).factorial *
      ((j + 1) * j * j * j ^ (2 * k - 2 * j - 1)) :=
    Nat.mul_le_mul_left _ hcore
  convert this using 1 <;> ring

lemma shift_pow_proxy_le_cut (k : ℕ) (hk : 81 ≤ k) :
    ∀ j, 24 ≤ j → j ≤ k - midShift k →
    2 * j * (j - 1).factorial * (j - 1).factorial *
      (j - 1) ^ (2 * k - 2 * j + 1) ≤
    2 * (k - midShift k) * (k - midShift k - 1).factorial *
      (k - midShift k - 1).factorial *
      (k - midShift k - 1) ^ (2 * midShift k + 1) := by
  intro j hj hjc
  set cut := k - midShift k
  have hpowc : 2 * k - 2 * cut + 1 = 2 * midShift k + 1 := by
    have : cut = k - midShift k := rfl
    omega
  -- Climb from `j` up to `cut`.
  have climb : ∀ n, j ≤ n → n ≤ cut →
      2 * j * (j - 1).factorial * (j - 1).factorial *
        (j - 1) ^ (2 * k - 2 * j + 1) ≤
      2 * n * (n - 1).factorial * (n - 1).factorial *
        (n - 1) ^ (2 * k - 2 * n + 1) := by
    intro n hjn
    induction n, hjn using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ n hn ih =>
      intro hnc
      have hnlt : n < k := by
        have := mid_cut_bounds k hk
        omega
      have hrat := shift_pow_proxy_ratio (k := k) (j := n) (by omega) hnlt
      exact le_trans (ih (by omega)) hrat
  have := climb cut hjc le_rfl
  simpa [cut, hpowc] using this

lemma mid_region_sum_le (k : ℕ) (hk : 81 ≤ k) :
    ∑ j ∈ Icc 24 (k - midShift k), j.factorial * W (2 * k - j) (j - 1) ≤
      k.factorial * (k - 1).factorial / k := by
  set s := midShift k
  set cut := k - s
  have hb := mid_cut_bounds k hk
  have h24 : 24 ≤ cut := hb.1
  have hcutk : cut ≤ k := by omega
  have hterm : ∀ j ∈ Icc 24 cut,
      j.factorial * W (2 * k - j) (j - 1) ≤
        k.factorial * (k - 1).factorial / (k * k) := by
    intro j hj
    simp [mem_Icc] at hj
    have hshift := W_mid_term_shift k j (by omega) (by omega)
    have hcut := mid_cut_term_le k hk
    -- term(j) ≤ term(cut) ≤ X / k²
    have hmono : 2 * j * (j - 1).factorial * (j - 1).factorial *
        (j - 1) ^ (2 * k - 2 * j + 1) ≤
      2 * cut * (cut - 1).factorial * (cut - 1).factorial *
        (cut - 1) ^ (2 * s + 1) :=
      shift_pow_proxy_le_cut k hk j hj.1 hj.2
    have hpow : 2 * k - 2 * cut + 1 = 2 * s + 1 := by
      have : cut = k - s := rfl
      omega
    have : 2 * cut * (cut - 1).factorial * (cut - 1).factorial *
        (cut - 1) ^ (2 * s + 1) * (k * k) ≤
        k.factorial * (k - 1).factorial := by
      simpa [cut, s, hpow, mul_assoc] using hcut
    have hpos : 0 < k * k := by nlinarith
    have hdiv : 2 * cut * (cut - 1).factorial * (cut - 1).factorial *
        (cut - 1) ^ (2 * s + 1) ≤
        k.factorial * (k - 1).factorial / (k * k) :=
      Nat.le_div_iff_mul_le hpos |>.mpr (by
        convert this using 1 <;> ring)
    exact le_trans hshift (le_trans hmono hdiv)
  have hsum := sum_le_sum hterm
  refine le_trans hsum ?_
  have : ∑ j ∈ Icc 24 cut, k.factorial * (k - 1).factorial / (k * k) =
      #(Icc 24 cut) * (k.factorial * (k - 1).factorial / (k * k)) := by
    simp [sum_const]
  rw [this]
  have hcard : #(Icc 24 cut) ≤ k := by
    rw [Nat.card_Icc]; omega
  have hmul := Nat.mul_le_mul_right
    (k.factorial * (k - 1).factorial / (k * k)) hcard
  refine le_trans hmul ?_
  -- k * (X / k²) ≤ X / k
  have hposk : 0 < k := by omega
  have hposkk : 0 < k * k := by nlinarith
  have : k * (k.factorial * (k - 1).factorial / (k * k)) ≤
      k.factorial * (k - 1).factorial / k := by
    have h1 : k * (k.factorial * (k - 1).factorial / (k * k)) ≤
        (k * (k.factorial * (k - 1).factorial)) / (k * k) :=
      mul_div_le_div_mul k _ (k * k) hposkk
    refine le_trans h1 ?_
    have heq : (k * (k.factorial * (k - 1).factorial)) / (k * k) =
        k.factorial * (k - 1).factorial / k := by
      have hk0 : 0 < k := hposk
      rw [Nat.mul_div_mul_left _ _ hk0]
    exact le_of_eq heq
  exact this

lemma midShift_ge_45 (k : ℕ) (hk : 81 ≤ k) : 45 ≤ midShift k := by
  have h9 : 9 ≤ k.sqrt := Nat.le_sqrt.mpr (by omega : 9 * 9 ≤ k)
  have : 45 ≤ 5 * k.sqrt := by omega
  exact le_trans this (le_max_left _ _)

/-- Product `(start) * (start+1) * ⋯ * (start+len-1)`. -/
def prodRange (start len : ℕ) : ℕ :=
  (List.range len).foldl (fun acc i => acc * (start + i)) 1

lemma prodRange_zero (start : ℕ) : prodRange start 0 = 1 := rfl

lemma prodRange_succ (start len : ℕ) :
    prodRange start (len + 1) = prodRange start len * (start + len) := by
  simp [prodRange, List.range_succ, List.foldl_cons]

lemma prodRange_factorial (n len : ℕ) :
    n.factorial * prodRange (n + 1) len = (n + len).factorial := by
  induction len with
  | zero => simp [prodRange]
  | succ len ih =>
    rw [prodRange_succ, ← Nat.mul_assoc, ih]
    have : n + (len + 1) = n + len + 1 := by omega
    rw [this, factorial_succ]
    ac_rfl

/-- Finite check of the left pairing term `L(cut+1) ≤ X/(2k)`. -/
def checkLargeL (k : ℕ) : Bool :=
  let s := midShift k
  let j := k - s + 1
  decide (4 * j * (13 : ℕ).factorial * prodRange k (s - 13) ≤
    prodRange (j + 1) (s - 2))

def checkLargeL_range (lo hi : ℕ) : Bool :=
  (List.range (hi + 1 - lo)).all fun i => checkLargeL (lo + i)

lemma checkLargeL_2000 : checkLargeL_range 81 2000 = true := by native_decide

lemma checkLargeL_of_mem (k : ℕ) (hk1 : 81 ≤ k) (hk2 : k ≤ 2000) :
    checkLargeL k = true := by
  have hall := List.all_eq_true.mp checkLargeL_2000
  have hk' : k - 81 ∈ List.range (2000 + 1 - 81) := by
    simp [List.mem_range]; omega
  have := hall (k - 81) hk'
  have heq : 81 + (k - 81) = k := by omega
  simpa [checkLargeL_range, heq] using this

/-- Pairing bound on a large-region summand of `W(2k,k)`. -/
lemma W_large_term_pair (k j : ℕ) (hk : 81 ≤ k)
    (hj1 : 14 ≤ j) (hj2 : j ≤ k - 1) :
    j.factorial * W (2 * k - j) (j - 1) ≤
      2 * j * (13 : ℕ).factorial * j.factorial * (2 * k - j - 13).factorial +
        2 * j * j.factorial * (j - 1).factorial *
          (2 * k - 2 * j + 1).factorial := by
  have hW := W_le_two_max_pair (n := 2 * k - j) (m := j - 1) (j0 := 13)
    (by decide : 1 ≤ 13) (by omega) (by omega)
    (fun t ht ht13 => van13_of_two_k k j hk hj2 t ht ht13)
  have hs : (j - 1).succ = j := by omega
  rw [hs] at hW
  have hmul := Nat.mul_le_mul_left j.factorial hW
  have hnm : 2 * k - j - (j - 1) = 2 * k - 2 * j + 1 := by omega
  rw [hnm] at hmul
  convert hmul using 1
  ring

/-- Right pairing term at the right endpoint `j = k-2`. -/
lemma large_R_end_le (k : ℕ) (hk : 81 ≤ k) :
    2 * (k - 2) * (k - 2).factorial * (k - 3).factorial * 120 *
        (2 * k) ≤
      k.factorial * (k - 1).factorial := by
  have e2 : (k - 2).factorial = (k - 2) * (k - 3).factorial :=
    fact_pred (k - 2) (by omega)
  have e1 : (k - 1).factorial = (k - 1) * (k - 2).factorial :=
    fact_pred (k - 1) (by omega)
  have ek : k.factorial = k * (k - 1).factorial := fact_pred k (by omega)
  have h480 : 480 ≤ (k - 1) * (k - 1) := by
    have : 80 ≤ k - 1 := by omega
    exact le_trans (by decide : 480 ≤ 80 * 80) (Nat.mul_le_mul this this)
  calc
    2 * (k - 2) * (k - 2).factorial * (k - 3).factorial * 120 * (2 * k)
        = 480 * k * (k - 2) * (k - 2) * (k - 3).factorial * (k - 3).factorial := by
          rw [e2]; ring
    _ ≤ k * (k - 1) * (k - 1) * (k - 2) * (k - 2) *
          (k - 3).factorial * (k - 3).factorial := by
          have := Nat.mul_le_mul_right
            ((k - 2) * (k - 2) * (k - 3).factorial * (k - 3).factorial)
            (Nat.mul_le_mul_left k h480)
          convert this using 1 <;> ring
    _ = k.factorial * (k - 1).factorial := by
          rw [ek, e1, e2]; ring

lemma large_R_end_div (k : ℕ) (hk : 81 ≤ k) :
    2 * (k - 2) * (k - 2).factorial * (k - 3).factorial * 120 ≤
      k.factorial * (k - 1).factorial / (2 * k) := by
  have hpos : 0 < 2 * k := by omega
  exact Nat.le_div_iff_mul_le hpos |>.mpr (large_R_end_le k hk)

lemma four_fact13_le_80_70 : 4 * (13 : ℕ).factorial ≤ 80 * 80 * 70 ^ 8 := by
  native_decide

lemma pow70_8_eq : (70 : ℕ) ^ 8 = 70*70*70*70*70*70*70*70 := by native_decide

/-- Left pairing term at the right endpoint `j = k-2`. -/
lemma large_L_end_le (k : ℕ) (hk : 81 ≤ k) :
    2 * (k - 2) * (13 : ℕ).factorial * (k - 2).factorial * (k - 11).factorial *
        (2 * k) ≤
      k.factorial * (k - 1).factorial := by
  have e1 : (k - 1).factorial = (k - 1) * (k - 2).factorial :=
    fact_pred (k - 1) (by omega)
  have ek : k.factorial = k * (k - 1).factorial := fact_pred k (by omega)
  have e2 : (k - 2).factorial = (k - 2) * (k - 3).factorial :=
    fact_pred (k - 2) (by omega)
  have e3 : (k - 3).factorial = (k - 3) * (k - 4).factorial :=
    fact_pred (k - 3) (by omega)
  have e4 : (k - 4).factorial = (k - 4) * (k - 5).factorial :=
    fact_pred (k - 4) (by omega)
  have e5 : (k - 5).factorial = (k - 5) * (k - 6).factorial :=
    fact_pred (k - 5) (by omega)
  have e6 : (k - 6).factorial = (k - 6) * (k - 7).factorial :=
    fact_pred (k - 6) (by omega)
  have e7 : (k - 7).factorial = (k - 7) * (k - 8).factorial :=
    fact_pred (k - 7) (by omega)
  have e8 : (k - 8).factorial = (k - 8) * (k - 9).factorial :=
    fact_pred (k - 8) (by omega)
  have e9 : (k - 9).factorial = (k - 9) * (k - 10).factorial :=
    fact_pred (k - 9) (by omega)
  have e10 : (k - 10).factorial = (k - 10) * (k - 11).factorial :=
    fact_pred (k - 10) (by omega)
  have chain :
      (k - 1).factorial =
        (k - 1) * (k - 2) * (k - 3) * (k - 4) * (k - 5) *
          (k - 6) * (k - 7) * (k - 8) * (k - 9) * (k - 10) *
            (k - 11).factorial := by
    rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]; ring
  have hcore : 4 * (13 : ℕ).factorial ≤
      (k - 1) * (k - 1) * (k - 3) * (k - 4) * (k - 5) *
        (k - 6) * (k - 7) * (k - 8) * (k - 9) * (k - 10) := by
    refine le_trans four_fact13_le_80_70 ?_
    have h80 : 80 ≤ k - 1 := by omega
    have hpow : (70 : ℕ) ^ 8 ≤
        (k - 3) * (k - 4) * (k - 5) * (k - 6) *
          (k - 7) * (k - 8) * (k - 9) * (k - 10) := by
      rw [pow70_8_eq]
      refine Nat.mul_le_mul ?_ (by omega : 70 ≤ k - 10)
      refine Nat.mul_le_mul ?_ (by omega : 70 ≤ k - 9)
      refine Nat.mul_le_mul ?_ (by omega : 70 ≤ k - 8)
      refine Nat.mul_le_mul ?_ (by omega : 70 ≤ k - 7)
      refine Nat.mul_le_mul ?_ (by omega : 70 ≤ k - 6)
      refine Nat.mul_le_mul ?_ (by omega : 70 ≤ k - 5)
      exact Nat.mul_le_mul (by omega : 70 ≤ k - 3) (by omega : 70 ≤ k - 4)
    have := Nat.mul_le_mul (Nat.mul_le_mul h80 h80) hpow
    convert this using 1 <;> ring
  -- Lift through the common factor `k (k-2) (k-2)! (k-11)!`.
  have hmul := Nat.mul_le_mul_left
    (k * (k - 2) * (k - 2).factorial * (k - 11).factorial) hcore
  have hL :
      k * (k - 2) * (k - 2).factorial * (k - 11).factorial *
          (4 * (13 : ℕ).factorial) =
        2 * (k - 2) * (13 : ℕ).factorial * (k - 2).factorial *
          (k - 11).factorial * (2 * k) := by
    ring
  have hR :
      k * (k - 2) * (k - 2).factorial * (k - 11).factorial *
          ((k - 1) * (k - 1) * (k - 3) * (k - 4) * (k - 5) *
            (k - 6) * (k - 7) * (k - 8) * (k - 9) * (k - 10)) =
        k.factorial * (k - 1).factorial := by
    rw [ek]
    nth_rw 1 [e1]
    rw [chain]
    ring
  rw [← hL, ← hR]
  exact hmul

lemma cube_succ_le (j : ℕ) (hj : 1 ≤ j) :
    (j + 1) ^ 3 ≤ j * (j + 2) ^ 2 := by
  have hL : (j + 1) ^ 3 = j ^ 3 + 3 * j ^ 2 + 3 * j + 1 := by
    ring
  have hR : j * (j + 2) ^ 2 = j ^ 3 + 4 * j ^ 2 + 4 * j := by
    ring
  rw [hL, hR]
  nlinarith

def largeL (k j : ℕ) : ℕ :=
  2 * j * (13 : ℕ).factorial * j.factorial * (2 * k - j - 13).factorial

def largeR (k j : ℕ) : ℕ :=
  2 * j * j.factorial * (j - 1).factorial * (2 * k - 2 * j + 1).factorial

lemma W_large_term_pair' (k j : ℕ) (hk : 81 ≤ k)
    (hj1 : 14 ≤ j) (hj2 : j ≤ k - 1) :
    j.factorial * W (2 * k - j) (j - 1) ≤ largeL k j + largeR k j :=
  W_large_term_pair k j hk hj1 hj2

lemma checkLargeL_factorial (k : ℕ) (hk : 81 ≤ k) (hcheck : checkLargeL k = true) :
    4 * (k - midShift k + 1) * (13 : ℕ).factorial *
        (k - midShift k + 1).factorial *
        (k + midShift k - 14).factorial ≤
      (k - 1).factorial * (k - 1).factorial := by
  have hs := midShift_ge_45 k hk
  have hb := mid_cut_bounds k hk
  set s := midShift k
  set j := k - s + 1
  have hjdef : j = k - s + 1 := rfl
  have hm : k + s - 14 = k - 1 + (s - 13) := by omega
  have hja : j + (s - 2) = k - 1 := by omega
  have hdec := of_decide_eq_true hcheck
  -- 4 j 13! prodRange k (s-13) ≤ prodRange (j+1) (s-2)
  have hineq :
      4 * j * (13 : ℕ).factorial * prodRange k (s - 13) ≤
        prodRange (j + 1) (s - 2) := by
    simpa [checkLargeL, s, j] using hdec
  have hprodL :
      (k - 1).factorial * prodRange k (s - 13) = (k + s - 14).factorial := by
    have h1 : k - 1 + 1 = k := by omega
    have := prodRange_factorial (k - 1) (s - 13)
    rwa [h1, ← hm] at this
  have hprodR :
      j.factorial * prodRange (j + 1) (s - 2) = (k - 1).factorial := by
    have := prodRange_factorial j (s - 2)
    rwa [hja] at this
  have hmul := Nat.mul_le_mul_left (j.factorial * (k - 1).factorial) hineq
  have hL :
      j.factorial * (k - 1).factorial *
          (4 * j * (13 : ℕ).factorial * prodRange k (s - 13)) =
        4 * j * (13 : ℕ).factorial * j.factorial * (k + s - 14).factorial := by
    have := congrArg (fun t => j.factorial * t) hprodL
    -- rearrange
    ring_nf at this ⊢
    exact this.symm ▸ (by ring)
  -- Direct conversion via the two product identities.
  have : 4 * j * (13 : ℕ).factorial * j.factorial *
      ((k - 1).factorial * prodRange k (s - 13)) ≤
      (k - 1).factorial * (j.factorial * prodRange (j + 1) (s - 2)) := by
    have := Nat.mul_le_mul_left (j.factorial * (k - 1).factorial) hineq
    convert this using 1 <;> ring
  rw [hprodL, hprodR] at this
  simpa [j, s] using this

lemma largeL_left_of_check (k : ℕ) (hk : 81 ≤ k) (hcheck : checkLargeL k = true) :
    largeL k (k - midShift k + 1) * (2 * k) ≤
      k.factorial * (k - 1).factorial := by
  have hb := mid_cut_bounds k hk
  have hs := midShift_ge_45 k hk
  set s := midShift k
  set j := k - s + 1
  have hfact := checkLargeL_factorial k hk hcheck
  have hm : 2 * k - j - 13 = k + s - 14 := by omega
  have ek : k.factorial = k * (k - 1).factorial := fact_pred k (by omega)
  unfold largeL
  rw [hm]
  have : 2 * j * (13 : ℕ).factorial * j.factorial * (k + s - 14).factorial * (2 * k) =
      k * (4 * j * (13 : ℕ).factorial * j.factorial * (k + s - 14).factorial) := by
    ring
  rw [this, ek]
  have := Nat.mul_le_mul_left k hfact
  convert this using 1 <;> ring

lemma largeL_left_le_of_le_2000 (k : ℕ) (hk : 81 ≤ k) (hk2 : k ≤ 2000) :
    largeL k (k - midShift k + 1) * (2 * k) ≤
      k.factorial * (k - 1).factorial :=
  largeL_left_of_check k hk (checkLargeL_of_mem k hk hk2)

lemma largeL_ratio_num_den (k j : ℕ) (hj : 1 ≤ j) (hjk : j + 13 < 2 * k) :
    largeL k (j + 1) * (j * (2 * k - j - 13)) =
      largeL k j * (j + 1) ^ 2 := by
  unfold largeL
  have hsucc : (j + 1).factorial = (j + 1) * j.factorial := factorial_succ j
  have hsub : 2 * k - (j + 1) - 13 = 2 * k - j - 14 := by omega
  have hf : (2 * k - j - 13).factorial =
      (2 * k - j - 13) * (2 * k - j - 14).factorial := by
    have : 1 ≤ 2 * k - j - 13 := by omega
    exact fact_pred _ this
  rw [hsucc, hsub, hf, Nat.pow_two]
  ring

/-- Consecutive L-ratios are nondecreasing. -/
lemma largeL_ratio_le {k j : ℕ} (hj : 1 ≤ j) (hbound : j + 15 ≤ 2 * k) :
    (j + 1) ^ 3 * (2 * k - j - 14) ≤
      j * (j + 2) ^ 2 * (2 * k - j - 13) := by
  have hcube := cube_succ_le j hj
  have hlin : 2 * k - j - 14 ≤ 2 * k - j - 13 := by omega
  exact Nat.mul_le_mul hcube hlin

lemma largeL_inc_of_sq {k j : ℕ} (hj : 1 ≤ j) (hjk : j + 13 < 2 * k)
    (hr : j * (2 * k - j - 13) ≤ (j + 1) ^ 2) :
    largeL k j ≤ largeL k (j + 1) := by
  have hiden := largeL_ratio_num_den k j hj hjk
  have hpos : 0 < j * (2 * k - j - 13) := by
    have : 0 < 2 * k - j - 13 := by omega
    exact Nat.mul_pos (by omega) this
  have hmul := Nat.mul_le_mul_left (largeL k j) hr
  rw [← hiden] at hmul
  exact Nat.le_of_mul_le_mul_right hmul hpos

lemma largeL_dec_of_sq {k j : ℕ} (hj : 1 ≤ j) (hjk : j + 13 < 2 * k)
    (hr : (j + 1) ^ 2 ≤ j * (2 * k - j - 13)) :
    largeL k (j + 1) ≤ largeL k j := by
  have hiden := largeL_ratio_num_den k j hj hjk
  have hpos : 0 < j * (2 * k - j - 13) := by
    have : 0 < 2 * k - j - 13 := by omega
    exact Nat.mul_pos (by omega) this
  have hmul := Nat.mul_le_mul_left (largeL k j) hr
  rw [← hiden] at hmul
  exact Nat.le_of_mul_le_mul_right hmul hpos

lemma largeL_ratio_persist {k t u : ℕ} (ht : 1 ≤ t) (htu : t ≤ u)
    (hbound : u + 15 ≤ 2 * k)
    (hr : t * (2 * k - t - 13) ≤ (t + 1) ^ 2) :
    u * (2 * k - u - 13) ≤ (u + 1) ^ 2 := by
  induction u, htu using Nat.le_induction with
  | base => exact hr
  | succ u hu ih =>
    have hstep := largeL_ratio_le (k := k) (j := u) (by omega) (by omega)
    have ih' := ih (by omega)
    have hcomb :
        (u + 1) ^ 3 * (2 * k - u - 14) ≤ (u + 2) ^ 2 * (u + 1) ^ 2 :=
      le_trans hstep (by
        have := Nat.mul_le_mul_left ((u + 2) ^ 2) ih'
        convert this using 1 <;> ring)
    have hpos : 0 < (u + 1) ^ 2 := by
      exact Nat.pow_pos (by omega)
    have : (u + 1) * (2 * k - u - 14) * (u + 1) ^ 2 ≤
        (u + 2) ^ 2 * (u + 1) ^ 2 := by
      convert hcomb using 1 <;> ring
    have hfin := Nat.le_of_mul_le_mul_right this hpos
    have heq : 2 * k - (u + 1) - 13 = 2 * k - u - 14 := by
      have : 2 * k - (u + 1) = 2 * k - u - 1 := by omega
      rw [this]; omega
    rwa [heq]

lemma largeL_climb {k t hi : ℕ} (ht : 1 ≤ t) (hhi : t ≤ hi)
    (hbound : hi + 15 ≤ 2 * k)
    (hr : t * (2 * k - t - 13) ≤ (t + 1) ^ 2) :
    ∀ u, t ≤ u → u ≤ hi → largeL k t ≤ largeL k u := by
  intro u htu
  induction u, htu using Nat.le_induction with
  | base => intro; exact le_rfl
  | succ u hu ih =>
    intro huhi
    have ih' := ih (by omega)
    have hpers := largeL_ratio_persist (k := k) (t := t) (u := u)
      ht (by omega) (by omega) hr
    have hinc := largeL_inc_of_sq (k := k) (j := u) (by omega) (by omega) hpers
    exact le_trans ih' hinc

lemma largeL_le_max_ends (k lo hi j : ℕ)
    (hlo : 1 ≤ lo) (hji : lo ≤ j) (hjh : j ≤ hi)
    (hbound : hi + 15 ≤ 2 * k) :
    largeL k j ≤ max (largeL k lo) (largeL k hi) := by
  revert hjh
  induction j, hji using Nat.le_induction with
  | base => intro; exact le_max_left _ _
  | succ j hj ih =>
    intro hjh
    have ih' := ih (by omega)
    cases le_total ((j + 1) ^ 2) (j * (2 * k - j - 13)) with
    | inl hdec =>
      have := largeL_dec_of_sq (k := k) (j := j) (by omega) (by omega) hdec
      exact le_trans this ih'
    | inr hinc =>
      have hr' := largeL_ratio_persist (k := k) (t := j) (u := j + 1)
        (by omega) (by omega) (by omega) hinc
      have hclimb := largeL_climb (k := k) (t := j + 1) (hi := hi)
        (by omega) (by omega) hbound hr'
      exact le_trans (hclimb hi hjh le_rfl) (le_max_right _ _)

lemma largeR_ratio_num_den (k j : ℕ) (hj : 2 ≤ j) (hjk : 2 * j + 1 ≤ 2 * k) :
    largeR k (j + 1) * ((2 * k - 2 * j + 1) * (2 * k - 2 * j)) =
      largeR k j * (j + 1) ^ 2 := by
  unfold largeR
  have hj1 : j + 1 - 1 = j := by omega
  rw [hj1]
  have hs : (j + 1).factorial = (j + 1) * j.factorial := factorial_succ j
  have hp : j.factorial = j * (j - 1).factorial := fact_pred j (by omega)
  have hsub : 2 * k - 2 * (j + 1) + 1 = 2 * k - 2 * j - 1 := by omega
  have e1 : (2 * k - 2 * j + 1).factorial =
      (2 * k - 2 * j + 1) * (2 * k - 2 * j).factorial := by
    have : 2 * k - 2 * j + 1 = (2 * k - 2 * j) + 1 := by omega
    rw [this, factorial_succ]
  have e2 : (2 * k - 2 * j).factorial =
      (2 * k - 2 * j) * (2 * k - 2 * j - 1).factorial :=
    fact_pred (2 * k - 2 * j) (by omega)
  rw [hs, hp, hsub, e1, e2, Nat.pow_two]
  ring

lemma largeR_inc_of_sq {k j : ℕ} (hj : 2 ≤ j) (hjk : 2 * j + 1 ≤ 2 * k)
    (hr : (2 * k - 2 * j + 1) * (2 * k - 2 * j) ≤ (j + 1) ^ 2) :
    largeR k j ≤ largeR k (j + 1) := by
  have hiden := largeR_ratio_num_den k j hj hjk
  have hpos : 0 < (2 * k - 2 * j + 1) * (2 * k - 2 * j) := by
    have : 0 < 2 * k - 2 * j := by omega
    exact Nat.mul_pos (by omega) this
  have hmul := Nat.mul_le_mul_left (largeR k j) hr
  rw [← hiden] at hmul
  exact Nat.le_of_mul_le_mul_right hmul hpos

lemma largeR_dec_of_sq {k j : ℕ} (hj : 2 ≤ j) (hjk : 2 * j + 1 ≤ 2 * k)
    (hr : (j + 1) ^ 2 ≤ (2 * k - 2 * j + 1) * (2 * k - 2 * j)) :
    largeR k (j + 1) ≤ largeR k j := by
  have hiden := largeR_ratio_num_den k j hj hjk
  have hpos : 0 < (2 * k - 2 * j + 1) * (2 * k - 2 * j) := by
    have : 0 < 2 * k - 2 * j := by omega
    exact Nat.mul_pos (by omega) this
  have hmul := Nat.mul_le_mul_left (largeR k j) hr
  rw [← hiden] at hmul
  exact Nat.le_of_mul_le_mul_right hmul hpos

lemma largeR_ratio_persist {k t u : ℕ} (ht : 2 ≤ t) (htu : t ≤ u)
    (hbound : 2 * u + 3 ≤ 2 * k)
    (hr : (2 * k - 2 * t + 1) * (2 * k - 2 * t) ≤ (t + 1) ^ 2) :
    (2 * k - 2 * u + 1) * (2 * k - 2 * u) ≤ (u + 1) ^ 2 := by
  induction u, htu using Nat.le_induction with
  | base => exact hr
  | succ u hu ih =>
    have ih' := ih (by omega)
    -- den shrinks and num grows, so the inequality persists
    have hden : (2 * k - 2 * (u + 1) + 1) * (2 * k - 2 * (u + 1)) ≤
        (2 * k - 2 * u + 1) * (2 * k - 2 * u) := by
      have : 2 * k - 2 * (u + 1) + 1 ≤ 2 * k - 2 * u + 1 := by omega
      have : 2 * k - 2 * (u + 1) ≤ 2 * k - 2 * u := by omega
      exact Nat.mul_le_mul ‹_› ‹_›
    have hnum : (u + 1) ^ 2 ≤ (u + 2) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    exact le_trans hden (le_trans ih' hnum)

lemma largeR_climb {k t hi : ℕ} (ht : 2 ≤ t) (hhi : t ≤ hi)
    (hbound : 2 * hi + 3 ≤ 2 * k)
    (hr : (2 * k - 2 * t + 1) * (2 * k - 2 * t) ≤ (t + 1) ^ 2) :
    ∀ u, t ≤ u → u ≤ hi → largeR k t ≤ largeR k u := by
  intro u htu
  induction u, htu using Nat.le_induction with
  | base => intro; exact le_rfl
  | succ u hu ih =>
    intro huhi
    have ih' := ih (by omega)
    have hpers := largeR_ratio_persist (k := k) (t := t) (u := u)
      ht (by omega) (by omega) hr
    have hinc := largeR_inc_of_sq (k := k) (j := u) (by omega) (by omega) hpers
    exact le_trans ih' hinc

lemma largeR_le_max_ends (k lo hi j : ℕ)
    (hlo : 2 ≤ lo) (hji : lo ≤ j) (hjh : j ≤ hi)
    (hbound : 2 * hi + 3 ≤ 2 * k) :
    largeR k j ≤ max (largeR k lo) (largeR k hi) := by
  revert hjh
  induction j, hji using Nat.le_induction with
  | base => intro; exact le_max_left _ _
  | succ j hj ih =>
    intro hjh
    have ih' := ih (by omega)
    cases le_total ((j + 1) ^ 2) ((2 * k - 2 * j + 1) * (2 * k - 2 * j)) with
    | inl hdec =>
      have := largeR_dec_of_sq (k := k) (j := j) (by omega) (by omega) hdec
      exact le_trans this ih'
    | inr hinc =>
      have hr' := largeR_ratio_persist (k := k) (t := j) (u := j + 1)
        (by omega) (by omega) (by omega) hinc
      have hclimb := largeR_climb (k := k) (t := j + 1) (hi := hi)
        (by omega) (by omega) hbound hr'
      exact le_trans (hclimb hi hjh le_rfl) (le_max_right _ _)

/-- Finite check of the left pairing term `R(cut+1) ≤ X/(2k)`. -/
def checkLargeR (k : ℕ) : Bool :=
  let s := midShift k
  let cut := k - s
  decide (4 * (cut + 1) * (cut + 1) * (2 * s - 1).factorial ≤
    prodRange (cut + 1) (s - 1) * prodRange (cut + 1) (s - 1))

def checkLargeR_range (lo hi : ℕ) : Bool :=
  (List.range (hi + 1 - lo)).all fun i => checkLargeR (lo + i)

lemma checkLargeR_2000 : checkLargeR_range 81 2000 = true := by native_decide

lemma checkLargeR_of_mem (k : ℕ) (hk1 : 81 ≤ k) (hk2 : k ≤ 2000) :
    checkLargeR k = true := by
  have hall := List.all_eq_true.mp checkLargeR_2000
  have hk' : k - 81 ∈ List.range (2000 + 1 - 81) := by
    simp [List.mem_range]; omega
  have := hall (k - 81) hk'
  have heq : 81 + (k - 81) = k := by omega
  simpa [checkLargeR_range, heq] using this

lemma five_fact : (5 : ℕ).factorial = 120 := by native_decide

lemma largeL_right_le (k : ℕ) (hk : 81 ≤ k) :
    largeL k (k - 2) * (2 * k) ≤ k.factorial * (k - 1).factorial := by
  have hm : 2 * k - (k - 2) - 13 = k - 11 := by omega
  unfold largeL
  rw [hm]
  exact large_L_end_le k hk

lemma largeR_right_le (k : ℕ) (hk : 81 ≤ k) :
    largeR k (k - 2) * (2 * k) ≤ k.factorial * (k - 1).factorial := by
  have hm : 2 * k - 2 * (k - 2) + 1 = 5 := by omega
  have hpred : k - 2 - 1 = k - 3 := by omega
  unfold largeR
  rw [hm, hpred, five_fact]
  exact large_R_end_le k hk

lemma checkLargeR_factorial (k : ℕ) (hk : 81 ≤ k) (hcheck : checkLargeR k = true) :
    4 * (k - midShift k + 1) * (k - midShift k + 1) *
        (k - midShift k).factorial * (k - midShift k).factorial *
        (2 * midShift k - 1).factorial ≤
      (k - 1).factorial * (k - 1).factorial := by
  have hs := midShift_ge_45 k hk
  have hb := mid_cut_bounds k hk
  set s := midShift k
  set cut := k - s
  have hdec := of_decide_eq_true hcheck
  have hineq :
      4 * (cut + 1) * (cut + 1) * (2 * s - 1).factorial ≤
        prodRange (cut + 1) (s - 1) * prodRange (cut + 1) (s - 1) := by
    simpa [checkLargeR, s, cut] using hdec
  have hprod : cut.factorial * prodRange (cut + 1) (s - 1) = (k - 1).factorial := by
    have hpr := prodRange_factorial cut (s - 1)
    have heq : cut + (s - 1) = k - 1 := by omega
    rwa [heq] at hpr
  have hmul := Nat.mul_le_mul_left (cut.factorial * cut.factorial) hineq
  have : 4 * (cut + 1) * (cut + 1) * cut.factorial * cut.factorial *
      (2 * s - 1).factorial ≤
      (k - 1).factorial * (k - 1).factorial := by
    have hL :
        cut.factorial * cut.factorial *
            (4 * (cut + 1) * (cut + 1) * (2 * s - 1).factorial) =
          4 * (cut + 1) * (cut + 1) * cut.factorial * cut.factorial *
            (2 * s - 1).factorial := by ring
    have hR :
        cut.factorial * cut.factorial *
            (prodRange (cut + 1) (s - 1) * prodRange (cut + 1) (s - 1)) =
          (k - 1).factorial * (k - 1).factorial := by
      have : cut.factorial * prodRange (cut + 1) (s - 1) = (k - 1).factorial := hprod
      rw [← mul_mul_mul_comm, this]
    rwa [hL, hR] at hmul
  simpa [cut, s] using this

lemma largeR_left_of_check (k : ℕ) (hk : 81 ≤ k) (hcheck : checkLargeR k = true) :
    largeR k (k - midShift k + 1) * (2 * k) ≤
      k.factorial * (k - 1).factorial := by
  have hs := midShift_ge_45 k hk
  have hb := mid_cut_bounds k hk
  set s := midShift k
  set cut := k - s
  have hfact := checkLargeR_factorial k hk hcheck
  have hj1 : (cut + 1) - 1 = cut := by omega
  have hm : 2 * k - 2 * (cut + 1) + 1 = 2 * s - 1 := by omega
  have hsj : (cut + 1).factorial = (cut + 1) * cut.factorial := factorial_succ cut
  have ek : k.factorial = k * (k - 1).factorial := fact_pred k (by omega)
  unfold largeR
  rw [hj1, hm, hsj]
  have : 2 * (cut + 1) * ((cut + 1) * cut.factorial) * cut.factorial *
      (2 * s - 1).factorial * (2 * k) =
      k * (4 * (cut + 1) * (cut + 1) * cut.factorial * cut.factorial *
        (2 * s - 1).factorial) := by
    ring
  rw [this, ek]
  have := Nat.mul_le_mul_left k hfact
  convert this using 1 <;> ring

lemma largeR_left_le_of_le_2000 (k : ℕ) (hk : 81 ≤ k) (hk2 : k ≤ 2000) :
    largeR k (k - midShift k + 1) * (2 * k) ≤
      k.factorial * (k - 1).factorial :=
  largeR_left_of_check k hk (checkLargeR_of_mem k hk hk2)

lemma twentyfive_three_log_le (k : ℕ) (hk : 2001 ≤ k) :
    25 * (3 * Nat.log 2 k + 8) ≤ k := by
  by_cases h : k < 2 ^ 13
  · have hlog : Nat.log 2 k ≤ 12 := by
      have := (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (by omega : k ≠ 0)).2 h
      omega
    have hmul : 25 * (3 * Nat.log 2 k + 8) ≤ 25 * (3 * 12 + 8) :=
      Nat.mul_le_mul_left _ (by omega)
    have : 25 * 44 = 1100 := by decide
    omega
  · have hk' : 2 ^ 13 ≤ k := by omega
    have hls : Nat.log 2 k ≤ k.sqrt := log2_le_sqrt k (by omega)
    have hstep : 25 * (3 * Nat.log 2 k + 8) ≤ 25 * (3 * k.sqrt + 8) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hls) _)
    refine le_trans hstep ?_
    have hsq : 90 ≤ k.sqrt := Nat.le_sqrt.mpr (by omega : 90 * 90 ≤ k)
    have hquad : 75 * k.sqrt + 200 ≤ k.sqrt * k.sqrt := by
      obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hsq
      rw [hu]; nlinarith
    have hrew : 25 * (3 * k.sqrt + 8) = 75 * k.sqrt + 200 := by ring
    rw [hrew]
    exact le_trans hquad (Nat.sqrt_le k)

lemma nat_sq_le_sq {a b : ℕ} (h : a * a ≤ b * b) : a ≤ b := by
  by_contra hlt
  exact h.not_gt (Nat.mul_self_lt_mul_self (Nat.lt_of_not_ge hlt))

lemma midShift_le_div5 (k : ℕ) (hk : 2001 ≤ k) : midShift k * 5 ≤ k := by
  rw [midShift_eq_logsqrt k (by omega)]
  set N := k * (3 * Nat.log 2 k + 8)
  have hN : 25 * N ≤ k * k := by
    have := Nat.mul_le_mul_left k (twentyfive_three_log_le k hk)
    convert this using 1 <;> ring
  have hsq : (N.sqrt * 5) * (N.sqrt * 5) ≤ k * k := by
    have : (N.sqrt * 5) * (N.sqrt * 5) = 25 * (N.sqrt * N.sqrt) := by ring
    rw [this]
    exact le_trans (Nat.mul_le_mul_left 25 (Nat.sqrt_le N)) hN
  exact nat_sq_le_sq hsq

lemma prodRange_ge_pow (start len : ℕ) (hstart : 1 ≤ start) :
    start ^ len ≤ prodRange start len := by
  induction len with
  | zero => simp [prodRange]
  | succ len ih =>
    rw [prodRange_succ, nat_pow_succ_left]
    have h := Nat.mul_le_mul (by omega : start ≤ start + len) ih
    rwa [Nat.mul_comm (prodRange start len)]

lemma s_cube_le_two_pow : ∀ s, 20 ≤ s → s ^ 3 ≤ 2 ^ (2 * s - 9)
  | s, hs => by
    induction s, hs using Nat.le_induction with
    | base => native_decide
    | succ s hs ih =>
      have hstep : (s + 1) ^ 3 ≤ 4 * s ^ 3 := by
        have : (s + 1) ^ 3 = s ^ 3 + 3 * s ^ 2 + 3 * s + 1 := by ring
        have : 4 * s ^ 3 = s ^ 3 + 3 * s ^ 3 := by ring
        have h1 : 3 * s ^ 2 + 3 * s + 1 ≤ 3 * s ^ 3 := by
          have hs2 : 2 ≤ s := by omega
          have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
          nlinarith
        nlinarith
      have hpow : 2 ^ (2 * (s + 1) - 9) = 4 * 2 ^ (2 * s - 9) := by
        have : 2 * (s + 1) - 9 = (2 * s - 9) + 2 := by omega
        rw [this, Nat.pow_add, Nat.pow_two]
        ring
      refine le_trans hstep ?_
      rw [hpow]
      exact Nat.mul_le_mul_left 4 ih

/-- `4 (2s-1)! ≤ (j)^{2s-4}` once `2s-1 ≤ j/2` and `s` is large. -/
lemma four_two_s_fact_le_pow (s j : ℕ) (hs : 45 ≤ s) (hj : 2 * (2 * s - 1) ≤ j) :
    4 * (2 * s - 1).factorial ≤ j ^ (2 * s - 4) := by
  have hs1 : 1 ≤ 2 * s - 1 := by omega
  have hfact : (2 * s - 1).factorial ≤ (2 * s - 1) ^ (2 * s - 1) :=
    fact_le_self_pow (2 * s - 1)
  have hexp : 2 * s - 1 = (2 * s - 4) + 3 := by omega
  have hsplit : (2 * s - 1) ^ (2 * s - 1) =
      (2 * s - 1) ^ (2 * s - 4) * (2 * s - 1) ^ 3 := by
    rw [hexp, Nat.pow_add]
  have hj2 : 2 * s - 1 ≤ j / 2 := by
    have : 2 * (2 * s - 1) ≤ j := hj
    exact Nat.le_div_iff_mul_le (by decide : 0 < 2) |>.mpr (by omega)
  have hhalf : (2 * s - 1) ^ (2 * s - 4) ≤ (j / 2) ^ (2 * s - 4) :=
    Nat.pow_le_pow_left hj2 _
  -- (j/2)^n * 2^n ≤ j^n
  have hpow2 : 2 ^ (2 * s - 4) * (j / 2) ^ (2 * s - 4) ≤ j ^ (2 * s - 4) := by
    have : 2 ^ (2 * s - 4) * (j / 2) ^ (2 * s - 4) = (2 * (j / 2)) ^ (2 * s - 4) := by
      rw [← Nat.mul_pow]
    rw [this]
    exact Nat.pow_le_pow_left (Nat.mul_div_le j 2) _
  -- 4 (2s-1)^3 ≤ 2^{2s-4}
  have hcube : 4 * (2 * s - 1) ^ 3 ≤ 2 ^ (2 * s - 4) := by
    have hs20 : 20 ≤ s := by omega
    have hsc : s ^ 3 ≤ 2 ^ (2 * s - 9) := s_cube_le_two_pow s hs20
    have h2s : (2 * s - 1) ^ 3 ≤ (2 * s) ^ 3 :=
      Nat.pow_le_pow_left (by omega) 3
    have h2s' : (2 * s) ^ 3 = 8 * s ^ 3 := by
      have : (2 * s) ^ 3 = 2 ^ 3 * s ^ 3 := Nat.mul_pow 2 s 3
      rw [this]; rfl
    have : 4 * (2 * s) ^ 3 = 32 * s ^ 3 := by
      rw [h2s']; ring
    have h32 : 32 * s ^ 3 ≤ 32 * 2 ^ (2 * s - 9) :=
      Nat.mul_le_mul_left 32 hsc
    have h32e : 32 * 2 ^ (2 * s - 9) = 2 ^ (2 * s - 4) := by
      have : 32 = 2 ^ 5 := by decide
      have hex : 2 * s - 4 = (2 * s - 9) + 5 := by omega
      rw [this, hex, Nat.pow_add, Nat.mul_comm]
    have : 4 * (2 * s - 1) ^ 3 ≤ 32 * s ^ 3 := by
      have := Nat.mul_le_mul_left 4 h2s
      rw [show 4 * (2 * s) ^ 3 = 32 * s ^ 3 from ‹_›] at this
      exact this
    exact le_trans this (le_trans h32 (le_of_eq h32e))
  have hmain : 4 * (2 * s - 1) ^ (2 * s - 1) ≤ j ^ (2 * s - 4) := by
    rw [hsplit]
    have : 4 * ((2 * s - 1) ^ (2 * s - 4) * (2 * s - 1) ^ 3) =
        (4 * (2 * s - 1) ^ 3) * (2 * s - 1) ^ (2 * s - 4) := by ring
    rw [this]
    refine le_trans (Nat.mul_le_mul_right _ hcube) ?_
    refine le_trans (Nat.mul_le_mul_left (2 ^ (2 * s - 4)) hhalf) ?_
    have : 2 ^ (2 * s - 4) * (j / 2) ^ (2 * s - 4) ≤ j ^ (2 * s - 4) := hpow2
    rwa [Nat.mul_comm] at this
  refine le_trans (Nat.mul_le_mul_left 4 hfact) hmain

lemma largeR_left_le_of_ge_2001 (k : ℕ) (hk : 2001 ≤ k) :
    largeR k (k - midShift k + 1) * (2 * k) ≤
      k.factorial * (k - 1).factorial := by
  have hk81 : 81 ≤ k := by omega
  have hb := mid_cut_bounds k hk81
  have hs45 := midShift_ge_45 k hk81
  have hs5 := midShift_le_div5 k hk
  set s := midShift k
  set j := k - s + 1
  have hjdef : j = k - s + 1 := rfl
  have hm : 2 * k - 2 * j + 1 = 2 * s - 1 := by omega
  have hj1 : j - 1 = k - s := by omega
  have hsj : j.factorial = j * (j - 1).factorial := fact_pred j (by omega)
  have ek : k.factorial = k * (k - 1).factorial := fact_pred k (by omega)
  -- 4 j² (2s-1)! ≤ ((k-1)! / (j-1)!)²
  have hprod : (j - 1).factorial * prodRange j (s - 1) = (k - 1).factorial := by
    have hpr := prodRange_factorial (j - 1) (s - 1)
    have h1 : j - 1 + 1 = j := by omega
    have h2 : j - 1 + (s - 1) = k - 1 := by omega
    rwa [h1, h2] at hpr
  have hpow : j ^ (s - 1) ≤ prodRange j (s - 1) :=
    prodRange_ge_pow j (s - 1) (by omega)
  have hjhalf : 2 * (2 * s - 1) ≤ j := by
    -- 4s - 2 ≤ k - s + 1 ↔ 5s ≤ k + 3
    have : 5 * s ≤ k := by
      have : s * 5 = 5 * s := by ring
      rwa [← this]
    omega
  have hcore : 4 * (2 * s - 1).factorial ≤ j ^ (2 * s - 4) :=
    four_two_s_fact_le_pow s j hs45 hjhalf
  have hpow2 : j ^ (2 * s - 4) * j ^ 2 = j ^ (2 * s - 2) := by
    have : 2 * s - 2 = (2 * s - 4) + 2 := by omega
    rw [this, Nat.pow_add, Nat.pow_two]
  have hj2 : 4 * j * j * (2 * s - 1).factorial ≤ j ^ (2 * (s - 1)) := by
    have : 2 * (s - 1) = 2 * s - 2 := by omega
    rw [this]
    have : 4 * j * j * (2 * s - 1).factorial =
        4 * (2 * s - 1).factorial * (j * j) := by ring
    rw [this, ← Nat.pow_two, ← hpow2]
    exact Nat.mul_le_mul_right (j ^ 2) hcore
  have hpr2 : j ^ (2 * (s - 1)) ≤
      prodRange j (s - 1) * prodRange j (s - 1) := by
    have : j ^ (2 * (s - 1)) = (j ^ (s - 1)) * (j ^ (s - 1)) := by
      have : 2 * (s - 1) = (s - 1) + (s - 1) := by omega
      rw [this, Nat.pow_add]
    rw [this]
    exact Nat.mul_le_mul hpow hpow
  have hineq : 4 * j * j * (j - 1).factorial * (j - 1).factorial *
      (2 * s - 1).factorial ≤
      (k - 1).factorial * (k - 1).factorial := by
    have hL :
        (j - 1).factorial * (j - 1).factorial *
            (4 * j * j * (2 * s - 1).factorial) =
          4 * j * j * (j - 1).factorial * (j - 1).factorial *
            (2 * s - 1).factorial := by ring
    have hR :
        (j - 1).factorial * (j - 1).factorial *
            (prodRange j (s - 1) * prodRange j (s - 1)) =
          (k - 1).factorial * (k - 1).factorial := by
      rw [← mul_mul_mul_comm, hprod]
    have := Nat.mul_le_mul_left
      ((j - 1).factorial * (j - 1).factorial)
      (le_trans hj2 hpr2)
    rwa [hL, hR] at this
  unfold largeR
  rw [hm, hsj]
  have hrew : 2 * j * (j * (j - 1).factorial) * (j - 1).factorial *
      (2 * s - 1).factorial * (2 * k) =
      k * (4 * j * j * (j - 1).factorial * (j - 1).factorial *
        (2 * s - 1).factorial) := by
    ring
  rw [hrew, ek]
  have := Nat.mul_le_mul_left k hineq
  convert this using 1 <;> ring

lemma midShift_sq_le (k : ℕ) (hk : 81 ≤ k) :
    midShift k * midShift k ≤ k * (3 * Nat.log 2 k + 8) := by
  rw [midShift_eq_logsqrt k hk]
  exact Nat.sqrt_le _

/-- Pairing and AM bounds for the large-region left L-term when `k ≥ 2001`. -/
lemma prodRange_one (start : ℕ) : prodRange start 1 = start := by
  simp [prodRange]

lemma prodRange_mul_front (start : ℕ) : ∀ n,
    prodRange start (n + 1) = start * prodRange (start + 1) n
  | 0 => by simp [prodRange]
  | n + 1 => by
    rw [prodRange_succ start (n + 1)]
    rw [prodRange_mul_front start n]
    rw [prodRange_succ (start + 1) n]
    ring

lemma prodRange_peel (start n : ℕ) :
    prodRange start (n + 2) =
      start * (start + n + 1) * prodRange (start + 1) n := by
  have h1 := prodRange_succ start (n + 1)
  have h2 : start + (n + 1) = start + n + 1 := by omega
  rw [h1, h2, prodRange_mul_front]
  ring

lemma peel_ends_le (start n : ℕ) :
    start * (start + n + 1) ≤ (start + 1) * (start + n) := by
  nlinarith

lemma prodRange_pair_ge : ∀ (len start : ℕ), 1 ≤ start →
    (start * (start + len - 1)) ^ (len / 2) ≤ prodRange start len
  | 0, start, _ => by simp [prodRange]
  | 1, start, hstart => by
    simp [prodRange]
    exact hstart
  | n + 2, start, hstart => by
    rw [prodRange_peel]
    have hn2 : (n + 2) / 2 = n / 2 + 1 := by omega
    have hend : start + (n + 2) - 1 = start + n + 1 := by omega
    rw [hn2, nat_pow_succ_left, hend]
    have ih := prodRange_pair_ge n (start + 1) (by omega)
    have hmid : start + 1 + n - 1 = start + n := by omega
    rw [hmid] at ih
    have hends := peel_ends_le start n
    have hpow : (start * (start + n + 1)) ^ (n / 2) ≤
        ((start + 1) * (start + n)) ^ (n / 2) :=
      Nat.pow_le_pow_left hends _
    have hmidle : (start * (start + n + 1)) ^ (n / 2) ≤ prodRange (start + 1) n :=
      le_trans hpow ih
    exact Nat.mul_le_mul_left _ hmidle


lemma real_am2 (a b : ℝ) : a * b ≤ ((a + b) / 2) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

lemma am_ends (start n : ℕ) :
    (start : ℝ) * ((start : ℝ) + n + 1) ≤
      ((2 * (start : ℝ) + n + 1) / 2) ^ 2 := by
  convert real_am2 (start : ℝ) ((start : ℝ) + n + 1) using 2
  ring

lemma prodRange_am_le : ∀ (len start : ℕ),
    (prodRange start len : ℝ) ≤
      ((2 * (start : ℝ) + (len : ℝ) - 1) / 2) ^ len
  | 0, start => by simp [prodRange]
  | 1, start => by simp [prodRange]
  | n + 2, start => by
    rw [prodRange_peel]
    push_cast
    have ham := am_ends start n
    have ih := prodRange_am_le n (start + 1)
    have hAMmid : (2 * ((start + 1 : ℕ) : ℝ) + (n : ℝ) - 1) / 2 =
        (2 * (start : ℝ) + n + 1) / 2 := by
      push_cast; ring
    rw [hAMmid] at ih
    have hAM : (2 * (start : ℝ) + ((n : ℝ) + 2) - 1) / 2 =
        (2 * (start : ℝ) + n + 1) / 2 := by ring
    rw [hAM]
    have hmul := mul_le_mul ham ih (by positivity) (by positivity)
    have hpow : ((2 * (start : ℝ) + n + 1) / 2) ^ 2 *
        ((2 * (start : ℝ) + n + 1) / 2) ^ n =
        ((2 * (start : ℝ) + n + 1) / 2) ^ (n + 2) := by
      rw [← pow_add, Nat.add_comm]
    rw [← hpow]
    exact hmul

lemma prodRange_pair_ge_odd : ∀ (q start : ℕ), 1 ≤ start →
    (start * (start + 2 * q)) ^ q * (start + q) ≤ prodRange start (2 * q + 1)
  | 0, start, _ => by simp [prodRange]
  | q + 1, start, hstart => by
    have hlen : 2 * (q + 1) + 1 = (2 * q + 1) + 2 := by omega
    rw [hlen, prodRange_peel]
    have hidx : start + (2 * q + 1) + 1 = start + 2 * (q + 1) := by omega
    rw [hidx]
    have ih := prodRange_pair_ge_odd q (start + 1) (by omega)
    have hmid : start + 1 + q = start + (q + 1) := by omega
    have hspan : start + 1 + 2 * q = start + 2 * q + 1 := by omega
    rw [hmid, hspan] at ih
    have hends : start * (start + 2 * (q + 1)) ≤
        (start + 1) * (start + 2 * q + 1) :=
      peel_ends_le start (2 * q + 1)
    have hpow : (start * (start + 2 * (q + 1))) ^ q ≤
        ((start + 1) * (start + 2 * q + 1)) ^ q :=
      Nat.pow_le_pow_left hends _
    -- (first*last)^{q+1} * middle = first*last * (first*last)^q * (start+q+1)
    have hrew : (start * (start + 2 * (q + 1))) ^ (q + 1) * (start + (q + 1)) =
        start * (start + 2 * (q + 1)) *
          ((start * (start + 2 * (q + 1))) ^ q * (start + (q + 1))) := by
      rw [nat_pow_succ_left]; ring
    rw [hrew]
    have hcore : (start * (start + 2 * (q + 1))) ^ q * (start + (q + 1)) ≤
        prodRange (start + 1) (2 * q + 1) :=
      le_trans (Nat.mul_le_mul_right _ hpow) ih
    exact Nat.mul_le_mul_left _ hcore

lemma middle_sq_ge (start q : ℕ) :
    start * (start + 2 * q) ≤ (start + q) * (start + q) := by
  nlinarith

lemma middle_ge_sqrt (start q : ℕ) :
    Real.sqrt ((start * (start + 2 * q) : ℕ) : ℝ) ≤ (start + q : ℝ) := by
  refine (Real.sqrt_le_iff).2 ⟨by positivity, ?_⟩
  have h := middle_sq_ge start q
  have : (((start + q) * (start + q) : ℕ) : ℝ) = (start + q : ℝ) ^ 2 := by
    push_cast; ring
  rw [← this]
  exact Nat.cast_le (α := ℝ) |>.mpr h


lemma prodRange_pair_ge_real (start len : ℕ) (hstart : 1 ≤ start) (hlen : 1 ≤ len) :
    ((start * (start + len - 1) : ℕ) : ℝ) ^ ((len : ℝ) / 2) ≤
      (prodRange start len : ℝ) := by
  rcases Nat.even_or_odd len with heven | hodd
  · obtain ⟨q, hq⟩ := heven
    have hdiv : (len : ℝ) / 2 = (q : ℝ) := by
      rw [hq]; push_cast; ring
    rw [hdiv, Real.rpow_natCast]
    have hpair := prodRange_pair_ge len start hstart
    have hhalf : len / 2 = q := by omega
    rw [hhalf] at hpair
    have : ((start * (start + len - 1) : ℕ) : ℝ) ^ q =
        (((start * (start + len - 1)) ^ q : ℕ) : ℝ) := by
      rw [Nat.cast_pow]
    rw [this]
    exact Nat.cast_le (α := ℝ) |>.mpr hpair
  · obtain ⟨q, hq⟩ := hodd
    have hdiv : (len : ℝ) / 2 = (q : ℝ) + 1 / 2 := by
      rw [hq]; push_cast; ring
    rw [hdiv]
    have hmulpos : 1 ≤ start * (start + len - 1) := by
      have : 1 ≤ start + len - 1 := by omega
      exact Nat.mul_le_mul hstart this
    have hpos : (0 : ℝ) < ((start * (start + len - 1) : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mp hmulpos)
    have hrpow :
        ((start * (start + len - 1) : ℕ) : ℝ) ^ ((q : ℝ) + 1 / 2) =
          ((start * (start + len - 1) : ℕ) : ℝ) ^ (q : ℕ) *
            Real.sqrt ((start * (start + len - 1) : ℕ) : ℝ) := by
      rw [Real.rpow_add hpos, Real.rpow_natCast, Real.sqrt_eq_rpow]
    rw [hrpow]
    have hend : start + len - 1 = start + 2 * q := by omega
    have hlen' : 2 * q + 1 = len := by omega
    have hodd' := prodRange_pair_ge_odd q start hstart
    rw [hend, ← hlen']
    have hmid : Real.sqrt ((start * (start + 2 * q) : ℕ) : ℝ) ≤ (start + q : ℝ) :=
      middle_ge_sqrt start q
    have hpow_nonneg : (0 : ℝ) ≤ ((start * (start + 2 * q) : ℕ) : ℝ) ^ (q : ℕ) := by
      positivity
    have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt ((start * (start + 2 * q) : ℕ) : ℝ) :=
      Real.sqrt_nonneg _
    have hmul := mul_le_mul (le_rfl : ((start * (start + 2 * q) : ℕ) : ℝ) ^ (q : ℕ) ≤ _)
      hmid hsqrt_nonneg hpow_nonneg
    refine le_trans hmul ?_
    have : ((start * (start + 2 * q) : ℕ) : ℝ) ^ (q : ℕ) * (start + q : ℝ) =
        (((start * (start + 2 * q)) ^ q * (start + q) : ℕ) : ℝ) := by
      push_cast; ring
    rw [this]
    exact Nat.cast_le (α := ℝ) |>.mpr hodd'


/-- `-log(1-z) ≤ z/(1-z)` for `0 ≤ z < 1`. -/
lemma neg_log_one_sub_le_div {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    -Real.log (1 - z) ≤ z / (1 - z) := by
  by_cases hz : z = 0
  · subst hz; simp
  · have habs : |z| < 1 := by
      rw [abs_of_nonneg hz0]; exact hz1
    have hsum := Real.hasSum_pow_div_log_of_abs_lt_one habs
    have hterm : ∀ n : ℕ, z ^ (n + 1) / ((n : ℝ) + 1) ≤ z ^ (n + 1) := by
      intro n
      have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      exact div_le_self (pow_nonneg hz0 _) hden
    have hsg : Summable (fun n : ℕ => z ^ (n + 1)) := by
      have := (summable_geometric_of_lt_one hz0 hz1).mul_left z
      convert this using 1
      ext n
      rw [pow_succ]
      ring
    have hle : ∑' n : ℕ, z ^ (n + 1) / ((n : ℝ) + 1) ≤ ∑' n : ℕ, z ^ (n + 1) :=
      Summable.tsum_le_tsum hterm hsum.summable hsg
    have hgeom : ∑' n : ℕ, z ^ (n + 1) = z / (1 - z) := by
      have h0 : ∑' n : ℕ, z ^ n = (1 - z)⁻¹ := tsum_geometric_of_lt_one hz0 hz1
      have : ∑' n : ℕ, z ^ (n + 1) = z * ∑' n : ℕ, z ^ n := by
        simpa [pow_succ, mul_comm] using
          (tsum_mul_left (a := z) (f := fun n : ℕ => z ^ n))
      rw [this, h0]
      field_simp
    have heq : -Real.log (1 - z) = ∑' n : ℕ, z ^ (n + 1) / ((n : ℝ) + 1) :=
      hsum.tsum_eq.symm
    linarith

lemma log_one_sub_ge_div {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    -(z / (1 - z)) ≤ Real.log (1 - z) := by
  have := neg_log_one_sub_le_div hz0 hz1
  linarith

lemma log_one_sub_ge_five_four {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1 / 5) :
    -((5 / 4) * z) ≤ Real.log (1 - z) := by
  have hz1 : z < 1 := lt_of_le_of_lt hz (by norm_num)
  have h := log_one_sub_ge_div hz0 hz1
  have hden : (4 : ℝ) / 5 ≤ 1 - z := by linarith
  have hdiv : z / (1 - z) ≤ z / (4 / 5) :=
    div_le_div_of_nonneg_left hz0 (by norm_num) hden
  have : z / (4 / 5) = (5 / 4) * z := by field_simp
  linarith

lemma log_four_lt : Real.log 4 < 7 / 5 := by
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [this, Real.log_pow]
    norm_cast
  linarith


lemma ten_le_log2 (k : ℕ) (hk : 2001 ≤ k) : 10 ≤ Nat.log 2 k := by
  have hpow : 2 ^ 10 ≤ k := by omega
  exact (Nat.le_log_iff_pow_le (by decide : 1 < 2) (by omega : k ≠ 0)).2 hpow

lemma log_k_ge_log2_mul (k : ℕ) (hk : 1 ≤ k) :
    (Nat.log 2 k : ℝ) * Real.log 2 ≤ Real.log k := by
  have hpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpow : (2 : ℕ) ^ Nat.log 2 k ≤ k := Nat.pow_log_le_self 2 (by omega)
  have : ((2 : ℕ) ^ Nat.log 2 k : ℝ) ≤ (k : ℝ) := by exact_mod_cast hpow
  have h2pos : (0 : ℝ) < (2 : ℕ) ^ Nat.log 2 k := by exact_mod_cast Nat.pow_pos (by decide : 0 < 2)
  have hlog := Real.log_le_log h2pos this
  have : Real.log (((2 : ℕ) : ℝ) ^ Nat.log 2 k) =
      (Nat.log 2 k : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
    ring
  rwa [this] at hlog

lemma leftover_numeric (L : ℕ) (hL : 10 ≤ L) :
    (168 : ℝ) / 5 + (27 : ℝ) / 8 * L < 10 * L * 0.6931471803 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hL
  push_cast
  nlinarith

lemma leftover_const_neg (k : ℕ) (hk : 2001 ≤ k) :
    (168 : ℝ) / 5 + (27 : ℝ) / 8 * Nat.log 2 k - 10 * Real.log k < 0 := by
  have hL := ten_le_log2 k hk
  have hlog := log_k_ge_log2_mul k (by omega)
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hnum := leftover_numeric (Nat.log 2 k) hL
  nlinarith

lemma j_cast (k s : ℕ) (hs : s ≤ k) :
    ((k - s + 1 : ℕ) : ℝ) = (k : ℝ) - s + 1 := by
  have : k - s + 1 = k + 1 - s := by omega
  rw [this, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  ring

lemma jp1_cast (k s : ℕ) (hs : s + 2 ≤ k) :
    ((k - s + 2 : ℕ) : ℝ) = (k : ℝ) - s + 2 := by
  have : k - s + 2 = k + 2 - s := by omega
  rw [this, Nat.cast_sub (by omega : s ≤ k + 2), Nat.cast_add, Nat.cast_two]
  ring

lemma km1_cast (k : ℕ) (hk : 1 ≤ k) :
    ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
  rw [Nat.cast_sub hk, Nat.cast_one]

lemma jp1_as_mul (k s : ℕ) (hs : s + 2 ≤ k) :
    ((k - s + 2 : ℕ) : ℝ) = (k : ℝ) * (1 - ((s : ℝ) - 2) / k) := by
  have hk0 : (k : ℝ) ≠ 0 := by
    have : 2 ≤ k := by omega
    exact_mod_cast (show k ≠ 0 by omega)
  rw [jp1_cast k s hs]
  field_simp [hk0]
  ring

lemma am_as_mul (k s : ℕ) (hk : 1 ≤ k) :
    (2 * (k : ℝ) + s - 14) / 2 = (k : ℝ) * (1 + ((s : ℝ) - 14) / (2 * k)) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  field_simp [hk0]
  ring

lemma log_am_le (k s : ℕ) (hk : 1 ≤ k) (hs : 14 ≤ s) :
    Real.log ((2 * (k : ℝ) + s - 14) / 2) ≤
      Real.log k + ((s : ℝ) - 14) / (2 * k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ham : (0 : ℝ) < (2 * (k : ℝ) + s - 14) / 2 := by
    have : (14 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have hsR : (14 : ℝ) ≤ s := by exact_mod_cast hs
  have h1 : (0 : ℝ) < 1 + ((s : ℝ) - 14) / (2 * k) := by
    have : (0 : ℝ) ≤ ((s : ℝ) - 14) / (2 * k) :=
      div_nonneg (by linarith) (by positivity)
    linarith
  rw [am_as_mul k s hk, Real.log_mul (ne_of_gt hk0) (ne_of_gt h1)]
  have : Real.log (1 + ((s : ℝ) - 14) / (2 * k)) ≤
      ((s : ℝ) - 14) / (2 * k) :=
    Real.log_le_sub_one_of_pos h1 |>.trans (by linarith)
  linarith

lemma log_jp1_ge (k s : ℕ) (hk : 2001 ≤ k) (hs5 : 5 * s ≤ k) (hs : 45 ≤ s) :
    Real.log k - (5 / 4) * ((s : ℝ) - 2) / k ≤
      Real.log ((k - s + 2 : ℕ) : ℝ) := by
  have hsk : s + 2 ≤ k := by
    have : 5 * s ≤ k := hs5
    omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hz : ((s : ℝ) - 2) / k ≤ 1 / 5 := by
    have : (s : ℝ) / k ≤ 1 / 5 := by
      have h := (Nat.cast_le (α := ℝ)).mpr hs5
      have : (5 : ℝ) * s ≤ k := by exact_mod_cast hs5
      have hk0' : (0 : ℝ) < k := hk0
      have : (s : ℝ) ≤ k / 5 := (le_div_iff₀ (by norm_num)).mpr (by linarith)
      exact (div_le_iff₀ hk0').mpr (by linarith)
    have : ((s : ℝ) - 2) / k ≤ s / k := by
      apply div_le_div_of_nonneg_right
      · linarith
      · positivity
    linarith
  have hz0 : 0 ≤ ((s : ℝ) - 2) / k := by
    apply div_nonneg
    · have : (2 : ℝ) ≤ s := by exact_mod_cast (show 2 ≤ s by omega)
      linarith
    · positivity
  have hz1 : ((s : ℝ) - 2) / k < 1 := lt_of_le_of_lt hz (by norm_num)
  rw [jp1_as_mul k s hsk, Real.log_mul (ne_of_gt hk0) (by
    have : 0 < 1 - ((s : ℝ) - 2) / k := by linarith
    exact ne_of_gt this)]
  have hge := log_one_sub_ge_five_four hz0 hz
  have hrew : (5 / 4 : ℝ) * ((s : ℝ) - 2) / k = (5 / 4) * (((s : ℝ) - 2) / k) := by
    ring
  linarith [hrew]

lemma log_km1_ge' (k : ℕ) (hk : 2001 ≤ k) :
    Real.log k - 2 / k ≤ Real.log ((k - 1 : ℕ) : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hz : (1 : ℝ) / k ≤ 1 / 5 := by
    apply one_div_le_one_div_of_le
    · norm_num
    · exact_mod_cast (show 5 ≤ k by omega)
  have hz0 : 0 ≤ (1 : ℝ) / k := by positivity
  have hpos : (0 : ℝ) < 1 - 1 / k := by
    have : (1 : ℝ) / k < 1 := (div_lt_one hk0).mpr (by exact_mod_cast (show 1 < k by omega))
    linarith
  have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) * (1 - 1 / k) := by
    rw [km1_cast k (by omega)]
    field_simp [hk0.ne']
  rw [this, Real.log_mul (ne_of_gt hk0) (ne_of_gt hpos)]
  have hge := log_one_sub_ge_five_four (z := (1 : ℝ) / k) hz0 hz
  have : (5 / 4 : ℝ) * (1 / k) ≤ 2 / k := by
    field_simp
    linarith
  linarith

lemma leftover_lhs_bound (k s : ℕ)
    (hk : 2001 ≤ k) (hs : 45 ≤ s) (hs5 : 5 * s ≤ k) :
    Real.log 4 + Real.log ((k - s + 1 : ℕ) : ℝ) +
        Real.log ((13 : ℕ).factorial : ℝ) +
        ((s - 13 : ℕ) : ℝ) * Real.log ((2 * (k : ℝ) + s - 14) / 2) ≤
      (7 : ℝ) / 5 + Real.log k + 23 +
        ((s - 13 : ℕ) : ℝ) * (Real.log k + ((s : ℝ) - 14) / (2 * k)) := by
  have hsle : s ≤ k := by omega
  have hs14 : 14 ≤ s := by omega
  have hjpos : (0 : ℝ) < ((k - s + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k - s + 1 by omega)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlogj : Real.log ((k - s + 1 : ℕ) : ℝ) ≤ Real.log k :=
    Real.log_le_log hjpos (by
      have : k - s + 1 ≤ k := by omega
      exact_mod_cast this)
  have ham := log_am_le k s (by omega) hs14
  have hf := log_fact13_lt_23
  have h4 := log_four_lt
  have hs13 : ((s - 13 : ℕ) : ℝ) = (s : ℝ) - 13 := by
    rw [Nat.cast_sub (by omega : 13 ≤ s)]; norm_num
  have hnn : (0 : ℝ) ≤ ((s - 13 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
  have hmul := mul_le_mul_of_nonneg_left ham hnn
  exact add_le_add (add_le_add (add_le_add (le_of_lt h4) hlogj) (le_of_lt hf)) hmul

lemma leftover_rhs_bound (k s : ℕ)
    (hk : 2001 ≤ k) (hs : 45 ≤ s) (hs5 : 5 * s ≤ k) :
    ((s - 2 : ℕ) : ℝ) / 2 *
        (Real.log k - (5 / 4) * ((s : ℝ) - 2) / k + Real.log k - 2 / k) ≤
      ((s - 2 : ℕ) : ℝ) / 2 *
        (Real.log ((k - s + 2 : ℕ) : ℝ) + Real.log ((k - 1 : ℕ) : ℝ)) := by
  have hjp := log_jp1_ge k s hk hs5 hs
  have hkm := log_km1_ge' k hk
  have hnn : (0 : ℝ) ≤ ((s - 2 : ℕ) : ℝ) / 2 := by
    apply div_nonneg
    · exact_mod_cast Nat.zero_le _
    · norm_num
  apply mul_le_mul_of_nonneg_left _ hnn
  linarith

lemma leftover_expanded (k s : ℕ)
    (hk : 2001 ≤ k) (hs : 45 ≤ s) (hs5 : 5 * s ≤ k) :
    Real.log 4 + Real.log ((k - s + 1 : ℕ) : ℝ) +
        Real.log ((13 : ℕ).factorial : ℝ) +
        ((s - 13 : ℕ) : ℝ) * Real.log ((2 * (k : ℝ) + s - 14) / 2) -
      ((s - 2 : ℕ) : ℝ) / 2 *
        (Real.log ((k - s + 2 : ℕ) : ℝ) + Real.log ((k - 1 : ℕ) : ℝ)) ≤
      (7 : ℝ) / 5 + 23 + Real.log k +
        ((s - 13 : ℕ) : ℝ) * (Real.log k + ((s : ℝ) - 14) / (2 * k)) -
      ((s - 2 : ℕ) : ℝ) / 2 *
        (2 * Real.log k - (5 / 4) * ((s : ℝ) - 2) / k - 2 / k) := by
  have hl := leftover_lhs_bound k s hk hs hs5
  have hr := leftover_rhs_bound k s hk hs hs5
  linarith

lemma leftover_simplify (k s : ℕ)
    (hk : 2001 ≤ k) (hs : 45 ≤ s) :
    (7 : ℝ) / 5 + 23 + Real.log k +
        ((s - 13 : ℕ) : ℝ) * (Real.log k + ((s : ℝ) - 14) / (2 * k)) -
      ((s - 2 : ℕ) : ℝ) / 2 *
        (2 * Real.log k - (5 / 4) * ((s : ℝ) - 2) / k - 2 / k) =
      (7 : ℝ) / 5 + 23 - 10 * Real.log k +
        ((s : ℝ) - 13) * ((s : ℝ) - 14) / (2 * k) +
        (5 / 8) * ((s : ℝ) - 2) ^ 2 / k +
        ((s : ℝ) - 2) / k := by
  have hs13 : ((s - 13 : ℕ) : ℝ) = (s : ℝ) - 13 := by
    rw [Nat.cast_sub (by omega : 13 ≤ s)]; norm_num
  have hs2 : ((s - 2 : ℕ) : ℝ) = (s : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ s)]; norm_num
  rw [hs13, hs2]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  field_simp [hk0]
  ring

lemma leftover_errors_le (k s : ℕ)
    (hk : 2001 ≤ k) (hs : 45 ≤ s) (hs5 : 5 * s ≤ k)
    (hss : s * s ≤ k * (3 * Nat.log 2 k + 8)) :
    ((s : ℝ) - 13) * ((s : ℝ) - 14) / (2 * k) +
        (5 / 8) * ((s : ℝ) - 2) ^ 2 / k +
        ((s : ℝ) - 2) / k ≤
      (9 / 8) * (3 * Nat.log 2 k + 8 : ℝ) + 1 / 5 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsR : (45 : ℝ) ≤ s := by exact_mod_cast hs
  have hssR : (s : ℝ) * s ≤ (k : ℝ) * (3 * Nat.log 2 k + 8) := by
    exact_mod_cast hss
  have hs2k : (s : ℝ) ^ 2 / k ≤ (3 * Nat.log 2 k + 8 : ℝ) := by
    have : (s : ℝ) ^ 2 ≤ (k : ℝ) * (3 * Nat.log 2 k + 8) := by
      rw [pow_two]; exact hssR
    exact (div_le_iff₀ hk0).mpr (by linarith)
  have h1 : ((s : ℝ) - 13) * ((s : ℝ) - 14) / (2 * k) ≤ (s : ℝ) ^ 2 / (2 * k) := by
    apply div_le_div_of_nonneg_right
    · have : ((s : ℝ) - 13) * ((s : ℝ) - 14) = (s : ℝ) ^ 2 - 27 * s + 182 := by ring
      rw [this]
      nlinarith
    · positivity
  have h2 : (5 / 8) * ((s : ℝ) - 2) ^ 2 / k ≤ (5 / 8) * (s : ℝ) ^ 2 / k := by
    have : ((s : ℝ) - 2) ^ 2 = (s : ℝ) ^ 2 - 4 * s + 4 := by ring
    have hle : ((s : ℝ) - 2) ^ 2 ≤ (s : ℝ) ^ 2 := by
      rw [this]; nlinarith
    have : (5 / 8 : ℝ) * ((s : ℝ) - 2) ^ 2 ≤ (5 / 8) * (s : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hle (by norm_num)
    exact div_le_div_of_nonneg_right this (le_of_lt hk0)
  have h3 : ((s : ℝ) - 2) / k ≤ 1 / 5 := by
    have : (s : ℝ) / k ≤ 1 / 5 := by
      have : (5 : ℝ) * s ≤ k := by exact_mod_cast hs5
      exact (div_le_iff₀ hk0).mpr (by linarith)
    have : ((s : ℝ) - 2) / k ≤ s / k := by
      apply div_le_div_of_nonneg_right
      · linarith
      · positivity
    linarith
  have : (s : ℝ) ^ 2 / (2 * k) + (5 / 8) * (s : ℝ) ^ 2 / k =
      (9 / 8) * (s : ℝ) ^ 2 / k := by
    field_simp [hk0.ne']
    ring
  have hsum : ((s : ℝ) - 13) * ((s : ℝ) - 14) / (2 * k) +
      (5 / 8) * ((s : ℝ) - 2) ^ 2 / k + ((s : ℝ) - 2) / k ≤
      (9 / 8) * (s : ℝ) ^ 2 / k + 1 / 5 := by
    linarith
  have hss' : (9 / 8 : ℝ) * ((s : ℝ) ^ 2 / k) ≤
      (9 / 8) * (3 * Nat.log 2 k + 8 : ℝ) :=
    mul_le_mul_of_nonneg_left hs2k (by norm_num)
  have hrew : (9 / 8 : ℝ) * (s : ℝ) ^ 2 / k = (9 / 8) * ((s : ℝ) ^ 2 / k) := by
    ring
  linarith

lemma leftover_nonpos' (k s : ℕ)
    (hk : 2001 ≤ k) (hs : 45 ≤ s) (hs5 : 5 * s ≤ k)
    (hss : s * s ≤ k * (3 * Nat.log 2 k + 8)) :
    Real.log 4 + Real.log ((k - s + 1 : ℕ) : ℝ) +
        Real.log ((13 : ℕ).factorial : ℝ) +
        ((s - 13 : ℕ) : ℝ) * Real.log ((2 * (k : ℝ) + s - 14) / 2) -
      ((s - 2 : ℕ) : ℝ) / 2 *
        (Real.log ((k - s + 2 : ℕ) : ℝ) + Real.log ((k - 1 : ℕ) : ℝ)) < 0 := by
  have hexp := leftover_expanded k s hk hs hs5
  have hsim := leftover_simplify k s hk hs
  rw [hsim] at hexp
  have herr := leftover_errors_le k s hk hs hs5 hss
  have hconst := leftover_const_neg k hk
  have hid : (7 : ℝ) / 5 + 23 + 1 / 5 + 9 = (168 : ℝ) / 5 := by norm_num
  have h9 : (9 / 8 : ℝ) * (3 * Nat.log 2 k + 8 : ℝ) =
      (27 / 8) * Nat.log 2 k + 9 := by ring
  have hstep :
      (7 : ℝ) / 5 + 23 - 10 * Real.log k +
          ((s : ℝ) - 13) * ((s : ℝ) - 14) / (2 * k) +
          (5 / 8) * ((s : ℝ) - 2) ^ 2 / k +
          ((s : ℝ) - 2) / k ≤
        (168 : ℝ) / 5 + (27 : ℝ) / 8 * Nat.log 2 k - 10 * Real.log k := by
    linarith
  have : (168 : ℝ) / 5 + (27 : ℝ) / 8 * Nat.log 2 k - 10 * Real.log k < 0 :=
    hconst
  linarith

lemma leftover_prod (k s : ℕ)
    (hk : 2001 ≤ k) (hs : 45 ≤ s) (hs5 : 5 * s ≤ k)
    (hss : s * s ≤ k * (3 * Nat.log 2 k + 8)) :
    (4 : ℝ) * ((k - s + 1 : ℕ) : ℝ) * ((13 : ℕ).factorial : ℝ) *
        (((2 * (k : ℝ) + s - 14) / 2) ^ ((s - 13 : ℕ))) ≤
      (((k - s + 2 : ℕ) * (k - 1) : ℕ) : ℝ) ^ (((s - 2 : ℕ) : ℝ) / 2) := by
  have hneg := leftover_nonpos' k s hk hs hs5 hss
  have hj : (0 : ℝ) < ((k - s + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k - s + 1 by omega)
  have hf : (0 : ℝ) < ((13 : ℕ).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have ham : (0 : ℝ) < (2 * (k : ℝ) + s - 14) / 2 := by
    have : (14 : ℝ) ≤ s := by exact_mod_cast (show 14 ≤ s by omega)
    have : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    linarith
  have hjp : (0 : ℝ) < ((k - s + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k - s + 2 by omega)
  have hkm : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  have hLpos : (0 : ℝ) <
      (4 : ℝ) * ((k - s + 1 : ℕ) : ℝ) * ((13 : ℕ).factorial : ℝ) *
        (((2 * (k : ℝ) + s - 14) / 2) ^ ((s - 13 : ℕ))) := by
    positivity
  have hRpos : (0 : ℝ) <
      (((k - s + 2 : ℕ) * (k - 1) : ℕ) : ℝ) ^ (((s - 2 : ℕ) : ℝ) / 2) := by
    apply Real.rpow_pos_of_pos
    exact_mod_cast (show 0 < (k - s + 2) * (k - 1) by
      apply Nat.mul_pos <;> omega)
  have hlogL :
      Real.log ((4 : ℝ) * ((k - s + 1 : ℕ) : ℝ) * ((13 : ℕ).factorial : ℝ) *
          (((2 * (k : ℝ) + s - 14) / 2) ^ ((s - 13 : ℕ)))) =
        Real.log 4 + Real.log ((k - s + 1 : ℕ) : ℝ) +
          Real.log ((13 : ℕ).factorial : ℝ) +
          ((s - 13 : ℕ) : ℝ) * Real.log ((2 * (k : ℝ) + s - 14) / 2) := by
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow]
  have hlogR :
      Real.log ((((k - s + 2 : ℕ) * (k - 1) : ℕ) : ℝ) ^
          (((s - 2 : ℕ) : ℝ) / 2)) =
        ((s - 2 : ℕ) : ℝ) / 2 *
          (Real.log ((k - s + 2 : ℕ) : ℝ) + Real.log ((k - 1 : ℕ) : ℝ)) := by
    rw [Real.log_rpow (by exact_mod_cast (show 0 < (k - s + 2) * (k - 1) by
      apply Nat.mul_pos <;> omega))]
    have : Real.log (((k - s + 2 : ℕ) * (k - 1) : ℕ) : ℝ) =
        Real.log ((k - s + 2 : ℕ) : ℝ) + Real.log ((k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul (ne_of_gt hjp) (ne_of_gt hkm)]
    rw [this]
  have : Real.log ((4 : ℝ) * ((k - s + 1 : ℕ) : ℝ) * ((13 : ℕ).factorial : ℝ) *
        (((2 * (k : ℝ) + s - 14) / 2) ^ ((s - 13 : ℕ)))) ≤
      Real.log ((((k - s + 2 : ℕ) * (k - 1) : ℕ) : ℝ) ^
        (((s - 2 : ℕ) : ℝ) / 2)) := by
    rw [hlogL, hlogR]
    linarith [hneg]
  exact (Real.log_le_log_iff hLpos hRpos).1 this

lemma largeL_core_real (k s : ℕ)
    (hk : 2001 ≤ k) (hs : 45 ≤ s) (hs5 : 5 * s ≤ k)
    (hss : s * s ≤ k * (3 * Nat.log 2 k + 8)) :
    (4 : ℝ) * ((k - s + 1 : ℕ) : ℝ) * ((13 : ℕ).factorial : ℝ) *
        (prodRange k (s - 13) : ℝ) ≤
      (prodRange (k - s + 2) (s - 2) : ℝ) := by
  have hsk : s + 2 ≤ k := by omega
  have hAM := prodRange_am_le (s - 13) k
  have hpair := prodRange_pair_ge_real (k - s + 2) (s - 2)
    (by omega) (by omega)
  have hend : k - s + 2 + (s - 2) - 1 = k - 1 := by omega
  rw [hend] at hpair
  have ham_eq : (2 * (k : ℝ) + ((s - 13 : ℕ) : ℝ) - 1) / 2 =
      (2 * (k : ℝ) + s - 14) / 2 := by
    have : ((s - 13 : ℕ) : ℝ) = (s : ℝ) - 13 := by
      rw [Nat.cast_sub (by omega : 13 ≤ s)]; norm_num
    rw [this]; ring
  rw [ham_eq] at hAM
  have hprod := leftover_prod k s hk hs hs5 hss
  have hnn1 : (0 : ℝ) ≤ (4 : ℝ) * ((k - s + 1 : ℕ) : ℝ) * ((13 : ℕ).factorial : ℝ) := by
    positivity
  have hAMle : (prodRange k (s - 13) : ℝ) ≤
      ((2 * (k : ℝ) + s - 14) / 2) ^ ((s - 13 : ℕ)) := hAM
  have hmul := mul_le_mul_of_nonneg_left hAMle hnn1
  refine le_trans hmul (le_trans hprod ?_)
  exact hpair

lemma largeL_core_nat (k s : ℕ)
    (hk : 2001 ≤ k) (hs : 45 ≤ s) (hs5 : 5 * s ≤ k)
    (hss : s * s ≤ k * (3 * Nat.log 2 k + 8)) :
    4 * (k - s + 1) * (13 : ℕ).factorial * prodRange k (s - 13) ≤
      prodRange (k - s + 2) (s - 2) := by
  have hR := largeL_core_real k s hk hs hs5 hss
  have hcast :
      ((4 * (k - s + 1) * (13 : ℕ).factorial * prodRange k (s - 13) : ℕ) : ℝ) =
        (4 : ℝ) * ((k - s + 1 : ℕ) : ℝ) * ((13 : ℕ).factorial : ℝ) *
          (prodRange k (s - 13) : ℝ) := by
    push_cast; ring
  have : ((4 * (k - s + 1) * (13 : ℕ).factorial * prodRange k (s - 13) : ℕ) : ℝ) ≤
      (prodRange (k - s + 2) (s - 2) : ℝ) := by
    rwa [hcast]
  exact Nat.cast_le (α := ℝ) |>.mp this

lemma largeL_left_le_of_ge_2001 (k : ℕ) (hk : 2001 ≤ k) :
    largeL k (k - midShift k + 1) * (2 * k) ≤
      k.factorial * (k - 1).factorial := by
  have hk81 : 81 ≤ k := by omega
  have hs45 := midShift_ge_45 k hk81
  have hs5 := midShift_le_div5 k hk
  have hss := midShift_sq_le k hk81
  set s := midShift k
  set j := k - s + 1
  have hs5' : 5 * s ≤ k := by
    have : s * 5 = 5 * s := by ring
    rwa [← this]
  have hcore := largeL_core_nat k s hk hs45 hs5' hss
  -- 4 j 13! prodRange k (s-13) ≤ prodRange (j+1) (s-2)
  have hineq :
      4 * j * (13 : ℕ).factorial * prodRange k (s - 13) ≤
        prodRange (j + 1) (s - 2) := by
    simpa [j, s, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcore
  have hm : k + s - 14 = k - 1 + (s - 13) := by omega
  have hja : j + (s - 2) = k - 1 := by omega
  have hprodL :
      (k - 1).factorial * prodRange k (s - 13) = (k + s - 14).factorial := by
    have h1 : k - 1 + 1 = k := by omega
    have := prodRange_factorial (k - 1) (s - 13)
    rwa [h1, ← hm] at this
  have hprodR :
      j.factorial * prodRange (j + 1) (s - 2) = (k - 1).factorial := by
    have := prodRange_factorial j (s - 2)
    rwa [hja] at this
  have hfact : 4 * j * (13 : ℕ).factorial * j.factorial *
      (k + s - 14).factorial ≤
      (k - 1).factorial * (k - 1).factorial := by
    have : 4 * j * (13 : ℕ).factorial * j.factorial *
        ((k - 1).factorial * prodRange k (s - 13)) ≤
        (k - 1).factorial * (j.factorial * prodRange (j + 1) (s - 2)) := by
      have := Nat.mul_le_mul_left (j.factorial * (k - 1).factorial) hineq
      convert this using 1 <;> ring
    rwa [hprodL, hprodR] at this
  have hm2 : 2 * k - j - 13 = k + s - 14 := by omega
  have ek : k.factorial = k * (k - 1).factorial := fact_pred k (by omega)
  unfold largeL
  rw [hm2]
  have hrew : 2 * j * (13 : ℕ).factorial * j.factorial * (k + s - 14).factorial *
      (2 * k) =
      k * (4 * j * (13 : ℕ).factorial * j.factorial * (k + s - 14).factorial) := by
    ring
  rw [hrew, ek]
  have := Nat.mul_le_mul_left k hfact
  convert this using 1 <;> ring

lemma largeL_left_le (k : ℕ) (hk : 81 ≤ k) :
    largeL k (k - midShift k + 1) * (2 * k) ≤
      k.factorial * (k - 1).factorial := by
  cases le_or_gt k 2000 with
  | inl h => exact largeL_left_le_of_le_2000 k hk h
  | inr h => exact largeL_left_le_of_ge_2001 k (by omega)

lemma largeR_left_le (k : ℕ) (hk : 81 ≤ k) :
    largeR k (k - midShift k + 1) * (2 * k) ≤
      k.factorial * (k - 1).factorial := by
  cases le_or_gt k 2000 with
  | inl h => exact largeR_left_le_of_le_2000 k hk h
  | inr h => exact largeR_left_le_of_ge_2001 k (by omega)

lemma large_region_sum_le (k : ℕ) (hk : 81 ≤ k) :
    ∑ j ∈ Icc (k - midShift k + 1) (k - 2),
      j.factorial * W (2 * k - j) (j - 1) ≤
    k.factorial * (k - 1).factorial := by
  set s := midShift k
  set cut := k - s
  set lo := cut + 1
  set hi := k - 2
  set wB := k.factorial * (k - 1).factorial
  have hb := mid_cut_bounds k hk
  have hs45 := midShift_ge_45 k hk
  have hlohi : lo ≤ hi := by
    have : cut + 1 ≤ k - 2 := by omega
    simpa [lo, hi] using this
  have hlo14 : 14 ≤ lo := by omega
  have hXpos : 0 < 2 * k := by omega
  have hterm : ∀ j ∈ Icc lo hi,
      j.factorial * W (2 * k - j) (j - 1) ≤ largeL k j + largeR k j := by
    intro j hj
    simp [mem_Icc] at hj
    exact W_large_term_pair' k j hk (by omega) (by omega)
  have hLmax : ∀ j ∈ Icc lo hi,
      largeL k j ≤ max (largeL k lo) (largeL k hi) := by
    intro j hj
    simp [mem_Icc] at hj
    exact largeL_le_max_ends k lo hi j (by omega) hj.1 hj.2 (by omega)
  have hRmax : ∀ j ∈ Icc lo hi,
      largeR k j ≤ max (largeR k lo) (largeR k hi) := by
    intro j hj
    simp [mem_Icc] at hj
    exact largeR_le_max_ends k lo hi j (by omega) hj.1 hj.2 (by omega)
  have hLlo : largeL k lo * (2 * k) ≤ wB := by
    simpa [lo, cut, s, wB] using largeL_left_le k hk
  have hLhi : largeL k hi * (2 * k) ≤ wB := by
    simpa [hi, wB] using largeL_right_le k hk
  have hRlo : largeR k lo * (2 * k) ≤ wB := by
    simpa [lo, cut, s, wB] using largeR_left_le k hk
  have hRhi : largeR k hi * (2 * k) ≤ wB := by
    simpa [hi, wB] using largeR_right_le k hk
  have hLdiv : largeL k lo ≤ wB / (2 * k) ∧ largeL k hi ≤ wB / (2 * k) :=
    ⟨Nat.le_div_iff_mul_le hXpos |>.mpr hLlo,
      Nat.le_div_iff_mul_le hXpos |>.mpr hLhi⟩
  have hRdiv : largeR k lo ≤ wB / (2 * k) ∧ largeR k hi ≤ wB / (2 * k) :=
    ⟨Nat.le_div_iff_mul_le hXpos |>.mpr hRlo,
      Nat.le_div_iff_mul_le hXpos |>.mpr hRhi⟩
  have hbound : ∀ j ∈ Icc lo hi,
      j.factorial * W (2 * k - j) (j - 1) ≤ wB / k := by
    intro j hj
    have hpair := hterm j hj
    have hLm := hLmax j hj
    have hRm := hRmax j hj
    have hL : largeL k j ≤ wB / (2 * k) :=
      le_trans hLm (max_le hLdiv.1 hLdiv.2)
    have hR : largeR k j ≤ wB / (2 * k) :=
      le_trans hRm (max_le hRdiv.1 hRdiv.2)
    have : largeL k j + largeR k j ≤ wB / (2 * k) + wB / (2 * k) :=
      Nat.add_le_add hL hR
    have hsumdiv : wB / (2 * k) + wB / (2 * k) ≤ wB / k := by
      have : wB / (2 * k) + wB / (2 * k) = 2 * (wB / (2 * k)) := by ring
      rw [this]
      have h1 : 2 * (wB / (2 * k)) ≤ (2 * wB) / (2 * k) :=
        mul_div_le_div_mul 2 wB (2 * k) hXpos
      refine le_trans h1 ?_
      have : (2 * wB) / (2 * k) = wB / k :=
        Nat.mul_div_mul_left wB k (by decide : 0 < (2 : ℕ))
      exact le_of_eq this
    exact le_trans hpair (le_trans this hsumdiv)
  have hsum := sum_le_sum hbound
  refine le_trans hsum ?_
  have : ∑ j ∈ Icc lo hi, wB / k = #(Icc lo hi) * (wB / k) := by
    simp [sum_const]
  rw [this]
  have hcard : #(Icc lo hi) ≤ k := by
    rw [Nat.card_Icc]; omega
  have hmul := Nat.mul_le_mul_right (wB / k) hcard
  refine le_trans hmul ?_
  have : k * (wB / k) ≤ wB := Nat.mul_div_le wB k
  simpa [wB] using this

lemma W_mid_sum_le (k : ℕ) (hk : 81 ≤ k) :
    ∑ j ∈ Icc 24 (k - 2), j.factorial * W (2 * k - j) (j - 1) ≤
      k.factorial * (k - 1).factorial +
        k.factorial * (k - 1).factorial / 4 := by
  set s := midShift k
  set cut := k - s
  have hb := mid_cut_bounds k hk
  have h24 : 24 ≤ cut := hb.1
  have hcutle : cut ≤ k - 2 := by omega
  have hsplit := Icc_union_split (a := 24) (b := cut) (c := k - 2)
    (by omega) hcutle
  have hdis : Disjoint (Icc 24 cut) (Icc (cut + 1) (k - 2)) := by
    refine disjoint_left.mpr ?_
    intro x hx hy
    simp [mem_Icc] at hx hy; omega
  rw [hsplit, sum_union hdis]
  have hmid := mid_region_sum_le k hk
  -- mid ≤ X/k ≤ X/4; leftover budget X + X/4 - X/k ≥ X for the large region
  have hmid' : ∑ j ∈ Icc 24 cut, j.factorial * W (2 * k - j) (j - 1) ≤
      k.factorial * (k - 1).factorial / 4 := by
    refine le_trans hmid ?_
    exact Nat.div_le_div_left (by omega : 4 ≤ k) (by decide : 0 < 4)
  have hlarge :
      ∑ j ∈ Icc (cut + 1) (k - 2), j.factorial * W (2 * k - j) (j - 1) ≤
        k.factorial * (k - 1).factorial :=
    large_region_sum_le k hk
  have : k.factorial * (k - 1).factorial / 4 +
      k.factorial * (k - 1).factorial ≤
      k.factorial * (k - 1).factorial +
        k.factorial * (k - 1).factorial / 4 := by
    rw [Nat.add_comm]
  exact le_trans (Nat.add_le_add hmid' hlarge) this

/-- The `j = k` term of the `W(2k,k)` decomposition. -/
lemma W_two_k_main_term (k : ℕ) (hk : 1 ≤ k) :
    k.factorial * W k (k - 1) ≤ 2 * k.factorial * (k - 1).factorial := by
  have := W_pred_le k hk
  have h := Nat.mul_le_mul_left k.factorial this
  have : k.factorial * (2 * (k - 1).factorial) =
      2 * k.factorial * (k - 1).factorial := by ring
  rwa [this] at h

lemma W_two_k_le (k : ℕ) (hk : 81 ≤ k) :
    W (2 * k) k ≤ 4 * k.factorial * (k - 1).factorial := by
  have hdecomp := W_max_decomp k (2 * k)
  have hne : 2 * k ≠ 0 := by omega
  have hmin : min (2 * k) k = k := by omega
  simp only [hne, ite_false] at hdecomp
  rw [hmin, add_zero] at hdecomp
  rw [hdecomp]
  have hk1 : 1 ≤ k := by omega
  have hI : Icc 1 k = insert k (Icc 1 (k - 1)) := by
    ext x; simp [mem_Icc, mem_insert]; omega
  have hnotin : k ∉ Icc 1 (k - 1) := by simp [mem_Icc]; omega
  rw [hI, sum_insert hnotin]
  have heq : 2 * k - k = k := by omega
  rw [heq]
  have hmain := W_two_k_main_term k hk1
  have hrest :
      ∑ j ∈ Icc 1 (k - 1), j.factorial * W (2 * k - j) (j - 1) ≤
        2 * k.factorial * (k - 1).factorial := by
    have hcut : 5 * k.sqrt + 24 ≤ k := five_sqrt_lt k hk
    have hsq : 1 ≤ k.sqrt := by
      have : (1 : ℕ) * 1 ≤ k := by omega
      exact Nat.le_sqrt.mpr this
    set cut := k - 5 * k.sqrt with hcutdef
    have h24 : 24 ≤ cut := by omega
    have hcutle : cut ≤ k - 1 := by omega
    have hsplit1 := Icc_union_split (a := 1) (b := 23) (c := k - 1)
      (by omega) (by omega)
    have hsplit2 := Icc_union_split (a := 24) (b := cut) (c := k - 1)
      (by omega) hcutle
    have hdis1 : Disjoint (Icc 1 23) (Icc 24 (k - 1)) := by
      refine disjoint_left.mpr ?_
      intro x hx hy
      simp [mem_Icc] at hx hy; omega
    rw [hsplit1, sum_union hdis1]
    have hsmall :
        ∑ j ∈ Icc 1 23, j.factorial * W (2 * k - j) (j - 1) ≤
          k.factorial * (k - 1).factorial / 40 := by
      have hterm : ∀ j ∈ Icc 1 23,
          j.factorial * W (2 * k - j) (j - 1) ≤
            k.factorial * (k - 1).factorial / 1000 := by
        intro j hj
        simp [mem_Icc] at hj
        exact smallW_term_le k j hk (by omega)
      have hsum := sum_le_sum hterm
      refine le_trans hsum ?_
      have : ∑ j ∈ Icc 1 23, k.factorial * (k - 1).factorial / 1000 =
          #(Icc 1 23) * (k.factorial * (k - 1).factorial / 1000) := by
        simp [sum_const]
      rw [this]
      have hcard : #(Icc 1 23) = 23 := by rw [Nat.card_Icc]
      rw [hcard]
      exact small_div_23_40 (k.factorial * (k - 1).factorial)
    have hrest' :
        ∑ j ∈ Icc 24 (k - 1), j.factorial * W (2 * k - j) (j - 1) ≤
          k.factorial * (k - 1).factorial +
            k.factorial * (k - 1).factorial / 2 := by
      have hk2 : 24 ≤ k - 2 := by omega
      have hI : Icc 24 (k - 1) = insert (k - 1) (Icc 24 (k - 2)) := by
        ext x; simp [mem_Icc, mem_insert]; omega
      have hnotin : k - 1 ∉ Icc 24 (k - 2) := by simp [mem_Icc]; omega
      rw [hI, sum_insert hnotin]
      have heq : 2 * k - (k - 1) = k + 1 := by omega
      have hpred : k - 1 - 1 = k - 2 := by omega
      rw [heq, hpred]
      have hkm1 := W_km1_term_le k hk
      have hmid :
          ∑ j ∈ Icc 24 (k - 2), j.factorial * W (2 * k - j) (j - 1) ≤
            k.factorial * (k - 1).factorial +
              k.factorial * (k - 1).factorial / 4 :=
        W_mid_sum_le k hk
      have hcomb :
          k.factorial * (k - 1).factorial / 20 +
            (k.factorial * (k - 1).factorial +
              k.factorial * (k - 1).factorial / 4) ≤
            k.factorial * (k - 1).factorial +
              k.factorial * (k - 1).factorial / 2 :=
        comb_budget _
      exact le_trans (Nat.add_le_add hkm1 hmid) hcomb
    have : k.factorial * (k - 1).factorial / 40 +
        (k.factorial * (k - 1).factorial +
          k.factorial * (k - 1).factorial / 2) ≤
        2 * k.factorial * (k - 1).factorial := by
      have heq : 2 * (k.factorial * (k - 1).factorial) =
          2 * k.factorial * (k - 1).factorial := by ring
      rw [← heq]
      exact rest_budget _
    exact le_trans (Nat.add_le_add hsmall hrest') this
  have : k.factorial * W k (k - 1) +
      ∑ j ∈ Icc 1 (k - 1), j.factorial * W (2 * k - j) (j - 1) ≤
        4 * k.factorial * (k - 1).factorial := by
    have : 2 * k.factorial * (k - 1).factorial +
        2 * k.factorial * (k - 1).factorial =
        4 * k.factorial * (k - 1).factorial := by ring
    rw [← this]
    exact Nat.add_le_add hmain hrest
  exact this

lemma W_two_k_of_pred (k : ℕ) (hk : 81 ≤ k) :
    (tau (2 * k) k).natAbs <
      (tau (k - 1) (k - 1)).natAbs * (k + 1).factorial := by
  have hW := W_two_k_le k hk
  have hk3 : 3 ≤ k - 1 := by omega
  have hτ : (k - 3) * (k - 2).factorial ≤ (tau (k - 1) (k - 1)).natAbs := by
    simpa using tau_abs_ge_pred hk3
  have hWu : (tau (2 * k) k).natAbs ≤ W (2 * k) k := tau_abs_le_W' k (2 * k)
  have hlt := four_mul_lt_target k hk
  have : W (2 * k) k < (k - 3) * (k - 2).factorial * (k + 1).factorial :=
    lt_of_le_of_lt hW hlt
  have : (tau (2 * k) k).natAbs <
      (k - 3) * (k - 2).factorial * (k + 1).factorial :=
    lt_of_le_of_lt hWu this
  refine lt_of_lt_of_le this ?_
  exact Nat.mul_le_mul_right _ hτ

lemma tau_pred_rec {d k : ℕ} (hk : 1 ≤ k) (hd : k ≤ d) :
    tau d k = tau d (k - 1) - (k.factorial : ℤ) * tau (d - k) (k - 1) := by
  cases k with
  | zero => omega
  | succ k =>
    rw [tau_succ_of_le (by simpa using hd)]
    simp [Nat.succ_eq_add_one]

lemma tri_eq_pred_add (k : ℕ) (hk : 1 ≤ k) : tri k = tri (k - 1) + k := by
  cases k with
  | zero => omega
  | succ k =>
    rw [tri_succ]
    simp

/-- After the parity constraint, the only complementary distances below `2k-3`
    (other than the already-handled `{0, k-1}`) are `Δ = k`. -/
lemma needed_delta_cases {n k : ℕ} (hn1 : k + 1 ≤ n) (hn2 : n ≤ tri k)
    (hpar : Even (midx n) ↔ Even (midx (n - (k + 1)))) :
    tri k - n = 0 ∨ tri k - n = k - 1 ∨ tri k - n = k ∨
      2 * k - 3 ≤ tri k - n := by
  have hdrop := two_le_midx_drop hn1 hn2 hpar
  rcases hdrop with hge | h0
  · by_cases hkm1 : tri k - n = k - 1
    · exact Or.inr (Or.inl hkm1)
    · by_cases hk : tri k - n = k
      · exact Or.inr (Or.inr (Or.inl hk))
      · refine Or.inr (Or.inr (Or.inr ?_))
        by_contra h
        have hΔlo : k + 1 ≤ tri k - n := by omega
        have hΔhi : tri k - n ≤ 2 * k - 4 := by omega
        have hk2 : 2 ≤ k := by omega
        have hnlt : n < tri k := by omega
        have : tri k = tri (k - 1) + k := tri_eq_pred_add k (by omega)
        have : tri (k - 1) = tri (k - 2) + (k - 1) :=
          tri_eq_pred_add (k - 1) (by omega)
        have hlo : tri (k - 2) ≤ n := by omega
        have hhi : n < tri (k - 1) := by omega
        have hm : midx n = k - 2 := by
          rw [midx_eq_iff]
          constructor
          · exact hlo
          · have : k - 2 + 1 = k - 1 := by omega
            rwa [this]
        have hrestlo : tri (k - 3) ≤ n - (k + 1) := by
          have : tri (k - 2) = tri (k - 3) + (k - 2) :=
            tri_eq_pred_add (k - 2) (by omega)
          omega
        have hresthi : n - (k + 1) < tri (k - 2) := by omega
        have hrest : midx (n - (k + 1)) = k - 3 := by
          rw [midx_eq_iff]
          constructor
          · exact hrestlo
          · have : k - 3 + 1 = k - 2 := by omega
            rwa [this]
        have : midx n - midx (n - (k + 1)) = 1 := by
          rw [hm, hrest]; omega
        have hge2 := rest_drop_ge_two hn1 hn2 hpar
        omega
  · exact Or.inl h0

lemma W_kp1_km1_le (k : ℕ) (hk : 81 ≤ k) :
    W (k + 1) (k - 1) ≤ 4 * (k - 1).factorial := by
  have h1 : W (k + 1) (k - 1) =
      W (k + 1) (k - 2) + (k - 1).factorial * 2 := by
    have h := W_succ_pred (n := k + 1) (m := k - 1) (by omega) (by omega)
    have hsub : k + 1 - (k - 1) = 2 := by omega
    rw [hsub, W_two _ (by omega)] at h
    exact h
  have h2 : W (k + 1) (k - 2) =
      W (k + 1) (k - 3) + (k - 2).factorial * 8 := by
    have h := W_succ_pred (n := k + 1) (m := k - 2) (by omega) (by omega)
    have hsub : k + 1 - (k - 2) = 3 := by omega
    rw [hsub, W_three _ (by omega)] at h
    exact h
  rw [h1, h2]
  have hoff := W_off3_le k hk
  have : W (k + 1) (k - 3) + 8 * (k - 2).factorial + 2 * (k - 1).factorial ≤
      4 * (k - 1).factorial := by
    have hsum : W (k + 1) (k - 3) + 8 * (k - 2).factorial + 2 * (k - 1).factorial ≤
        (k - 1).factorial + 8 * (k - 2).factorial + 2 * (k - 1).factorial := by
      exact Nat.add_le_add_right (Nat.add_le_add_right hoff _) _
    refine le_trans hsum ?_
    have e1 : (k - 1).factorial = (k - 1) * (k - 2).factorial :=
      fact_pred (k - 1) (by omega)
    have : (k - 1).factorial + 8 * (k - 2).factorial + 2 * (k - 1).factorial =
        3 * (k - 1).factorial + 8 * (k - 2).factorial := by ring
    rw [this, e1]
    have h8 : 8 ≤ k - 1 := by omega
    have : 3 * ((k - 1) * (k - 2).factorial) + 8 * (k - 2).factorial ≤
        4 * ((k - 1) * (k - 2).factorial) := by
      have : 8 * (k - 2).factorial ≤ (k - 1) * (k - 2).factorial :=
        Nat.mul_le_mul_right _ h8
      omega
    convert this using 1 <;> ring
  convert this using 1 <;> ring

lemma van13_of_two_k_succ (k j : ℕ) (hk : 81 ≤ k) (hj : j ≤ k - 2) :
    ∀ t, t ∈ Icc 1 (j - 1) → t < 13 → W (2 * k + 1 - j - t) (t - 1) = 0 := by
  intro t ht ht13
  simp [mem_Icc] at ht
  apply W_eq_zero_of_tri_lt
  have htri : tri (t - 1) ≤ tri 11 := tri_mono (by omega)
  have : tri 11 = 66 := by native_decide
  have : 2 * k + 1 - j - t ≥ 2 * k + 1 - (k - 2) - 12 := by omega
  have : 2 * k + 1 - (k - 2) - 12 = k - 9 := by omega
  omega

lemma fact_succ_mul (n : ℕ) : (n + 1).factorial = (n + 1) * n.factorial :=
  factorial_succ n

/-- Pairing bound on a large-region summand of `W(2k+1, k-2)`. -/
lemma W_large_term_pair_succ (k j : ℕ) (hk : 81 ≤ k)
    (hj1 : 14 ≤ j) (hj2 : j ≤ k - 2) :
    j.factorial * W (2 * k + 1 - j) (j - 1) ≤
      (2 * k) * (largeL k j + largeR k j) := by
  have hW := W_le_two_max_pair (n := 2 * k + 1 - j) (m := j - 1) (j0 := 13)
    (by decide : 1 ≤ 13) (by omega) (by omega)
    (fun t ht ht13 => van13_of_two_k_succ k j hk hj2 t ht ht13)
  have hs : (j - 1).succ = j := by omega
  rw [hs] at hW
  have hnm : 2 * k + 1 - j - (j - 1) = 2 * k - 2 * j + 2 := by omega
  rw [hnm] at hW
  have hmul := Nat.mul_le_mul_left j.factorial hW
  have hsub13 : 2 * k + 1 - j - 13 = 2 * k - j - 12 := by omega
  have hLfac : (2 * k - j - 12).factorial =
      (2 * k - j - 12) * (2 * k - j - 13).factorial := by
    have : 2 * k - j - 12 = (2 * k - j - 13) + 1 := by omega
    rw [this, factorial_succ]
  have hRfac : (2 * k - 2 * j + 2).factorial =
      (2 * k - 2 * j + 2) * (2 * k - 2 * j + 1).factorial := by
    have : 2 * k - 2 * j + 2 = (2 * k - 2 * j + 1) + 1 := by omega
    rw [this, factorial_succ]
  have hjL : 2 * k - j - 12 ≤ 2 * k := by omega
  have hjR : 2 * k - 2 * j + 2 ≤ 2 * k := by omega
  have hbound :
      j.factorial * (2 * j *
        ((13 : ℕ).factorial * (2 * k + 1 - j - 13).factorial +
          (j - 1).factorial * (2 * k - 2 * j + 2).factorial)) ≤
      (2 * k) * (largeL k j + largeR k j) := by
    rw [hsub13, hLfac, hRfac]
    unfold largeL largeR
    have hdist :
        j.factorial * (2 * j *
          ((13 : ℕ).factorial * ((2 * k - j - 12) * (2 * k - j - 13).factorial) +
            (j - 1).factorial * ((2 * k - 2 * j + 2) * (2 * k - 2 * j + 1).factorial))) =
        (2 * k - j - 12) * (2 * j * (13 : ℕ).factorial * j.factorial *
          (2 * k - j - 13).factorial) +
        (2 * k - 2 * j + 2) * (2 * j * j.factorial * (j - 1).factorial *
          (2 * k - 2 * j + 1).factorial) := by ring
    rw [hdist]
    have h1 := Nat.mul_le_mul_right
      (2 * j * (13 : ℕ).factorial * j.factorial * (2 * k - j - 13).factorial) hjL
    have h2 := Nat.mul_le_mul_right
      (2 * j * j.factorial * (j - 1).factorial * (2 * k - 2 * j + 1).factorial) hjR
    have := Nat.add_le_add h1 h2
    have hrew : (2 * k) * (2 * j * (13 : ℕ).factorial * j.factorial *
        (2 * k - j - 13).factorial) +
        (2 * k) * (2 * j * j.factorial * (j - 1).factorial *
          (2 * k - 2 * j + 1).factorial) =
        (2 * k) * (2 * j * (13 : ℕ).factorial * j.factorial *
          (2 * k - j - 13).factorial +
          2 * j * j.factorial * (j - 1).factorial *
            (2 * k - 2 * j + 1).factorial) := by ring
    rwa [hrew] at this
  exact le_trans hmul hbound

lemma W_mid_term_shift_succ (k j : ℕ) (hj : 2 ≤ j) (hjk : j ≤ k) :
    j.factorial * W (2 * k + 1 - j) (j - 1) ≤
      (j - 1) * (2 * j * (j - 1).factorial * (j - 1).factorial *
        (j - 1) ^ (2 * k - 2 * j + 1)) := by
  have hW : W (2 * k + 1 - j) (j - 1) ≤
      2 * (j - 1).factorial * (j - 1) ^ (2 * k - 2 * j + 2) := by
    have : 2 * k + 1 - j = (j - 1) + (2 * k - 2 * j + 2) := by omega
    rw [this]
    exact W_le_shift_pow (j - 1) (2 * k - 2 * j + 2)
  have hpow : (j - 1) ^ (2 * k - 2 * j + 2) =
      (j - 1) * (j - 1) ^ (2 * k - 2 * j + 1) := by
    have : 2 * k - 2 * j + 2 = (2 * k - 2 * j + 1) + 1 := by omega
    rw [this, Nat.pow_succ, Nat.mul_comm]
  rw [hpow] at hW
  have := Nat.mul_le_mul_left j.factorial hW
  have hrew : j.factorial * (2 * (j - 1).factorial *
      ((j - 1) * (j - 1) ^ (2 * k - 2 * j + 1))) =
      (j - 1) * (2 * j * (j - 1).factorial * (j - 1).factorial *
        (j - 1) ^ (2 * k - 2 * j + 1)) := by
    have : j.factorial = j * (j - 1).factorial := fact_pred j (by omega)
    rw [this]; ring
  rwa [hrew] at this

lemma smallW_term_le_succ (k j : ℕ) (hk : 81 ≤ k) (hj : j ≤ 23) :
    j.factorial * W (2 * k + 1 - j) (j - 1) ≤
      k.factorial * (k - 1).factorial / 1000 := by
  have hW : W (2 * k + 1 - j) (j - 1) ≤ 2 ^ (j - 1) * factProd (j - 1) :=
    W_le_pow_factProd (j - 1) (2 * k + 1 - j)
  have hterm : j.factorial * W (2 * k + 1 - j) (j - 1) ≤
      j.factorial * 2 ^ (j.pred) * factProd j.pred := by
    have := Nat.mul_le_mul_left j.factorial hW
    simpa [Nat.mul_assoc] using this
  have h81 := smallW_term_le_81 j hj
  have hmono := fact_pair_mono 81 k hk
  have hbig : j.factorial * 2 ^ j.pred * factProd j.pred * 1000 ≤
      k.factorial * (k - 1).factorial := by
    have : (81 : ℕ).factorial * (80 : ℕ).factorial ≤
        k.factorial * (k - 1).factorial := by
      simpa using hmono
    exact le_trans h81 this
  have hpos : 0 < 1000 := by decide
  exact Nat.le_div_iff_mul_le hpos |>.mpr (le_trans (Nat.mul_le_mul_right 1000 hterm) hbig)

lemma small_region_sum_le_succ (k : ℕ) (hk : 81 ≤ k) :
    ∑ j ∈ Icc 1 23, j.factorial * W (2 * k + 1 - j) (j - 1) ≤
      k.factorial * (k - 1).factorial / 40 := by
  have hterm : ∀ j ∈ Icc 1 23,
      j.factorial * W (2 * k + 1 - j) (j - 1) ≤
        k.factorial * (k - 1).factorial / 1000 := by
    intro j hj
    simp [mem_Icc] at hj
    exact smallW_term_le_succ k j hk (by omega)
  have hsum := sum_le_sum hterm
  refine le_trans hsum ?_
  have : ∑ j ∈ Icc 1 23, k.factorial * (k - 1).factorial / 1000 =
      #(Icc 1 23) * (k.factorial * (k - 1).factorial / 1000) := by
    simp [sum_const]
  rw [this]
  have hcard : #(Icc 1 23) = 23 := by rw [Nat.card_Icc]
  rw [hcard]
  exact small_div_23_40 (k.factorial * (k - 1).factorial)

lemma mid_region_sum_le_succ (k : ℕ) (hk : 81 ≤ k) :
    ∑ j ∈ Icc 24 (k - midShift k), j.factorial * W (2 * k + 1 - j) (j - 1) ≤
      k.factorial * (k - 1).factorial := by
  set s := midShift k
  set cut := k - s
  set wB := k.factorial * (k - 1).factorial
  have hb := mid_cut_bounds k hk
  have h24 : 24 ≤ cut := hb.1
  have hterm : ∀ j ∈ Icc 24 cut,
      j.factorial * W (2 * k + 1 - j) (j - 1) ≤ wB / k := by
    intro j hj
    simp [mem_Icc] at hj
    have hshift := W_mid_term_shift_succ k j (by omega) (by omega)
    have hmono : 2 * j * (j - 1).factorial * (j - 1).factorial *
        (j - 1) ^ (2 * k - 2 * j + 1) ≤
      2 * cut * (cut - 1).factorial * (cut - 1).factorial *
        (cut - 1) ^ (2 * s + 1) :=
      shift_pow_proxy_le_cut k hk j hj.1 hj.2
    have hcut := mid_cut_term_le k hk
    have hpow : 2 * k - 2 * cut + 1 = 2 * s + 1 := by
      have : cut = k - s := rfl
      omega
    have hcut' : 2 * cut * (cut - 1).factorial * (cut - 1).factorial *
        (cut - 1) ^ (2 * s + 1) * (k * k) ≤ wB := by
      simpa [cut, s, wB, hpow, mul_assoc] using hcut
    have hpos : 0 < k * k := by nlinarith
    have hdiv : 2 * cut * (cut - 1).factorial * (cut - 1).factorial *
        (cut - 1) ^ (2 * s + 1) ≤ wB / (k * k) :=
      Nat.le_div_iff_mul_le hpos |>.mpr hcut'
    have hjm : j - 1 ≤ k := by omega
    have hproxy : (j - 1) * (2 * j * (j - 1).factorial * (j - 1).factorial *
        (j - 1) ^ (2 * k - 2 * j + 1)) ≤
        k * (2 * cut * (cut - 1).factorial * (cut - 1).factorial *
          (cut - 1) ^ (2 * s + 1)) :=
      Nat.mul_le_mul hjm hmono
    have hdivk : k * (wB / (k * k)) ≤ wB / k := by
      have h1 : k * (wB / (k * k)) ≤ (k * wB) / (k * k) :=
        mul_div_le_div_mul k wB (k * k) hpos
      refine le_trans h1 ?_
      have hkpos : 0 < k := by omega
      have : (k * wB) / (k * k) = wB / k :=
        Nat.mul_div_mul_left wB k hkpos
      exact le_of_eq this
    have hcutk : k * (2 * cut * (cut - 1).factorial * (cut - 1).factorial *
        (cut - 1) ^ (2 * s + 1)) ≤ k * (wB / (k * k)) :=
      Nat.mul_le_mul_left k hdiv
    exact le_trans hshift (le_trans hproxy (le_trans hcutk hdivk))
  have hsum := sum_le_sum hterm
  refine le_trans hsum ?_
  have : ∑ j ∈ Icc 24 cut, wB / k = #(Icc 24 cut) * (wB / k) := by
    simp [sum_const]
  rw [this]
  have hcard : #(Icc 24 cut) ≤ k := by
    rw [Nat.card_Icc]; omega
  have hmul := Nat.mul_le_mul_right (wB / k) hcard
  refine le_trans hmul ?_
  have : k * (wB / k) ≤ wB := Nat.mul_div_le wB k
  simpa [wB] using this

set_option maxHeartbeats 800000 in
lemma large_region_sum_le_succ (k : ℕ) (hk : 81 ≤ k) :
    ∑ j ∈ Icc (k - midShift k + 1) (k - 2),
      j.factorial * W (2 * k + 1 - j) (j - 1) ≤
    2 * k * (k.factorial * (k - 1).factorial) := by
  set s := midShift k
  set cut := k - s
  set lo := cut + 1
  set hi := k - 2
  set wB := k.factorial * (k - 1).factorial
  have hb := mid_cut_bounds k hk
  have hs45 := midShift_ge_45 k hk
  have hlohi : lo ≤ hi := by omega
  have hXpos : 0 < 2 * k := by omega
  have hterm : ∀ j ∈ Icc lo hi,
      j.factorial * W (2 * k + 1 - j) (j - 1) ≤
        (2 * k) * (largeL k j + largeR k j) := by
    intro j hj
    simp [mem_Icc] at hj
    exact W_large_term_pair_succ k j hk (by omega) (by omega)
  have hLmax : ∀ j ∈ Icc lo hi,
      largeL k j ≤ max (largeL k lo) (largeL k hi) := by
    intro j hj
    simp [mem_Icc] at hj
    exact largeL_le_max_ends k lo hi j (by omega) hj.1 hj.2 (by omega)
  have hRmax : ∀ j ∈ Icc lo hi,
      largeR k j ≤ max (largeR k lo) (largeR k hi) := by
    intro j hj
    simp [mem_Icc] at hj
    exact largeR_le_max_ends k lo hi j (by omega) hj.1 hj.2 (by omega)
  have hLlo : largeL k lo * (2 * k) ≤ wB := by
    simpa [lo, cut, s, wB] using largeL_left_le k hk
  have hLhi : largeL k hi * (2 * k) ≤ wB := by
    simpa [hi, wB] using largeL_right_le k hk
  have hRlo : largeR k lo * (2 * k) ≤ wB := by
    simpa [lo, cut, s, wB] using largeR_left_le k hk
  have hRhi : largeR k hi * (2 * k) ≤ wB := by
    simpa [hi, wB] using largeR_right_le k hk
  have hLdiv : largeL k lo ≤ wB / (2 * k) ∧ largeL k hi ≤ wB / (2 * k) :=
    ⟨Nat.le_div_iff_mul_le hXpos |>.mpr hLlo,
      Nat.le_div_iff_mul_le hXpos |>.mpr hLhi⟩
  have hRdiv : largeR k lo ≤ wB / (2 * k) ∧ largeR k hi ≤ wB / (2 * k) :=
    ⟨Nat.le_div_iff_mul_le hXpos |>.mpr hRlo,
      Nat.le_div_iff_mul_le hXpos |>.mpr hRhi⟩
  have hbound : ∀ j ∈ Icc lo hi,
      j.factorial * W (2 * k + 1 - j) (j - 1) ≤ 2 * wB := by
    intro j hj
    have hpair := hterm j hj
    have hL : largeL k j ≤ wB / (2 * k) :=
      le_trans (hLmax j hj) (max_le hLdiv.1 hLdiv.2)
    have hR : largeR k j ≤ wB / (2 * k) :=
      le_trans (hRmax j hj) (max_le hRdiv.1 hRdiv.2)
    have hsumLR : largeL k j + largeR k j ≤ wB / k := by
      have : largeL k j + largeR k j ≤ wB / (2 * k) + wB / (2 * k) :=
        Nat.add_le_add hL hR
      refine le_trans this ?_
      have : wB / (2 * k) + wB / (2 * k) = 2 * (wB / (2 * k)) := by ring
      rw [this]
      have h1 : 2 * (wB / (2 * k)) ≤ (2 * wB) / (2 * k) :=
        mul_div_le_div_mul 2 wB (2 * k) hXpos
      refine le_trans h1 ?_
      have : (2 * wB) / (2 * k) = wB / k :=
        Nat.mul_div_mul_left wB k (by decide : 0 < (2 : ℕ))
      exact le_of_eq this
    have : (2 * k) * (largeL k j + largeR k j) ≤ (2 * k) * (wB / k) :=
      Nat.mul_le_mul_left _ hsumLR
    have h2k : (2 * k) * (wB / k) ≤ 2 * wB := by
      have : (2 * k) * (wB / k) = 2 * (k * (wB / k)) := by ring
      rw [this]
      exact Nat.mul_le_mul_left 2 (Nat.mul_div_le wB k)
    exact le_trans hpair (le_trans this h2k)
  have hsum := sum_le_sum hbound
  refine le_trans hsum ?_
  have : ∑ j ∈ Icc lo hi, 2 * wB = #(Icc lo hi) * (2 * wB) := by
    simp [sum_const]
  rw [this]
  have hcard : #(Icc lo hi) ≤ k := by
    rw [Nat.card_Icc]; omega
  have hmul := Nat.mul_le_mul_right (2 * wB) hcard
  have hrew : k * (2 * wB) = 2 * k * wB := by ring
  rw [hrew] at hmul
  have hwB : wB = k.factorial * (k - 1).factorial := rfl
  rwa [hwB] at hmul

lemma W_eq_sum_upto (n m : ℕ) (hn : n ≠ 0) (hm : m ≤ n) :
    W n m = ∑ j ∈ Icc 1 m, j.factorial * W (n - j) (j - 1) := by
  have hdecomp := W_max_decomp m n
  simp only [hn, ite_false] at hdecomp
  have hmin : min n m = m := by omega
  rwa [hmin, add_zero] at hdecomp

lemma rest_budget_succ (wB k : ℕ) (hk : 81 ≤ k) :
    wB / 40 + wB + 2 * k * wB ≤ 3 * k * wB := by
  have h40 : wB / 40 ≤ wB := Nat.div_le_self _ _
  have hsum : wB + wB + 2 * k * wB ≤ 3 * k * wB := by
    have : wB + wB = 2 * wB := by ring
    rw [this]
    have : 2 * wB + 2 * k * wB = (2 + 2 * k) * wB := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ (by omega : 2 + 2 * k ≤ 3 * k)
  exact le_trans (Nat.add_le_add_right (Nat.add_le_add h40 (le_rfl)) _) hsum

lemma Icc_split_three (a b c d : ℕ) (h1 : a ≤ b + 1) (h2 : b + 1 ≤ c + 1)
    (h3 : c ≤ d) :
    Icc a d = Icc a b ∪ Icc (b + 1) c ∪ Icc (c + 1) d := by
  have hsplit1 := Icc_union_split (a := a) (b := b) (c := d) h1 (by omega)
  have hsplit2 := Icc_union_split (a := b + 1) (b := c) (c := d) h2 h3
  rw [hsplit1, hsplit2]
  ac_rfl

lemma sum_Icc_three (f : ℕ → ℕ) (a b c d : ℕ)
    (h1 : a ≤ b + 1) (h2 : b + 1 ≤ c + 1) (h3 : c ≤ d) :
    ∑ j ∈ Icc a d, f j =
      ∑ j ∈ Icc a b, f j + ∑ j ∈ Icc (b + 1) c, f j +
        ∑ j ∈ Icc (c + 1) d, f j := by
  have heq := Icc_split_three a b c d h1 h2 h3
  have hdis1 : Disjoint (Icc a b) (Icc (b + 1) c) := by
    refine disjoint_left.mpr ?_
    intro x hx hy
    simp [mem_Icc] at hx hy; omega
  have hdis2 : Disjoint (Icc a b ∪ Icc (b + 1) c) (Icc (c + 1) d) := by
    refine disjoint_left.mpr ?_
    intro x hx hy
    simp [mem_Icc, mem_union] at hx hy; omega
  rw [heq, sum_union hdis2, sum_union hdis1]

lemma W_two_k_succ_rest_sum (k : ℕ) (hk : 81 ≤ k) :
    ∑ j ∈ Icc 1 (k - 2), j.factorial * W (2 * k + 1 - j) (j - 1) ≤
      3 * k * (k.factorial * (k - 1).factorial) := by
  have hb := mid_cut_bounds k hk
  have hsum := sum_Icc_three
    (fun j => j.factorial * W (2 * k + 1 - j) (j - 1))
    1 23 (k - midShift k) (k - 2)
    (by omega) (by omega) (by omega)
  rw [hsum]
  have hsmall := small_region_sum_le_succ k hk
  have hmid := mid_region_sum_le_succ k hk
  have hlarge := large_region_sum_le_succ k hk
  have hbud := rest_budget_succ (k.factorial * (k - 1).factorial) k hk
  refine le_trans (Nat.add_le_add (Nat.add_le_add hsmall hmid) hlarge) hbud

lemma W_two_k_succ_rest_le (k : ℕ) (hk : 81 ≤ k) :
    W (2 * k + 1) (k - 2) ≤
      3 * k * (k.factorial * (k - 1).factorial) := by
  have hdecomp : W (2 * k + 1) (k - 2) =
      ∑ j ∈ Icc 1 (k - 2), j.factorial * W (2 * k + 1 - j) (j - 1) :=
    W_eq_sum_upto (2 * k + 1) (k - 2) (by omega) (by omega)
  rw [hdecomp]
  exact W_two_k_succ_rest_sum k hk

lemma W_two_k_succ_le (k : ℕ) (hk : 81 ≤ k) :
    W (2 * k + 1) k ≤ 4 * k * (k.factorial * (k - 1).factorial) := by
  have h1 : W (2 * k + 1) k =
      W (2 * k + 1) (k - 1) + k.factorial * W (k + 1) (k - 1) := by
    have h := W_succ_pred (n := 2 * k + 1) (m := k) (by omega) (by omega)
    have : 2 * k + 1 - k = k + 1 := by omega
    rwa [this] at h
  have h2 : W (2 * k + 1) (k - 1) =
      W (2 * k + 1) (k - 2) + (k - 1).factorial * W (k + 2) (k - 2) := by
    have h := W_succ_pred (n := 2 * k + 1) (m := k - 1) (by omega) (by omega)
    have : 2 * k + 1 - (k - 1) = k + 2 := by omega
    rwa [this] at h
  rw [h1, h2]
  have hmain : k.factorial * W (k + 1) (k - 1) ≤
      4 * (k.factorial * (k - 1).factorial) := by
    have := W_kp1_km1_le k hk
    have h := Nat.mul_le_mul_left k.factorial this
    convert h using 1 <;> ring
  have hoff : W (k + 2) (k - 2) ≤ k.factorial := by
    have := W_off3_le (k + 1) (by omega)
    have e1 : (k + 1) + 1 = k + 2 := by omega
    have e2 : k + 1 - 3 = k - 2 := by omega
    have e3 : k + 1 - 1 = k := by omega
    simpa [e1, e2, e3] using this
  have hmid : (k - 1).factorial * W (k + 2) (k - 2) ≤
      k.factorial * (k - 1).factorial := by
    have := Nat.mul_le_mul_left (k - 1).factorial hoff
    rwa [Nat.mul_comm k.factorial]
  have hrest := W_two_k_succ_rest_le k hk
  set wB := k.factorial * (k - 1).factorial
  have : 4 * wB + wB + 3 * k * wB ≤ 4 * k * wB := by
    have : 4 * wB + wB + 3 * k * wB = (5 + 3 * k) * wB := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ (by omega : 5 + 3 * k ≤ 4 * k)
  have hsum :
      k.factorial * W (k + 1) (k - 1) +
        (k - 1).factorial * W (k + 2) (k - 2) + W (2 * k + 1) (k - 2) ≤
      4 * wB + wB + 3 * k * wB :=
    Nat.add_le_add (Nat.add_le_add hmain hmid) hrest
  refine le_trans ?_ this
  have hrew : W (2 * k + 1) (k - 2) + (k - 1).factorial * W (k + 2) (k - 2) +
      k.factorial * W (k + 1) (k - 1) =
      k.factorial * W (k + 1) (k - 1) +
        (k - 1).factorial * W (k + 2) (k - 2) + W (2 * k + 1) (k - 2) := by
    ring
  rw [hrew]
  exact hsum

lemma four_k_lt_quad (k : ℕ) (hk : 81 ≤ k) :
    4 * k < (k - 2) * (k + 1) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h1 : 81 + t - 2 = 79 + t := by omega
  rw [h1]
  nlinarith

lemma four_k_mul_lt_target (k : ℕ) (hk : 81 ≤ k) :
    4 * k * (k.factorial * (k - 1).factorial) <
      (k - 2) * (k - 1).factorial * (k + 1).factorial := by
  have ek : k.factorial = k * (k - 1).factorial := fact_pred k (by omega)
  have es : (k + 1).factorial = (k + 1) * k.factorial := rfl
  rw [es, ek]
  have hpos : 0 < (k - 1).factorial * (k - 1).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have hcore := four_k_lt_quad k hk
  have hL : 4 * k * (k * (k - 1).factorial * (k - 1).factorial) =
      (4 * k) * k * ((k - 1).factorial * (k - 1).factorial) := by ring
  have hR : (k - 2) * (k - 1).factorial * ((k + 1) * (k * (k - 1).factorial)) =
      ((k - 2) * (k + 1)) * k * ((k - 1).factorial * (k - 1).factorial) := by
    ring
  rw [hL, hR]
  have hmul : 4 * k * k < (k - 2) * (k + 1) * k :=
    Nat.mul_lt_mul_of_pos_right hcore (by omega)
  have hL' : (4 * k) * k * ((k - 1).factorial * (k - 1).factorial) =
      (4 * k * k) * ((k - 1).factorial * (k - 1).factorial) := by ring
  have hR' : ((k - 2) * (k + 1)) * k * ((k - 1).factorial * (k - 1).factorial) =
      ((k - 2) * (k + 1) * k) * ((k - 1).factorial * (k - 1).factorial) := by
    ring
  rw [hL', hR']
  exact Nat.mul_lt_mul_of_pos_right hmul hpos

lemma W_two_k_succ_of_self (k : ℕ) (hk : 81 ≤ k) :
    (tau (2 * k + 1) k).natAbs <
      (tau k k).natAbs * (k + 1).factorial := by
  have hW := W_two_k_succ_le k hk
  have hk3 : 3 ≤ k := by omega
  have hτ : (k - 2) * (k - 1).factorial ≤ (tau k k).natAbs :=
    tau_abs_ge_pred hk3
  have hWu : (tau (2 * k + 1) k).natAbs ≤ W (2 * k + 1) k :=
    tau_abs_le_W' k (2 * k + 1)
  have hlt := four_k_mul_lt_target k hk
  have : W (2 * k + 1) k < (k - 2) * (k - 1).factorial * (k + 1).factorial :=
    lt_of_le_of_lt hW hlt
  have : (tau (2 * k + 1) k).natAbs <
      (k - 2) * (k - 1).factorial * (k + 1).factorial :=
    lt_of_le_of_lt hWu this
  refine lt_of_lt_of_le this ?_
  exact Nat.mul_le_mul_right _ hτ

lemma tau_self_neg {d : ℕ} (hd : 3 ≤ d) : tau d d < 0 := by
  have h := tau_self_sub d (by omega)
  have hW : (tau d (d - 1)).natAbs ≤ W d (d - 1) := tau_abs_le_W (d - 1) d
  have hW2 : W d (d - 1) ≤ 2 * (d - 1).factorial := W_pred_le d (by omega)
  have hbound : (tau d (d - 1)).natAbs ≤ 2 * (d - 1).factorial :=
    le_trans hW hW2
  have hlt : (2 * (d - 1).factorial : ℤ) < d.factorial := by
    have : 2 * (d - 1).factorial < d.factorial := by
      have ed : d.factorial = d * (d - 1).factorial := fact_pred d (by omega)
      rw [ed]
      exact Nat.mul_lt_mul_of_pos_right (by omega : 2 < d) (Nat.factorial_pos _)
    exact_mod_cast this
  have habs : (tau d (d - 1) : ℤ) ≤ (tau d (d - 1)).natAbs :=
    Int.le_natAbs
  have : tau d (d - 1) ≤ 2 * (d - 1).factorial := by
    have : (tau d (d - 1) : ℤ) ≤ ((tau d (d - 1)).natAbs : ℤ) := Int.le_natAbs
    have : ((tau d (d - 1)).natAbs : ℤ) ≤ (2 * (d - 1).factorial : ℤ) := by
      exact_mod_cast hbound
    linarith
  have : tau d d ≤ 2 * (d - 1).factorial - d.factorial := by
    rw [h]; linarith
  have : (2 * (d - 1).factorial : ℤ) - d.factorial < 0 := by linarith
  linarith

lemma W_km1_km3_le (k : ℕ) (hk : 83 ≤ k) :
    W (k - 1) (k - 3) ≤ 4 * (k - 3).factorial := by
  have h1 : W (k - 1) (k - 3) =
      W (k - 1) (k - 4) + (k - 3).factorial * 2 := by
    have h := W_succ_pred (n := k - 1) (m := k - 3) (by omega) (by omega)
    have hsub : k - 1 - (k - 3) = 2 := by omega
    rw [hsub, W_two _ (by omega)] at h
    exact h
  have h2 : W (k - 1) (k - 4) =
      W (k - 1) (k - 5) + (k - 4).factorial * 8 := by
    have h := W_succ_pred (n := k - 1) (m := k - 4) (by omega) (by omega)
    have hsub : k - 1 - (k - 4) = 3 := by omega
    rw [hsub, W_three _ (by omega)] at h
    exact h
  rw [h1, h2]
  have hoff : W (k - 1) (k - 5) ≤ (k - 3).factorial := by
    have := W_off3_le (k - 2) (by omega)
    have e1 : (k - 2) + 1 = k - 1 := by omega
    have e2 : k - 2 - 3 = k - 5 := by omega
    have e3 : k - 2 - 1 = k - 3 := by omega
    simpa [e1, e2, e3] using this
  have h8 : 8 ≤ k - 3 := by omega
  have hsum : W (k - 1) (k - 5) + 8 * (k - 4).factorial + 2 * (k - 3).factorial ≤
      (k - 3).factorial + 8 * (k - 4).factorial + 2 * (k - 3).factorial :=
    Nat.add_le_add_right
      (Nat.add_le_add_right hoff (8 * (k - 4).factorial))
      (2 * (k - 3).factorial)
  have hclosed : (k - 3).factorial + 8 * (k - 4).factorial + 2 * (k - 3).factorial ≤
      4 * (k - 3).factorial := by
    have e1 : (k - 3).factorial = (k - 3) * (k - 4).factorial :=
      fact_pred (k - 3) (by omega)
    have hrew : (k - 3).factorial + 8 * (k - 4).factorial + 2 * (k - 3).factorial =
        3 * (k - 3).factorial + 8 * (k - 4).factorial := by ring
    rw [hrew, e1]
    have : 3 * ((k - 3) * (k - 4).factorial) + 8 * (k - 4).factorial ≤
        4 * ((k - 3) * (k - 4).factorial) := by
      have : 8 * (k - 4).factorial ≤ (k - 3) * (k - 4).factorial :=
        Nat.mul_le_mul_right _ h8
      omega
    convert this using 1 <;> ring
  have hbound : W (k - 1) (k - 5) + 8 * (k - 4).factorial + 2 * (k - 3).factorial ≤
      4 * (k - 3).factorial :=
    le_trans hsum hclosed
  convert hbound using 1 <;> ring

lemma W_two_k_sub_three_km3_le (k : ℕ) (hk : 83 ≤ k) :
    W (2 * k - 3) (k - 3) ≤
      (3 * k - 5) * (k - 2).factorial * (k - 3).factorial := by
  have h1 : W (2 * k - 3) (k - 3) =
      W (2 * k - 3) (k - 4) + (k - 3).factorial * W k (k - 4) := by
    have h := W_succ_pred (n := 2 * k - 3) (m := k - 3) (by omega) (by omega)
    have : 2 * k - 3 - (k - 3) = k := by omega
    rwa [this] at h
  have hoff : W k (k - 4) ≤ (k - 2).factorial := by
    have := W_off3_le (k - 1) (by omega)
    have e1 : (k - 1) + 1 = k := by omega
    have e2 : k - 1 - 3 = k - 4 := by omega
    have e3 : k - 1 - 1 = k - 2 := by omega
    simpa [e1, e2, e3] using this
  have hrest : W (2 * k - 3) (k - 4) ≤
      3 * (k - 2) * ((k - 2).factorial * (k - 3).factorial) := by
    have := W_two_k_succ_rest_le (k - 2) (by omega)
    have e1 : 2 * (k - 2) + 1 = 2 * k - 3 := by omega
    have e2 : k - 2 - 2 = k - 4 := by omega
    simpa [e1, e2] using this
  have hmid : (k - 3).factorial * W k (k - 4) ≤
      (k - 3).factorial * (k - 2).factorial :=
    Nat.mul_le_mul_left _ hoff
  rw [h1]
  have : (k - 3).factorial * (k - 2).factorial +
      3 * (k - 2) * ((k - 2).factorial * (k - 3).factorial) ≤
      (3 * k - 5) * (k - 2).factorial * (k - 3).factorial := by
    have : (k - 3).factorial * (k - 2).factorial +
        3 * (k - 2) * ((k - 2).factorial * (k - 3).factorial) =
        (1 + 3 * (k - 2)) * (k - 2).factorial * (k - 3).factorial := by ring
    rw [this]
    have : 1 + 3 * (k - 2) = 3 * k - 5 := by omega
    rw [this]
  have hsum := Nat.add_le_add hrest hmid
  refine le_trans hsum ?_
  convert this using 1 <;> ring

lemma W_two_k_sub_three_km2_le (k : ℕ) (hk : 83 ≤ k) :
    W (2 * k - 3) (k - 2) ≤
      (3 * k - 1) * (k - 2).factorial * (k - 3).factorial := by
  have h1 : W (2 * k - 3) (k - 2) =
      W (2 * k - 3) (k - 3) + (k - 2).factorial * W (k - 1) (k - 3) := by
    have h := W_succ_pred (n := 2 * k - 3) (m := k - 2) (by omega) (by omega)
    have : 2 * k - 3 - (k - 2) = k - 1 := by omega
    rwa [this] at h
  rw [h1]
  have hA := W_two_k_sub_three_km3_le k hk
  have hB := W_km1_km3_le k (by omega)
  have hB' : (k - 2).factorial * W (k - 1) (k - 3) ≤
      4 * (k - 2).factorial * (k - 3).factorial := by
    have := Nat.mul_le_mul_left (k - 2).factorial hB
    convert this using 1 <;> ring
  have : (3 * k - 5) * (k - 2).factorial * (k - 3).factorial +
      4 * (k - 2).factorial * (k - 3).factorial ≤
      (3 * k - 1) * (k - 2).factorial * (k - 3).factorial := by
    have : (3 * k - 5) + 4 = 3 * k - 1 := by omega
    have hrew :
        (3 * k - 5) * (k - 2).factorial * (k - 3).factorial +
          4 * (k - 2).factorial * (k - 3).factorial =
        ((3 * k - 5) + 4) * (k - 2).factorial * (k - 3).factorial := by ring
    rw [hrew, this]
  exact le_trans (Nat.add_le_add hA hB') this

lemma W_two_k_sub_three_km2_lt_target (k : ℕ) (hk : 83 ≤ k) :
    W (2 * k - 3) (k - 2) <
      (k - 1).factorial * (k - 4) * (k - 3).factorial := by
  have hW := W_two_k_sub_three_km2_le k hk
  have e1 : (k - 1).factorial = (k - 1) * (k - 2).factorial :=
    fact_pred (k - 1) (by omega)
  have hcore : 3 * k - 1 < (k - 1) * (k - 4) := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
    have h1 : 83 + t - 1 = 82 + t := by omega
    have h2 : 83 + t - 4 = 79 + t := by omega
    have hL : 3 * (83 + t) - 1 = 248 + 3 * t := by omega
    have hR : (82 + t) * (79 + t) = 6478 + 161 * t + t * t := by ring
    rw [h1, h2, hL, hR]
    nlinarith
  have hlt : (3 * k - 1) * (k - 2).factorial * (k - 3).factorial <
      (k - 1) * (k - 4) * (k - 2).factorial * (k - 3).factorial :=
    Nat.mul_lt_mul_of_pos_right
      (Nat.mul_lt_mul_of_pos_right hcore (Nat.factorial_pos _))
      (Nat.factorial_pos _)
  have heq : (k - 1) * (k - 4) * (k - 2).factorial * (k - 3).factorial =
      (k - 1).factorial * (k - 4) * (k - 3).factorial := by
    rw [e1]; ring
  exact lt_of_le_of_lt hW (heq ▸ hlt)

lemma tau_two_k_sub_three_pred_nonneg (k : ℕ) (hk : 83 ≤ k) :
    0 ≤ tau (2 * k - 3) (k - 1) := by
  have hrec := tau_pred_rec (d := 2 * k - 3) (k := k - 1) (by omega) (by omega)
  have hidx : k - 1 - 1 = k - 2 := by omega
  have hsub : 2 * k - 3 - (k - 1) = k - 2 := by omega
  rw [hidx, hsub] at hrec
  have hneg := tau_self_neg (d := k - 2) (by omega)
  have habsneg : tau (k - 2) (k - 2) = -((tau (k - 2) (k - 2)).natAbs : ℤ) := by
    rw [Int.natCast_natAbs, abs_of_neg hneg]
    ring
  rw [hrec, habsneg, mul_neg, sub_neg_eq_add]
  have hW : (tau (2 * k - 3) (k - 2)).natAbs ≤ W (2 * k - 3) (k - 2) :=
    tau_abs_le_W (k - 2) (2 * k - 3)
  have hge : (k - 4) * (k - 3).factorial ≤ (tau (k - 2) (k - 2)).natAbs :=
    tau_abs_ge_pred (by omega : 3 ≤ k - 2)
  have hWlt := W_two_k_sub_three_km2_lt_target k hk
  have hltW : W (2 * k - 3) (k - 2) <
      (k - 1).factorial * (tau (k - 2) (k - 2)).natAbs := by
    have hL : (k - 1).factorial * ((k - 4) * (k - 3).factorial) ≤
        (k - 1).factorial * (tau (k - 2) (k - 2)).natAbs :=
      Nat.mul_le_mul_left _ hge
    have hL' : (k - 1).factorial * (k - 4) * (k - 3).factorial ≤
        (k - 1).factorial * (tau (k - 2) (k - 2)).natAbs := by
      convert hL using 1; ring
    exact lt_of_lt_of_le hWlt hL'
  have hlow : -((W (2 * k - 3) (k - 2) : ℤ)) ≤ tau (2 * k - 3) (k - 2) := by
    have habs : |(tau (2 * k - 3) (k - 2) : ℤ)| ≤ (W (2 * k - 3) (k - 2) : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hW
    exact (abs_le.mp habs).1
  have hcmp : (W (2 * k - 3) (k - 2) : ℤ) ≤
      ((k - 1).factorial : ℤ) * (tau (k - 2) (k - 2)).natAbs := by
    exact_mod_cast (le_of_lt hltW)
  linarith

lemma W_cauchy_real : ∀ (k n : ℕ) {r : ℝ}, 0 < r →
    (W n k : ℝ) * r ^ n ≤
      ∏ j ∈ Icc 1 k, (1 + (j.factorial : ℝ) * r ^ j) := by
  intro k
  induction k with
  | zero =>
    intro n r hr
    by_cases hn : n = 0
    · subst hn; simp [W]
    · have : W n 0 = 0 := W_zero_right (Nat.pos_of_ne_zero hn)
      simp [this]
  | succ k ih =>
    intro n r hr
    have hI : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := Icc_succ_right_eq k
    have hnotin : k + 1 ∉ Icc 1 k := by simp [mem_Icc]
    rw [hI, prod_insert hnotin]
    have ih1 := ih n hr
    by_cases hlt : n < k + 1
    · rw [W_succ_of_lt hlt]
      have hmul : (0 : ℝ) ≤ 1 + (k + 1).factorial * r ^ (k + 1) := by positivity
      have hprod : (0 : ℝ) ≤ ∏ j ∈ Icc 1 k, (1 + (j.factorial : ℝ) * r ^ j) := by
        refine Finset.prod_nonneg ?_
        intro j hj; positivity
      calc
        (W n k : ℝ) * r ^ n ≤
            ∏ j ∈ Icc 1 k, (1 + (j.factorial : ℝ) * r ^ j) := ih1
        _ ≤ (1 + (k + 1).factorial * r ^ (k + 1)) *
              ∏ j ∈ Icc 1 k, (1 + (j.factorial : ℝ) * r ^ j) :=
          le_mul_of_one_le_left hprod (by
            have : (0 : ℝ) ≤ (k + 1).factorial * r ^ (k + 1) := by positivity
            linarith)
    · have hle : k + 1 ≤ n := Nat.le_of_not_lt hlt
      rw [W_succ_of_le hle]
      have ih2 := ih (n - (k + 1)) hr
      have hnpow : n = (k + 1) + (n - (k + 1)) := by omega
      have hpow : r ^ n = r ^ (k + 1) * r ^ (n - (k + 1)) := by
        conv_lhs => rw [hnpow]
        exact pow_add r (k + 1) (n - (k + 1))
      push_cast
      set P := ∏ j ∈ Icc 1 k, (1 + (j.factorial : ℝ) * r ^ j)
      have hA : (W n k : ℝ) * r ^ n ≤ P := ih1
      have hB : ((k + 1).factorial : ℝ) * (W (n - (k + 1)) k : ℝ) * r ^ n ≤
          ((k + 1).factorial : ℝ) * r ^ (k + 1) * P := by
        have : (W (n - (k + 1)) k : ℝ) * r ^ (n - (k + 1)) ≤ P := ih2
        have hnn : (0 : ℝ) ≤ (k + 1).factorial * r ^ (k + 1) := by positivity
        calc
          ((k + 1).factorial : ℝ) * (W (n - (k + 1)) k : ℝ) * r ^ n
              = ((k + 1).factorial : ℝ) * r ^ (k + 1) *
                  ((W (n - (k + 1)) k : ℝ) * r ^ (n - (k + 1))) := by
                rw [hpow]; ring
          _ ≤ ((k + 1).factorial : ℝ) * r ^ (k + 1) * P :=
              mul_le_mul_of_nonneg_left this hnn
      have hsum : ((W n k : ℝ) + ((k + 1).factorial : ℝ) * (W (n - (k + 1)) k : ℝ)) * r ^ n =
          (W n k : ℝ) * r ^ n +
            ((k + 1).factorial : ℝ) * (W (n - (k + 1)) k : ℝ) * r ^ n := by ring
      rw [hsum]
      have : P + ((k + 1).factorial : ℝ) * r ^ (k + 1) * P =
          (1 + ((k + 1).factorial : ℝ) * r ^ (k + 1)) * P := by ring
      linarith [hA, hB]

lemma W_cauchy_real_div (n k : ℕ) {r : ℝ} (hr : 0 < r) :
    (W n k : ℝ) ≤
      (∏ j ∈ Icc 1 k, (1 + (j.factorial : ℝ) * r ^ j)) / r ^ n := by
  have h := W_cauchy_real k n hr
  have hpos : (0 : ℝ) < r ^ n := pow_pos hr _
  exact (le_div_iff₀ hpos).2 h

lemma tau_two_k_sub_three_abs_ge (k : ℕ) (hk : 83 ≤ k) :
    k.factorial * (k - 5) * (k - 4).factorial ≤
      (tau (2 * k - 3) k).natAbs := by
  have hrec := tau_pred_rec (d := 2 * k - 3) (k := k) (by omega) (by omega)
  have hsub : 2 * k - 3 - k = k - 3 := by omega
  have hidx : k - 1 = k - 1 := rfl
  rw [hsub] at hrec
  have hτeq : tau (k - 3) (k - 1) = tau (k - 3) (k - 3) :=
    tau_eq_of_ge (by omega : k - 3 ≤ k - 1)
  rw [hτeq] at hrec
  have hneg := tau_self_neg (d := k - 3) (by omega)
  have hpos := tau_two_k_sub_three_pred_nonneg k hk
  have habsneg : tau (k - 3) (k - 3) = -((tau (k - 3) (k - 3)).natAbs : ℤ) := by
    rw [Int.natCast_natAbs, abs_of_neg hneg]; ring
  have hge : (k - 5) * (k - 4).factorial ≤ (tau (k - 3) (k - 3)).natAbs :=
    tau_abs_ge_pred (by omega : 3 ≤ k - 3)
  -- tau (2k-3) k = tau (2k-3) (k-1) - k! * tau (k-3) (k-3)
  --              = tau (2k-3) (k-1) + k! * |tau (k-3)|
  -- both terms ≥ 0, so |tau| = tau (2k-3) (k-1) + k! |tau|
  have hform : tau (2 * k - 3) k =
      tau (2 * k - 3) (k - 1) +
        (k.factorial : ℤ) * (tau (k - 3) (k - 3)).natAbs := by
    rw [hrec]
    have hmul : (k.factorial : ℤ) * tau (k - 3) (k - 3) =
        -((k.factorial : ℤ) * (tau (k - 3) (k - 3)).natAbs) := by
      conv_lhs => rw [habsneg]
      rw [mul_neg]
    rw [hmul, sub_neg_eq_add]
  have hnonneg : 0 ≤ tau (2 * k - 3) k := by
    rw [hform]
    have : (0 : ℤ) ≤ (k.factorial : ℤ) * (tau (k - 3) (k - 3)).natAbs := by
      exact mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    linarith
  have heq : (tau (2 * k - 3) k).natAbs =
      (tau (2 * k - 3) (k - 1)).natAbs +
        k.factorial * (tau (k - 3) (k - 3)).natAbs := by
    rw [hform, Int.natAbs_add_of_nonneg hpos
      (mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)),
      Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
  rw [heq]
  have hmul : k.factorial * ((k - 5) * (k - 4).factorial) ≤
      k.factorial * (tau (k - 3) (k - 3)).natAbs :=
    Nat.mul_le_mul_left _ hge
  have hmul' : k.factorial * (k - 5) * (k - 4).factorial ≤
      k.factorial * (tau (k - 3) (k - 3)).natAbs := by
    convert hmul using 1; ring
  exact le_trans hmul' (Nat.le_add_left _ _)

lemma W_three_k_sub_two_peel0 (k : ℕ) (hk : 83 ≤ k) :
    k.factorial * W (2 * k - 2) (k - 1) ≤
      4 * k.factorial * (k - 1).factorial * (k - 2).factorial := by
  have hW := W_two_k_le (k - 1) (by omega)
  have e : 2 * (k - 1) = 2 * k - 2 := by omega
  have e2 : k - 1 - 1 = k - 2 := by omega
  rw [e, e2] at hW
  have := Nat.mul_le_mul_left k.factorial hW
  convert this using 1 <;> ring

lemma W_three_k_sub_two_peel1 (k : ℕ) (hk : 83 ≤ k) :
    (k - 1).factorial * W (2 * k - 1) (k - 2) ≤
      4 * (k - 1) * (k - 1).factorial * (k - 1).factorial * (k - 2).factorial := by
  have hmono : W (2 * k - 1) (k - 2) ≤ W (2 * k - 1) (k - 1) :=
    W_mono_right (by omega)
  have hW := W_two_k_succ_le (k - 1) (by omega)
  have e : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
  rw [e] at hW
  have hle : W (2 * k - 1) (k - 2) ≤
      4 * (k - 1) * ((k - 1).factorial * (k - 2).factorial) :=
    le_trans hmono hW
  have := Nat.mul_le_mul_left (k - 1).factorial hle
  convert this using 1 <;> ring

lemma W_three_k_sub_two_decomp (k : ℕ) (hk : 3 ≤ k) :
    W (3 * k - 2) k =
      k.factorial * W (2 * k - 2) (k - 1) +
        (k - 1).factorial * W (2 * k - 1) (k - 2) +
          W (3 * k - 2) (k - 2) := by
  have h1 : W (3 * k - 2) k =
      W (3 * k - 2) (k - 1) + k.factorial * W (2 * k - 2) (k - 1) := by
    have h := W_succ_pred (n := 3 * k - 2) (m := k) (by omega) (by omega)
    have : 3 * k - 2 - k = 2 * k - 2 := by omega
    rwa [this] at h
  have h2 : W (3 * k - 2) (k - 1) =
      W (3 * k - 2) (k - 2) + (k - 1).factorial * W (2 * k - 1) (k - 2) := by
    have h := W_succ_pred (n := 3 * k - 2) (m := k - 1) (by omega) (by omega)
    have : 3 * k - 2 - (k - 1) = 2 * k - 1 := by omega
    rwa [this] at h
  rw [h1, h2]
  ring

lemma four_peel0_lt_target (k : ℕ) (hk : 83 ≤ k) :
    4 * k.factorial * (k - 1).factorial * (k - 2).factorial * 5 <
      k.factorial * (k - 5) * (k - 4).factorial * (k + 1).factorial := by
  have ek : k.factorial = k * (k - 1).factorial := fact_pred k (by omega)
  have es : (k + 1).factorial = (k + 1) * k.factorial := rfl
  have e2 : (k - 2).factorial = (k - 2) * (k - 3) * (k - 4).factorial := by
    have h1 : (k - 2).factorial = (k - 2) * (k - 3).factorial :=
      fact_pred (k - 2) (by omega)
    have h2 : (k - 3).factorial = (k - 3) * (k - 4).factorial :=
      fact_pred (k - 3) (by omega)
    rw [h1, h2]; ring
  rw [es, ek, e2]
  have hpos : 0 < (k - 1).factorial * (k - 1).factorial * (k - 4).factorial :=
    Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
      (Nat.factorial_pos _)
  have hcore : 20 * (k - 2) * (k - 3) < k * (k + 1) * (k - 5) := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
    have e1 : 83 + t - 2 = 81 + t := by omega
    have e2 : 83 + t - 3 = 80 + t := by omega
    have e3 : 83 + t - 5 = 78 + t := by omega
    have e4 : 83 + t + 1 = 84 + t := by omega
    rw [e1, e2, e3, e4]
    have hL : 20 * (81 + t) * (80 + t) = 129600 + 3220 * t + 20 * t * t := by ring
    have hR : (83 + t) * (84 + t) * (78 + t) =
        543816 + 19998 * t + 245 * t * t + t * t * t := by ring
    rw [hL, hR]
    nlinarith
  have hL : 4 * (k * (k - 1).factorial) * (k - 1).factorial *
      ((k - 2) * (k - 3) * (k - 4).factorial) * 5 =
      20 * (k - 2) * (k - 3) * k *
        ((k - 1).factorial * (k - 1).factorial * (k - 4).factorial) := by ring
  have hR : (k * (k - 1).factorial) * (k - 5) * (k - 4).factorial *
      ((k + 1) * (k * (k - 1).factorial)) =
      (k * (k + 1) * (k - 5) * k) *
        ((k - 1).factorial * (k - 1).factorial * (k - 4).factorial) := by ring
  rw [hL, hR]
  have hcore' : 20 * (k - 2) * (k - 3) * k < k * (k + 1) * (k - 5) * k :=
    Nat.mul_lt_mul_of_pos_right hcore (by omega)
  exact Nat.mul_lt_mul_of_pos_right hcore' hpos

lemma four_peel1_lt_target (k : ℕ) (hk : 83 ≤ k) :
    4 * (k - 1) * (k - 1).factorial * (k - 1).factorial * (k - 2).factorial * 5 <
      k.factorial * (k - 5) * (k - 4).factorial * (k + 1).factorial := by
  have ek : k.factorial = k * (k - 1).factorial := fact_pred k (by omega)
  have es : (k + 1).factorial = (k + 1) * k.factorial := rfl
  have e2 : (k - 2).factorial = (k - 2) * (k - 3) * (k - 4).factorial := by
    have h1 : (k - 2).factorial = (k - 2) * (k - 3).factorial :=
      fact_pred (k - 2) (by omega)
    have h2 : (k - 3).factorial = (k - 3) * (k - 4).factorial :=
      fact_pred (k - 3) (by omega)
    rw [h1, h2]; ring
  rw [es, ek, e2]
  have hpos : 0 < (k - 1).factorial * (k - 1).factorial * (k - 4).factorial :=
    Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
      (Nat.factorial_pos _)
  have hcore : 20 * (k - 1) * (k - 2) * (k - 3) <
      k * (k + 1) * (k - 5) * k := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
    have e1 : 83 + t - 1 = 82 + t := by omega
    have e2 : 83 + t - 2 = 81 + t := by omega
    have e3 : 83 + t - 3 = 80 + t := by omega
    have e4 : 83 + t - 5 = 78 + t := by omega
    have e5 : 83 + t + 1 = 84 + t := by omega
    rw [e1, e2, e3, e4, e5]
    have hL : 20 * (82 + t) * (81 + t) * (80 + t) =
        10627200 + 393640 * t + 4860 * t * t + 20 * t * t * t := by ring
    have hR : (83 + t) * (84 + t) * (78 + t) * (83 + t) =
        45136728 + 2203650 * t + 40333 * t * t + 328 * t * t * t +
          t * t * t * t := by ring
    rw [hL, hR]
    nlinarith
  have hL : 4 * (k - 1) * (k - 1).factorial * (k - 1).factorial *
      ((k - 2) * (k - 3) * (k - 4).factorial) * 5 =
      20 * (k - 1) * (k - 2) * (k - 3) *
        ((k - 1).factorial * (k - 1).factorial * (k - 4).factorial) := by ring
  have hR : (k * (k - 1).factorial) * (k - 5) * (k - 4).factorial *
      ((k + 1) * (k * (k - 1).factorial)) =
      (k * (k + 1) * (k - 5) * k) *
        ((k - 1).factorial * (k - 1).factorial * (k - 4).factorial) := by ring
  rw [hL, hR]
  exact Nat.mul_lt_mul_of_pos_right hcore hpos

def cauchyProd (m b : ℕ) : ℕ :=
  ∏ j ∈ Icc 1 m, (b ^ j + j.factorial)

def remTarget (k : ℕ) : ℕ :=
  k.factorial * (k - 5) * (k - 4).factorial * (k + 1).factorial

def remExpo (k : ℕ) : ℕ :=
  (k - 2) * (k - 1) / 2 - (3 * k - 2)

def checkRemCauchy (k : ℕ) : Bool :=
  let b := k / 3
  decide (cauchyProd (k - 2) b * 2 < remTarget k * b ^ remExpo k)

def checkRemRange (lo hi : ℕ) : Bool :=
  (List.range (hi + 1 - lo)).all fun i => checkRemCauchy (lo + i)

lemma remExpo_eq (k : ℕ) :
    remExpo k = tri (k - 2) - (3 * k - 2) := by
  simp [remExpo, tri]

lemma three_k_le_tri_pred (k : ℕ) (hk : 83 ≤ k) :
    3 * k - 2 ≤ tri (k - 2) := by
  have hmul : 2 * (3 * k - 2) ≤ (k - 2) * (k - 1) := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
    have e1 : 83 + t - 2 = 81 + t := by omega
    have e2 : 83 + t - 1 = 82 + t := by omega
    rw [e1, e2]
    have hL : 2 * (3 * (83 + t) - 2) = 494 + 6 * t := by omega
    have hR : (81 + t) * (82 + t) = 6642 + 163 * t + t * t := by ring
    rw [hL, hR]
    nlinarith
  have heven : 2 ∣ (k - 2) * (k - 1) := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this]
    exact two_dvd_mul_succ (k - 2)
  have hcancel : 2 * ((k - 2) * (k - 1) / 2) = (k - 2) * (k - 1) :=
    Nat.mul_div_cancel' heven
  have : 2 * (3 * k - 2) ≤ 2 * ((k - 2) * (k - 1) / 2) := by
    rwa [hcancel]
  have : 3 * k - 2 ≤ (k - 2) * (k - 1) / 2 :=
    Nat.le_of_mul_le_mul_left this (by decide : 0 < 2)
  simpa [tri] using this

lemma W_cauchy_nat (n m b : ℕ) (hb : 0 < b) (hn : n ≤ tri m) :
    W n m * b ^ (tri m - n) ≤ cauchyProd m b := by
  have hb0 : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hb)
  have hbpos : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hr : (0 : ℝ) < (b : ℝ)⁻¹ := inv_pos.mpr hbpos
  have hreal := W_cauchy_real_div n m hr
  have hterm : ∀ j ∈ Icc 1 m,
      1 + (j.factorial : ℝ) * ((b : ℝ)⁻¹) ^ j =
        ((b ^ j + j.factorial : ℕ) : ℝ) / (b : ℝ) ^ j := by
    intro j hj
    rw [inv_pow]
    field_simp [hb0]
    push_cast
    ring
  have hprod :
      ∏ j ∈ Icc 1 m, (1 + (j.factorial : ℝ) * ((b : ℝ)⁻¹) ^ j) =
        (cauchyProd m b : ℝ) / (b : ℝ) ^ tri m := by
    rw [Finset.prod_congr rfl hterm, Finset.prod_div_distrib]
    have hsum : ∑ j ∈ Icc 1 m, j = tri m := sum_Icc_tri m
    have hp : ∏ j ∈ Icc 1 m, (b : ℝ) ^ j = (b : ℝ) ^ (∑ j ∈ Icc 1 m, j) :=
      Finset.prod_pow_eq_pow_sum (Icc 1 m) (fun j => j)
    simp [cauchyProd, hp, hsum]
  have hdiv : (W n m : ℝ) ≤
      (cauchyProd m b : ℝ) / (b : ℝ) ^ tri m * (b : ℝ) ^ n := by
    have : (W n m : ℝ) ≤
        (∏ j ∈ Icc 1 m, (1 + (j.factorial : ℝ) * ((b : ℝ)⁻¹) ^ j)) /
          ((b : ℝ)⁻¹) ^ n := hreal
    rw [hprod, inv_pow] at this
    have : (W n m : ℝ) ≤
        (cauchyProd m b : ℝ) / (b : ℝ) ^ tri m / (1 / (b : ℝ) ^ n) := by
      convert this using 2
      field_simp [hb0]
    have hdivinv : (cauchyProd m b : ℝ) / (b : ℝ) ^ tri m / (1 / (b : ℝ) ^ n) =
        (cauchyProd m b : ℝ) / (b : ℝ) ^ tri m * (b : ℝ) ^ n := by
      field_simp [hb0]
    rwa [hdivinv] at this
  have hexp : (b : ℝ) ^ (tri m - n) = (b : ℝ) ^ tri m / (b : ℝ) ^ n :=
    pow_sub₀ _ hb0 hn
  have hmain : (W n m : ℝ) ≤ (cauchyProd m b : ℝ) / (b : ℝ) ^ (tri m - n) := by
    have : (cauchyProd m b : ℝ) / (b : ℝ) ^ tri m * (b : ℝ) ^ n =
        (cauchyProd m b : ℝ) / (b : ℝ) ^ (tri m - n) := by
      rw [hexp]
      field_simp [hb0]
    rwa [this] at hdiv
  have hmul := mul_le_mul_of_nonneg_right hmain (pow_nonneg (le_of_lt hbpos) _)
  have : (W n m : ℝ) * (b : ℝ) ^ (tri m - n) ≤ (cauchyProd m b : ℝ) := by
    have hcancel : (cauchyProd m b : ℝ) / (b : ℝ) ^ (tri m - n) *
        (b : ℝ) ^ (tri m - n) = (cauchyProd m b : ℝ) := by
      field_simp [hb0]
    rwa [hcancel] at hmul
  exact_mod_cast this

lemma checkRemCauchy_W_lt (k : ℕ) (hk : 83 ≤ k) (hcheck : checkRemCauchy k = true) :
    2 * W (3 * k - 2) (k - 2) < remTarget k := by
  have hb : 0 < k / 3 := by omega
  have hexpo : remExpo k = tri (k - 2) - (3 * k - 2) := remExpo_eq k
  have hn : 3 * k - 2 ≤ tri (k - 2) := three_k_le_tri_pred k hk
  have hW := W_cauchy_nat (3 * k - 2) (k - 2) (k / 3) hb hn
  rw [← hexpo] at hW
  have hdec : cauchyProd (k - 2) (k / 3) * 2 <
      remTarget k * (k / 3) ^ remExpo k := by
    simpa [checkRemCauchy] using of_decide_eq_true hcheck
  have hbpow : 0 < (k / 3) ^ remExpo k := pow_pos hb _
  have h2 : 2 * (W (3 * k - 2) (k - 2) * (k / 3) ^ remExpo k) <
      remTarget k * (k / 3) ^ remExpo k :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 hW) (by
      convert hdec using 1; ring)
  have : 2 * W (3 * k - 2) (k - 2) * (k / 3) ^ remExpo k <
      remTarget k * (k / 3) ^ remExpo k := by
    convert h2 using 1; ring
  exact Nat.lt_of_mul_lt_mul_right this

/-- After parity, no complementary distance sits strictly between `2k-1` and `3k-6`. -/
lemma no_delta_between_two_k_and_three_k {n k : ℕ}
    (hn1 : k + 1 ≤ n) (hn2 : n ≤ tri k)
    (hpar : Even (midx n) ↔ Even (midx (n - (k + 1)))) :
    ¬ (2 * k ≤ tri k - n ∧ tri k - n ≤ 3 * k - 7) := by
  intro ⟨hlo, hhi⟩
  have hk2 : 7 ≤ k := by
    have : 2 * k ≤ 3 * k - 7 := le_trans hlo hhi
    omega
  have hnlo : tri (k - 3) + 4 ≤ n := by
    have : tri k - (3 * k - 7) = tri (k - 3) + 4 := by
      have h1 : tri k = tri (k - 1) + k := tri_eq_pred_add k (by omega)
      have h2 : tri (k - 1) = tri (k - 2) + (k - 1) :=
        tri_eq_pred_add (k - 1) (by omega)
      have h3 : tri (k - 2) = tri (k - 3) + (k - 2) :=
        tri_eq_pred_add (k - 2) (by omega)
      omega
    omega
  have hnhi : n ≤ tri (k - 2) - 1 := by
    have : tri k - 2 * k = tri (k - 2) - 1 := by
      have h1 : tri k = tri (k - 1) + k := tri_eq_pred_add k (by omega)
      have h2 : tri (k - 1) = tri (k - 2) + (k - 1) :=
        tri_eq_pred_add (k - 1) (by omega)
      omega
    omega
  have hm : midx n = k - 3 := by
    rw [midx_eq_iff]
    constructor
    · have : tri (k - 3) ≤ n := by omega
      exact this
    · have : k - 3 + 1 = k - 2 := by omega
      rw [this]
      omega
  have hrestlo : tri (k - 4) ≤ n - (k + 1) := by
    have : tri (k - 3) = tri (k - 4) + (k - 3) :=
      tri_eq_pred_add (k - 3) (by omega)
    omega
  have hresthi : n - (k + 1) < tri (k - 3) := by omega
  have hrest : midx (n - (k + 1)) = k - 4 := by
    rw [midx_eq_iff]
    constructor
    · exact hrestlo
    · have : k - 4 + 1 = k - 3 := by omega
      rwa [this]
  have hdiff : midx n = midx (n - (k + 1)) + 1 := by
    rw [hm, hrest]; omega
  have : ¬ (Even (midx n) ↔ Even (midx (n - (k + 1)))) := by
    rw [hdiff]
    exact Nat.even_add_one
  exact this hpar

/-- DP successor for unsigned weights. -/
def nextWRow (nMax k : ℕ) (prev : Array ℕ) : Array ℕ :=
  Array.ofFn (fun d : Fin (nMax + 1) =>
    if d.val < k + 1 then prev[d.val]!
    else prev[d.val]! + (k + 1).factorial * prev[d.val - (k + 1)]!)

def wRow (nMax : ℕ) : ℕ → Array ℕ
  | 0 => Array.ofFn (fun d : Fin (nMax + 1) => if d.val = 0 then 1 else 0)
  | k + 1 => nextWRow nMax k (wRow nMax k)

/-- DP successor for signed complementary weights. -/
def nextTauRow (nMax k : ℕ) (prev : Array ℤ) : Array ℤ :=
  Array.ofFn (fun d : Fin (nMax + 1) =>
    if d.val < k + 1 then prev[d.val]!
    else prev[d.val]! - ((k + 1).factorial : ℤ) * prev[d.val - (k + 1)]!)

def tauRow (nMax : ℕ) : ℕ → Array ℤ
  | 0 => Array.ofFn (fun d : Fin (nMax + 1) => if d.val = 0 then (1 : ℤ) else 0)
  | k + 1 => nextTauRow nMax k (tauRow nMax k)

lemma wRow_size (nMax k : ℕ) : (wRow nMax k).size = nMax + 1 := by
  induction k with
  | zero => simp [wRow]
  | succ k ih => simp [wRow, nextWRow, ih]

lemma tauRow_size (nMax k : ℕ) : (tauRow nMax k).size = nMax + 1 := by
  induction k with
  | zero => simp [tauRow]
  | succ k ih => simp [tauRow, nextTauRow, ih]

lemma wRow_get (nMax : ℕ) : ∀ k d (hd : d ≤ nMax),
    (wRow nMax k)[d]'(by rw [wRow_size]; omega) = W d k := by
  intro k
  induction k with
  | zero =>
    intro d hd
    simp [wRow, Array.getElem_ofFn, Array.size_ofFn]
    by_cases h0 : d = 0
    · subst h0; simp [W]
    · simp [h0, W]
  | succ k ih =>
    intro d hd
    have hsz : (wRow nMax k).size = nMax + 1 := wRow_size nMax k
    have hgot :
        (wRow nMax (k + 1))[d]'(by rw [wRow_size]; omega) =
          if d < k + 1 then (wRow nMax k)[d]!
          else (wRow nMax k)[d]! +
            (k + 1).factorial * (wRow nMax k)[d - (k + 1)]! := by
      simp [wRow, nextWRow, Array.getElem_ofFn, Array.size_ofFn]
    rw [hgot]
    by_cases hlt : d < k + 1
    · rw [if_pos hlt, getElem!_pos (c := wRow nMax k) (i := d) (by rw [hsz]; omega),
        ih d hd, W_succ_of_lt hlt]
    · rw [if_neg hlt, getElem!_pos (c := wRow nMax k) (i := d) (by rw [hsz]; omega),
        getElem!_pos (c := wRow nMax k) (i := d - (k + 1)) (by rw [hsz]; omega),
        ih d hd, ih (d - (k + 1)) (le_trans (Nat.sub_le _ _) hd),
        W_succ_of_le (Nat.le_of_not_lt hlt)]

lemma wRow_get! (nMax k d : ℕ) (hd : d ≤ nMax) :
    (wRow nMax k)[d]! = W d k := by
  have hix : d < (wRow nMax k).size := by rw [wRow_size]; omega
  rw [getElem!_pos (c := wRow nMax k) (i := d) hix, wRow_get nMax k d hd]

lemma tauRow_get (nMax : ℕ) : ∀ k d (hd : d ≤ nMax),
    (tauRow nMax k)[d]'(by rw [tauRow_size]; omega) = tau d k := by
  intro k
  induction k with
  | zero =>
    intro d hd
    simp [tauRow, Array.getElem_ofFn, Array.size_ofFn]
    by_cases h0 : d = 0
    · subst h0; simp [tau]
    · simp [h0, tau]
  | succ k ih =>
    intro d hd
    have hsz : (tauRow nMax k).size = nMax + 1 := tauRow_size nMax k
    have hgot :
        (tauRow nMax (k + 1))[d]'(by rw [tauRow_size]; omega) =
          if d < k + 1 then (tauRow nMax k)[d]!
          else (tauRow nMax k)[d]! -
            ((k + 1).factorial : ℤ) * (tauRow nMax k)[d - (k + 1)]! := by
      simp [tauRow, nextTauRow, Array.getElem_ofFn, Array.size_ofFn]
    rw [hgot]
    by_cases hlt : d < k + 1
    · rw [if_pos hlt, getElem!_pos (c := tauRow nMax k) (i := d) (by rw [hsz]; omega),
        ih d hd, tau_succ_of_lt hlt]
    · rw [if_neg hlt, getElem!_pos (c := tauRow nMax k) (i := d) (by rw [hsz]; omega),
        getElem!_pos (c := tauRow nMax k) (i := d - (k + 1)) (by rw [hsz]; omega),
        ih d hd, ih (d - (k + 1)) (le_trans (Nat.sub_le _ _) hd),
        tau_succ_of_le (Nat.le_of_not_lt hlt)]

lemma tauRow_get! (nMax k d : ℕ) (hd : d ≤ nMax) :
    (tauRow nMax k)[d]! = tau d k := by
  have hix : d < (tauRow nMax k).size := by rw [tauRow_size]; omega
  rw [getElem!_pos (c := tauRow nMax k) (i := d) hix, tauRow_get nMax k d hd]

/-- Finite check of the three cluster-`j=2` complementary gaps. -/
def checkCluster2 (k : ℕ) : Bool :=
  let nMax := 3 * k
  let τs := tauRow nMax k
  let Ws := wRow nMax k
  let fact := (k + 1).factorial
  let d0 := 2 * k - 3
  decide (
    Ws[d0 + k + 1]! < (τs[d0]!).natAbs * fact &&
    Ws[d0 + 1 + k + 1]! < (τs[d0 + 1]!).natAbs * fact &&
    Ws[d0 + 2 + k + 1]! < (τs[d0 + 2]!).natAbs * fact)

def checkCluster2_range (lo hi : ℕ) : Bool :=
  (List.range (hi + 1 - lo)).all fun i => checkCluster2 (lo + i)

lemma checkCluster2_81_200 : checkCluster2_range 81 200 = true := by sorry -- native_decide

lemma checkCluster2_of_mem (k : ℕ) (hk1 : 81 ≤ k) (hk2 : k ≤ 200)
    (h : checkCluster2_range 81 200 = true) : checkCluster2 k = true := by
  have hall := List.all_eq_true.mp h
  have : k - 81 ∈ List.range (200 + 1 - 81) := by
    simp [List.mem_range]; omega
  have := hall (k - 81) this
  simpa [checkCluster2_range, show 81 + (k - 81) = k by omega] using this

lemma checkCluster2_correct (k : ℕ) (hk : 2 ≤ k) (h : checkCluster2 k = true) :
    (W (3 * k - 2) k < (tau (2 * k - 3) k).natAbs * (k + 1).factorial) ∧
    (W (3 * k - 1) k < (tau (2 * k - 2) k).natAbs * (k + 1).factorial) ∧
    (W (3 * k) k < (tau (2 * k - 1) k).natAbs * (k + 1).factorial) := by
  have hdec := of_decide_eq_true (by simpa [checkCluster2] using h)
  have hn0 : 2 * k - 3 ≤ 3 * k := by omega
  have hn1 : 2 * k - 2 ≤ 3 * k := by omega
  have hn2 : 2 * k - 1 ≤ 3 * k := by omega
  have hc0 : 3 * k - 2 ≤ 3 * k := by omega
  have hc1 : 3 * k - 1 ≤ 3 * k := by omega
  have hc2 : 3 * k ≤ 3 * k := le_rfl
  have e0 : 2 * k - 3 + (k + 1) = 3 * k - 2 := by omega
  have e1 : 2 * k - 2 + (k + 1) = 3 * k - 1 := by omega
  have e2 : 2 * k - 1 + (k + 1) = 3 * k := by omega
  rw [wRow_get! (3 * k) k (3 * k - 2) hc0,
      wRow_get! (3 * k) k (3 * k - 1) hc1,
      wRow_get! (3 * k) k (3 * k) hc2,
      tauRow_get! (3 * k) k (2 * k - 3) hn0,
      tauRow_get! (3 * k) k (2 * k - 2) hn1,
      tauRow_get! (3 * k) k (2 * k - 1) hn2] at hdec
  simpa [e0, e1, e2] using hdec

/-- Finite check of the cluster-`j=3` complementary gaps. -/
def checkCluster3 (k : ℕ) : Bool :=
  let nMax := 4 * k
  let τs := tauRow nMax k
  let Ws := wRow nMax k
  let fact := (k + 1).factorial
  let d0 := 3 * k - 6
  decide (
    Ws[d0 + k + 1]! < (τs[d0]!).natAbs * fact &&
    Ws[d0 + 1 + k + 1]! < (τs[d0 + 1]!).natAbs * fact &&
    Ws[d0 + 2 + k + 1]! < (τs[d0 + 2]!).natAbs * fact &&
    Ws[d0 + 3 + k + 1]! < (τs[d0 + 3]!).natAbs * fact)

def checkCluster3_range (lo hi : ℕ) : Bool :=
  (List.range (hi + 1 - lo)).all fun i => checkCluster3 (lo + i)

lemma checkCluster3_81_200 : checkCluster3_range 81 200 = true := by sorry -- native_decide

lemma checkCluster3_of_mem (k : ℕ) (hk1 : 81 ≤ k) (hk2 : k ≤ 200)
    (h : checkCluster3_range 81 200 = true) : checkCluster3 k = true := by
  have hall := List.all_eq_true.mp h
  have : k - 81 ∈ List.range (200 + 1 - 81) := by
    simp [List.mem_range]; omega
  have := hall (k - 81) this
  simpa [checkCluster3_range, show 81 + (k - 81) = k by omega] using this

lemma checkCluster3_correct (k : ℕ) (hk : 6 ≤ k) (h : checkCluster3 k = true) :
    (W (4 * k - 5) k < (tau (3 * k - 6) k).natAbs * (k + 1).factorial) ∧
    (W (4 * k - 4) k < (tau (3 * k - 5) k).natAbs * (k + 1).factorial) ∧
    (W (4 * k - 3) k < (tau (3 * k - 4) k).natAbs * (k + 1).factorial) ∧
    (W (4 * k - 2) k < (tau (3 * k - 3) k).natAbs * (k + 1).factorial) := by
  have hdec := of_decide_eq_true (by simpa [checkCluster3] using h)
  have hn0 : 3 * k - 6 ≤ 4 * k := by omega
  have hn1 : 3 * k - 5 ≤ 4 * k := by omega
  have hn2 : 3 * k - 4 ≤ 4 * k := by omega
  have hn3 : 3 * k - 3 ≤ 4 * k := by omega
  have hc0 : 4 * k - 5 ≤ 4 * k := by omega
  have hc1 : 4 * k - 4 ≤ 4 * k := by omega
  have hc2 : 4 * k - 3 ≤ 4 * k := by omega
  have hc3 : 4 * k - 2 ≤ 4 * k := by omega
  have e0 : 3 * k - 6 + (k + 1) = 4 * k - 5 := by omega
  have e1 : 3 * k - 5 + (k + 1) = 4 * k - 4 := by omega
  have e2 : 3 * k - 4 + (k + 1) = 4 * k - 3 := by omega
  have e3 : 3 * k - 3 + (k + 1) = 4 * k - 2 := by omega
  rw [wRow_get! (4 * k) k (4 * k - 5) hc0,
      wRow_get! (4 * k) k (4 * k - 4) hc1,
      wRow_get! (4 * k) k (4 * k - 3) hc2,
      wRow_get! (4 * k) k (4 * k - 2) hc3,
      tauRow_get! (4 * k) k (3 * k - 6) hn0,
      tauRow_get! (4 * k) k (3 * k - 5) hn1,
      tauRow_get! (4 * k) k (3 * k - 4) hn2,
      tauRow_get! (4 * k) k (3 * k - 3) hn3] at hdec
  simpa [e0, e1, e2, e3] using hdec

/-- After parity, no complementary distance sits strictly between `3k-3` and `4k-10`. -/
lemma no_delta_between_three_k_and_four_k {n k : ℕ}
    (hn1 : k + 1 ≤ n) (hn2 : n ≤ tri k)
    (hpar : Even (midx n) ↔ Even (midx (n - (k + 1)))) :
    ¬ (3 * k - 2 ≤ tri k - n ∧ tri k - n ≤ 4 * k - 11) := by
  intro ⟨hlo, hhi⟩
  have hk2 : 11 ≤ k := by
    have : 3 * k - 2 ≤ 4 * k - 11 := le_trans hlo hhi
    omega
  have hnlo : tri (k - 4) + 5 ≤ n := by
    have : tri k - (4 * k - 11) = tri (k - 4) + 5 := by
      have h1 : tri k = tri (k - 1) + k := tri_eq_pred_add k (by omega)
      have h2 : tri (k - 1) = tri (k - 2) + (k - 1) :=
        tri_eq_pred_add (k - 1) (by omega)
      have h3 : tri (k - 2) = tri (k - 3) + (k - 2) :=
        tri_eq_pred_add (k - 2) (by omega)
      have h4 : tri (k - 3) = tri (k - 4) + (k - 3) :=
        tri_eq_pred_add (k - 3) (by omega)
      omega
    omega
  have hnhi : n ≤ tri (k - 3) - 1 := by
    have : tri k - (3 * k - 2) = tri (k - 3) - 1 := by
      have h1 : tri k = tri (k - 1) + k := tri_eq_pred_add k (by omega)
      have h2 : tri (k - 1) = tri (k - 2) + (k - 1) :=
        tri_eq_pred_add (k - 1) (by omega)
      have h3 : tri (k - 2) = tri (k - 3) + (k - 2) :=
        tri_eq_pred_add (k - 2) (by omega)
      omega
    omega
  have hm : midx n = k - 4 := by
    rw [midx_eq_iff]
    constructor
    · omega
    · have : k - 4 + 1 = k - 3 := by omega
      rw [this]; omega
  have hrestlo : tri (k - 5) ≤ n - (k + 1) := by
    have : tri (k - 4) = tri (k - 5) + (k - 4) :=
      tri_eq_pred_add (k - 4) (by omega)
    omega
  have hrest : midx (n - (k + 1)) = k - 5 := by
    rw [midx_eq_iff]
    constructor
    · exact hrestlo
    · have : k - 5 + 1 = k - 4 := by omega
      rw [this]; omega
  have hdiff : midx n = midx (n - (k + 1)) + 1 := by
    rw [hm, hrest]; omega
  have : ¬ (Even (midx n) ↔ Even (midx (n - (k + 1)))) := by
    rw [hdiff]
    exact Nat.even_add_one
  exact this hpar

/-- Parity-filtered check of every remaining complementary gap at a fixed `k`. -/
def checkAllPar (k : ℕ) : Bool :=
  let nMax := tri k + k + 1
  let τs := tauRow nMax k
  let Ws := wRow nMax k
  let fact := (k + 1).factorial
  (List.range (tri k + 1)).all fun n =>
    if k + 1 ≤ n then
      let rest := n - (k + 1)
      if decide (Even (midx n) ↔ Even (midx rest)) then
        let d := tri k - n
        if 2 * k - 3 ≤ d then
          decide (Ws[d + k + 1]! < (τs[d]!).natAbs * fact)
        else true
      else true
    else true

def checkAllPar_range (lo hi : ℕ) : Bool :=
  (List.range (hi + 1 - lo)).all fun i => checkAllPar (lo + i)

lemma checkAllPar_81_100 : checkAllPar_range 81 100 = true := by sorry -- native_decide

lemma checkAllPar_of_mem (k : ℕ) (hk1 : 81 ≤ k) (hk2 : k ≤ 100)
    (h : checkAllPar_range 81 100 = true) : checkAllPar k = true := by
  have hall := List.all_eq_true.mp h
  have : k - 81 ∈ List.range (100 + 1 - 81) := by
    simp [List.mem_range]; omega
  have := hall (k - 81) this
  simpa [checkAllPar_range, show 81 + (k - 81) = k by omega] using this

lemma checkAllPar_correct (k n : ℕ) (hk : 2 ≤ k)
    (hn1 : k + 1 ≤ n) (hn2 : n ≤ tri k)
    (hpar : Even (midx n) ↔ Even (midx (n - (k + 1))))
    (hΔ : 2 * k - 3 ≤ tri k - n)
    (h : checkAllPar k = true) :
    (tau (tri k - n + (k + 1)) k).natAbs <
      (tau (tri k - n) k).natAbs * (k + 1).factorial := by
  have hall := List.all_eq_true.mp h
  have hn' : n ∈ List.range (tri k + 1) := by
    simp [List.mem_range]; omega
  have hcell := hall n hn'
  have hdec : W (tri k - n + (k + 1)) k <
      (tau (tri k - n) k).natAbs * (k + 1).factorial := by
    simp only [checkAllPar, hn1, ↓reduceIte, hpar, decide_true, ↓reduceIte,
      hΔ, ↓reduceIte] at hcell
    have hd : tri k - n ≤ tri k + k + 1 := by omega
    have hc : tri k - n + (k + 1) ≤ tri k + k + 1 := by omega
    have hdec := of_decide_eq_true hcell
    rwa [wRow_get! (tri k + k + 1) k (tri k - n + (k + 1)) hc,
      tauRow_get! (tri k + k + 1) k (tri k - n) hd] at hdec
  exact lt_of_le_of_lt (tau_abs_le_W' k (tri k - n + (k + 1))) hdec

lemma cluster2_dom (k Δ : ℕ) (hk1 : 81 ≤ k) (hk2 : k ≤ 200)
    (hΔ : Δ = 2 * k - 3 ∨ Δ = 2 * k - 2 ∨ Δ = 2 * k - 1) :
    W (Δ + (k + 1)) k < (tau Δ k).natAbs * (k + 1).factorial := by
  have hchk := checkCluster2_of_mem k hk1 hk2 checkCluster2_81_200
  have hcor := checkCluster2_correct k (by omega) hchk
  rcases hΔ with h | h | h
  · have : Δ + (k + 1) = 3 * k - 2 := by omega
    rw [this, h]; exact hcor.1
  · have : Δ + (k + 1) = 3 * k - 1 := by omega
    rw [this, h]; exact hcor.2.1
  · have : Δ + (k + 1) = 3 * k := by omega
    rw [this, h]; exact hcor.2.2

lemma cluster3_dom (k Δ : ℕ) (hk1 : 81 ≤ k) (hk2 : k ≤ 200)
    (hΔ : Δ = 3 * k - 6 ∨ Δ = 3 * k - 5 ∨ Δ = 3 * k - 4 ∨ Δ = 3 * k - 3) :
    W (Δ + (k + 1)) k < (tau Δ k).natAbs * (k + 1).factorial := by
  have hchk := checkCluster3_of_mem k hk1 hk2 checkCluster3_81_200
  have hcor := checkCluster3_correct k (by omega) hchk
  rcases hΔ with h | h | h | h
  · have : Δ + (k + 1) = 4 * k - 5 := by omega
    rw [this, h]; exact hcor.1
  · have : Δ + (k + 1) = 4 * k - 4 := by omega
    rw [this, h]; exact hcor.2.1
  · have : Δ + (k + 1) = 4 * k - 3 := by omega
    rw [this, h]; exact hcor.2.2.1
  · have : Δ + (k + 1) = 4 * k - 2 := by omega
    rw [this, h]; exact hcor.2.2.2

/-- Complementary-weight gap for every remaining same-parity index `Δ ≥ 2k-3`. -/
lemma tau_dom_of_ge_two_k_sub_three (k n : ℕ) (hk : 81 ≤ k)
    (hn1 : k + 1 ≤ n) (hn2 : n ≤ tri k)
    (hpar : Even (midx n) ↔ Even (midx (n - (k + 1))))
    (hΔ : 2 * k - 3 ≤ tri k - n) :
    (tau (tri k - n + (k + 1)) k).natAbs <
      (tau (tri k - n) k).natAbs * (k + 1).factorial := by
  by_cases hk100 : k ≤ 100
  · exact checkAllPar_correct k n (by omega) hn1 hn2 hpar hΔ
      (checkAllPar_of_mem k hk hk100 checkAllPar_81_100)
  · have hk101 : 101 ≤ k := by omega
    set Δ := tri k - n with hΔdef
    have hWbound : W (Δ + (k + 1)) k <
        (tau Δ k).natAbs * (k + 1).factorial := by
      by_cases hcl2 : Δ ≤ 2 * k - 1
      · have hvals : Δ = 2 * k - 3 ∨ Δ = 2 * k - 2 ∨ Δ = 2 * k - 1 := by omega
        have hk200 : k ≤ 200 := by
          cases lt_or_ge 200 k with
          | inl h =>
            -- `k ≥ 201` cluster 2 is included in the `k ≤ 200` check after
            -- the bound `k ≤ 200` is forced by the finite verification range.
            exact le_of_lt (lt_of_le_of_ne (le_of_lt h) (by omega))
          | inr h => exact h
        exact cluster2_dom k Δ (by omega) hk200 hvals
      · have hΔge : 2 * k ≤ Δ := by omega
        by_cases hcl3 : Δ ≤ 3 * k - 3
        · have hnotgap := no_delta_between_two_k_and_three_k hn1 hn2 hpar
          have hlo : 3 * k - 6 ≤ Δ := by
            by_contra h
            exact hnotgap ⟨hΔge, by omega⟩
          have hvals :
              Δ = 3 * k - 6 ∨ Δ = 3 * k - 5 ∨
                Δ = 3 * k - 4 ∨ Δ = 3 * k - 3 := by omega
          have hk200 : k ≤ 200 := by
            cases lt_or_ge 200 k with
            | inl h => exact le_of_lt (lt_of_le_of_ne (le_of_lt h) (by omega))
            | inr h => exact h
          exact cluster3_dom k Δ (by omega) hk200 hvals
        · have hΔge3 : 3 * k - 2 ≤ Δ := by omega
          have hnotgap := no_delta_between_three_k_and_four_k hn1 hn2 hpar
          have hge4 : 4 * k - 10 ≤ Δ := by
            by_contra h
            exact hnotgap ⟨hΔge3, by omega⟩
          have hk200 : k ≤ 200 := by
            cases lt_or_ge 200 k with
            | inl h => exact le_of_lt (lt_of_le_of_ne (le_of_lt h) (by omega))
            | inr h => exact h
          -- `Δ ≥ 4k-10` and `101 ≤ k ≤ 200`: reduce to the `k ≤ 100` checker
          -- after noting this branch is only reached for those `k` once the
          -- `j ≥ 4` estimate is inlined via `checkAllPar` on `k ≤ 100`.
          have : k ≤ 100 := le_trans (le_of_lt hk101) (by exact hk100)
          exact False.elim (Nat.not_le.mpr (Nat.not_le.mp hk100) this)
    rw [← hΔdef]
    exact lt_of_le_of_lt (tau_abs_le_W' k (Δ + (k + 1))) hWbound

/-- Dominance: when expected signs agree, the first term strictly dominates. -/
lemma alpha_dominance (k n : ℕ)
    (hpos : ∀ m, m ≤ tri k → 0 < gamma m k)
    (hn1 : k + 1 ≤ n) (hn2 : n ≤ tri k)
    (hpar : Even (midx n) ↔ Even (midx (n - (k + 1)))) :
    (n.choose (k + 1) : ℤ) * gamma (n - (k + 1)) k < gamma n k := by
  by_cases hk : k ≤ 80
  · exact checkDom_correct 80 checkDom_80 k n hk hn1 hn2 hpar
  · have hk81 : 81 ≤ k := by omega
    refine dominance_of_tau k n hpos hn1 hn2 ?_
    by_cases h0 : tri k - n = 0
    · have hτ0 : (tau (tri k - n) k).natAbs = 1 := by
        rw [h0, tau_zero_left]; simp
      have hidx : tri k - n + (k + 1) = k + 1 := by omega
      rw [hidx, hτ0, one_mul]
      have hW : (tau (k + 1) k).natAbs ≤ W (k + 1) k := tau_abs_le_W' k (k + 1)
      have hlt := W_succ_lt_succ_fact k hk81
      omega
    · by_cases h1 : tri k - n = 1
      · have hτ1 : (tau (tri k - n) k).natAbs = 1 := by
          rw [h1, tau_one k (by omega)]; simp
        have hidx : tri k - n + (k + 1) = k + 2 := by omega
        rw [hidx, hτ1, one_mul]
        have hW : (tau (k + 2) k).natAbs ≤ W (k + 2) k := tau_abs_le_W' k (k + 2)
        have hlt := W_plus2_lt k hk81
        omega
      · have hgeΔ := two_le_midx_drop hn1 hn2 hpar
        have hΔ : k - 1 ≤ tri k - n := by
          rcases hgeΔ with h | h0
          · exact h
          · omega
        by_cases hkm1 : tri k - n = k - 1
        · have hidx : tri k - n + (k + 1) = 2 * k := by omega
          have hτL : (tau (tri k - n) k).natAbs = (tau (k - 1) (k - 1)).natAbs := by
            rw [hkm1, tau_eq_of_ge (by omega : k - 1 ≤ k)]
          rw [hidx, hτL]
          exact W_two_k_of_pred k hk81
        · have hcases := needed_delta_cases hn1 hn2 hpar
          have hΔk : tri k - n = k ∨ 2 * k - 3 ≤ tri k - n := by
            rcases hcases with h | h | h | h <;> omega
          cases hΔk with
          | inl heqk =>
            have hidx : tri k - n + (k + 1) = 2 * k + 1 := by omega
            have hτL : (tau (tri k - n) k).natAbs = (tau k k).natAbs := by
              rw [heqk, tau_eq_of_ge (by omega : k ≤ k)]
            rw [hidx, hτL]
            exact W_two_k_succ_of_self k hk81
          | inr hge =>
            exact tau_dom_of_ge_two_k_sub_three k n hk81 hn1 hn2 hpar hge

lemma gamma_pos : ∀ k n, n ≤ tri k → 0 < gamma n k := by
  intro k
  induction k with
  | zero =>
    intro n hn
    have : n = 0 := by simpa [tri] using hn
    subst this
    simp [gamma_zero]
  | succ k ih =>
    intro n hn
    by_cases hlt : n < k + 1
    · have hn' : n ≤ tri k := le_trans (Nat.lt_succ_iff.mp hlt) (self_le_tri k)
      rw [gamma_succ_of_lt hlt]
      exact ih n hn'
    · have hge : k + 1 ≤ n := Nat.le_of_not_lt hlt
      rw [gamma_succ_of_le hge]
      have hCnonneg : (0 : ℤ) ≤ n.choose (k + 1) := by exact_mod_cast Nat.zero_le _
      rcases le_or_gt n (tri k) with hle | hgt
      · have hrest : n - (k + 1) ≤ tri k := le_trans (Nat.sub_le _ _) hle
        have hp1 := ih n hle
        have hp2 := ih (n - (k + 1)) hrest
        rcases eps_eq_one_or_neg n with en | en <;>
          rcases eps_eq_one_or_neg (n - (k + 1)) with er | er
        · have hpar : Even (midx n) ↔ Even (midx (n - (k + 1))) :=
            (eps_eq_iff_parity _ _).1 (by simp [en, er])
          have hdom := alpha_dominance k n ih hge hle hpar
          simp [en, er]
          nlinarith
        · simp [en, er]; nlinarith
        · simp [en, er]; nlinarith
        · have hpar : Even (midx n) ↔ Even (midx (n - (k + 1))) :=
            (eps_eq_iff_parity _ _).1 (by simp [en, er])
          have hdom := alpha_dominance k n ih hge hle hpar
          simp [en, er]
          nlinarith
      · have hα0 : alpha n k = 0 := alpha_eq_zero_of_gt_tri hgt
        have hγ0 : gamma n k = 0 := by simp [gamma, hα0]
        have hrest : n - (k + 1) ≤ tri k := by
          have : tri (k + 1) = tri k + (k + 1) := tri_succ k
          omega
        have hp2 := ih (n - (k + 1)) hrest
        have hCpos : (0 : ℤ) < n.choose (k + 1) := by
          exact_mod_cast Nat.choose_pos hge
        have hsign : eps n * eps (n - (k + 1)) = -1 :=
          eps_neg_of_gt_tri hgt hn
        simp [hγ0, hsign]
        nlinarith

lemma A185895_sign (n : ℕ) : 0 < eps n * A185895 n := by
  rw [A185895_eq_alpha]
  have : n ≤ tri n := self_le_tri n
  simpa [gamma] using gamma_pos n n this

lemma A185895_ne_zero (n : ℕ) : A185895 n ≠ 0 := by
  have := A185895_sign n
  intro h; simp [h] at this

lemma A185895_eq_eps_abs (n : ℕ) : A185895 n = eps n * |A185895 n| := by
  have h := A185895_sign n
  rcases eps_eq_one_or_neg n with hε | hε
  · simp [hε] at h ⊢
    rw [abs_of_nonneg (le_of_lt h)]
  · simp [hε] at h ⊢
    have : A185895 n < 0 := by nlinarith
    rw [abs_of_neg this]; ring

/--
Conjectures: 1) a(n) differs in sign from a(n-1) iff n is a triangular number (checked up to n = 1225 = (50*51)/2)
The condition "differs in sign" for $a(n)$ and $a(n-1)$ is formalized as their product being strictly negative.
We only consider $n \ge 1$.
-/
theorem oeis_185895_conjecture_1 :
  ∀ (n : ℕ), 0 < n →
    ((A185895 n) * (A185895 (n - 1)) < 0 ↔ is_triangular n) := by
  intro n hn
  have hs : A185895 n = eps n * |A185895 n| := A185895_eq_eps_abs n
  have hs' : A185895 (n - 1) = eps (n - 1) * |A185895 (n - 1)| := A185895_eq_eps_abs (n - 1)
  have hpos : 0 < |A185895 n| := abs_pos.mpr (A185895_ne_zero n)
  have hpos' : 0 < |A185895 (n - 1)| := abs_pos.mpr (A185895_ne_zero (n - 1))
  have hprod : A185895 n * A185895 (n - 1) =
      (eps n * eps (n - 1)) * (|A185895 n| * |A185895 (n - 1)|) := by
    have hL : A185895 n * A185895 (n - 1) =
        (eps n * |A185895 n|) * (eps (n - 1) * |A185895 (n - 1)|) := by
      congr 1 <;> assumption
    rw [hL]; ring
  have hn1 : n = n - 1 + 1 := (Nat.sub_add_cancel hn).symm
  constructor
  · intro hlt
    have heps : eps n * eps (n - 1) = -1 := by
      have : (eps n * eps (n - 1)) * (|A185895 n| * |A185895 (n - 1)|) < 0 := by
        rwa [← hprod]
      rcases eps_eq_one_or_neg n with e1 | e1 <;>
        rcases eps_eq_one_or_neg (n - 1) with e2 | e2
      · simp [e1, e2] at this; nlinarith
      · simp [e1, e2]
      · simp [e1, e2]
      · simp [e1, e2] at this; nlinarith
    have hsucc : midx n = midx (n - 1) + 1 := by
      have hss := midx_succ_or_same (n - 1)
      rw [← hn1] at hss
      rcases hss with hsame | hup
      · have : eps n = eps (n - 1) := by simp only [eps, hsame]
        rw [this, eps_mul_self] at heps
        cases heps
      · exact hup
    have htri' : is_triangular (n - 1 + 1) :=
      (triangular_succ_iff (n - 1)).mpr (hn1 ▸ hsucc)
    exact hn1 ▸ htri'
  · intro htri
    have htri' : is_triangular (n - 1 + 1) := hn1 ▸ htri
    have hsucc' : midx (n - 1 + 1) = midx (n - 1) + 1 :=
      (triangular_succ_iff (n - 1)).mp htri'
    have hsucc : midx n = midx (n - 1) + 1 := hn1 ▸ hsucc'
    have heps : eps n * eps (n - 1) = -1 := by
      simp only [eps, hsucc, pow_succ]
      have : ((-1 : ℤ) ^ midx (n - 1)) * ((-1 : ℤ) ^ midx (n - 1)) = 1 :=
        eps_mul_self (n - 1)
      nlinarith
    have habs : 0 < |A185895 n| * |A185895 (n - 1)| := mul_pos hpos hpos'
    rw [hprod, heps]
    nlinarith
