import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset
open scoped Nat

/-!
Auxiliary development of the Frobenius factorization for
`exp(∑ c_k x^k / k)` and the associated supercongruences.
This file is only used while developing the proof; the final
argument will live in `Submission/Spec.lean`.
-/

def cCoeff (m k : ℕ) : ℕ :=
  (m * k).factorial / (k.factorial ^ m)

lemma factorial_pow_dvd (m k : ℕ) :
    k.factorial ^ m ∣ (m * k).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul]
    exact dvd_trans (mul_dvd_mul ih (dvd_refl _))
      (Nat.factorial_mul_factorial_dvd_factorial_add (m * k) k)

lemma cCoeff_mul (m k : ℕ) :
    cCoeff m k * k.factorial ^ m = (m * k).factorial := by
  simpa [cCoeff] using Nat.div_mul_cancel (factorial_pow_dvd m k)

/-- Rational exponential coefficients for driving sequence `d`. -/
noncomputable def expQ (d : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 =>
      (∑ j ∈ range (k + 1), d (j + 1) * expQ d (k - j)) / (k + 1 : ℚ)

lemma expQ_zero (d : ℕ → ℚ) : expQ d 0 = 1 := by simp [expQ]

lemma expQ_succ (d : ℕ → ℚ) (k : ℕ) :
    expQ d (k + 1) =
      (∑ j ∈ range (k + 1), d (j + 1) * expQ d (k - j)) / (k + 1 : ℚ) := by
  simp [expQ]

lemma expQ_mul_succ (d : ℕ → ℚ) (k : ℕ) :
    (k + 1 : ℚ) * expQ d (k + 1) =
      ∑ j ∈ range (k + 1), d (j + 1) * expQ d (k - j) := by
  have hk : (k + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [expQ_succ, mul_div_cancel₀ _ hk]

/-- `α_j(N) = [x^j] A_m(x)^N`. -/
noncomputable def alphaQ (m N j : ℕ) : ℚ :=
  expQ (fun k => (N : ℚ) * (cCoeff m k : ℚ)) j

lemma alphaQ_zero (m N : ℕ) : alphaQ m N 0 = 1 := expQ_zero _

lemma alphaQ_rec (m N k : ℕ) :
    (k + 1 : ℚ) * alphaQ m N (k + 1) =
      (N : ℚ) * ∑ j ∈ range (k + 1),
        (cCoeff m (j + 1) : ℚ) * alphaQ m N (k - j) := by
  unfold alphaQ
  rw [expQ_mul_succ]
  simp [mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Driving coefficients of the Frobenius remainder `G`. -/
def eDrive (m p j : ℕ) : ℤ :=
  if p = 0 then 0
  else if p ∣ j then
    (p : ℤ) * ((cCoeff m j : ℤ) - (cCoeff m (j / p) : ℤ))
  else
    (p : ℤ) * (cCoeff m j : ℤ)

lemma eDrive_of_not_dvd {m p j : ℕ} (hp : p ≠ 0) (h : ¬ p ∣ j) :
    eDrive m p j = (p : ℤ) * (cCoeff m j : ℤ) := by
  simp [eDrive, hp, h]

lemma eDrive_of_dvd {m p j : ℕ} (hp : p ≠ 0) (h : p ∣ j) :
    eDrive m p j = (p : ℤ) * ((cCoeff m j : ℤ) - (cCoeff m (j / p) : ℤ)) := by
  simp [eDrive, hp, h]

/-- `γ_j(N) = [x^j] G(x)^N`, as a rational. -/
noncomputable def gammaQ (m p N j : ℕ) : ℚ :=
  expQ (fun k => (N : ℚ) * (eDrive m p k : ℚ)) j

lemma gammaQ_zero (m p N : ℕ) : gammaQ m p N 0 = 1 := expQ_zero _

lemma gammaQ_rec (m p N k : ℕ) :
    (k + 1 : ℚ) * gammaQ m p N (k + 1) =
      (N : ℚ) * ∑ j ∈ range (k + 1),
        (eDrive m p (j + 1) : ℚ) * gammaQ m p N (k - j) := by
  unfold gammaQ
  rw [expQ_mul_succ]
  simp [mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Stretched Cauchy product `∑_i α_i(N) γ_{k - p i}(N)`. -/
noncomputable def cauchyPG (m p N k : ℕ) : ℚ :=
  ∑ i ∈ range (k / p + 1), alphaQ m N i * gammaQ m p N (k - p * i)

lemma cauchyPG_zero (m p N : ℕ) : cauchyPG m p N 0 = 1 := by
  simp [cauchyPG, alphaQ_zero, gammaQ_zero]

lemma mem_range_of_mul_le {p i k : ℕ} (hp : 0 < p) (hle : p * i ≤ k) :
    i ∈ range (k / p + 1) := by
  rw [mem_range, Nat.lt_succ_iff]
  have : p * i / p ≤ k / p := Nat.div_le_div_right hle
  rwa [Nat.mul_div_right i hp] at this

lemma mul_le_of_mem_div_range {p i k : ℕ} (hp : 0 < p)
    (hi : i ∈ range (k / p + 1)) : p * i ≤ k := by
  have : i ≤ k / p := Nat.lt_succ_iff.mp (mem_range.mp hi)
  calc p * i ≤ p * (k / p) := Nat.mul_le_mul_left p this
    _ ≤ k := Nat.mul_div_le k p

lemma cauchyPG_eq (m p N k : ℕ) (hp : 0 < p) :
    cauchyPG m p N k =
      ∑ i ∈ range (k + 1),
        (if p * i ≤ k then alphaQ m N i * gammaQ m p N (k - p * i) else 0) := by
  unfold cauchyPG
  apply Eq.symm
  rw [sum_ite]
  have hfilter :
      (range (k + 1)).filter (fun i => p * i ≤ k) = range (k / p + 1) := by
    ext i
    simp only [mem_filter, mem_range]
    constructor
    · intro ⟨_, hle⟩
      exact mem_range.mp (mem_range_of_mul_le hp hle)
    · intro hi
      have hle := mul_le_of_mem_div_range (p := p) (i := i) (k := k) hp (mem_range.mpr hi)
      have : i ≤ k / p := Nat.lt_succ_iff.mp hi
      exact ⟨Nat.lt_succ_of_le (this.trans (Nat.div_le_self k p)), hle⟩
  simp [hfilter]

lemma alphaQ_rec' (m N n : ℕ) (hn : n ≠ 0) :
    (n : ℚ) * alphaQ m N n =
      (N : ℚ) * ∑ j ∈ range n,
        (cCoeff m (j + 1) : ℚ) * alphaQ m N (n - 1 - j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simpa [Nat.succ_eq_add_one] using alphaQ_rec m N k

lemma gammaQ_rec' (m p N n : ℕ) (hn : n ≠ 0) :
    (n : ℚ) * gammaQ m p N n =
      (N : ℚ) * ∑ j ∈ range n,
        (eDrive m p (j + 1) : ℚ) * gammaQ m p N (n - 1 - j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simpa [Nat.succ_eq_add_one] using gammaQ_rec m p N k

lemma eDrive_decompose (m p j : ℕ) (hp : p ≠ 0) :
    (eDrive m p j : ℚ) =
      (p : ℚ) * (cCoeff m j : ℚ) -
        (if p ∣ j then (p : ℚ) * (cCoeff m (j / p) : ℚ) else 0) := by
  by_cases h : p ∣ j
  · rw [eDrive_of_dvd hp h]
    simp [h]
    ring
  · rw [eDrive_of_not_dvd hp h]
    simp [h]

lemma gammaQ_mul (m p N n : ℕ) :
    (n : ℚ) * gammaQ m p N n =
      if n = 0 then 0
      else (N : ℚ) * ∑ j ∈ range n,
        (eDrive m p (j + 1) : ℚ) * gammaQ m p N (n - 1 - j) := by
  rcases n with _ | n
  · simp
  · simp [gammaQ_rec]

lemma alphaQ_mul (m N n : ℕ) :
    (n : ℚ) * alphaQ m N n =
      if n = 0 then 0
      else (N : ℚ) * ∑ j ∈ range n,
        (cCoeff m (j + 1) : ℚ) * alphaQ m N (n - 1 - j) := by
  rcases n with _ | n
  · simp
  · simp [alphaQ_rec]

lemma cauchyPG_term (m p N n i : ℕ) (hp : 0 < p) :
    (if p * i ≤ n then alphaQ m N i * gammaQ m p N (n - p * i) else 0) =
      if p * i ≤ n then alphaQ m N i * gammaQ m p N (n - p * i) else 0 := rfl

/-- Recurrence for the stretched Cauchy product. -/
lemma cauchyPG_rec (m p N k : ℕ) (hp : p.Prime) :
    ((k + 1 : ℕ) : ℚ) * cauchyPG m p N (k + 1) =
      ((N * p : ℕ) : ℚ) * ∑ j ∈ range (k + 1),
        (cCoeff m (j + 1) : ℚ) * cauchyPG m p N (k - j) := by
  have hp0 : 0 < p := hp.pos
  have hpne : p ≠ 0 := hp.ne_zero
  -- Expand both sides via the definitions of `alphaQ` / `gammaQ`.
  -- First write `S_{k+1}` as a sum over `i ≤ (k+1)/p`.
  set n := k + 1
  have hn : n = k + 1 := rfl
  -- `n * S_n = ∑_i A_i * n * G_{n-pi}`
  have hexpand :
      (n : ℚ) * cauchyPG m p N n =
        ∑ i ∈ range (n / p + 1),
          alphaQ m N i * ((n : ℚ) * gammaQ m p N (n - p * i)) := by
    simp [cauchyPG, mul_sum, mul_left_comm]
  -- Split `n G_q = q G_q + p i G_q`.
  have hsplit : ∀ i, p * i ≤ n →
      (n : ℚ) * gammaQ m p N (n - p * i) =
        ((n - p * i : ℕ) : ℚ) * gammaQ m p N (n - p * i) +
          (p * i : ℚ) * gammaQ m p N (n - p * i) := by
    intro i hle
    have : (n : ℚ) = ((n - p * i : ℕ) : ℚ) + (p * i : ℚ) := by
      have := Nat.sub_add_cancel hle
      exact_mod_cast this.symm
    rw [this, add_mul]
  -- Use the recurrences and reindex. Details follow the standard
  -- Leibniz rule for `x (UG)' / (UG) = x U'/U + x G'/G`.
  have hgoal : (n : ℚ) * cauchyPG m p N n =
      ((N * p : ℕ) : ℚ) * ∑ j ∈ range n,
        (cCoeff m (j + 1) : ℚ) * cauchyPG m p N (n - 1 - j) := by
    -- Direct expansion becomes very large; we use uniqueness of
    -- sequences satisfying the same initial condition and the same
    -- first-order convolution, applied after verifying the driving
    -- coefficients add correctly. See `eDrive_decompose`.
    --
    -- `n S_n = ∑_i A_i (q G_q + p i G_q)` with `q = n - p i`.
    -- The `q G_q` terms produce `N ∑_j e_j S_{n-j}`.
    -- The `p i G_q` terms produce `N p ∑_t c_t S_{n-p t}`.
    -- Adding and using `e_j = p c_j - 1_{p|j} p c_{j/p}` yields
    -- `N p ∑_j c_j S_{n-j}`.
    sorry
  simpa [n] using hgoal

/-- The Frobenius product identity: `[x^k] F^{Np} = ∑_i α_i(N) γ_{k-pi}(N)`. -/
lemma cauchyPG_eq_alpha (m p N : ℕ) (hp : p.Prime) :
    ∀ k, cauchyPG m p N k = alphaQ m (N * p) k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · simp [cauchyPG_zero, alphaQ_zero]
    have hα :
        ((k + 1 : ℕ) : ℚ) * alphaQ m (N * p) (k + 1) =
          ((N * p : ℕ) : ℚ) * ∑ j ∈ range (k + 1),
            (cCoeff m (j + 1) : ℚ) * alphaQ m (N * p) (k - j) := by
      simpa [Nat.cast_mul] using alphaQ_rec m (N * p) k
    have hS := cauchyPG_rec m p N k hp
    have hk0 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    apply mul_left_cancel₀ hk0
    rw [hS, hα]
    refine congrArg _ (sum_congr rfl fun j hj => ?_)
    exact congrArg _ (ih (k - j) (Nat.sub_lt_succ _ _))

