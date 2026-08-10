import FormalConjectures.Util.ProblemImports

/--
A348295: The sequence $a(n) = \sum_{k=1}^n (-1)^{\lfloor k(\sqrt{2}-1) \rfloor}.$
-/
noncomputable def a (n : ℕ) : ℤ :=
  Finset.sum (Finset.Ioc 0 n) fun k : ℕ =>
    let k_real : ℝ := k
    let exponent_real : ℝ := k_real * (Real.sqrt 2 - 1)
    let exponent_int : ℤ := Int.floor exponent_real
    -- The exponent $\lfloor k(\sqrt{2}-1) \rfloor$ is non-negative for $k \ge 1$.
    (-1 : ℤ) ^ exponent_int.toNat

namespace A348295

open Real

/-- `s2` is `√2`. -/
noncomputable abbrev s2 : ℝ := Real.sqrt 2

lemma hs2 : s2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

lemma hs2mul : s2 * s2 = 2 := by have := hs2; nlinarith [this]

lemma one_lt_s2 : (1 : ℝ) < s2 := by nlinarith [hs2, Real.sqrt_nonneg 2]

lemma s2_lt_two : s2 < 2 := by nlinarith [hs2, Real.sqrt_nonneg 2]

/-- Pell numbers `0,1,2,5,12,29,...`. -/
def Pn : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => 2 * Pn (n + 1) + Pn n

/-- Companion Pell (half NSW) numbers `1,1,3,7,17,41,...`. -/
def Qn : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (n + 2) => 2 * Qn (n + 1) + Qn n

@[simp] lemma Pn_zero : Pn 0 = 0 := rfl
@[simp] lemma Pn_one : Pn 1 = 1 := rfl
lemma Pn_succ_succ (n : ℕ) : Pn (n + 2) = 2 * Pn (n + 1) + Pn n := rfl
@[simp] lemma Qn_zero : Qn 0 = 1 := rfl
@[simp] lemma Qn_one : Qn 1 = 1 := rfl
lemma Qn_succ_succ (n : ℕ) : Qn (n + 2) = 2 * Qn (n + 1) + Qn n := rfl

/-- `x = 1 + √2` satisfies `x^2 = 2x + 1`. -/
lemma sq_one_add : (1 + s2) ^ 2 = 2 * (1 + s2) + 1 := by
  have := hs2; nlinarith [this]

lemma sq_one_sub : (1 - s2) ^ 2 = 2 * (1 - s2) + 1 := by
  have := hs2; nlinarith [this]

/-- `(Qn n) + (Pn n)·√2 = (1+√2)^n`. -/
lemma Pell_add (n : ℕ) : (Qn n : ℝ) + (Pn n : ℝ) * s2 = (1 + s2) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
      rw [Qn_succ_succ, Pn_succ_succ]
      push_cast
      have e : (1 + s2) ^ (n + 2) = 2 * (1 + s2) ^ (n + 1) + (1 + s2) ^ n := by
        have : (1 + s2) ^ (n + 2) = (1 + s2) ^ 2 * (1 + s2) ^ n := by ring
        rw [this, sq_one_add]; ring
      rw [e, ← ih1, ← ih2]; ring

/-- `(Qn n) - (Pn n)·√2 = (1-√2)^n`. -/
lemma Pell_sub (n : ℕ) : (Qn n : ℝ) - (Pn n : ℝ) * s2 = (1 - s2) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
      rw [Qn_succ_succ, Pn_succ_succ]
      push_cast
      have e : (1 - s2) ^ (n + 2) = 2 * (1 - s2) ^ (n + 1) + (1 - s2) ^ n := by
        have : (1 - s2) ^ (n + 2) = (1 - s2) ^ 2 * (1 - s2) ^ n := by ring
        rw [this, sq_one_sub]; ring
      rw [e, ← ih1, ← ih2]; ring

/-- `Pn n ≥ 1` for `n ≥ 1`. -/
lemma Pn_pos (n : ℕ) : 1 ≤ Pn (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => rw [Pn_succ_succ]; simp
  | more n ih1 ih2 =>
      rw [Pn_succ_succ]; omega

/-- `Pn` is strictly increasing. -/
lemma Pn_lt (n : ℕ) : Pn n < Pn (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => rw [Pn_succ_succ]; simp
  | more n ih1 ih2 =>
      rw [Pn_succ_succ, Pn_succ_succ]; omega

lemma Pn_lt_two (n : ℕ) : Pn n < Pn (n + 2) := lt_trans (Pn_lt n) (Pn_lt (n + 1))

/-- `Qn (n+1) = Pn (n+1) + Pn n`. -/
lemma Qsum (n : ℕ) : Qn (n + 1) = Pn (n + 1) + Pn n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih1 ih2 =>
      have hP := Pn_succ_succ n
      rw [Qn_succ_succ, Pn_succ_succ]
      omega

/-- Determinant identity `Qn k · Pn (k+1) − Pn k · Qn (k+1) = (-1)^k`. -/
lemma det_id (k : ℕ) :
    (Qn k : ℤ) * (Pn (k + 1) : ℤ) - (Pn k : ℤ) * (Qn (k + 1) : ℤ) = (-1) ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Qn_succ_succ, Pn_succ_succ, pow_succ]
      push_cast at ih ⊢
      linear_combination -ih

/-- Solving a `2×2` unimodular system: if `Qk·Pk1 − Pk·Qk1 = D` and `D² = 1`
then any `(p,q)` is an integer combination of the columns. -/
lemma repr (Qk Qk1 Pk Pk1 p q D : ℤ)
    (hDdef : Qk * Pk1 - Pk * Qk1 = D) (hDD : D * D = 1) :
    ∃ A B : ℤ, p = A * Qk + B * Qk1 ∧ q = A * Pk + B * Pk1 := by
  refine ⟨D * (p * Pk1 - Qk1 * q), D * (Qk * q - Pk * p), ?_, ?_⟩
  · symm
    calc (D * (p * Pk1 - Qk1 * q)) * Qk + (D * (Qk * q - Pk * p)) * Qk1
        = D * p * (Qk * Pk1 - Pk * Qk1) := by ring
      _ = D * p * D := by rw [hDdef]
      _ = p := by linear_combination p * hDD
  · symm
    calc (D * (p * Pk1 - Qk1 * q)) * Pk + (D * (Qk * q - Pk * p)) * Pk1
        = D * q * (Qk * Pk1 - Pk * Qk1) := by ring
      _ = D * q * D := by rw [hDdef]
      _ = q := by linear_combination q * hDD

/-- Case analysis giving the lower bound `1 ≤ |A + B(1-√2)|`. -/
lemma cases_bound (k : ℕ) (hk : 1 ≤ k) (A B : ℤ)
    (hq0 : 0 < A * (Pn k : ℤ) + B * (Pn (k + 1) : ℤ))
    (hq : A * (Pn k : ℤ) + B * (Pn (k + 1) : ℤ) < (Pn (k + 1) : ℤ)) :
    1 ≤ |(A : ℝ) + (B : ℝ) * (1 - s2)| := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hPkPos : (1 : ℤ) ≤ (Pn (k' + 1) : ℤ) := by exact_mod_cast Pn_pos k'
  have hPklt : (Pn (k' + 1) : ℤ) < (Pn (k' + 1 + 1) : ℤ) := by exact_mod_cast Pn_lt (k' + 1)
  set Pk : ℤ := (Pn (k' + 1) : ℤ) with hPk
  set Pk1 : ℤ := (Pn (k' + 1 + 1) : ℤ) with hPk1
  have hs2gt : (1 : ℝ) < s2 := one_lt_s2
  rw [le_abs]
  rcases lt_trichotomy B 0 with hB | hB | hB
  · -- B < 0, so A ≥ 1
    have hA : (0 : ℤ) < A := by nlinarith [hq0, hPkPos, hPklt, hB]
    have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    have hBneg : (B : ℝ) ≤ -1 := by
      have : B ≤ -1 := by omega
      exact_mod_cast this
    left
    nlinarith [hA1, hBneg, hs2gt]
  · -- B = 0, so A ≥ 1
    subst hB
    have hA : (0 : ℤ) < A := by nlinarith [hq0, hPkPos]
    have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    left
    push_cast
    nlinarith [hA1]
  · -- B > 0, so A ≤ -1
    have hA : A < (0 : ℤ) := by nlinarith [hq, hPkPos, hPklt, hB]
    have hA1 : (A : ℝ) ≤ -1 := by
      have : A ≤ -1 := by omega
      exact_mod_cast this
    have hBpos : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    right
    nlinarith [hA1, hBpos, hs2gt]

/-- Best-approximation bound: for `1 ≤ k` and `0 < q < Pn (k+1)`,
`(√2-1)^k ≤ |p - q√2|`. -/
lemma approx (k : ℕ) (hk : 1 ≤ k) (p q : ℤ) (hq0 : 0 < q)
    (hq : q < (Pn (k + 1) : ℤ)) :
    (s2 - 1) ^ k ≤ |(p : ℝ) - (q : ℝ) * s2| := by
  obtain ⟨A, B, hpAB, hqAB⟩ :=
    repr (Qn k) (Qn (k + 1)) (Pn k) (Pn (k + 1)) p q ((-1) ^ k)
      (det_id k) (by rw [← mul_pow]; norm_num)
  -- real value
  have hval : (p : ℝ) - (q : ℝ) * s2 = (1 - s2) ^ k * ((A : ℝ) + (B : ℝ) * (1 - s2)) := by
    have hpr : (p : ℝ) = (A : ℝ) * (Qn k : ℝ) + (B : ℝ) * (Qn (k + 1) : ℝ) := by
      exact_mod_cast hpAB
    have hqr : (q : ℝ) = (A : ℝ) * (Pn k : ℝ) + (B : ℝ) * (Pn (k + 1) : ℝ) := by
      exact_mod_cast hqAB
    have hk1 := Pell_sub k
    have hk2 := Pell_sub (k + 1)
    rw [hpr, hqr]
    have hpow : (1 - s2) ^ (k + 1) = (1 - s2) ^ k * (1 - s2) := by ring
    rw [hpow] at hk2
    linear_combination (A : ℝ) * hk1 + (B : ℝ) * hk2
  have habs : |(p : ℝ) - (q : ℝ) * s2| = (s2 - 1) ^ k * |(A : ℝ) + (B : ℝ) * (1 - s2)| := by
    have h1 : |(1 : ℝ) - s2| = s2 - 1 := by
      rw [abs_of_neg (by linarith [one_lt_s2])]; ring
    rw [hval, abs_mul, abs_pow, h1]
  rw [habs]
  have hpos : (0 : ℝ) < (s2 - 1) ^ k := pow_pos (by linarith [one_lt_s2]) k
  have hcb : 1 ≤ |(A : ℝ) + (B : ℝ) * (1 - s2)| := by
    apply cases_bound k hk A B
    · rw [← hqAB]; exact hq0
    · rw [← hqAB]; exact hq
  nlinarith [hpos, hcb]

/-- `(√2-1)^n = (-1)^n · (Qn n - Pn n · √2)`. -/
lemma pow_eq (n : ℕ) :
    (s2 - 1) ^ n = (-1 : ℝ) ^ n * ((Qn n : ℝ) - (Pn n : ℝ) * s2) := by
  rw [Pell_sub n, show s2 - 1 = (-1) * (1 - s2) from by ring, mul_pow]

/-- Key floor identity: shifting the argument by `Pn (m+1)` shifts the floor by
`Pn m`, provided `1 ≤ j < Pn (m+2)`. -/
lemma crux (m j : ℕ) (hj : 1 ≤ j) (hjb : j < Pn (m + 2)) :
    ⌊((Pn (m + 1) + j : ℕ) : ℝ) * (s2 - 1)⌋ = (Pn m : ℤ) + ⌊(j : ℝ) * (s2 - 1)⌋ := by
  have hs2gt := one_lt_s2
  set x : ℝ := (j : ℝ) * (s2 - 1) with hx
  set w : ℝ := -((1 : ℝ) - s2) ^ (m + 1) with hw
  have hQ : (Qn (m + 1) : ℝ) = (Pn (m + 1) : ℝ) + (Pn m : ℝ) := by exact_mod_cast Qsum m
  have hPS := Pell_sub (m + 1)
  have hshift : (Pn (m + 1) : ℝ) * (s2 - 1) = (Pn m : ℝ) + w := by
    rw [hw]
    have h1 : ((1 : ℝ) - s2) ^ (m + 1) = (Qn (m + 1) : ℝ) - (Pn (m + 1) : ℝ) * s2 := hPS.symm
    rw [h1, hQ]; ring
  have harg : ((Pn (m + 1) + j : ℕ) : ℝ) * (s2 - 1) = ((Pn m : ℤ) : ℝ) + (x + w) := by
    have hc : ((Pn (m + 1) + j : ℕ) : ℝ) = (Pn (m + 1) : ℝ) + (j : ℝ) := by push_cast; ring
    rw [hc, add_mul, hshift]
    push_cast; ring
  rw [harg, Int.floor_intCast_add]
  congr 1
  have hjs2 : (j : ℝ) * s2 = x + (j : ℝ) := by rw [hx]; ring
  have hfloor_le : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x
  have hlt_floor : x < (⌊x⌋ : ℤ) + 1 := Int.lt_floor_add_one x
  have hpwpos : (0 : ℝ) < (s2 - 1) ^ (m + 1) := pow_pos (by linarith) _
  have hlo : (s2 - 1) ^ (m + 1) ≤ x - (⌊x⌋ : ℝ) := by
    have happ := approx (m + 1) (by omega) (⌊x⌋ + (j : ℤ)) (j : ℤ)
      (by exact_mod_cast hj) (by exact_mod_cast hjb)
    have hA : ((⌊x⌋ + (j : ℤ) : ℤ) : ℝ) - ((j : ℤ) : ℝ) * s2 = (⌊x⌋ : ℝ) - x := by
      push_cast; rw [hjs2]; ring
    rw [hA, abs_of_nonpos (by linarith)] at happ
    linarith
  rw [Int.floor_eq_iff]
  rcases Nat.even_or_odd m with he | ho
  · -- m even, so w = (s2-1)^(m+1) > 0
    have hwv : w = (s2 - 1) ^ (m + 1) := by
      rw [hw, show (1 : ℝ) - s2 = (-1) * (s2 - 1) from by ring, mul_pow,
        Odd.neg_one_pow he.add_one]; ring
    have hup : (s2 - 1) ^ (m + 1) < (⌊x⌋ : ℝ) + 1 - x := by
      have happ2 := approx (m + 1) (by omega) (⌊x⌋ + (j : ℤ) + 1) (j : ℤ)
        (by exact_mod_cast hj) (by exact_mod_cast hjb)
      have hA2 : ((⌊x⌋ + (j : ℤ) + 1 : ℤ) : ℝ) - ((j : ℤ) : ℝ) * s2 = (⌊x⌋ : ℝ) + 1 - x := by
        push_cast; rw [hjs2]; ring
      rw [hA2, abs_of_nonneg (by linarith)] at happ2
      rcases lt_or_eq_of_le happ2 with h | h
      · exact h
      · exfalso
        have hpe := pow_eq (m + 1)
        rw [Odd.neg_one_pow he.add_one] at hpe
        set M : ℤ := (Pn (m + 1) : ℤ) + (j : ℤ) with hM
        set Z : ℤ := ⌊x⌋ + 1 + (j : ℤ) + (Qn (m + 1) : ℤ) with hZ
        have hMne : M ≠ 0 := by rw [hM]; have := Pn_pos m; omega
        have heq2 : (M : ℝ) * s2 = (Z : ℝ) := by
          rw [hM, hZ]; push_cast; linear_combination h - hpe + hjs2
        exact absurd heq2 ((irrational_sqrt_two.intCast_mul hMne).ne_int Z)
    refine ⟨?_, ?_⟩
    · rw [hwv]; linarith
    · rw [hwv]; linarith
  · -- m odd, so w = -(s2-1)^(m+1) < 0
    have hwv : w = -(s2 - 1) ^ (m + 1) := by
      rw [hw, show (1 : ℝ) - s2 = (-1) * (s2 - 1) from by ring, mul_pow,
        Even.neg_one_pow ho.add_one]; ring
    refine ⟨?_, ?_⟩
    · rw [hwv]; linarith
    · rw [hwv]; linarith

/-- The exponent `⌊k(√2-1)⌋`. -/
noncomputable def E (k : ℕ) : ℤ := ⌊(k : ℝ) * (s2 - 1)⌋

/-- The `k`-th summand of `a`. -/
noncomputable def term (k : ℕ) : ℤ := (-1 : ℤ) ^ (E k).toNat

lemma a_eq (n : ℕ) : a n = ∑ k ∈ Finset.Ioc 0 n, term k := rfl

lemma a_zero : a 0 = 0 := by rw [a_eq]; simp

lemma a_succ (n : ℕ) : a (n + 1) = a n + term (n + 1) := by
  rw [a_eq, a_eq, Finset.sum_Ioc_succ_top (Nat.zero_le n) term]

lemma term_one : term 1 = 1 := by
  have hE : E 1 = 0 := by
    show ⌊((1 : ℕ) : ℝ) * (s2 - 1)⌋ = 0
    rw [Int.floor_eq_zero_iff, Set.mem_Ico]
    refine ⟨by push_cast; nlinarith [one_lt_s2], by push_cast; nlinarith [s2_lt_two]⟩
  show (-1 : ℤ) ^ (E 1).toNat = 1
  rw [hE]; simp

lemma a_one : a 1 = 1 := by
  have h : a 1 = a 0 + term 1 := a_succ 0
  rw [h, a_zero, term_one]; norm_num

/-- `(-1)^(Pn m) = (-1)^m`. -/
lemma neg_one_Pn (m : ℕ) : (-1 : ℤ) ^ (Pn m) = (-1) ^ m := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
      rw [Pn_succ_succ, pow_add, pow_mul]
      simp only [neg_one_sq, one_pow, one_mul, ih1]
      rw [pow_add]; norm_num

/-- Term-wise self-similarity. -/
lemma term_shift (m j : ℕ) (hj : 1 ≤ j) (hjb : j < Pn (m + 2)) :
    term (Pn (m + 1) + j) = (-1 : ℤ) ^ (Pn m) * term j := by
  have hEj : 0 ≤ E j := by
    show (0 : ℤ) ≤ ⌊(j : ℝ) * (s2 - 1)⌋
    apply Int.floor_nonneg.mpr
    have h2 : (0 : ℝ) ≤ s2 - 1 := by linarith [one_lt_s2]
    exact mul_nonneg (by positivity) h2
  have hkey : E (Pn (m + 1) + j) = (Pn m : ℤ) + E j := crux m j hj hjb
  unfold term
  rw [hkey]
  have h3 : ((Pn m : ℤ) + E j).toNat = Pn m + (E j).toNat := by omega
  rw [h3, pow_add]

/-- Summation self-similarity. -/
lemma key (m : ℕ) : ∀ M : ℕ, M < Pn (m + 2) →
    a (Pn (m + 1) + M) = a (Pn (m + 1)) + (-1 : ℤ) ^ (Pn m) * a M := by
  intro M
  induction M with
  | zero => intro _; simp [a_zero]
  | succ M ih =>
      intro hM
      have hM' : M < Pn (m + 2) := by omega
      have h1 : a (Pn (m + 1) + (M + 1)) =
          a (Pn (m + 1) + M) + term (Pn (m + 1) + (M + 1)) := by
        have := a_succ (Pn (m + 1) + M)
        rwa [show (Pn (m + 1) + M) + 1 = Pn (m + 1) + (M + 1) from by ring] at this
      rw [h1, ih hM', term_shift m (M + 1) (by omega) hM, a_succ M]
      ring

/-- Two-step recursion for `a (Pn m)`. -/
lemma b_rec (m : ℕ) :
    a (Pn (m + 2)) = (1 + (-1 : ℤ) ^ (Pn m)) * a (Pn (m + 1)) + a (Pn m) := by
  have hR : Pn (m + 2) = Pn (m + 1) + (Pn (m + 1) + Pn m) := by rw [Pn_succ_succ]; ring
  have hRlt : Pn (m + 1) + Pn m < Pn (m + 2) := by
    rw [Pn_succ_succ]; have := Pn_pos m; omega
  have hPmlt : Pn m < Pn (m + 2) := Pn_lt_two m
  have e1 : a (Pn (m + 2)) =
      a (Pn (m + 1)) + (-1 : ℤ) ^ (Pn m) * a (Pn (m + 1) + Pn m) := by
    rw [hR]; exact key m (Pn (m + 1) + Pn m) hRlt
  have e2 : a (Pn (m + 1) + Pn m) =
      a (Pn (m + 1)) + (-1 : ℤ) ^ (Pn m) * a (Pn m) := key m (Pn m) hPmlt
  have hsq : (-1 : ℤ) ^ (Pn m) * (-1 : ℤ) ^ (Pn m) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨Pn m, rfl⟩
  rw [e1, e2]
  linear_combination (a (Pn m)) * hsq

/-- The record subsequence: `a (Pn (2t)) = 2t` and `a (Pn (2t+1)) = 1`. -/
lemma b_even (t : ℕ) : a (Pn (2 * t)) = 2 * (t : ℤ) ∧ a (Pn (2 * t + 1)) = 1 := by
  induction t with
  | zero =>
      refine ⟨?_, ?_⟩
      · have : Pn (2 * 0) = 0 := by decide
        rw [this, a_zero]; norm_num
      · have : Pn (2 * 0 + 1) = 1 := by decide
        rw [this]; exact a_one
  | succ t ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hc0 : (-1 : ℤ) ^ (Pn (2 * t)) = 1 := by rw [neg_one_Pn, pow_mul]; norm_num
      have hc1 : (-1 : ℤ) ^ (Pn (2 * t + 1)) = -1 := by
        rw [neg_one_Pn, pow_succ, pow_mul]; norm_num
      refine ⟨?_, ?_⟩
      · have hb := b_rec (2 * t)
        rw [hc0] at hb
        rw [show 2 * (t + 1) = 2 * t + 2 from by ring, hb, ih1, ih2]
        push_cast; ring
      · have hb := b_rec (2 * t + 1)
        rw [hc1] at hb
        rw [show 2 * (t + 1) + 1 = (2 * t + 1) + 2 from by ring, hb, ih2]
        ring

end A348295

/--
Conjecture (1) for A348295: The sequence is unbounded from above.
Moreover, it seems that the earliest occurrence of m is A000129(m) for even m
and A001333(m) for odd m (this has been confirmed for m <= 32 by Chai Wah Wu,
Oct 21 2021). See A084068 for the conjectured indices of records.
-/
theorem oeis_348295_conjecture_0 : ∀ (M : ℤ), ∃ (n : ℕ), a n > M := by
  intro M
  refine ⟨A348295.Pn (2 * (M.toNat + 1)), ?_⟩
  rw [(A348295.b_even (M.toNat + 1)).1]
  omega
