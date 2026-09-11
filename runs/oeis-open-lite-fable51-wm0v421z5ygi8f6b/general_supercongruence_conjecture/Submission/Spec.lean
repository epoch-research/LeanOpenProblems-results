import FormalConjectures.Util.ProblemImports

open Nat BigOperators Int

/-- The generalized coefficient $c_{m} (k) = \frac{(m k)!}{(k!)^m}$ in $\mathbb{N}$. -/
def coeff_of_log_gf_gen (m k : ℕ) : ℕ :=
  (m * k).factorial / (k.factorial ^ m)

/--
A generalized recursive definition for the coefficients of any exponential series $\exp(\sum d_k \frac{x^k}{k})$.
The coefficients $a_k$ satisfy $k \cdot a_k = \sum_{j=1}^k d_j \cdot a_{k-j}$.
This is a local helper function inside `b_m_int`.
-/
noncomputable def generalized_exp_coeff (d : ℕ → ℕ) : ℕ → ℕ
| 0 => 1
| k' + 1 =>
  let k := k' + 1
  (Finset.sum (Finset.range k) fun j =>
    (d (j + 1)) * (generalized_exp_coeff d (k - (j + 1)))) / k

/--
The sequence $b_m(n)$ is defined by $b_m(n) := [x^n] A_m(x)^n$ for $n \ge 1$.
We define $b_m(n)$ as the $n$-th coefficient of the series $\exp(L_{m,n}(x))$, where the driving coefficients are $d_k = n \cdot c_m(k)$.
Since this sequence is in $\mathbb{N}$, we define it in $\mathbb{Z}$ for the congruence.
-/
noncomputable def b_m_int (m n : ℕ) : ℤ :=
  if n = 0 then 0 -- Not in the domain of the conjecture, but required for total function.
  else
    let d (k : ℕ) : ℕ := n * coeff_of_log_gf_gen m k
    (generalized_exp_coeff d n : ℤ)

/- ## Section: PV -/

/- # p-adic valuation bounds API on `ℚ_[p]` -/

namespace Supercong

variable {p : ℕ} [hp : Fact p.Prime]

/-- `PV k x` means `‖x‖ ≤ p^(-k)`, i.e. the valuation of `x` is at least `k`. -/
def PV (p : ℕ) [Fact p.Prime] (k : ℤ) (x : ℚ_[p]) : Prop := ‖x‖ ≤ (p : ℝ) ^ (-k)

lemma one_lt_p_real : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt

lemma p_real_pos : (0 : ℝ) < p := by linarith [one_lt_p_real (p := p)]

lemma PV_zero (k : ℤ) : PV p k (0 : ℚ_[p]) := by
  unfold PV; simp only [norm_zero]; positivity

lemma PV_mono {k l : ℤ} {x : ℚ_[p]} (h : PV p k x) (hl : l ≤ k) : PV p l x := by
  unfold PV at *
  refine h.trans ?_
  exact zpow_le_zpow_right₀ (le_of_lt one_lt_p_real) (by omega)

lemma PV_add {k : ℤ} {x y : ℚ_[p]} (hx : PV p k x) (hy : PV p k y) : PV p k (x + y) := by
  unfold PV at *
  exact (Padic.nonarchimedean x y).trans (max_le hx hy)

lemma PV_neg {k : ℤ} {x : ℚ_[p]} (hx : PV p k x) : PV p k (-x) := by
  unfold PV at *; simpa using hx

lemma PV_sub {k : ℤ} {x y : ℚ_[p]} (hx : PV p k x) (hy : PV p k y) : PV p k (x - y) := by
  rw [sub_eq_add_neg]; exact PV_add hx (PV_neg hy)

lemma PV_mul {k l : ℤ} {x y : ℚ_[p]} (hx : PV p k x) (hy : PV p l y) : PV p (k + l) (x * y) := by
  unfold PV at *
  rw [norm_mul, neg_add, zpow_add₀ (_root_.ne_of_gt p_real_pos)]
  exact mul_le_mul hx hy (norm_nonneg _) (by positivity)

lemma PV_sum {ι : Type*} {s : Finset ι} {k : ℤ} {f : ι → ℚ_[p]}
    (h : ∀ i ∈ s, PV p k (f i)) : PV p k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PV_zero k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact PV_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma PV_prod {ι : Type*} {s : Finset ι} {k : ι → ℤ} {f : ι → ℚ_[p]}
    (h : ∀ i ∈ s, PV p (k i) (f i)) : PV p (∑ i ∈ s, k i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty]; unfold PV; simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact PV_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma PV_pow {k : ℤ} {x : ℚ_[p]} (hx : PV p k x) (n : ℕ) : PV p (n * k) (x ^ n) := by
  induction n with
  | zero => unfold PV; simp
  | succ n ih =>
    rw [pow_succ]
    have := PV_mul ih hx
    have e : ((n + 1 : ℕ) : ℤ) * k = n * k + k := by push_cast; ring
    rw [e]; exact this

lemma PV_one : PV p 0 (1 : ℚ_[p]) := by unfold PV; simp

lemma PV_int (z : ℤ) : PV p 0 (z : ℚ_[p]) := by
  unfold PV; simpa using Padic.norm_int_le_one z

lemma PV_nat (n : ℕ) : PV p 0 (n : ℚ_[p]) := by
  have := PV_int (p := p) n; simpa using this

lemma PV_int_iff (z : ℤ) (k : ℕ) : PV p k (z : ℚ_[p]) ↔ (p ^ k : ℤ) ∣ z := by
  unfold PV; exact Padic.norm_int_le_pow_iff_dvd z k

lemma PV_nat_iff (n : ℕ) (k : ℕ) : PV p k (n : ℚ_[p]) ↔ p ^ k ∣ n := by
  have := PV_int_iff (p := p) (n : ℤ) k
  rw [Int.natCast_dvd_natCast.symm] ; push_cast at this ⊢; exact this

lemma PV_of_dvd {n : ℕ} {k : ℕ} (h : p ^ k ∣ n) : PV p k (n : ℚ_[p]) := (PV_nat_iff n k).2 h

lemma norm_natCast_unit {n : ℕ} (h : ¬ p ∣ n) : ‖(n : ℚ_[p])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 h

lemma PV_inv_unit {n : ℕ} (h : ¬ p ∣ n) : PV p 0 ((n : ℚ_[p])⁻¹) := by
  unfold PV; rw [norm_inv, norm_natCast_unit h]; simp

lemma PV_mul_unit_inv {k : ℤ} {x : ℚ_[p]} (hx : PV p k x) {n : ℕ} (h : ¬ p ∣ n) :
    PV p k (x * (n : ℚ_[p])⁻¹) := by
  have := PV_mul hx (PV_inv_unit h); simpa using this

lemma PV_div_unit {k : ℤ} {x : ℚ_[p]} (hx : PV p k x) {n : ℕ} (h : ¬ p ∣ n) :
    PV p k (x / (n : ℚ_[p])) := by
  rw [div_eq_mul_inv]; exact PV_mul_unit_inv hx h

lemma PV_p_pow (k : ℕ) : PV p k ((p : ℚ_[p]) ^ k) := by
  unfold PV; rw [Padic.norm_p_pow]

lemma PV_p : PV p 1 (p : ℚ_[p]) := by
  have := PV_p_pow (p := p) 1; simpa using this

lemma PV_p_pow_mul {k : ℤ} {x : ℚ_[p]} (hx : PV p k x) (j : ℕ) :
    PV p (k + j) ((p : ℚ_[p]) ^ j * x) := by
  have := PV_mul (PV_p_pow (p := p) j) hx
  convert this using 1; ring

/-- Norm of a nonzero natural number in terms of its `p`-adic valuation. -/
lemma norm_natCast_eq {n : ℕ} (hn : n ≠ 0) :
    ‖(n : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
  rw [show ((n : ℚ_[p])) = ((n : ℚ) : ℚ_[p]) by norm_cast, Padic.eq_padicNorm]
  rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn)]
  push_cast
  congr 2

lemma PV_nat_val (n : ℕ) : PV p (padicValNat p n) (n : ℚ_[p]) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simpa using PV_zero (p := p) _
  · unfold PV; rw [norm_natCast_eq (Nat.pos_iff_ne_zero.mp h)]

/-- Inverse of a nonzero natural number. -/
lemma PV_nat_inv (n : ℕ) (hn : n ≠ 0) : PV p (-(padicValNat p n : ℤ)) ((n : ℚ_[p])⁻¹) := by
  unfold PV; rw [norm_inv, norm_natCast_eq hn, ← zpow_neg, neg_neg]

lemma PV_div_nat {k : ℤ} {x : ℚ_[p]} (hx : PV p k x) (n : ℕ) (hn : n ≠ 0) :
    PV p (k - padicValNat p n) (x / (n : ℚ_[p])) := by
  rw [div_eq_mul_inv, sub_eq_add_neg]; exact PV_mul hx (PV_nat_inv n hn)

/-- If `PV k x` and `‖y‖ = 1` (`y` a unit) then `PV k (x * y)`. -/
lemma PV_mul_norm_one {k : ℤ} {x y : ℚ_[p]} (hx : PV p k x) (hy : ‖y‖ = 1) : PV p k (x * y) := by
  unfold PV at *; rw [norm_mul, hy, mul_one]; exact hx

lemma PV_of_norm_le_one {x : ℚ_[p]} (h : ‖x‖ ≤ 1) : PV p 0 x := by unfold PV; simpa using h

lemma norm_le_one_of_PV {x : ℚ_[p]} (h : PV p 0 x) : ‖x‖ ≤ 1 := by unfold PV at h; simpa using h

lemma PV_int_sub_iff (a b : ℤ) (k : ℕ) : PV p k ((a : ℚ_[p]) - (b : ℚ_[p])) ↔ (p ^ k : ℤ) ∣ a - b := by
  rw [← PV_int_iff]; push_cast; rfl

lemma PV_smul_nat {k : ℤ} {x : ℚ_[p]} (hx : PV p k x) (n : ℕ) : PV p k ((n : ℚ_[p]) * x) := by
  have := PV_mul (PV_nat (p := p) n) hx; simpa using this

lemma PV_mul_nat_left {k : ℤ} {x : ℚ_[p]} (hx : PV p k x) (n : ℕ) (j : ℕ) (h : p ^ j ∣ n) :
    PV p (k + j) ((n : ℚ_[p]) * x) := by
  have := PV_mul (PV_of_dvd (p := p) h) hx; convert this using 1; ring

/-- Norm of a rational number that is `p`-integral, as an element. -/
lemma PV_ratCast_int (q : ℚ) (hq : q.den = 1) : PV p 0 ((q : ℚ_[p])) := by
  have : q = (q.num : ℚ) := by
    have := Rat.num_div_den q; rw [hq] at this; simpa using this.symm
  rw [this]; push_cast; exact PV_int _

lemma norm_eq_one_of_PV_zero_of_PV_zero_inv {x : ℚ_[p]} (hx : x ≠ 0) (h1 : PV p 0 x)
    (h2 : PV p 0 x⁻¹) : ‖x‖ = 1 := by
  unfold PV at *
  simp only [neg_zero, zpow_zero, norm_inv] at h1 h2
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have := (inv_le_one₀ hx').1 h2
  linarith

end Supercong

/- ## Section: ECalc -/

/- # Formal exponential calculus for power series `exp(∑ d_k x^k / k)` -/

namespace Supercong

open PowerSeries

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [CharZero K]

/-- The exponential coefficient sequence: `expSeq d k` is the `k`-th coefficient of
`exp (∑_{j ≥ 1} d j X^j / j)`. Mirrors `generalized_exp_coeff`. -/
noncomputable def expSeq (d : ℕ → K) : ℕ → K
  | 0 => 1
  | k' + 1 =>
    let k := k' + 1
    (∑ j ∈ Finset.range k, d (j + 1) * expSeq d (k - (j + 1))) / k

lemma expSeq_zero (d : ℕ → K) : expSeq d 0 = 1 := by simp [expSeq]

lemma expSeq_succ (d : ℕ → K) (k : ℕ) :
    expSeq d (k + 1) = (∑ j ∈ Finset.range (k + 1), d (j + 1) * expSeq d (k - j)) / (k + 1) := by
  rw [expSeq]
  simp only [Nat.add_sub_add_right]
  push_cast; rfl

/-- `expSeq` only depends on values of `d` at positive indices. -/
lemma expSeq_congr {d d' : ℕ → K} (h : ∀ j, 1 ≤ j → d j = d' j) : expSeq d = expSeq d' := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [expSeq_zero]
    | succ k =>
      rw [expSeq_succ, expSeq_succ]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [h (j+1) (by omega), ih (k - j) (by omega)]

/-- `expSeq` commutes with ring homomorphisms. -/
lemma expSeq_map {L : Type*} [Field L] [CharZero L] (g : K →+* L) (d : ℕ → K) (n : ℕ) :
    expSeq (fun j => g (d j)) n = g (expSeq d n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [expSeq_zero]
    | succ k =>
      rw [expSeq_succ, expSeq_succ, map_div₀, map_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        rw [map_mul, ih (k - j) (by omega)]
      · simp

/-- The exponential power series associated to a "logarithmic derivative datum" `D`
(a power series with zero constant coefficient): `ES D = exp (∑ coeff j D * X^j / j)`. -/
noncomputable def ES (D : K⟦X⟧) : K⟦X⟧ := mk (expSeq (fun j => coeff j D))

lemma coeff_ES (D : K⟦X⟧) (n : ℕ) : coeff n (ES D) = expSeq (fun j => coeff j D) n := coeff_mk _ _

/-- `F` is the exponential of the datum `D`: `F(0) = 1` and `X F' = D F`. -/
def IsExp (D F : K⟦X⟧) : Prop := constantCoeff F = 1 ∧ X * derivative K F = D * F

lemma IsExp.coeff_succ {D F : K⟦X⟧} (h : IsExp D F) (k : ℕ) :
    coeff (k + 1) F * (k + 1) = ∑ ij ∈ Finset.antidiagonal (k + 1), coeff ij.1 D * coeff ij.2 F := by
  have := congrArg (coeff (k + 1)) h.2
  rwa [coeff_succ_X_mul, coeff_derivative, coeff_mul] at this

lemma IsExp.coeff_succ' {D F : K⟦X⟧} (h : IsExp D F) (hD : constantCoeff D = 0) (k : ℕ) :
    coeff (k + 1) F * (k + 1) = ∑ j ∈ Finset.range (k + 1), coeff (j + 1) D * coeff (k - j) F := by
  rw [h.coeff_succ, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => coeff a D * coeff b F),
    Finset.sum_range_succ']
  simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, ← coeff_zero_eq_constantCoeff_apply] at hD ⊢
  rw [hD, zero_mul, add_zero]

lemma isExp_ES (D : K⟦X⟧) (hD : constantCoeff D = 0) : IsExp D (ES D) := by
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_ES, expSeq_zero]
  · ext n
    cases n with
    | zero =>
      rw [coeff_zero_X_mul, coeff_zero_eq_constantCoeff_apply, map_mul, hD, zero_mul]
    | succ k =>
      rw [coeff_succ_X_mul, coeff_derivative, coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => coeff a D * coeff b (ES D)),
        Finset.sum_range_succ']
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      rw [← coeff_zero_eq_constantCoeff_apply] at hD
      rw [hD, zero_mul, add_zero, coeff_ES, expSeq_succ]
      have hk : ((k : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      rw [div_mul_cancel₀ _ hk]
      apply Finset.sum_congr rfl
      intro j _
      rw [coeff_ES]

lemma isExp_unique {D F G : K⟦X⟧} (hD : constantCoeff D = 0) (hF : IsExp D F) (hG : IsExp D G) :
    F = G := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, hF.1, hG.1]
    | succ k =>
      have hk : ((k : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      have h1 := hF.coeff_succ' hD k
      have h2 := hG.coeff_succ' hD k
      have : ∑ j ∈ Finset.range (k + 1), coeff (j + 1) D * coeff (k - j) F =
          ∑ j ∈ Finset.range (k + 1), coeff (j + 1) D * coeff (k - j) G := by
        apply Finset.sum_congr rfl
        intro j _
        rw [ih (k - j) (by omega)]
      rw [this, ← h2] at h1
      exact mul_right_cancel₀ hk h1

lemma isExp_mul {D D' F G : K⟦X⟧} (hF : IsExp D F) (hG : IsExp D' G) :
    IsExp (D + D') (F * G) := by
  refine ⟨by rw [map_mul, hF.1, hG.1, mul_one], ?_⟩
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_add]
  have e1 : X * (F * derivative K G) = F * (X * derivative K G) := by ring
  have e2 : X * (G * derivative K F) = G * (X * derivative K F) := by ring
  rw [e1, e2, hF.2, hG.2]; ring

lemma isExp_one : IsExp (0 : K⟦X⟧) 1 := by
  refine ⟨map_one _, ?_⟩
  rw [Derivation.map_one_eq_zero]; simp

lemma isExp_pow {D F : K⟦X⟧} (hF : IsExp D F) (n : ℕ) : IsExp (n • D) (F ^ n) := by
  induction n with
  | zero => simpa using isExp_one
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact isExp_mul ih hF

lemma ES_add {D D' : K⟦X⟧} (hD : constantCoeff D = 0) (hD' : constantCoeff D' = 0) :
    ES (D + D') = ES D * ES D' :=
  isExp_unique (by rw [map_add, hD, hD', add_zero]) (isExp_ES _ (by rw [map_add, hD, hD', add_zero]))
    (isExp_mul (isExp_ES D hD) (isExp_ES D' hD'))

lemma ES_nsmul {D : K⟦X⟧} (hD : constantCoeff D = 0) (n : ℕ) : ES (n • D) = (ES D) ^ n :=
  isExp_unique (by rw [map_nsmul, hD, smul_zero]) (isExp_ES _ (by rw [map_nsmul, hD, smul_zero]))
    (isExp_pow (isExp_ES D hD) n)

/- ### Expansion `X ↦ X^q` -/

lemma derivative_expand (q : ℕ) (hq : q ≠ 0) (F : K⟦X⟧) :
    derivative K (expand q hq F) = (q : K) • (X ^ (q - 1) * expand q hq (derivative K F)) := by
  ext n
  rw [coeff_derivative, coeff_expand, coeff_smul, coeff_X_pow_mul']
  by_cases h : q ∣ n + 1
  · rw [if_pos h]
    have hq1 : q - 1 ≤ n := by
      obtain ⟨c, hc⟩ := h
      rcases Nat.eq_zero_or_pos c with hc0 | hc0
      · subst hc0; simp at hc
      · have : q ≤ n + 1 := by rw [hc]; exact Nat.le_mul_of_pos_right q hc0
        omega
    rw [if_pos hq1]
    have h' : q ∣ n - (q - 1) := by
      have : n - (q - 1) = n + 1 - q := by omega
      rw [this]; exact (Nat.dvd_sub h (dvd_refl q))
    rw [coeff_expand, if_pos h', coeff_derivative]
    have e : (n - (q - 1)) / q + 1 = (n + 1) / q := by
      obtain ⟨c, hc⟩ := h
      have hc0 : 0 < c := by
        rcases Nat.eq_zero_or_pos c with hc0 | hc0
        · subst hc0; simp at hc
        · exact hc0
      have : n - (q - 1) = q * (c - 1) := by
        have := Nat.pos_of_ne_zero hq
        zify [Nat.one_le_iff_ne_zero.mpr hq, hc0, (show q - 1 ≤ n by omega)] at hc ⊢
        linarith
      rw [this, hc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hq),
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hq)]
      omega
    have e' : (((n - (q - 1)) / q : ℕ) : K) + 1 = (((n + 1) / q : ℕ) : K) := by exact_mod_cast e
    rw [e, e', smul_eq_mul]
    have e2 : ((n : K) + 1) = (q : K) * (((n + 1) / q : ℕ) : K) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' h]; push_cast; rfl
    rw [e2]
    ring
  · rw [if_neg h]
    by_cases h1 : q - 1 ≤ n
    · rw [if_pos h1, coeff_expand, if_neg]
      · simp
      · intro h2
        apply h
        have : n - (q - 1) = n + 1 - q := by omega
        rw [this] at h2
        have := Nat.dvd_add h2 (dvd_refl q)
        rwa [Nat.sub_add_cancel (by omega)] at this
    · rw [if_neg h1]; simp

lemma isExp_expand {D F : K⟦X⟧} (hF : IsExp D F) (q : ℕ) (hq : q ≠ 0) :
    IsExp ((q : K) • expand q hq D) (expand q hq F) := by
  refine ⟨by rw [constantCoeff_expand, hF.1], ?_⟩
  rw [derivative_expand, smul_mul_assoc, mul_smul_comm, ← mul_assoc, ← _root_.pow_succ',
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq), ← expand_X q hq, ← map_mul, hF.2, map_mul]

lemma ES_expand {D : K⟦X⟧} (hD : constantCoeff D = 0) (q : ℕ) (hq : q ≠ 0) :
    ES ((q : K) • expand q hq D) = expand q hq (ES D) :=
  isExp_unique (by rw [smul_eq_C_mul, map_mul, constantCoeff_C, constantCoeff_expand, hD, mul_zero])
    (isExp_ES _ (by rw [smul_eq_C_mul, map_mul, constantCoeff_C, constantCoeff_expand, hD, mul_zero]))
    (isExp_expand (isExp_ES D hD) q hq)

/- ### The exponential as a sum `∑ G^d / d!` -/

lemma coeff_pow_eq_zero_of_lt {G : K⟦X⟧} (hG : constantCoeff G = 0) {n d : ℕ} (h : n < d) :
    coeff n (G ^ d) = 0 := by
  obtain ⟨H, hH⟩ := X_dvd_iff.mpr hG
  rw [hH, mul_pow, coeff_X_pow_mul', if_neg (by omega)]

/-- `expComp G = ∑_{d} G^d / d!` for `G` with zero constant coefficient. -/
noncomputable def expComp (G : K⟦X⟧) : K⟦X⟧ :=
  mk fun n => ∑ d ∈ Finset.range (n + 1), ((d.factorial : K)⁻¹) * coeff n (G ^ d)

lemma coeff_expComp {G : K⟦X⟧} (hG : constantCoeff G = 0) (n M : ℕ) (hM : n ≤ M) :
    coeff n (expComp G) = ∑ d ∈ Finset.range (M + 1), ((d.factorial : K)⁻¹) * coeff n (G ^ d) := by
  rw [expComp, coeff_mk]
  apply Finset.sum_subset
  · intro d hd; simp only [Finset.mem_range] at hd ⊢; omega
  · intro d _ hd
    simp only [Finset.mem_range, not_lt] at hd
    rw [coeff_pow_eq_zero_of_lt hG (by omega), mul_zero]

lemma isExp_expComp {G : K⟦X⟧} (hG : constantCoeff G = 0) :
    IsExp (X * derivative K G) (expComp G) := by
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, expComp, coeff_mk]
    simp
  · ext n
    cases n with
    | zero =>
      rw [coeff_zero_X_mul, coeff_zero_eq_constantCoeff_apply, map_mul, map_mul,
        constantCoeff_X, zero_mul, zero_mul]
    | succ k =>
      rw [coeff_succ_X_mul, coeff_derivative, mul_assoc, coeff_succ_X_mul, coeff_mul]
      -- RHS
      have hR : ∀ ij ∈ Finset.antidiagonal k,
          coeff ij.1 (derivative K G) * coeff ij.2 (expComp G) =
          ∑ d ∈ Finset.range (k + 1), ((d.factorial : K)⁻¹) *
            (coeff ij.1 (derivative K G) * coeff ij.2 (G ^ d)) := by
        intro ij hij
        rw [Finset.mem_antidiagonal] at hij
        rw [coeff_expComp hG ij.2 k (by omega), Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _; ring
      rw [Finset.sum_congr rfl hR, Finset.sum_comm]
      simp_rw [← Finset.mul_sum, ← coeff_mul]
      -- coeff k (G' * G^d) = coeff (k+1) (G^(d+1)) * (k+1) / (d+1)
      have hd : ∀ d : ℕ, coeff k (derivative K G * G ^ d) =
          coeff (k + 1) (G ^ (d + 1)) * (k + 1) / (d + 1) := by
        intro d
        have h1 : derivative K (G ^ (d + 1)) = (d + 1 : K) • (G ^ d * derivative K G) := by
          rw [Derivation.leibniz_pow, Nat.add_sub_cancel, smul_eq_mul, ← Nat.cast_smul_eq_nsmul K]
          push_cast
          rfl
        have h2 := congrArg (coeff k) h1
        rw [coeff_derivative, coeff_smul] at h2
        have hd1 : ((d : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
        rw [eq_div_iff hd1, h2, smul_eq_mul]; ring
      simp_rw [hd]
      rw [coeff_expComp hG (k + 1) (k + 1) le_rfl, Finset.sum_range_succ']
      simp only [pow_zero, coeff_one, Nat.succ_ne_zero, if_false, mul_zero, add_zero]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      have hd1 : ((d : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
      rw [Nat.factorial_succ]
      push_cast
      field_simp

lemma ES_eq_expComp {G : K⟦X⟧} (hG : constantCoeff G = 0) :
    ES (X * derivative K G) = expComp G :=
  isExp_unique (by rw [map_mul, constantCoeff_X, zero_mul])
    (isExp_ES _ (by rw [map_mul, constantCoeff_X, zero_mul])) (isExp_expComp hG)

/-- The "integrated" series `G` of a datum `D`: `coeff j G = coeff j D / j`. -/
noncomputable def intg (D : K⟦X⟧) : K⟦X⟧ := mk fun j => if j = 0 then 0 else coeff j D / j

lemma constantCoeff_intg (D : K⟦X⟧) : constantCoeff (intg D) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, intg, coeff_mk]; simp

lemma coeff_intg (D : K⟦X⟧) (j : ℕ) (hj : j ≠ 0) : coeff j (intg D) = coeff j D / j := by
  rw [intg, coeff_mk, if_neg hj]

lemma X_mul_derivative_intg (D : K⟦X⟧) (hD : constantCoeff D = 0) :
    X * derivative K (intg D) = D := by
  ext n
  cases n with
  | zero => rw [coeff_zero_X_mul, coeff_zero_eq_constantCoeff_apply, hD]
  | succ k =>
    rw [coeff_succ_X_mul, coeff_derivative, coeff_intg _ _ (Nat.succ_ne_zero k)]
    have hk : ((k : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    push_cast
    rw [div_mul_cancel₀ _ hk]

lemma ES_eq_expComp_intg (D : K⟦X⟧) (hD : constantCoeff D = 0) : ES D = expComp (intg D) := by
  rw [← ES_eq_expComp (constantCoeff_intg D), X_mul_derivative_intg D hD]

lemma coeff_ES_eq_sum (D : K⟦X⟧) (hD : constantCoeff D = 0) (n : ℕ) :
    coeff n (ES D) = ∑ d ∈ Finset.range (n + 1), ((d.factorial : K)⁻¹) * coeff n ((intg D) ^ d) := by
  rw [ES_eq_expComp_intg D hD, expComp, coeff_mk]

/- ### Map along ring homs -/

lemma ES_map {L : Type*} [Field L] [CharZero L] (g : K →+* L) (D : K⟦X⟧) :
    map g (ES D) = ES (map g D) := by
  ext n
  rw [coeff_map, coeff_ES, coeff_ES, ← expSeq_map]
  exact congrArg (fun f => expSeq f n) (funext fun j => (coeff_map g j D).symm)

end Supercong

/- ## Section: Binom -/

set_option linter.unusedSectionVars false

namespace Supercong
open Finset

/-- c_m(k) = (mk)!/(k!)^m -/
def cm (m k : ℕ) : ℕ := (m * k).factorial / (k.factorial ^ m)

lemma factorial_mul_eq (m k : ℕ) :
    (m * k).factorial = (∏ i ∈ Finset.range m, ((i+1)*k).choose k) * k.factorial ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, pow_succ, show (m+1)*k = m*k + k by ring]
    have := Nat.choose_mul_factorial_mul_factorial (n := m*k+k) (k := k) (by omega)
    rw [Nat.add_sub_cancel] at this
    rw [← this, ih]; ring

lemma cm_eq_prod (m k : ℕ) : cm m k = ∏ i ∈ Finset.range m, ((i+1)*k).choose k := by
  unfold cm; rw [factorial_mul_eq]; exact Nat.mul_div_cancel _ (by positivity)

lemma cm_pos (m k : ℕ) : 0 < cm m k := by
  rw [cm_eq_prod]; apply prod_pos; intro i _; exact Nat.choose_pos (by nlinarith)

lemma cm_one (k : ℕ) : cm 1 k = 1 := by simp [cm_eq_prod]

lemma choose_two_dvd_cm (m k : ℕ) (hm : 2 ≤ m) : (2*k).choose k ∣ cm m k := by
  rw [cm_eq_prod]
  have : (1 : ℕ) ∈ Finset.range m := by simp; omega
  have h := dvd_prod_of_mem (fun i => ((i+1)*k).choose k) this
  simpa using h

/-- the index set of integers below `M` not divisible by `p` -/
def Iset (p M : ℕ) : Finset ℕ := (Finset.range M).filter (fun i => ¬ p ∣ i)

lemma mem_Iset {p M i : ℕ} : i ∈ Iset p M ↔ i < M ∧ ¬ p ∣ i := by
  simp [Iset]

/-- reindexing the part not divisible by `p` -/
lemma prod_filter_not_dvd_succ {M : Type*} [CommMonoid M] (p K : ℕ) (hp : 0 < p) (g : ℕ → M) :
    ∏ i ∈ (Finset.range (K*p)).filter (fun i => ¬ p ∣ i + 1), g (i+1) = ∏ i ∈ Iset p (K*p), g i := by
  apply prod_nbij' (fun i => i + 1) (fun i => i - 1)
  · intro i hi
    simp only [mem_filter, mem_range] at hi
    rw [mem_Iset]
    refine ⟨?_, hi.2⟩
    rcases Nat.lt_or_ge (i+1) (K*p) with h | h
    · exact h
    · exfalso
      have : i + 1 = K * p := by omega
      exact hi.2 (this ▸ dvd_mul_left p K)
  · intro i hi
    rw [mem_Iset] at hi
    simp only [mem_filter, mem_range]
    have : i ≠ 0 := by rintro rfl; exact hi.2 (dvd_zero p)
    refine ⟨by omega, ?_⟩
    rw [Nat.sub_add_cancel (by omega)]; exact hi.2
  · intro i _; simp
  · intro i hi
    rw [mem_Iset] at hi
    have : i ≠ 0 := by rintro rfl; exact hi.2 (dvd_zero p)
    omega
  · intro i _; rfl

/-- reindexing the part divisible by `p` -/
lemma prod_filter_dvd_succ {M : Type*} [CommMonoid M] (p K : ℕ) (hp : 0 < p) (g : ℕ → M) :
    ∏ i ∈ (Finset.range (K*p)).filter (fun i => p ∣ i + 1), g (i+1) = ∏ j ∈ Finset.range K, g ((j+1)*p) := by
  apply prod_nbij' (fun i => (i+1)/p - 1) (fun j => (j+1)*p - 1)
  · intro i hi
    simp only [mem_filter, mem_range] at hi
    simp only [mem_range]
    obtain ⟨c, hc⟩ := hi.2
    rw [hc, Nat.mul_div_cancel_left _ hp]
    have : c * p < (K+1) * p := by nlinarith
    have hcK : c < K + 1 := Nat.lt_of_mul_lt_mul_right this
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; omega
      · exact h
    omega
  · intro j hj
    simp only [mem_range] at hj
    simp only [mem_filter, mem_range]
    have h1 : 1 ≤ (j+1)*p := by nlinarith
    constructor
    · have : (j+1)*p ≤ K * p := Nat.mul_le_mul_right p hj
      omega
    · rw [Nat.sub_add_cancel h1]; exact dvd_mul_left p (j+1)
  · intro i hi
    simp only [mem_filter, mem_range] at hi
    obtain ⟨c, hc⟩ := hi.2
    rw [hc, Nat.mul_div_cancel_left _ hp]
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; omega
      · exact h
    rw [Nat.sub_add_cancel hc1, mul_comm]; omega
  · intro j hj
    have h1 : 1 ≤ (j+1)*p := by nlinarith
    rw [Nat.sub_add_cancel h1, Nat.mul_div_cancel _ hp]; simp
  · intro i hi
    simp only [mem_filter, mem_range] at hi
    obtain ⟨c, hc⟩ := hi.2
    rw [hc, Nat.mul_div_cancel_left _ hp]
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; omega
      · exact h
    rw [Nat.sub_add_cancel hc1, mul_comm]

lemma prod_range_mul_split {M : Type*} [CommMonoid M] (p K : ℕ) (hp : 0 < p) (g : ℕ → M) :
    ∏ i ∈ Finset.range (K*p), g (i+1) = (∏ j ∈ Finset.range K, g ((j+1)*p)) * ∏ i ∈ Iset p (K*p), g i := by
  rw [← prod_filter_mul_prod_filter_not (Finset.range (K*p)) (fun i => p ∣ i + 1),
    prod_filter_dvd_succ p K hp, prod_filter_not_dvd_succ p K hp]

lemma factorial_mul_p_split (p K : ℕ) (hp : 0 < p) :
    (K*p).factorial = p^K * K.factorial * ∏ i ∈ Iset p (K*p), i := by
  rw [Nat.factorial_eq_prod_range_add_one, prod_range_mul_split p K hp (fun i => i)]
  congr 1
  rw [← Finset.prod_range_add_one_eq_factorial, show p^K = ∏ _j ∈ Finset.range K, p by simp,
    ← prod_mul_distrib]
  apply prod_congr rfl; intro j _; ring

lemma ascFactorial_mul_p_split (p K D : ℕ) (hp : 0 < p) :
    (D*p+1).ascFactorial (K*p) = p^K * K.factorial * (D+K).choose K
        * ∏ i ∈ Iset p (K*p), (i + D*p) := by
  rw [Nat.ascFactorial_eq_prod_range]
  have h := prod_range_mul_split p K hp (fun i => i + D*p)
  simp only at h
  have : ∏ i ∈ Finset.range (K*p), (D*p + 1 + i) = ∏ i ∈ Finset.range (K*p), (i + 1 + D*p) := by
    apply prod_congr rfl; intro i _; ring
  rw [this, h]
  congr 1
  rw [mul_assoc, ← Nat.ascFactorial_eq_factorial_mul_choose, Nat.ascFactorial_eq_prod_range,
    show p^K = ∏ _j ∈ Finset.range K, p by simp, ← prod_mul_distrib]
  apply prod_congr rfl; intro j _; ring

/-- Jacobsthal's multiplicative identity. -/
theorem jacobsthal_identity (p K D : ℕ) (hp : 0 < p) :
    ((K + D) * p).choose (K * p) * ∏ i ∈ Iset p (K*p), i
      = (K + D).choose K * ∏ i ∈ Iset p (K*p), (i + D * p) := by
  have h1 := Nat.ascFactorial_eq_factorial_mul_choose (D*p) (K*p)
  rw [ascFactorial_mul_p_split p K D hp, factorial_mul_p_split p K hp] at h1
  have hpos : 0 < p^K * K.factorial := by positivity
  have h2 : p^K * K.factorial * ((K + D) * p).choose (K * p) * ∏ i ∈ Iset p (K*p), i
      = p^K * K.factorial * ((K + D).choose K * ∏ i ∈ Iset p (K*p), (i + D * p)) := by
    rw [show (K+D)*p = D*p + K*p by ring, add_comm K D]
    linarith [h1]
  have h3 : p^K * K.factorial * (((K + D) * p).choose (K * p) * ∏ i ∈ Iset p (K*p), i)
      = p^K * K.factorial * ((K + D).choose K * ∏ i ∈ Iset p (K*p), (i + D * p)) := by
    rw [← mul_assoc]; exact h2
  exact Nat.eq_of_mul_eq_mul_left hpos h3


lemma padicValNat_le_of_dvd (p : ℕ) [Fact p.Prime] {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
    padicValNat p a ≤ padicValNat p b := by
  rw [← padicValNat_dvd_iff_le hb]
  exact dvd_trans pow_padicValNat_dvd h

lemma kummer_central (p : ℕ) [Fact p.Prime] (u b : ℕ) (hb : Nat.log p (2*u) < b) :
    padicValNat p ((2*u).choose u) =
      ((Ico 1 b).filter (fun i => p^i ≤ u % p^i + u % p^i)).card := by
  rw [padicValNat_choose (by omega) hb]
  congr 1
  apply filter_congr
  intro i _
  rw [show 2*u - u = u by omega]

lemma sum_mod_eq_of_dvd {q a b : ℕ} (hq : 0 < q) (ha : a < q) (hb : b < q) (ha0 : 0 < a)
    (h : q ∣ a + b) : a + b = q := by
  obtain ⟨c, hc⟩ := h
  rcases c with _ | _ | c
  · omega
  · simpa using hc
  · exfalso
    rw [Nat.mul_succ, Nat.mul_succ] at hc
    omega

/-- the carry lemma -/
theorem carry_lemma (p : ℕ) [hp : Fact p.Prime] (u u' : ℕ) (hu : ¬ p ∣ u) (hu' : 0 < u') :
    padicValNat p (u + u') ≤ padicValNat p ((2*u).choose u) + padicValNat p ((2*u').choose u') := by
  have hu0 : 0 < u := Nat.pos_of_ne_zero (by rintro rfl; exact hu (dvd_zero p))
  set k := padicValNat p (u + u') with hk
  set b := k + 1 + 2*u + 2*u' with hb
  rw [kummer_central p u b (lt_of_lt_of_le (Nat.log_lt_self p (by omega)) (by omega)),
      kummer_central p u' b (lt_of_lt_of_le (Nat.log_lt_self p (by omega)) (by omega))]
  have hsub : Ico 1 (k+1) ⊆ (Ico 1 b).filter (fun i => p^i ≤ u % p^i + u % p^i) ∪
      (Ico 1 b).filter (fun i => p^i ≤ u' % p^i + u' % p^i) := by
    intro i hi
    rw [mem_Ico] at hi
    have hdvd : p^i ∣ u + u' := by
      rw [padicValNat_dvd_iff_le (by omega)]; omega
    have hq : 0 < p^i := pow_pos hp.out.pos i
    have ha : u % p^i < p^i := Nat.mod_lt _ hq
    have hb' : u' % p^i < p^i := Nat.mod_lt _ hq
    have ha0 : 0 < u % p^i := by
      rcases Nat.eq_zero_or_pos (u % p^i) with h | h
      · exfalso
        apply hu
        have : p ∣ p^i := dvd_pow_self p (by omega)
        exact dvd_trans this (Nat.dvd_of_mod_eq_zero h)
      · exact h
    have hsum : u % p^i + u' % p^i = p^i := by
      apply sum_mod_eq_of_dvd hq ha hb' ha0
      have : (u + u') % p^i = 0 := Nat.mod_eq_zero_of_dvd hdvd
      rw [Nat.add_mod] at this
      exact Nat.dvd_of_mod_eq_zero this
    rw [mem_union, mem_filter, mem_filter, mem_Ico]
    omega
  calc k = (Ico 1 (k+1)).card := by simp
    _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _

theorem carry_lemma_cm (p : ℕ) [hp : Fact p.Prime] (m u u' : ℕ) (hm : 2 ≤ m) (hu : ¬ p ∣ u)
    (hu' : 0 < u') :
    padicValNat p (u + u') ≤ padicValNat p (cm m u) + padicValNat p (cm m u') := by
  have h := carry_lemma p u u' hu hu'
  have h1 := padicValNat_le_of_dvd p (cm_pos m u).ne' (choose_two_dvd_cm m u hm)
  have h2 := padicValNat_le_of_dvd p (cm_pos m u').ne' (choose_two_dvd_cm m u' hm)
  omega

end Supercong

/- ## Section: Val -/

set_option linter.unusedSectionVars false

namespace Supercong
open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- the `p`-free part -/
def ordc (p n : ℕ) : ℕ := n / p ^ (padicValNat p n)

lemma val_decomp (n : ℕ) : n = p ^ (padicValNat p n) * ordc p n := by
  unfold ordc
  rw [Nat.mul_div_cancel' pow_padicValNat_dvd]

lemma ordc_ne_zero {n : ℕ} (hn : n ≠ 0) : ordc p n ≠ 0 := by
  intro h
  have := val_decomp (p := p) n
  rw [h, mul_zero] at this
  exact hn this

lemma not_dvd_ordc {n : ℕ} (hn : n ≠ 0) : ¬ p ∣ ordc p n := by
  intro h
  apply pow_succ_padicValNat_not_dvd (p := p) hn
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  conv_lhs => rw [val_decomp (p := p) n]
  rw [hc, pow_succ]; ring

lemma padicValNat_pow_mul {s u : ℕ} (hu : ¬ p ∣ u) : padicValNat p (p^s * u) = s := by
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero p)
  rw [padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hu0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hu, add_zero]

lemma ordc_pow_mul {s u : ℕ} (hu : ¬ p ∣ u) : ordc p (p^s * u) = u := by
  unfold ordc
  rw [padicValNat_pow_mul hu, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos s)]

lemma padicValNat_mul_pow {s u : ℕ} (hu : ¬ p ∣ u) : padicValNat p (u * p^s) = s := by
  rw [mul_comm]; exact padicValNat_pow_mul hu

lemma ordc_mul_pow {s u : ℕ} (hu : ¬ p ∣ u) : ordc p (u * p^s) = u := by
  rw [mul_comm]; exact ordc_pow_mul hu

lemma le_padicValNat_of_pow_dvd {t n : ℕ} (hn : n ≠ 0) (h : p^t ∣ n) : t ≤ padicValNat p n :=
  (padicValNat_dvd_iff_le hn).1 h

lemma pow_dvd_of_le_padicValNat {t n : ℕ} (h : t ≤ padicValNat p n) : p^t ∣ n :=
  dvd_trans (pow_dvd_pow p h) pow_padicValNat_dvd

/-- valuation of a sum when valuations differ -/
lemma padicValNat_add_of_lt {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : padicValNat p a < padicValNat p b) : padicValNat p (a + b) = padicValNat p a := by
  set va := padicValNat p a
  set vb := padicValNat p b
  have hb' : b = p^va * (p^(vb - va) * ordc p b) := by
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h.le]; exact val_decomp b
  have : a + b = p^va * (ordc p a + p^(vb - va) * ordc p b) := by
    rw [mul_add, ← hb']; congr 1; exact val_decomp a
  rw [this]
  apply padicValNat_pow_mul
  intro hd
  apply not_dvd_ordc (p := p) ha
  have hpd : p ∣ p^(vb - va) * ordc p b :=
    dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
  exact (Nat.dvd_add_left hpd).1 hd

lemma padicValNat_add_of_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : padicValNat p a = padicValNat p b) :
    padicValNat p (a + b) = padicValNat p a + padicValNat p (ordc p a + ordc p b) := by
  have : a + b = p^(padicValNat p a) * (ordc p a + ordc p b) := by
    rw [mul_add]
    conv_lhs => rw [val_decomp (p := p) a, val_decomp (p := p) b]
    rw [h]
  have h1 : ordc p a + ordc p b ≠ 0 := by have := ordc_ne_zero (p := p) ha; omega
  rw [this, padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) h1, padicValNat.prime_pow]

/-- the (V)-type bound in terms of `cm`. -/
theorem padicValNat_add_le_cm (m : ℕ) (hm : 2 ≤ m) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat p (a + b) ≤ padicValNat p a + padicValNat p b
      + padicValNat p (cm m (ordc p a)) + padicValNat p (cm m (ordc p b)) := by
  rcases lt_trichotomy (padicValNat p a) (padicValNat p b) with h | h | h
  · rw [padicValNat_add_of_lt ha hb h]; omega
  · rw [padicValNat_add_of_eq ha hb h]
    have := carry_lemma_cm p m (ordc p a) (ordc p b) hm (not_dvd_ordc ha)
      (Nat.pos_of_ne_zero (ordc_ne_zero hb))
    omega
  · rw [add_comm, padicValNat_add_of_lt hb ha h]; omega

lemma four_mul_padicValNat_factorial_le (h5 : 5 ≤ p) {d : ℕ} (hd : d ≠ 0) :
    4 * padicValNat p d.factorial + 1 ≤ d := by
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hd
  have : 4 * padicValNat p d.factorial ≤ (p - 1) * padicValNat p d.factorial :=
    Nat.mul_le_mul_right _ (by omega)
  omega

end Supercong

/- ## Section: Wolst -/

set_option linter.unusedSectionVars false

namespace Supercong
open Finset

variable {p : ℕ} [hp : Fact p.Prime]

lemma not_dvd_of_lt_prime {n : ℕ} (h0 : 0 < n) (h : n < p) : ¬ p ∣ n :=
  fun hd => absurd (Nat.le_of_dvd h0 hd) (not_le.mpr h)

lemma not_dvd_two (h5 : 5 ≤ p) : ¬ p ∣ 2 := not_dvd_of_lt_prime (by norm_num) (by omega)
lemma not_dvd_three (h5 : 5 ≤ p) : ¬ p ∣ 3 := not_dvd_of_lt_prime (by norm_num) (by omega)
lemma not_dvd_four (h5 : 5 ≤ p) : ¬ p ∣ 4 := not_dvd_of_lt_prime (by norm_num) (by omega)

lemma PV_two_inv_mul (h5 : 5 ≤ p) {k : ℤ} {x : ℚ_[p]} (hx : PV p k x) : PV p k (x / 2) := by
  have := PV_div_unit hx (not_dvd_two h5); simpa using this

/-- product expansion lemma -/
lemma PV_prod_one_add_sub {ι : Type*} (h5 : 5 ≤ p) (s : Finset ι) (x : ι → ℚ_[p]) (k : ℕ)
    (hx : ∀ i ∈ s, PV p k (x i)) :
    PV p (3*k) (∏ i ∈ s, (1 + x i) -
      (1 + (∑ i ∈ s, x i) + ((∑ i ∈ s, x i)^2 - ∑ i ∈ s, (x i)^2) / 2)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; exact PV_zero _
  | insert a s ha ih =>
    have hxa : PV p k (x a) := hx a (mem_insert_self a s)
    have ih' := ih (fun i hi => hx i (mem_insert_of_mem hi))
    rw [prod_insert ha, sum_insert ha, sum_insert ha]
    set P := ∏ i ∈ s, (1 + x i)
    set E := ∑ i ∈ s, x i
    set Q := ∑ i ∈ s, (x i)^2
    have key : (1 + x a) * P - (1 + (x a + E) + ((x a + E)^2 - (x a ^2 + Q))/2)
        = (P - (1 + E + (E^2 - Q)/2)) * (1 + x a) + x a * ((E^2 - Q)/2) := by ring
    rw [key]
    have h1 : PV p (3*k) ((P - (1 + E + (E^2 - Q)/2)) * (1 + x a)) := by
      have := PV_mul ih' (PV_add PV_one (PV_mono hxa (by omega)))
      simpa using this
    have h2 : PV p (3*k) (x a * ((E^2 - Q)/2)) := by
      have hE : PV p k E := PV_sum (fun i hi => hx i (mem_insert_of_mem hi))
      have hQ : PV p (2*k) Q := by
        apply PV_sum; intro i hi
        have := PV_pow (hx i (mem_insert_of_mem hi)) 2; simpa using this
      have hE2 : PV p (2*k) (E^2) := by have := PV_pow hE 2; simpa using this
      have := PV_mul hxa (PV_two_inv_mul h5 (PV_sub hE2 hQ))
      exact PV_mono this (by omega)
    exact PV_add h1 h2

/-- product of congruent factors -/
lemma PV_prod_sub_prod {ι : Type*} (s : Finset ι) (A B : ι → ℚ_[p]) (k : ℕ)
    (hA : ∀ i ∈ s, PV p 0 (A i)) (hB : ∀ i ∈ s, PV p 0 (B i))
    (hAB : ∀ i ∈ s, PV p k (A i - B i)) :
    PV p k (∏ i ∈ s, A i - ∏ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; exact PV_zero _
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    have key : A a * ∏ i ∈ s, A i - B a * ∏ i ∈ s, B i
        = A a * (∏ i ∈ s, A i - ∏ i ∈ s, B i) + (A a - B a) * ∏ i ∈ s, B i := by ring
    rw [key]
    apply PV_add
    · have := PV_mul (hA a (mem_insert_self a s))
        (ih (fun i hi => hA i (mem_insert_of_mem hi)) (fun i hi => hB i (mem_insert_of_mem hi))
          (fun i hi => hAB i (mem_insert_of_mem hi)))
      simpa using this
    · have := PV_mul (hAB a (mem_insert_self a s))
        (PV_prod (k := fun _ => 0) (fun i hi => hB i (mem_insert_of_mem hi)))
      simpa using this

lemma PV_prod_one_add_sub_one {ι : Type*} (s : Finset ι) (x : ι → ℚ_[p]) (k : ℕ)
    (hx : ∀ i ∈ s, PV p k (x i)) : PV p k (∏ i ∈ s, (1 + x i) - 1) := by
  have := PV_prod_sub_prod s (fun i => 1 + x i) (fun _ => 1) k
    (fun i hi => PV_add PV_one (PV_mono (hx i hi) (by omega))) (fun _ _ => PV_one)
    (fun i hi => by simpa using hx i hi)
  simpa using this

lemma norm_eq_one_of_norm_sub_one_lt {y : ℚ_[p]} (h : ‖y - 1‖ < 1) : ‖y‖ = 1 := by
  have h1 : ‖y‖ ≤ 1 := by
    have := Padic.nonarchimedean (y - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact le_trans this (max_le h.le le_rfl)
  have h2 : 1 ≤ ‖y‖ := by
    by_contra hc
    push_neg at hc
    have := Padic.nonarchimedean y (-(y - 1))
    rw [show y + -(y - 1) = 1 by ring, norm_one, norm_neg] at this
    have := lt_of_le_of_lt this (max_lt hc h)
    linarith
  linarith

lemma norm_eq_one_of_PV_sub_one {y : ℚ_[p]} (k : ℕ) (hk : 1 ≤ k) (h : PV p k (y - 1)) : ‖y‖ = 1 := by
  apply norm_eq_one_of_norm_sub_one_lt
  have h1 : PV p 1 (y - 1) := PV_mono h (by omega)
  unfold PV at h1
  refine lt_of_le_of_lt h1 ?_
  have := one_lt_p_real (p := p)
  rw [zpow_neg, zpow_one]; exact inv_lt_one_of_one_lt₀ this

lemma norm_prod_one_add {ι : Type*} (s : Finset ι) (x : ι → ℚ_[p]) (k : ℕ) (hk : 1 ≤ k)
    (hx : ∀ i ∈ s, PV p k (x i)) : ‖∏ i ∈ s, (1 + x i)‖ = 1 :=
  norm_eq_one_of_PV_sub_one k hk (PV_prod_one_add_sub_one s x k hx)


/- ### Wolstenholme-type sums -/

lemma sum_Iset_mul {M : Type*} [AddCommMonoid M] (q k' : ℕ) (hq : p ∣ q) (f : ℕ → M) :
    ∑ i ∈ Iset p (k' * q), f i = ∑ j ∈ Finset.range k', ∑ ρ ∈ Iset p q, f (j * q + ρ) := by
  induction k' with
  | zero => simp [Iset]
  | succ k' ih =>
    rw [sum_range_succ, ← ih]
    unfold Iset
    rw [sum_filter, sum_filter, sum_filter, add_mul, one_mul, sum_range_add]
    congr 1
    apply sum_congr rfl
    intro x _
    have : p ∣ k' * q + x ↔ p ∣ x := by
      constructor
      · intro h; exact (Nat.dvd_add_right (dvd_mul_of_dvd_right hq _)).1 h
      · intro h; exact dvd_add (dvd_mul_of_dvd_right hq _) h
    simp only [this]

lemma natCast_ne_zero_of_not_dvd {a : ℕ} (ha : ¬ p ∣ a) : (a : ℚ_[p]) ≠ 0 := by
  have : a ≠ 0 := by rintro rfl; exact ha (dvd_zero p)
  exact_mod_cast this

lemma PV_inv_sub_inv {a b : ℕ} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) {k : ℤ}
    (h : PV p k ((a : ℚ_[p]) - (b : ℚ_[p]))) :
    PV p k ((a : ℚ_[p])⁻¹ - (b : ℚ_[p])⁻¹) := by
  have ha0 := natCast_ne_zero_of_not_dvd ha
  have hb0 := natCast_ne_zero_of_not_dvd hb
  have : (a : ℚ_[p])⁻¹ - (b : ℚ_[p])⁻¹ = (-((a : ℚ_[p]) - (b : ℚ_[p]))) * (a : ℚ_[p])⁻¹ * (b : ℚ_[p])⁻¹ := by
    field_simp; ring
  rw [this]
  exact PV_mul_unit_inv (PV_mul_unit_inv (PV_neg h) ha) hb

lemma PV_inv_sq_sub_inv_sq {a b : ℕ} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) {k : ℤ}
    (h : PV p k ((a : ℚ_[p]) - (b : ℚ_[p]))) :
    PV p k (((a : ℚ_[p])⁻¹)^2 - ((b : ℚ_[p])⁻¹)^2) := by
  have : ((a : ℚ_[p])⁻¹)^2 - ((b : ℚ_[p])⁻¹)^2
      = ((a : ℚ_[p])⁻¹ - (b : ℚ_[p])⁻¹) * ((a : ℚ_[p])⁻¹ + (b : ℚ_[p])⁻¹) := by ring
  rw [this]
  have := PV_mul (PV_inv_sub_inv ha hb h) (PV_add (PV_inv_unit ha) (PV_inv_unit hb))
  simpa using this

lemma odd_p_pow (h5 : 5 ≤ p) (u : ℕ) : Odd (p ^ u) := by
  apply Odd.pow
  exact hp.out.odd_of_ne_two (by omega)

/-- the doubling bijection on `Iset p (p^u)` -/
lemma sum_Iset_double {M : Type*} [AddCommMonoid M] (h5 : 5 ≤ p) (u : ℕ) (hu : 1 ≤ u) (f : ℕ → M) :
    ∑ ρ ∈ Iset p (p^u), f ρ = ∑ ρ ∈ Iset p (p^u), f ((2 * ρ) % p^u) := by
  set q := p^u with hq
  have hq0 : 0 < q := pow_pos hp.out.pos u
  have hpq : p ∣ q := dvd_pow_self p (by omega)
  have hodd : Odd q := odd_p_pow h5 u
  obtain ⟨h, hh⟩ := hodd
  -- q = 2*h + 1
  have hp2 : ¬ p ∣ 2 := not_dvd_two h5
  have hph : ¬ p ∣ (h + 1) := by
    intro hd
    have h2 : p ∣ 2 * (h+1) := dvd_mul_of_dvd_right hd 2
    rw [show 2 * (h+1) = q + 1 by omega] at h2
    have h1 : p ∣ 1 := (Nat.dvd_add_right hpq).1 h2
    exact hp.out.one_lt.ne' (Nat.dvd_one.1 h1)
  have key : ∀ ρ, (2 * ((ρ * (h+1)) % q)) % q = ρ % q := by
    intro ρ
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, mul_comm 2 ρ, mul_assoc,
      show 2 * (h+1) = q + 1 by omega, mul_add, mul_one, mul_comm ρ q, Nat.mul_add_mod]
  have key2 : ∀ ρ, (((2 * ρ) % q) * (h+1)) % q = ρ % q := by
    intro ρ
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, show 2 * ρ * (h+1) = ρ * (2 * (h+1)) by ring,
      show 2 * (h+1) = q + 1 by omega, mul_add, mul_one, mul_comm ρ q, Nat.mul_add_mod]
  symm
  apply sum_nbij' (fun ρ => (2 * ρ) % q) (fun ρ => (ρ * (h+1)) % q)
  · intro ρ hρ
    rw [mem_Iset] at hρ ⊢
    refine ⟨Nat.mod_lt _ hq0, ?_⟩
    rw [Nat.dvd_mod_iff hpq]
    intro hd
    rcases (Nat.Prime.dvd_mul hp.out).1 hd with h1 | h1
    · exact hp2 h1
    · exact hρ.2 h1
  · intro ρ hρ
    rw [mem_Iset] at hρ ⊢
    refine ⟨Nat.mod_lt _ hq0, ?_⟩
    rw [Nat.dvd_mod_iff hpq]
    intro hd
    rcases (Nat.Prime.dvd_mul hp.out).1 hd with h1 | h1
    · exact hρ.2 h1
    · exact hph h1
  · intro ρ hρ
    rw [mem_Iset] at hρ
    rw [key2, Nat.mod_eq_of_lt hρ.1]
  · intro ρ hρ
    rw [mem_Iset] at hρ
    rw [key, Nat.mod_eq_of_lt hρ.1]
  · intro ρ _; rfl

lemma PV_natCast_sub_mod (q : ℕ) (u : ℕ) (hq : q = p^u) (n : ℕ) :
    PV p u ((n : ℚ_[p]) - ((n % q : ℕ) : ℚ_[p])) := by
  have : (n : ℚ_[p]) - ((n % q : ℕ) : ℚ_[p]) = ((q * (n / q) : ℕ) : ℚ_[p]) := by
    nth_rewrite 1 [← Nat.div_add_mod n q]
    push_cast; ring
  rw [this]
  apply PV_of_dvd
  rw [hq]; exact dvd_mul_right _ _

/-- (W2) core: sum of inverse squares over a full reduced residue system mod `p^u`. -/
lemma PV_sum_inv_sq_core (h5 : 5 ≤ p) (u : ℕ) (hu : 1 ≤ u) :
    PV p u (∑ ρ ∈ Iset p (p^u), ((ρ : ℚ_[p])⁻¹)^2) := by
  set q := p^u with hq
  have hpq : p ∣ q := dvd_pow_self p (by omega)
  set T := ∑ ρ ∈ Iset p q, ((ρ : ℚ_[p])⁻¹)^2 with hT
  have h1 : T = ∑ ρ ∈ Iset p q, ((((2*ρ) % q : ℕ) : ℚ_[p])⁻¹)^2 :=
    sum_Iset_double h5 u hu (fun ρ => ((ρ : ℚ_[p])⁻¹)^2)
  have h2 : PV p u (∑ ρ ∈ Iset p q, (((((2*ρ) % q : ℕ) : ℚ_[p])⁻¹)^2 - (((2*ρ : ℕ) : ℚ_[p])⁻¹)^2)) := by
    apply PV_sum
    intro ρ hρ
    rw [mem_Iset] at hρ
    have hnd : ¬ p ∣ 2 * ρ := by
      intro hd
      rcases (Nat.Prime.dvd_mul hp.out).1 hd with h1 | h1
      · exact not_dvd_two h5 h1
      · exact hρ.2 h1
    apply PV_inv_sq_sub_inv_sq
    · rw [Nat.dvd_mod_iff hpq]; exact hnd
    · exact hnd
    · have := PV_neg (PV_natCast_sub_mod q u hq (2*ρ))
      rw [neg_sub] at this; exact this
  have h3 : ∑ ρ ∈ Iset p q, (((2*ρ : ℕ) : ℚ_[p])⁻¹)^2 = T / 4 := by
    rw [hT, sum_div]
    apply sum_congr rfl
    intro ρ _
    push_cast
    have : (2 : ℚ_[p]) ≠ 0 := two_ne_zero
    field_simp
    ring
  rw [sum_sub_distrib, h3, ← h1] at h2
  have h4 : T = (T - T / 4) * ((4 : ℕ) : ℚ_[p]) / ((3 : ℕ) : ℚ_[p]) := by push_cast; ring
  rw [h4]
  exact PV_div_unit (PV_mul_norm_one h2 (norm_natCast_unit (not_dvd_four h5))) (not_dvd_three h5)

/-- (W2) -/
theorem PV_sum_inv_sq (h5 : 5 ≤ p) (u : ℕ) (hu : 1 ≤ u) (M : ℕ) (hM : p^u ∣ M) :
    PV p u (∑ i ∈ Iset p M, ((i : ℚ_[p])⁻¹)^2) := by
  obtain ⟨k', hk'⟩ := hM
  rw [hk', mul_comm, sum_Iset_mul (p^u) k' (dvd_pow_self p (by omega))]
  apply PV_sum
  intro j _
  have : ∑ ρ ∈ Iset p (p^u), (((j * p^u + ρ : ℕ) : ℚ_[p])⁻¹)^2
      = ∑ ρ ∈ Iset p (p^u), ((ρ : ℚ_[p])⁻¹)^2 +
        ∑ ρ ∈ Iset p (p^u), ((((j * p^u + ρ : ℕ) : ℚ_[p])⁻¹)^2 - ((ρ : ℚ_[p])⁻¹)^2) := by
    rw [← sum_add_distrib]; apply sum_congr rfl; intro ρ _; ring
  rw [this]
  apply PV_add (PV_sum_inv_sq_core h5 u hu)
  apply PV_sum
  intro ρ hρ
  rw [mem_Iset] at hρ
  have hpq : p ∣ p^u := dvd_pow_self p (by omega)
  apply PV_inv_sq_sub_inv_sq
  · intro hd
    exact hρ.2 ((Nat.dvd_add_right (dvd_mul_of_dvd_right hpq j)).1 hd)
  · exact hρ.2
  · have : ((j * p^u + ρ : ℕ) : ℚ_[p]) - (ρ : ℚ_[p]) = ((j * p^u : ℕ) : ℚ_[p]) := by
      push_cast; ring
    rw [this]
    exact PV_of_dvd (dvd_mul_left _ _)

/-- the involution `i ↦ M - i` on `Iset p M` -/
lemma sum_Iset_reflect {N : Type*} [AddCommMonoid N] (M : ℕ) (hM : p ∣ M) (f : ℕ → N) :
    ∑ i ∈ Iset p M, f i = ∑ i ∈ Iset p M, f (M - i) := by
  have hmem : ∀ i ∈ Iset p M, M - i ∈ Iset p M := by
    intro i hi
    rw [mem_Iset] at hi ⊢
    have hi0 : i ≠ 0 := by rintro rfl; exact hi.2 (dvd_zero p)
    refine ⟨by omega, ?_⟩
    intro hd
    apply hi.2
    have := Nat.dvd_sub hM hd
    rwa [Nat.sub_sub_self hi.1.le] at this
  symm
  apply sum_nbij' (fun i => M - i) (fun i => M - i) hmem hmem
  · intro i hi; rw [mem_Iset] at hi; omega
  · intro i hi; rw [mem_Iset] at hi; omega
  · intro i _; rfl

/-- (W1) -/
theorem PV_sum_inv (h5 : 5 ≤ p) (u : ℕ) (hu : 1 ≤ u) (M : ℕ) (hM : p^u ∣ M) :
    PV p (2*u) (∑ i ∈ Iset p M, (i : ℚ_[p])⁻¹) := by
  have hpM : p ∣ M := dvd_trans (dvd_pow_self p (by omega)) hM
  set S₁ := ∑ i ∈ Iset p M, (i : ℚ_[p])⁻¹ with hS₁
  have h2 : S₁ + S₁ = ∑ i ∈ Iset p M, ((i : ℚ_[p])⁻¹ + (((M - i : ℕ) : ℚ_[p])⁻¹)) := by
    rw [sum_add_distrib, hS₁]
    congr 1
    exact sum_Iset_reflect M hpM (fun i => (i : ℚ_[p])⁻¹)
  have h3 : ∀ i ∈ Iset p M, (i : ℚ_[p])⁻¹ + (((M - i : ℕ) : ℚ_[p])⁻¹)
      = (M : ℚ_[p]) * (-((i : ℚ_[p])⁻¹)^2 + (M : ℚ_[p]) * (((i : ℚ_[p])⁻¹)^2 * (((M - i : ℕ) : ℚ_[p])⁻¹))) := by
    intro i hi
    have hi' := hi
    rw [mem_Iset] at hi
    have hi0 : (i : ℚ_[p]) ≠ 0 := natCast_ne_zero_of_not_dvd hi.2
    have hMi : ¬ p ∣ M - i := by
      intro hd; apply hi.2
      have := Nat.dvd_sub hpM hd
      rwa [Nat.sub_sub_self hi.1.le] at this
    have hw0 : ((M - i : ℕ) : ℚ_[p]) ≠ 0 := natCast_ne_zero_of_not_dvd hMi
    have hsum : (M : ℚ_[p]) = (i : ℚ_[p]) + ((M - i : ℕ) : ℚ_[p]) := by
      rw [← Nat.cast_add, Nat.add_sub_cancel' hi.1.le]
    rw [hsum]
    field_simp
    ring
  rw [sum_congr rfl h3, ← mul_sum] at h2
  have h4 : PV p (2*u) (S₁ + S₁) := by
    have hMu : PV p u (M : ℚ_[p]) := PV_of_dvd hM
    have hA : PV p u (-(∑ i ∈ Iset p M, ((i : ℚ_[p])⁻¹)^2)) := PV_neg (PV_sum_inv_sq h5 u hu M hM)
    have hB : PV p u ((M : ℚ_[p]) * ∑ i ∈ Iset p M, ((i : ℚ_[p])⁻¹)^2 * (((M - i : ℕ) : ℚ_[p])⁻¹)) := by
      have := PV_mul hMu (PV_sum (k := 0) (fun i hi => by
        rw [mem_Iset] at hi
        have hMi : ¬ p ∣ M - i := by
          intro hd; apply hi.2
          have := Nat.dvd_sub hpM hd
          rwa [Nat.sub_sub_self hi.1.le] at this
        have := PV_mul (PV_pow (PV_inv_unit hi.2) 2) (PV_inv_unit hMi)
        simpa using this))
      simpa using this
    have hC := PV_mul hMu (PV_add hA hB)
    rw [h2, sum_add_distrib, sum_neg_distrib, ← mul_sum]
    exact PV_mono hC (by omega)
  have : S₁ = (S₁ + S₁) / 2 := by ring
  rw [this]
  exact PV_two_inv_mul h5 h4


/- ### Jacobsthal -/

lemma norm_prod_Iset (M : ℕ) : ‖∏ i ∈ Iset p M, (i : ℚ_[p])‖ = 1 := by
  rw [norm_prod]
  apply prod_eq_one
  intro i hi
  rw [mem_Iset] at hi
  exact norm_natCast_unit hi.2

lemma prod_Iset_ne_zero (M : ℕ) : ∏ i ∈ Iset p M, (i : ℚ_[p]) ≠ 0 := by
  intro h
  have := norm_prod_Iset (p := p) M
  rw [h, norm_zero] at this
  exact zero_ne_one this

lemma pow_dvd_mul_p {s K : ℕ} (hs : 1 ≤ s) (hK : p^(s-1) ∣ K) : p^s ∣ K * p := by
  obtain ⟨c, hc⟩ := hK
  have : p^s = p^(s-1) * p := by rw [← pow_succ]; congr 1; omega
  rw [this, hc]; exact ⟨c, by ring⟩

lemma prod_X_eq (K D : ℕ) :
    ∏ i ∈ Iset p (K*p), ((i + D*p : ℕ) : ℚ_[p])
      = (∏ i ∈ Iset p (K*p), (i : ℚ_[p])) *
        ∏ i ∈ Iset p (K*p), (1 + ((D*p : ℕ) : ℚ_[p]) * (i : ℚ_[p])⁻¹) := by
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  rw [mem_Iset] at hi
  have := natCast_ne_zero_of_not_dvd hi.2
  push_cast
  field_simp

/-- Jacobsthal: weak form (any prime). -/
theorem PV_X_sub_Y_weak (s : ℕ) (hs : 1 ≤ s) (K D : ℕ) (hD : p^(s-1) ∣ D) :
    PV p s ((∏ i ∈ Iset p (K*p), ((i + D*p : ℕ) : ℚ_[p])) - ∏ i ∈ Iset p (K*p), (i : ℚ_[p])) := by
  have hDp : p^s ∣ D*p := pow_dvd_mul_p hs hD
  rw [prod_X_eq, ← _root_.mul_sub_one, mul_comm]
  apply PV_mul_norm_one _ (norm_prod_Iset _)
  apply PV_prod_one_add_sub_one
  intro i hi
  rw [mem_Iset] at hi
  exact PV_mul_unit_inv (PV_of_dvd hDp) hi.2

/-- Jacobsthal: strong form. -/
theorem PV_X_sub_Y (h5 : 5 ≤ p) (s : ℕ) (hs : 1 ≤ s) (K D : ℕ) (hK : p^(s-1) ∣ K)
    (hD : p^(s-1) ∣ D) :
    PV p (3*s) ((∏ i ∈ Iset p (K*p), ((i + D*p : ℕ) : ℚ_[p])) - ∏ i ∈ Iset p (K*p), (i : ℚ_[p])) := by
  have hDp : p^s ∣ D*p := pow_dvd_mul_p hs hD
  have hKp : p^s ∣ K*p := pow_dvd_mul_p hs hK
  rw [prod_X_eq, ← _root_.mul_sub_one, mul_comm (∏ i ∈ Iset p (K*p), (i : ℚ_[p]))]
  apply PV_mul_norm_one _ (norm_prod_Iset _)
  set I := Iset p (K*p)
  set x : ℕ → ℚ_[p] := fun i => ((D*p : ℕ) : ℚ_[p]) * (i : ℚ_[p])⁻¹ with hx
  have hxs : ∀ i ∈ I, PV p s (x i) := by
    intro i hi
    rw [mem_Iset] at hi
    exact PV_mul_unit_inv (PV_of_dvd hDp) hi.2
  have hmain := PV_prod_one_add_sub h5 I x s hxs
  have hE : PV p (3*s) (∑ i ∈ I, x i) := by
    have : ∑ i ∈ I, x i = ((D*p : ℕ) : ℚ_[p]) * ∑ i ∈ I, (i : ℚ_[p])⁻¹ := by
      rw [mul_sum]
    rw [this]
    have := PV_mul (PV_of_dvd hDp) (PV_sum_inv h5 s hs (K*p) hKp)
    exact PV_mono this (by omega)
  have hQ : PV p (3*s) (∑ i ∈ I, (x i)^2) := by
    have : ∑ i ∈ I, (x i)^2 = (((D*p : ℕ) : ℚ_[p]))^2 * ∑ i ∈ I, ((i : ℚ_[p])⁻¹)^2 := by
      rw [mul_sum]; apply sum_congr rfl; intro i _; rw [hx]; ring
    rw [this]
    have h1 := PV_pow (PV_of_dvd hDp) 2
    have := PV_mul h1 (PV_sum_inv_sq h5 s hs (K*p) hKp)
    exact PV_mono this (by omega)
  have hE2 : PV p (3*s) ((∑ i ∈ I, x i)^2) := by
    have := PV_pow hE 2; exact PV_mono this (by omega)
  have : ∏ i ∈ I, (1 + x i) - 1
      = (∏ i ∈ I, (1 + x i) - (1 + (∑ i ∈ I, x i) + ((∑ i ∈ I, x i)^2 - ∑ i ∈ I, (x i)^2) / 2))
        + (∑ i ∈ I, x i) + ((∑ i ∈ I, x i)^2 - ∑ i ∈ I, (x i)^2) / 2 := by ring
  rw [this]
  exact PV_add (PV_add hmain hE) (PV_two_inv_mul h5 (PV_sub hE2 hQ))

/- ### consequences for `cm` -/

lemma cm_mul_p_nat (m K : ℕ) :
    cm m (K*p) * (∏ i ∈ Iset p (K*p), i)^m
      = cm m K * ∏ i ∈ Finset.range m, ∏ j ∈ Iset p (K*p), (j + (i*K)*p) := by
  rw [cm_eq_prod, cm_eq_prod,
    show (∏ i ∈ Iset p (K*p), i)^m = ∏ _i ∈ Finset.range m, ∏ j ∈ Iset p (K*p), j by simp,
    ← prod_mul_distrib, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  have := jacobsthal_identity p K (i*K) hp.out.pos
  rw [show (K + i*K)*p = (i+1)*(K*p) by ring, show K + i*K = (i+1)*K by ring] at this
  exact this

lemma cm_mul_p_eq (m K : ℕ) :
    (cm m (K*p) : ℚ_[p]) = (cm m K : ℚ_[p]) *
      ∏ i ∈ Finset.range m, (∏ j ∈ Iset p (K*p), ((j + (i*K)*p : ℕ) : ℚ_[p])) /
        (∏ j ∈ Iset p (K*p), (j : ℚ_[p])) := by
  have h := cm_mul_p_nat (p := p) m K
  have hY := prod_Iset_ne_zero (p := p) (K*p)
  have h' : ((cm m (K*p) * (∏ i ∈ Iset p (K*p), i)^m : ℕ) : ℚ_[p])
      = ((cm m K * ∏ i ∈ Finset.range m, ∏ j ∈ Iset p (K*p), (j + (i*K)*p) : ℕ) : ℚ_[p]) := by rw [h]
  push_cast at h'
  rw [prod_div_distrib, prod_const, card_range, mul_div_assoc', eq_div_iff (pow_ne_zero m hY)]
  push_cast
  exact h'

lemma norm_X_div_Y (K D : ℕ) :
    ‖(∏ j ∈ Iset p (K*p), ((j + D*p : ℕ) : ℚ_[p])) / (∏ j ∈ Iset p (K*p), (j : ℚ_[p]))‖ = 1 := by
  rw [norm_div, norm_prod_Iset, div_one, norm_prod]
  apply prod_eq_one
  intro j hj
  rw [mem_Iset] at hj
  apply norm_natCast_unit
  intro hd
  exact hj.2 ((Nat.dvd_add_left (dvd_mul_left p D)).1 hd)

theorem norm_cm_mul_p (m K : ℕ) : ‖(cm m (K*p) : ℚ_[p])‖ = ‖(cm m K : ℚ_[p])‖ := by
  rw [cm_mul_p_eq, norm_mul, norm_prod]
  rw [prod_eq_one (fun i _ => norm_X_div_Y K (i*K)), mul_one]

theorem norm_cm_mul_pow (m u t : ℕ) : ‖(cm m (u * p^t) : ℚ_[p])‖ = ‖(cm m u : ℚ_[p])‖ := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← mul_assoc, norm_cm_mul_p, ih]

lemma padicValNat_cm_mul_pow (m u t : ℕ) :
    padicValNat p (cm m (u * p^t)) = padicValNat p (cm m u) := by
  have h := norm_cm_mul_pow (p := p) m u t
  rw [norm_natCast_eq (cm_pos _ _).ne', norm_natCast_eq (cm_pos _ _).ne'] at h
  have := zpow_right_injective₀ (p_real_pos (p := p)) (one_lt_p_real (p := p)).ne' h
  omega

lemma PV_X_div_Y_sub_one {k : ℤ} (K D : ℕ)
    (h : PV p k ((∏ i ∈ Iset p (K*p), ((i + D*p : ℕ) : ℚ_[p])) - ∏ i ∈ Iset p (K*p), (i : ℚ_[p]))) :
    PV p k ((∏ j ∈ Iset p (K*p), ((j + D*p : ℕ) : ℚ_[p])) / (∏ j ∈ Iset p (K*p), (j : ℚ_[p])) - 1) := by
  have hY := prod_Iset_ne_zero (p := p) (K*p)
  have : (∏ j ∈ Iset p (K*p), ((j + D*p : ℕ) : ℚ_[p])) / (∏ j ∈ Iset p (K*p), (j : ℚ_[p])) - 1
      = ((∏ i ∈ Iset p (K*p), ((i + D*p : ℕ) : ℚ_[p])) - ∏ i ∈ Iset p (K*p), (i : ℚ_[p]))
        * (∏ j ∈ Iset p (K*p), (j : ℚ_[p]))⁻¹ := by
    field_simp
  rw [this]
  apply PV_mul_norm_one h
  rw [norm_inv, norm_prod_Iset, inv_one]

lemma cm_mul_p_sub_of_PV (m K : ℕ) (k : ℕ)
    (h : ∀ i ∈ Finset.range m, PV p k ((∏ j ∈ Iset p (K*p), ((j + (i*K)*p : ℕ) : ℚ_[p])) /
        (∏ j ∈ Iset p (K*p), (j : ℚ_[p])) - 1)) :
    PV p (k + padicValNat p (cm m K)) ((cm m (K*p) : ℚ_[p]) - (cm m K : ℚ_[p])) := by
  rw [cm_mul_p_eq, ← _root_.mul_sub_one]
  have := PV_mul (PV_prod_one_add_sub_one (Finset.range m)
    (fun i => (∏ j ∈ Iset p (K*p), ((j + (i*K)*p : ℕ) : ℚ_[p])) /
        (∏ j ∈ Iset p (K*p), (j : ℚ_[p])) - 1) k (fun i hi => h i hi)) (PV_nat_val (cm m K))
  simp only [add_sub_cancel] at this
  rw [mul_comm]
  exact this

/-- weak congruence (any prime): `cm m (K p) ≡ cm m K mod p^s` when `p^(s-1) ∣ K`. -/
theorem cm_mul_p_sub_weak (m K s : ℕ) (hs : 1 ≤ s) (hK : p^(s-1) ∣ K) :
    PV p s ((cm m (K*p) : ℚ_[p]) - (cm m K : ℚ_[p])) := by
  have := cm_mul_p_sub_of_PV (p := p) m K s (fun i _ =>
    PV_X_div_Y_sub_one K (i*K) (PV_X_sub_Y_weak s hs K (i*K) (dvd_mul_of_dvd_right hK i)))
  exact PV_mono this (by omega)

/-- strong congruence (`p ≥ 5`). -/
theorem cm_mul_p_sub (h5 : 5 ≤ p) (m K s : ℕ) (hs : 1 ≤ s) (hK : p^(s-1) ∣ K) :
    PV p (3*s + padicValNat p (cm m K)) ((cm m (K*p) : ℚ_[p]) - (cm m K : ℚ_[p])) :=
  cm_mul_p_sub_of_PV (p := p) m K (3*s) (fun i _ =>
    PV_X_div_Y_sub_one K (i*K) (PV_X_sub_Y h5 s hs K (i*K) hK (dvd_mul_of_dvd_right hK i)))

theorem cm_pow_sub (h5 : 5 ≤ p) (m u s : ℕ) (hs : 1 ≤ s) :
    PV p (3*s + padicValNat p (cm m u))
      ((cm m (u * p^s) : ℚ_[p]) - (cm m (u * p^(s-1)) : ℚ_[p])) := by
  have h := cm_mul_p_sub h5 m (u * p^(s-1)) s hs (dvd_mul_left _ _)
  rw [padicValNat_cm_mul_pow] at h
  rw [show u * p^s = u * p^(s-1) * p by rw [mul_assoc, ← pow_succ]; congr 2; omega]
  exact h

theorem cm_pow_sub_weak (m u s : ℕ) (hs : 1 ≤ s) :
    PV p s ((cm m (u * p^s) : ℚ_[p]) - (cm m (u * p^(s-1)) : ℚ_[p])) := by
  have h := cm_mul_p_sub_weak m (u * p^(s-1)) s hs (dvd_mul_left _ _)
  rw [show u * p^s = u * p^(s-1) * p by rw [mul_assoc, ← pow_succ]; congr 2; omega]
  exact h

end Supercong

/- ## Section: LemmaH -/

set_option linter.unusedSectionVars false

namespace Supercong
open Finset PowerSeries

variable {p : ℕ} [hp : Fact p.Prime]

/- ### coefficient bounds for products and powers -/

lemma PV_coeff_mul {A B : ℚ_[p]⟦X⟧} {k l : ℤ} (hA : ∀ n, PV p k (coeff n A))
    (hB : ∀ n, PV p l (coeff n B)) (n : ℕ) : PV p (k + l) (coeff n (A * B)) := by
  rw [coeff_mul]
  apply PV_sum
  intro x _
  exact PV_mul (hA _) (hB _)

lemma PV_coeff_pow {A : ℚ_[p]⟦X⟧} {k : ℤ} (hA : ∀ n, PV p k (coeff n A)) (d : ℕ) (n : ℕ) :
    PV p (d * k) (coeff n (A ^ d)) := by
  induction d generalizing n with
  | zero =>
    simp only [pow_zero, coeff_one, Nat.cast_zero, zero_mul]
    split_ifs
    · exact PV_one
    · exact PV_zero _
  | succ d ih =>
    rw [pow_succ]
    have := PV_coeff_mul ih hA n
    exact PV_mono this (le_of_eq (by push_cast; ring))

/- ### the data `Dc` and `DD` -/

/-- `Dc m = ∑_{i ≥ 1} cm m i X^i` -/
noncomputable def Dc (m : ℕ) : ℚ_[p]⟦X⟧ := mk fun i => if i = 0 then 0 else (cm m i : ℚ_[p])

lemma coeff_Dc (m i : ℕ) : coeff i (Dc (p := p) m) = if i = 0 then 0 else (cm m i : ℚ_[p]) :=
  coeff_mk _ _

lemma coeff_Dc_of_ne (m : ℕ) {i : ℕ} (hi : i ≠ 0) : coeff i (Dc (p := p) m) = (cm m i : ℚ_[p]) := by
  rw [coeff_Dc, if_neg hi]

lemma constantCoeff_Dc (m : ℕ) : constantCoeff (Dc (p := p) m) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_Dc, if_pos rfl]

/-- `DD m = p • Dc m - p • expand p (Dc m)` -/
noncomputable def DD (m : ℕ) : ℚ_[p]⟦X⟧ :=
  (p : ℚ_[p]) • Dc m - (p : ℚ_[p]) • expand p hp.out.ne_zero (Dc m)

lemma coeff_DD (m i : ℕ) : coeff i (DD (p := p) m) =
    (p : ℚ_[p]) * (coeff i (Dc m) - if p ∣ i then coeff (i / p) (Dc m) else 0) := by
  rw [DD, map_sub, coeff_smul, coeff_smul, coeff_expand, smul_eq_mul, smul_eq_mul, mul_sub]

lemma constantCoeff_DD (m : ℕ) : constantCoeff (DD (p := p) m) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_DD, if_pos (dvd_zero p), Nat.zero_div,
    coeff_Dc, if_pos rfl]; simp

lemma constantCoeff_smul_DD (m : ℕ) (c : ℚ_[p]) : constantCoeff (c • DD (p := p) m) = 0 := by
  rw [smul_eq_C_mul, map_mul, constantCoeff_C, constantCoeff_DD, mul_zero]

/-- the bound (G) on the coefficients of `intg (DD m)` -/
theorem PV_coeff_intg_DD (h5 : 5 ≤ p) (m : ℕ) {i : ℕ} (hi : i ≠ 0) :
    PV p (1 + 2 * padicValNat p i + padicValNat p (cm m (ordc p i)))
      (coeff i (intg (DD (p := p) m))) := by
  rw [coeff_intg _ _ hi, coeff_DD]
  set s := padicValNat p i with hs
  set u := ordc p i with hu
  have hpu : ¬ p ∣ u := not_dvd_ordc hi
  have hi' : i = u * p^s := by rw [mul_comm]; exact val_decomp (p := p) i
  rcases Nat.eq_zero_or_pos s with h0 | hpos
  · -- p ∤ i
    have hnd : ¬ p ∣ i := by
      intro hd
      have := (dvd_iff_padicValNat_ne_zero hi).1 hd
      rw [← hs] at this; exact this h0
    rw [if_neg hnd, sub_zero, coeff_Dc_of_ne _ hi]
    have hui : u = i := by rw [hi', h0, pow_zero, mul_one]
    rw [hui, h0]
    have := PV_div_unit (PV_mul (PV_p (p := p)) (PV_nat_val (cm m i))) hnd
    exact PV_mono this (by push_cast; omega)
  · have hd : p ∣ i := by
      rw [hi']; exact dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) u
    rw [if_pos hd, coeff_Dc_of_ne _ hi]
    have hdiv : i / p = u * p^(s-1) := by
      rw [hi', show s = (s - 1) + 1 by omega, pow_succ, ← mul_assoc, Nat.mul_div_cancel _ hp.out.pos]
      simp
    have hne : i / p ≠ 0 := by
      rw [hdiv]
      exact Nat.mul_ne_zero (by intro h0; rw [h0] at hpu; exact hpu (dvd_zero p))
        (pow_ne_zero _ hp.out.ne_zero)
    rw [coeff_Dc_of_ne _ hne, hdiv]
    have h1 := cm_pow_sub h5 m u s hpos
    rw [← hi'] at h1
    have h2 := PV_div_nat (PV_mul (PV_p (p := p)) h1) i hi
    refine PV_mono h2 ?_
    rw [← hs]; push_cast; omega

lemma PV_coeff_intg_DD_one (h5 : 5 ≤ p) (m : ℕ) (i : ℕ) :
    PV p 1 (coeff i (intg (DD (p := p) m))) := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_intg]; exact PV_zero _
  · exact PV_mono (PV_coeff_intg_DD h5 m hpos.ne') (by omega)

/- ### Lemma H -/

/-- the exponent `ψ` -/
def ψ (κ β v : ℕ) : ℤ := 1 + κ + 2 * min (v : ℤ) (κ + 1) + max 0 (min (β : ℤ) (κ + 1 - v))

lemma ψ_le (κ β v : ℕ) : ψ κ β v ≤ 3 * (κ + 1) := by
  unfold ψ; omega

lemma ψ_le' (κ β v : ℕ) : ψ κ β v ≤ 2 * (κ + 1) + v := by
  unfold ψ; omega

lemma intg_smul (c : ℚ_[p]) (D : ℚ_[p]⟦X⟧) : intg (c • D) = c • intg D := by
  ext j
  rw [coeff_smul, intg, intg, coeff_mk, coeff_mk]
  split_ifs
  · simp
  · rw [coeff_smul, smul_eq_mul, smul_eq_mul, mul_div_assoc]

lemma coeff_smul_pow (c : ℚ_[p]) (G : ℚ_[p]⟦X⟧) (d n : ℕ) :
    coeff n ((c • G)^d) = c^d * coeff n (G^d) := by
  rw [smul_pow, coeff_smul, smul_eq_mul]

/-- Lemma H. -/
theorem lemmaH (h5 : 5 ≤ p) (m : ℕ) (hm : 2 ≤ m) (κ N : ℕ) (hN : p^κ ∣ N) {i : ℕ} (hi : i ≠ 0) :
    PV p (ψ κ (padicValNat p (cm m (ordc p i))) (padicValNat p i))
      (coeff i (ES ((N : ℚ_[p]) • DD (p := p) m))) := by
  rw [coeff_ES_eq_sum _ (constantCoeff_smul_DD m _), intg_smul]
  set G := intg (DD (p := p) m) with hG
  have hG0 : constantCoeff G = 0 := constantCoeff_intg _
  have hg1 : ∀ j, PV p 1 (coeff j G) := PV_coeff_intg_DD_one h5 m
  have hNκ : PV p κ (N : ℚ_[p]) := PV_of_dvd hN
  apply PV_sum
  intro d _
  rw [coeff_smul_pow]
  rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ 3 ≤ d by omega) with rfl | rfl | rfl | hd
  · -- d = 0
    simp only [pow_zero, coeff_one, if_neg hi, mul_zero]; exact PV_zero _
  · -- d = 1
    simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_mul, pow_one]
    have := PV_mul hNκ (PV_coeff_intg_DD h5 m hi)
    refine PV_mono this ?_
    unfold ψ; omega
  · -- d = 2
    have hfac2 : ((Nat.factorial 2 : ℕ) : ℚ_[p])⁻¹ = ((2 : ℕ) : ℚ_[p])⁻¹ := by
      norm_num [Nat.factorial]
    rw [hfac2, pow_two G, coeff_mul, mul_sum, mul_comm (((2:ℕ):ℚ_[p])⁻¹)]
    apply PV_mul_unit_inv _ (not_dvd_two h5)
    apply PV_sum
    intro x hx
    rw [mem_antidiagonal] at hx
    rcases Nat.eq_zero_or_pos x.1 with ha | ha
    · rw [ha, coeff_zero_eq_constantCoeff_apply, hG0]; simp only [zero_mul, mul_zero]; exact PV_zero _
    rcases Nat.eq_zero_or_pos x.2 with hb | hb
    · rw [hb, coeff_zero_eq_constantCoeff_apply, hG0]; simp only [zero_mul, mul_zero]; exact PV_zero _
    have hN2 : PV p (2 * κ) ((N : ℚ_[p])^2) := by have := PV_pow hNκ 2; simpa using this
    have := PV_mul hN2 (PV_mul (PV_coeff_intg_DD h5 m ha.ne') (PV_coeff_intg_DD h5 m hb.ne'))
    refine PV_mono this ?_
    have hv := padicValNat_add_le_cm (p := p) m hm ha.ne' hb.ne'
    rw [hx] at hv
    have := ψ_le' κ (padicValNat p (cm m (ordc p i))) (padicValNat p i)
    omega
  · -- d ≥ 3
    have hd0 : d ≠ 0 := by omega
    have hfac : PV p (-(padicValNat p d.factorial : ℤ)) ((d.factorial : ℚ_[p])⁻¹) :=
      PV_nat_inv _ (Nat.factorial_ne_zero d)
    have hNd : PV p ((d : ℤ) * κ) ((N : ℚ_[p])^d) :=
      PV_mono (PV_pow hNκ d) (le_of_eq (by push_cast; ring))
    have hGd : PV p (d : ℤ) (coeff i (G^d)) :=
      PV_mono (PV_coeff_pow hg1 d i) (le_of_eq (by push_cast; ring))
    have := PV_mul hfac (PV_mul hNd hGd)
    refine PV_mono this ?_
    have h4 := four_mul_padicValNat_factorial_le h5 hd0
    have h4' : (4:ℤ) * (padicValNat p d.factorial : ℤ) + 1 ≤ d := by exact_mod_cast h4
    have hψ := ψ_le κ (padicValNat p (cm m (ordc p i))) (padicValNat p i)
    have hv : (padicValNat p d.factorial : ℤ) ≤ d - 3 := by omega
    have hdk : (3:ℤ) * κ ≤ (d : ℤ) * κ := by
      apply mul_le_mul_of_nonneg_right _ (by omega)
      omega
    omega

end Supercong

/- ## Section: Comb -/

set_option linter.unusedSectionVars false

namespace Supercong
open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- the exponent attached to a term `l t` of the `t`-th factor -/
def ψt (p : ℕ) (r : ℕ) (β : ℕ → ℕ) (x : ℕ) (t : ℕ) : ℤ :=
  r + 2 * min (padicValNat p x : ℤ) r - 3 * t
    + max 0 (min (β (ordc p x) : ℤ) (r - padicValNat p x))

lemma sum_ge_one {S : Finset ℕ} {f : ℕ → ℤ} (hf : ∀ t ∈ S, 0 ≤ f t) {a : ℕ} (ha : a ∈ S) :
    f a ≤ ∑ t ∈ S, f t :=
  single_le_sum hf ha

lemma sum_ge_two {S : Finset ℕ} {f : ℕ → ℤ} (hf : ∀ t ∈ S, 0 ≤ f t) {a b : ℕ} (ha : a ∈ S)
    (hb : b ∈ S) (hab : a ≠ b) : f a + f b ≤ ∑ t ∈ S, f t := by
  have hsub : ({a, b} : Finset ℕ) ⊆ S := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
  have := sum_le_sum_of_subset_of_nonneg hsub (fun t ht _ => hf t ht)
  rwa [sum_pair hab] at this

lemma sum_ge_three {S : Finset ℕ} {f : ℕ → ℤ} (hf : ∀ t ∈ S, 0 ≤ f t) {a b c : ℕ} (ha : a ∈ S)
    (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    f a + f b + f c ≤ ∑ t ∈ S, f t := by
  have hsub : ({a, b, c} : Finset ℕ) ⊆ S := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have := sum_le_sum_of_subset_of_nonneg hsub (fun t ht _ => hf t ht)
  have hnot : a ∉ ({b, c} : Finset ℕ) := by simp [hab, hac]
  rwa [sum_insert hnot, sum_pair hbc, ← add_assoc] at this

/-- The combinatorial lemma. -/
theorem comb_lemma (r : ℕ) (hr : 1 ≤ r) (S : Finset ℕ) (hS : ∀ t ∈ S, t < r) (h0 : 0 ∈ S)
    (l : ℕ → ℕ) (hl : ∀ t ∈ S, l t ≠ 0 ∧ p^t ∣ l t) (hsum : p^r ∣ ∑ t ∈ S, l t)
    (β : ℕ → ℕ) (hβ : ∀ u u', ¬ p ∣ u → ¬ p ∣ u' → padicValNat p (u + u') ≤ β u + β u') :
    (3 * r : ℤ) ≤ ∑ t ∈ S, ψt p r β (l t) t := by
  set f : ℕ → ℤ := fun t => ψt p r β (l t) t with hf
  -- basic facts
  have hvlt : ∀ t ∈ S, t ≤ padicValNat p (l t) := fun t ht => le_padicValNat_of_pow_dvd (hl t ht).1 (hl t ht).2
  have hnonneg : ∀ t ∈ S, 0 ≤ f t := by
    intro t ht
    have h1 := hvlt t ht
    have h2 := hS t ht
    simp only [hf, ψt]
    omega
  have hdecomp : ∀ t, l t = p^(padicValNat p (l t)) * ordc p (l t) := fun t => val_decomp (p := p) (l t)
  have hu : ∀ t ∈ S, ¬ p ∣ ordc p (l t) := fun t ht => not_dvd_ordc (hl t ht).1
  -- the minimal valuation
  obtain ⟨t₀, ht₀S, ht₀min⟩ := exists_min_image S (fun t => padicValNat p (l t)) ⟨0, h0⟩
  set s := padicValNat p (l t₀) with hs
  rcases Nat.lt_or_ge s r with hsr | hsr
  swap
  · -- case (A)
    have h1 : f 0 ≤ ∑ t ∈ S, f t := sum_ge_one hnonneg h0
    have h2 : s ≤ padicValNat p (l 0) := ht₀min 0 h0
    have : (3 * r : ℤ) ≤ f 0 := by
      simp only [hf, ψt]
      have : (r : ℤ) ≤ padicValNat p (l 0) := by omega
      omega
    linarith
  -- case (B): s < r
  -- there is a second element with valuation s
  have hex : ∃ t₁ ∈ S, t₁ ≠ t₀ ∧ padicValNat p (l t₁) = s := by
    by_contra hcon
    push_neg at hcon
    have hrest : p^(s+1) ∣ ∑ t ∈ S.erase t₀, l t := by
      apply dvd_sum
      intro t ht
      rw [mem_erase] at ht
      have h1 := ht₀min t ht.2
      have h2 := hcon t ht.2 ht.1
      exact pow_dvd_of_le_padicValNat (by
        show s + 1 ≤ padicValNat p (l t)
        omega)
    have htot : p^(s+1) ∣ ∑ t ∈ S, l t := dvd_trans (pow_dvd_pow p (by omega)) hsum
    rw [← add_sum_erase S l ht₀S] at htot
    have := (Nat.dvd_add_left hrest).1 htot
    exact pow_succ_padicValNat_not_dvd (hl t₀ ht₀S).1 this
  obtain ⟨t₁, ht₁S, ht₁ne, ht₁s⟩ := hex
  -- bound for an element of valuation s
  have hbs : ∀ t ∈ S, padicValNat p (l t) = s → (r : ℤ) - s ≤ f t := by
    intro t ht hts
    have h1 := hvlt t ht
    simp only [hf, ψt]
    omega
  rcases Nat.lt_or_ge s (padicValNat p (l 0)) with h0s | h0s
  · -- case (B1): 0 has bigger valuation
    have hne0 : 0 ≠ t₀ := by intro h; rw [← h] at hs; omega
    have hne1 : 0 ≠ t₁ := by intro h; rw [← h] at ht₁s; omega
    have h3 := sum_ge_three hnonneg h0 ht₀S ht₁S hne0 hne1 ht₁ne.symm
    have hf0 : (r : ℤ) + 2 * (s + 1) ≤ f 0 := by
      simp only [hf, ψt]
      omega
    have := hbs t₀ ht₀S rfl
    have := hbs t₁ ht₁S ht₁s
    linarith
  -- case: padicValNat p (l 0) = s
  have h0s' : padicValNat p (l 0) = s := by have := ht₀min 0 h0; omega
  -- pick t ≠ 0 with padicValNat p (l t) = s
  obtain ⟨t, htS, ht0, hts⟩ : ∃ t ∈ S, t ≠ 0 ∧ padicValNat p (l t) = s := by
    by_cases h : t₀ = 0
    · exact ⟨t₁, ht₁S, fun h' => ht₁ne (h'.trans h.symm), ht₁s⟩
    · exact ⟨t₀, ht₀S, h, rfl⟩
  have hf0 : (r : ℤ) + 2 * s ≤ f 0 := by
    simp only [hf, ψt]; omega
  have hft := hbs t htS hts
  by_cases hex2 : ∃ t' ∈ S, t' ≠ 0 ∧ t' ≠ t ∧ padicValNat p (l t') = s
  · -- case (B2)
    obtain ⟨t', ht'S, ht'0, ht't, ht's⟩ := hex2
    have h3 := sum_ge_three hnonneg h0 htS ht'S (Ne.symm ht0) (Ne.symm ht'0) (Ne.symm ht't)
    have := hbs t' ht'S ht's
    linarith
  -- case (B3)
  push_neg at hex2
  have hrest_ge : ∀ t' ∈ S, t' ≠ 0 → t' ≠ t → s + 1 ≤ padicValNat p (l t') := by
    intro t' ht' h1 h2
    have := ht₀min t' ht'
    have := hex2 t' ht' h1 h2
    omega
  have hsplit : ∑ t' ∈ S, l t' = l 0 + l t + ∑ t' ∈ (S.erase 0).erase t, l t' := by
    rw [add_assoc, add_sum_erase _ _ (mem_erase.2 ⟨ht0, htS⟩), add_sum_erase _ _ h0]
  have hrest_dvd : ∀ k, (∀ t' ∈ S, t' ≠ 0 → t' ≠ t → k ≤ padicValNat p (l t')) →
      p^k ∣ ∑ t' ∈ (S.erase 0).erase t, l t' := by
    intro k hk
    apply dvd_sum
    intro t' ht'
    simp only [mem_erase] at ht'
    exact pow_dvd_of_le_padicValNat (hk t' ht'.2.2 ht'.2.1 ht'.1)
  have hl0t : l 0 + l t = p^s * (ordc p (l 0) + ordc p (l t)) := by
    calc l 0 + l t = p^(padicValNat p (l 0)) * ordc p (l 0) + p^(padicValNat p (l t)) * ordc p (l t) := by
          rw [← hdecomp 0, ← hdecomp t]
      _ = p^s * (ordc p (l 0) + ordc p (l t)) := by rw [h0s', hts, mul_add]
  have hdvd_l0t : ∀ k, k ≤ r → p^k ∣ ∑ t' ∈ (S.erase 0).erase t, l t' → p^k ∣ l 0 + l t := by
    intro k hk hrest
    have htot : p^k ∣ ∑ t' ∈ S, l t' := dvd_trans (pow_dvd_pow p hk) hsum
    rw [hsplit] at htot
    exact (Nat.dvd_add_left hrest).1 htot
  have hpu : p ∣ ordc p (l 0) + ordc p (l t) := by
    have := hdvd_l0t (s+1) hsr (hrest_dvd (s+1) hrest_ge)
    rw [hl0t, pow_succ] at this
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos s) this
  set s' := padicValNat p (ordc p (l 0) + ordc p (l t)) with hs'
  have hs'pos : 1 ≤ s' := by
    have := (dvd_iff_padicValNat_ne_zero (by
      have := ordc_ne_zero (p := p) (hl 0 h0).1; omega)).1 hpu
    omega
  have hs'β := hβ _ _ (hu 0 h0) (hu t htS)
  have hb0t : min (s' : ℤ) (r - s) ≤ f 0 + f t - (2 * r + 4 * s - 3 * t) := by
    simp only [hf, ψt, h0s', hts]
    omega
  have hts' : t ≤ s := hts ▸ hvlt t htS
  rcases Nat.lt_or_ge (s + s') r with hss | hss
  swap
  · -- s + s' ≥ r
    have h2 := sum_ge_two hnonneg h0 htS (Ne.symm ht0)
    have : (3 * r : ℤ) ≤ f 0 + f t := by omega
    linarith
  -- s + s' < r: there is t'' with valuation ≤ s + s'
  have hex3 : ∃ t'' ∈ S, t'' ≠ 0 ∧ t'' ≠ t ∧ padicValNat p (l t'') ≤ s + s' := by
    by_contra hcon
    push_neg at hcon
    have hrest := hrest_dvd (s + s' + 1) (fun t' h1 h2 h3 => hcon t' h1 h2 h3)
    have := hdvd_l0t (s + s' + 1) hss (hrest)
    rw [hl0t, show s + s' + 1 = s + (s' + 1) by ring, pow_add] at this
    have := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos s) this
    exact pow_succ_padicValNat_not_dvd (by
      have := ordc_ne_zero (p := p) (hl 0 h0).1; omega) this
  obtain ⟨t'', ht''S, ht''0, ht''t, ht''le⟩ := hex3
  have h3 := sum_ge_three hnonneg h0 htS ht''S (Ne.symm ht0) (Ne.symm ht''0) (Ne.symm ht''t)
  have hft'' : (r : ℤ) - s - s' ≤ f t'' := by
    have h1 := hvlt t'' ht''S
    simp only [hf, ψt]
    omega
  have : (3 * r : ℤ) ≤ f 0 + f t + f t'' := by omega
  linarith

end Supercong

/- ## Section: Integ -/

set_option linter.unusedSectionVars false

namespace Supercong
open Finset PowerSeries

variable {p : ℕ} [hp : Fact p.Prime]

/- ### integrality predicates -/

/-- all coefficients are `p`-integral -/
def IntS (P : ℚ_[p]⟦X⟧) : Prop := ∀ n, PV p 0 (coeff n P)
/-- all coefficients are divisible by `p` -/
def Cong1 (P : ℚ_[p]⟦X⟧) : Prop := ∀ n, PV p 1 (coeff n P)

lemma IntS.mul {A B : ℚ_[p]⟦X⟧} (hA : IntS A) (hB : IntS B) : IntS (A * B) := by
  intro n; have := PV_coeff_mul hA hB n; simpa using this

lemma IntS.pow {A : ℚ_[p]⟦X⟧} (hA : IntS A) (d : ℕ) : IntS (A ^ d) := by
  intro n; have := PV_coeff_pow hA d n; simpa using this

lemma IntS.add {A B : ℚ_[p]⟦X⟧} (hA : IntS A) (hB : IntS B) : IntS (A + B) := by
  intro n; rw [map_add]; exact PV_add (hA n) (hB n)

lemma IntS.sum {ι : Type*} {s : Finset ι} {f : ι → ℚ_[p]⟦X⟧} (h : ∀ i ∈ s, IntS (f i)) :
    IntS (∑ i ∈ s, f i) := by
  intro n; rw [map_sum]; exact PV_sum (fun i hi => h i hi n)

lemma IntS.C_mul_X_pow {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) (j : ℕ) : IntS (C c * X ^ j) := by
  intro n
  rw [coeff_C_mul_X_pow]
  split_ifs
  · exact PV_of_norm_le_one hc
  · exact PV_zero _

lemma IntS.one : IntS (1 : ℚ_[p]⟦X⟧) := by
  intro n; rw [coeff_one]; split_ifs
  · exact PV_one
  · exact PV_zero _

lemma IntS.natCast_mul {A : ℚ_[p]⟦X⟧} (hA : IntS A) (k : ℕ) : IntS ((k : ℚ_[p]⟦X⟧) * A) := by
  intro n
  rw [← map_natCast C k, coeff_C_mul]
  exact PV_smul_nat (hA n) k

lemma Cong1.add {A B : ℚ_[p]⟦X⟧} (hA : Cong1 A) (hB : Cong1 B) : Cong1 (A + B) := by
  intro n; rw [map_add]; exact PV_add (hA n) (hB n)

lemma Cong1.sub {A B : ℚ_[p]⟦X⟧} (hA : Cong1 A) (hB : Cong1 B) : Cong1 (A - B) := by
  intro n; rw [map_sub]; exact PV_sub (hA n) (hB n)

lemma Cong1.p_mul {A : ℚ_[p]⟦X⟧} (hA : IntS A) : Cong1 ((p : ℚ_[p]⟦X⟧) * A) := by
  intro n
  rw [← map_natCast C p, coeff_C_mul]
  have := PV_mul (PV_p (p := p)) (hA n)
  simpa using this

lemma Cong1.zero : Cong1 (0 : ℚ_[p]⟦X⟧) := by intro n; rw [map_zero]; exact PV_zero _

/- ### Fermat in `ℚ_[p]` -/

lemma fermat_padic {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) : PV p 1 (c ^ p - c) := by
  set z : ℤ_[p] := ⟨c, hc⟩ with hz
  have h1 : PadicInt.toZMod (z ^ p - z) = 0 := by
    rw [map_sub, map_pow, ZMod.pow_card, sub_self]
  have h2 : z ^ p - z ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker]; exact h1
  rw [PadicInt.maximalIdeal_eq_span_p] at h2
  have h3 : ‖z ^ p - z‖ ≤ (p : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, pow_one]; exact h2
  rw [PadicInt.norm_def] at h3
  unfold PV
  have : ((z ^ p - z : ℤ_[p]) : ℚ_[p]) = c ^ p - c := by
    rw [PadicInt.coe_sub, PadicInt.coe_pow]
  rw [this] at h3
  simpa using h3

/- ### Frobenius congruence for polynomials -/

lemma expand_C_mul_X_pow (c : ℚ_[p]) (j : ℕ) :
    expand p hp.out.ne_zero (C c * X ^ j) = C c * X ^ (j * p) := by
  rw [map_mul, expand_C, map_pow, expand_X, ← pow_mul, mul_comm p j]

lemma frob_cong (s : Finset ℕ) (c : ℕ → ℚ_[p]) (hc : ∀ j, ‖c j‖ ≤ 1) :
    Cong1 ((∑ j ∈ s, C (c j) * X ^ j) ^ p
      - expand p hp.out.ne_zero (∑ j ∈ s, C (c j) * X ^ j)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty, zero_pow hp.out.ne_zero, map_zero, sub_zero]
    exact Cong1.zero
  | insert a s ha ih =>
    rw [sum_insert ha, add_pow_prime_eq hp.out, map_add]
    set A := C (c a) * X ^ a with hA
    set B := ∑ j ∈ s, C (c j) * X ^ j with hB
    have hAI : IntS A := IntS.C_mul_X_pow (hc a) a
    have hBI : IntS B := IntS.sum (fun j _ => IntS.C_mul_X_pow (hc j) j)
    have key : A ^ p + B ^ p + (p : ℚ_[p]⟦X⟧) * A * B *
          ∑ k ∈ Ioo 0 p, A ^ (k - 1) * B ^ (p - k - 1) * ((p.choose k / p : ℕ) : ℚ_[p]⟦X⟧)
        - (expand p hp.out.ne_zero A + expand p hp.out.ne_zero B)
        = (A ^ p - expand p hp.out.ne_zero A) + (B ^ p - expand p hp.out.ne_zero B)
          + (p : ℚ_[p]⟦X⟧) * (A * B *
            ∑ k ∈ Ioo 0 p, A ^ (k - 1) * B ^ (p - k - 1) * ((p.choose k / p : ℕ) : ℚ_[p]⟦X⟧)) := by
      ring
    rw [key]
    refine Cong1.add (Cong1.add ?_ ih) ?_
    · -- the monomial
      rw [hA, expand_C_mul_X_pow, mul_pow, ← map_pow, ← pow_mul, ← sub_mul, ← map_sub]
      intro n
      rw [coeff_C_mul_X_pow]
      split_ifs
      · exact fermat_padic (hc a)
      · exact PV_zero _
    · apply Cong1.p_mul
      refine IntS.mul (IntS.mul hAI hBI) (IntS.sum ?_)
      intro k _
      have : ((p.choose k / p : ℕ) : ℚ_[p]⟦X⟧) = ((p.choose k / p : ℕ) : ℚ_[p]⟦X⟧) * 1 := by ring
      rw [this]
      exact IntS.mul (IntS.mul (hAI.pow _) (hBI.pow _)) (IntS.natCast_mul IntS.one _)


/- ### the weak bound on `intg (DD m)` (any prime) -/

lemma PV_coeff_intg_DD_weak (m : ℕ) (i : ℕ) : PV p 1 (coeff i (intg (DD (p := p) m))) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_intg]; exact PV_zero _
  have hi' : i ≠ 0 := hi.ne'
  rw [coeff_intg _ _ hi', coeff_DD]
  set s := padicValNat p i with hs
  set u := ordc p i with hu
  have hpu : ¬ p ∣ u := not_dvd_ordc hi'
  have hdec : i = u * p^s := by rw [mul_comm]; exact val_decomp (p := p) i
  rcases Nat.eq_zero_or_pos s with h0 | hpos
  · have hnd : ¬ p ∣ i := by
      intro hd
      have := (dvd_iff_padicValNat_ne_zero hi').1 hd
      rw [← hs] at this; exact this h0
    rw [if_neg hnd, sub_zero, coeff_Dc_of_ne _ hi']
    have := PV_div_unit (PV_mul (PV_p (p := p)) (PV_nat (cm m i))) hnd
    exact PV_mono this (by omega)
  · have hd : p ∣ i := by
      rw [hdec]; exact dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) u
    rw [if_pos hd, coeff_Dc_of_ne _ hi']
    have hdiv : i / p = u * p^(s-1) := by
      rw [hdec, show s = (s - 1) + 1 by omega, pow_succ, ← mul_assoc, Nat.mul_div_cancel _ hp.out.pos]
      simp
    have hne : i / p ≠ 0 := by
      rw [hdiv]
      exact Nat.mul_ne_zero (by intro h0; rw [h0] at hpu; exact hpu (dvd_zero p))
        (pow_ne_zero _ hp.out.ne_zero)
    rw [coeff_Dc_of_ne _ hne, hdiv]
    have h1 := cm_pow_sub_weak (p := p) m u s hpos
    rw [← hdec] at h1
    have h2 := PV_div_nat (PV_mul (PV_p (p := p)) h1) i hi'
    refine PV_mono h2 ?_
    rw [← hs]; omega

lemma PV_coeff_ES_DD (m : ℕ) {j : ℕ} (hj : j ≠ 0) : PV p 1 (coeff j (ES (DD (p := p) m))) := by
  rw [coeff_ES_eq_sum _ (constantCoeff_DD m)]
  apply PV_sum
  intro d _
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [pow_zero, coeff_one, if_neg hj, mul_zero]; exact PV_zero _
  have hfac : PV p (-(padicValNat p d.factorial : ℤ)) ((d.factorial : ℚ_[p])⁻¹) :=
    PV_nat_inv _ (Nat.factorial_ne_zero d)
  have hGd : PV p (d : ℤ) (coeff j ((intg (DD (p := p) m))^d)) :=
    PV_mono (PV_coeff_pow (PV_coeff_intg_DD_weak m) d j) (le_of_eq (by push_cast; ring))
  have := PV_mul hfac hGd
  refine PV_mono this ?_
  have := padicValNat_factorial_lt_of_ne_zero p hd.ne'
  omega

/- ### the single step decomposition -/

lemma smul_Dc_decomp (m N : ℕ) :
    ((N * p : ℕ) : ℚ_[p]) • Dc (p := p) m
      = (p : ℚ_[p]) • expand p hp.out.ne_zero ((N : ℚ_[p]) • Dc m) + (N : ℚ_[p]) • DD m := by
  ext i
  simp only [map_add, coeff_smul, coeff_expand, coeff_DD, smul_eq_mul]
  push_cast
  split_ifs <;> ring

lemma constantCoeff_smul_Dc (m : ℕ) (c : ℚ_[p]) : constantCoeff (c • Dc (p := p) m) = 0 := by
  rw [smul_eq_C_mul, map_mul, constantCoeff_C, constantCoeff_Dc, mul_zero]

theorem ES_step (m N : ℕ) :
    ES (((N * p : ℕ) : ℚ_[p]) • Dc (p := p) m)
      = expand p hp.out.ne_zero (ES ((N : ℚ_[p]) • Dc m)) * ES ((N : ℚ_[p]) • DD m) := by
  rw [smul_Dc_decomp, ES_add, ES_expand (constantCoeff_smul_Dc m _)]
  · rw [smul_eq_C_mul, map_mul, constantCoeff_C, constantCoeff_expand, constantCoeff_smul_Dc,
      mul_zero]
  · exact constantCoeff_smul_DD m _

/- ### Dwork's lemma -/

theorem dwork (m : ℕ) : IntS (ES (Dc (p := p) m)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [coeff_zero_eq_constantCoeff_apply, (isExp_ES _ (constantCoeff_Dc m)).1]; exact PV_one
  set F := ES (Dc (p := p) m) with hF
  have hF0 : constantCoeff F = 1 := (isExp_ES _ (constantCoeff_Dc m)).1
  set c : ℕ → ℚ_[p] := fun j => if j < i then coeff j F else 0 with hc
  have hcnorm : ∀ j, ‖c j‖ ≤ 1 := by
    intro j; simp only [hc]; split_ifs with h
    · exact norm_le_one_of_PV (ih j h)
    · simp
  set T : ℚ_[p]⟦X⟧ := ∑ j ∈ Finset.range i, C (c j) * X ^ j with hT
  have hTcoeff : ∀ j, coeff j T = if j < i then coeff j F else 0 := by
    intro j
    rw [hT, map_sum]
    simp only [coeff_C_mul_X_pow]
    rw [sum_ite_eq (Finset.range i) j]
    simp only [mem_range, hc]
    split_ifs <;> rfl
  have hT0 : constantCoeff T = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hTcoeff, if_pos hi, coeff_zero_eq_constantCoeff_apply, hF0]
  have hFT : F - T = X ^ i * PowerSeries.mk (fun j => coeff (i + j) F) := by
    ext j
    rw [map_sub, coeff_X_pow_mul', hTcoeff, coeff_mk]
    split_ifs with h1 h2 h2
    · omega
    · rw [sub_self]
    · rw [Nat.add_sub_cancel' h2, sub_zero]
    · omega
  have hFp : F ^ p = expand p hp.out.ne_zero F * ES (DD m) := by
    have h := ES_step (p := p) m 1
    simp only [one_mul, Nat.cast_one, one_smul] at h
    rw [hF, ← ES_nsmul (constantCoeff_Dc m), ← Nat.cast_smul_eq_nsmul ℚ_[p]]
    exact h
  have hgeom : F ^ p - T ^ p = (F - T) * ∑ k ∈ Finset.range p, F ^ k * T ^ (p - 1 - k) := by
    rw [mul_comm, geom_sum₂_mul]
  have hdiff : coeff i (F ^ p) - coeff i (T ^ p) = (p : ℚ_[p]) * coeff i F := by
    rw [← map_sub, hgeom, hFT, mul_assoc, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, map_mul, map_sum]
    have : ∀ k ∈ Finset.range p, constantCoeff (F ^ k * T ^ (p - 1 - k)) = 1 := by
      intro k _; rw [map_mul, map_pow, map_pow, hF0, hT0, one_pow, one_pow, mul_one]
    rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul, mul_one,
      ← coeff_zero_eq_constantCoeff_apply, coeff_mk, add_zero, mul_comm]
  -- expand of T and F agree at i
  have hexp : coeff i (expand p hp.out.ne_zero T) = coeff i (expand p hp.out.ne_zero F) := by
    rw [coeff_expand, coeff_expand]
    split_ifs with h
    · rw [hTcoeff, if_pos]
      exact Nat.div_lt_self hi hp.out.one_lt
    · rfl
  -- the Frobenius congruence for T
  have hfrob : PV p 1 (coeff i (T ^ p) - coeff i (expand p hp.out.ne_zero T)) := by
    have := frob_cong (Finset.range i) c hcnorm i
    rwa [map_sub] at this
  -- coefficient of F^p
  have hFp_coeff : PV p 1 (coeff i (F ^ p) - coeff i (expand p hp.out.ne_zero F)) := by
    rw [hFp, coeff_mul]
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [Finset.Nat.sum_antidiagonal_succ']
    have hE0 : coeff 0 (ES (DD (p := p) m)) = 1 := by
      rw [coeff_zero_eq_constantCoeff_apply, (isExp_ES _ (constantCoeff_DD m)).1]
    rw [hE0, mul_one, add_sub_cancel_left]
    apply PV_sum
    intro q hq
    rw [mem_antidiagonal] at hq
    have h1 : PV p 0 (coeff q.1 (expand p hp.out.ne_zero F)) := by
      rw [coeff_expand]
      split_ifs with h
      · apply ih
        have : q.1 / p ≤ q.1 := Nat.div_le_self _ _
        omega
      · exact PV_zero _
    have h2 := PV_coeff_ES_DD (p := p) m (Nat.succ_ne_zero q.2)
    have := PV_mul h1 h2
    simpa using this
  -- conclude
  have hpf : PV p 1 ((p : ℚ_[p]) * coeff i F) := by
    rw [← hdiff]
    have : coeff i (F ^ p) - coeff i (T ^ p)
        = (coeff i (F ^ p) - coeff i (expand p hp.out.ne_zero F))
          - (coeff i (T ^ p) - coeff i (expand p hp.out.ne_zero T)) := by
      rw [hexp]; ring
    rw [this]
    exact PV_sub hFp_coeff hfrob
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : coeff i F = ((p : ℚ_[p]) * coeff i F) / (p : ℚ_[p]) := by field_simp
  rw [this]
  have := PV_div_nat hpf p hp.out.ne_zero
  rw [padicValNat_self] at this
  simpa using this


end Supercong

namespace Supercong
open Finset PowerSeries

variable {p : ℕ} [hp : Fact p.Prime]

lemma expSeq_nonneg (d : ℕ → ℚ) (hd : ∀ j, 0 ≤ d j) (k : ℕ) : 0 ≤ expSeq d k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => rw [expSeq_zero]; exact zero_le_one
    | succ k =>
      rw [expSeq_succ]
      apply div_nonneg
      · apply sum_nonneg
        intro j _
        exact mul_nonneg (hd _) (ih (k - j) (by omega))
      · positivity

/-- a rational number which is `ℓ`-integral for every prime `ℓ` is an integer. -/
theorem rat_den_eq_one_of_padic (q : ℚ)
    (h : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ‖(q : ℚ_[ℓ])‖ ≤ 1) : q.den = 1 := by
  by_contra hden
  obtain ⟨ℓ, hℓ, hdvd⟩ := Nat.exists_prime_and_dvd hden
  haveI := Fact.mk hℓ
  have hq := h ℓ
  rw [Padic.eq_padicNorm] at hq
  have hq0 : q ≠ 0 := by rintro rfl; exact hden Rat.den_zero
  rw [padicNorm.eq_zpow_of_nonzero hq0] at hq
  have hden1 : 1 ≤ padicValNat ℓ q.den := one_le_padicValNat_of_dvd q.den_nz hdvd
  have hnum : padicValInt ℓ q.num = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro hd
    rw [Int.natCast_dvd] at hd
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd q.reduced) hdvd
    exact hℓ.one_lt.ne' this
  have hval : padicValRat ℓ q < 0 := by
    unfold padicValRat; rw [hnum]; omega
  have h1 : (1 : ℚ) < (ℓ : ℚ) ^ (-padicValRat ℓ q) :=
    one_lt_zpow₀ (by exact_mod_cast hℓ.one_lt) (by omega)
  have : ((ℓ : ℚ) ^ (-padicValRat ℓ q) : ℚ) ≤ 1 := by exact_mod_cast hq
  linarith

lemma expSeq_rat_cast (d : ℕ → ℕ) (k : ℕ) :
    ((expSeq (fun j => (d j : ℚ)) k : ℚ) : ℚ_[p]) = expSeq (fun j => (d j : ℚ_[p])) k := by
  have := expSeq_map (Rat.castHom ℚ_[p]) (fun j => (d j : ℚ)) k
  simp only [Rat.coe_castHom, Rat.cast_natCast] at this
  rw [← this]

lemma expSeq_eq_coeff_ES (n m k : ℕ) :
    expSeq (fun j => ((n * cm m j : ℕ) : ℚ_[p])) k = coeff k (ES ((n : ℚ_[p]) • Dc (p := p) m)) := by
  rw [coeff_ES]
  rw [expSeq_congr (d := fun j => ((n * cm m j : ℕ) : ℚ_[p])) (d' := fun j => coeff j ((n : ℚ_[p]) • Dc (p := p) m))]
  intro j hj
  rw [coeff_smul, coeff_Dc_of_ne _ (by omega), smul_eq_mul]
  push_cast; rfl

lemma IntS_ES_smul_Dc (n m : ℕ) : IntS (ES ((n : ℚ_[p]) • Dc (p := p) m)) := by
  rw [Nat.cast_smul_eq_nsmul, ES_nsmul (constantCoeff_Dc m)]
  exact (dwork m).pow n

end Supercong

/- ## Section: Main -/

set_option linter.unusedSectionVars false

namespace Supercong
open Finset PowerSeries

variable {p : ℕ} [hp : Fact p.Prime]

/- ### iterated expansion -/

/-- `Ex t = expand (p^t)` -/
noncomputable def Ex (p : ℕ) [hp : Fact p.Prime] (t : ℕ) : ℚ_[p]⟦X⟧ →ₐ[ℚ_[p]] ℚ_[p]⟦X⟧ :=
  expand (p ^ t) (pow_ne_zero t hp.out.ne_zero)

lemma expand_congr {a b : ℕ} (h : a = b) (ha : a ≠ 0) (hb : b ≠ 0) (F : ℚ_[p]⟦X⟧) :
    expand a ha F = expand b hb F := by subst h; rfl

lemma Ex_zero (F : ℚ_[p]⟦X⟧) : Ex p 0 F = F := by
  unfold Ex
  rw [expand_congr (pow_zero p) _ one_ne_zero, PowerSeries.expand_one]; rfl

lemma Ex_succ (t : ℕ) (F : ℚ_[p]⟦X⟧) : expand p hp.out.ne_zero (Ex p t F) = Ex p (t + 1) F := by
  unfold Ex
  rw [← expand_mul p hp.out.ne_zero (p ^ t) (pow_ne_zero t hp.out.ne_zero)]
  exact expand_congr (pow_succ' p t).symm _ _ F

lemma coeff_Ex (t : ℕ) (F : ℚ_[p]⟦X⟧) (x : ℕ) :
    coeff x (Ex p t F) = if p ^ t ∣ x then coeff (x / p ^ t) F else 0 := by
  unfold Ex; rw [coeff_expand]

/-- the iterated decomposition -/
theorem ES_decomp (m n r : ℕ) :
    ES (((n * p ^ r : ℕ) : ℚ_[p]) • Dc (p := p) m)
      = Ex p r (ES ((n : ℚ_[p]) • Dc m)) *
        ∏ t ∈ Finset.range r, Ex p t (ES (((n * p ^ (r - 1 - t) : ℕ) : ℚ_[p]) • DD m)) := by
  induction r with
  | zero => simp [Ex_zero]
  | succ r ih =>
    rw [show n * p ^ (r + 1) = (n * p ^ r) * p by ring, ES_step, ih, map_mul, map_prod, Ex_succ,
      prod_range_succ', mul_assoc, Ex_zero, show r + 1 - 1 - 0 = r by omega]
    refine congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) ?_ rfl)
    apply prod_congr rfl
    intro t _
    rw [Ex_succ, show r + 1 - 1 - (t + 1) = r - 1 - t by omega]

/- ### the factors `G` -/

/-- the factors of the difference `b(np^r) - b(np^(r-1))` -/
noncomputable def Gf (p : ℕ) [hp : Fact p.Prime] (m n r : ℕ) (t : ℕ) : ℚ_[p]⟦X⟧ :=
  if t = 0 then ES (((n * p ^ (r - 1) : ℕ) : ℚ_[p]) • DD m) - 1
  else if t = r then Ex p r (ES ((n : ℚ_[p]) • Dc m))
  else Ex p t (ES (((n * p ^ (r - 1 - t) : ℕ) : ℚ_[p]) • DD m))

theorem prod_Gf (m n r : ℕ) (hr : 1 ≤ r) :
    ∏ t ∈ Finset.range (r + 1), Gf p m n r t
      = expand p hp.out.ne_zero (ES (((n * p ^ (r - 1) : ℕ) : ℚ_[p]) • Dc m)) *
        (ES (((n * p ^ (r - 1) : ℕ) : ℚ_[p]) • DD m) - 1) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel, ES_decomp, map_mul, map_prod, Ex_succ, prod_range_succ', prod_range_succ]
  refine congrArg₂ (· * ·) ?_ ?_
  · rw [mul_comm]
    refine congrArg₂ (· * ·) ?_ ?_
    · simp [Gf]
    · apply prod_congr rfl
      intro t ht
      rw [mem_range] at ht
      have h1 : t + 1 ≠ 0 := Nat.succ_ne_zero t
      have h2 : t + 1 ≠ r' + 1 := by omega
      simp only [Gf, if_neg h1, if_neg h2, Ex_succ]
      rw [show r' + 1 - 1 - (t + 1) = r' - 1 - t by omega]
  · simp [Gf]

/-- the difference of the two `b`-coefficients as one coefficient of `∏ Gf` -/
theorem coeff_diff (m n r : ℕ) (hr : 1 ≤ r) :
    coeff (n * p ^ r) (ES (((n * p ^ r : ℕ) : ℚ_[p]) • Dc (p := p) m))
      - coeff (n * p ^ (r - 1)) (ES (((n * p ^ (r - 1) : ℕ) : ℚ_[p]) • Dc m))
      = coeff (n * p ^ r) (∏ t ∈ Finset.range (r + 1), Gf p m n r t) := by
  rw [prod_Gf m n r hr]
  have h1 : n * p ^ r = (n * p ^ (r - 1)) * p := by
    rw [mul_assoc, ← pow_succ]; congr 2; omega
  rw [h1, ES_step, _root_.mul_sub_one, map_sub]
  congr 1
  rw [coeff_expand, if_pos (dvd_mul_left _ _), Nat.mul_div_cancel _ hp.out.pos]


/- ### coefficient bounds for the factors -/

/-- the exponent function -/
noncomputable def phif (p : ℕ) (r : ℕ) (β : ℕ → ℕ) (t x : ℕ) : ℤ :=
  if t = 0 then (if x = 0 then 3 * r else ψt p r β x 0)
  else if t = r then (if p ^ r ∣ x then 0 else 3 * r)
  else (if x = 0 then 0 else if p ^ t ∣ x then ψt p r β x t else 3 * r)

lemma padicValNat_pow_mul_of_ne {t y : ℕ} (hy : y ≠ 0) :
    padicValNat p (p ^ t * y) = t + padicValNat p y := by
  rw [padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hy, padicValNat.prime_pow]

lemma ordc_pow_mul_of_ne {t y : ℕ} (hy : y ≠ 0) : ordc p (p ^ t * y) = ordc p y := by
  unfold ordc
  rw [padicValNat_pow_mul_of_ne hy, pow_add, Nat.mul_div_mul_left _ _ (pow_pos hp.out.pos t)]

lemma ψ_eq_ψt (r t : ℕ) (ht : t < r) (β : ℕ → ℕ) {y : ℕ} (hy : y ≠ 0) :
    ψ (r - 1 - t) (β (ordc p y)) (padicValNat p y) = ψt p r β (p ^ t * y) t := by
  rw [ψt, ordc_pow_mul_of_ne hy, padicValNat_pow_mul_of_ne hy, ψ]
  omega

lemma ψ_eq_ψt0 (r : ℕ) (hr : 1 ≤ r) (β : ℕ → ℕ) (x : ℕ) :
    ψ (r - 1) (β (ordc p x)) (padicValNat p x) = ψt p r β x 0 := by
  rw [ψt, ψ]
  omega

theorem PV_coeff_Gf (h5 : 5 ≤ p) (m : ℕ) (hm : 2 ≤ m) (n r : ℕ) (hr : 1 ≤ r) (t : ℕ) (x : ℕ) :
    PV p (phif p r (fun u => padicValNat p (cm m u)) t x) (coeff x (Gf p m n r t)) := by
  by_cases ht0 : t = 0
  · subst ht0
    have e1 : Gf p m n r 0 = ES (((n * p ^ (r - 1) : ℕ) : ℚ_[p]) • DD m) - 1 := by simp [Gf]
    have e2 : phif p r (fun u => padicValNat p (cm m u)) 0 x
        = if x = 0 then 3 * (r : ℤ) else ψt p r (fun u => padicValNat p (cm m u)) x 0 := by simp [phif]
    rw [e1, e2, map_sub, coeff_one]
    by_cases hx : x = 0
    · subst hx
      rw [if_pos rfl, if_pos rfl, coeff_zero_eq_constantCoeff_apply,
        (isExp_ES _ (constantCoeff_smul_DD m _)).1, sub_self]
      exact PV_zero _
    · rw [if_neg hx, if_neg hx, sub_zero]
      have := lemmaH h5 m hm (r - 1) (n * p ^ (r - 1)) (dvd_mul_left _ _) hx
      have h := ψ_eq_ψt0 (p := p) r hr (fun u => padicValNat p (cm m u)) x
      simp only at h
      rw [h] at this
      exact this
  by_cases htr : t = r
  · subst htr
    have e1 : Gf p m n t t = Ex p t (ES ((n : ℚ_[p]) • Dc m)) := by simp [Gf, ht0]
    have e2 : phif p t (fun u => padicValNat p (cm m u)) t x = if p ^ t ∣ x then 0 else 3 * (t : ℤ) := by
      simp [phif, ht0]
    rw [e1, e2, coeff_Ex]
    split_ifs
    · exact IntS_ES_smul_Dc n m _
    · exact PV_zero _
  have e1 : Gf p m n r t = Ex p t (ES (((n * p ^ (r - 1 - t) : ℕ) : ℚ_[p]) • DD m)) := by
    simp [Gf, ht0, htr]
  have e2 : phif p r (fun u => padicValNat p (cm m u)) t x
      = if x = 0 then 0 else if p ^ t ∣ x then ψt p r (fun u => padicValNat p (cm m u)) x t
        else 3 * (r : ℤ) := by
    simp [phif, ht0, htr]
  rw [e1, e2, coeff_Ex]
  by_cases hx : x = 0
  · subst hx
    rw [if_pos rfl, if_pos (dvd_zero _), Nat.zero_div, coeff_zero_eq_constantCoeff_apply,
      (isExp_ES _ (constantCoeff_smul_DD m _)).1]
    exact PV_one
  rw [if_neg hx]
  by_cases hdvd : p ^ t ∣ x
  · rw [if_pos hdvd, if_pos hdvd]
    obtain ⟨y, rfl⟩ := hdvd
    have hy : y ≠ 0 := by rintro rfl; exact hx (mul_zero _)
    rw [Nat.mul_div_cancel_left _ (pow_pos hp.out.pos t)]
    rcases Nat.lt_or_ge t r with htlt | htge
    · have := lemmaH h5 m hm (r - 1 - t) (n * p ^ (r - 1 - t)) (dvd_mul_left _ _) hy
      have h := ψ_eq_ψt (p := p) r t htlt (fun u => padicValNat p (cm m u)) hy
      simp only at h
      rw [h] at this
      exact this
    · -- `t > r`: the bound `ψt` is still valid since `lemmaH` gives at least the weaker `ψ 0`
      have := lemmaH h5 m hm (r - 1 - t) (n * p ^ (r - 1 - t)) (dvd_mul_left _ _) hy
      refine PV_mono this ?_
      have hrt : r - 1 - t = 0 := by omega
      rw [hrt, ψt, ψ, ordc_pow_mul_of_ne hy, padicValNat_pow_mul_of_ne hy]
      have : r < t := lt_of_le_of_ne htge (Ne.symm htr)
      omega
  · rw [if_neg hdvd, if_neg hdvd]; exact PV_zero _


/- ### the sum bound -/

lemma phif_nonneg (r : ℕ) (β : ℕ → ℕ) {t : ℕ} (ht : t ≤ r) (x : ℕ) : 0 ≤ phif p r β t x := by
  unfold phif
  split_ifs with h1 h2 h3 h4 h5 h6
  · positivity
  · rw [ψt]; omega
  · exact le_rfl
  · positivity
  · exact le_rfl
  · have hv : t ≤ padicValNat p x := le_padicValNat_of_pow_dvd h5 h6
    rw [ψt]; omega
  · positivity

theorem sum_phif_ge (m : ℕ) (hm : 2 ≤ m) (n r : ℕ) (hr : 1 ≤ r) (l : ℕ → ℕ)
    (hl : ∑ t ∈ Finset.range (r + 1), l t = n * p ^ r) :
    (3 * r : ℤ) ≤ ∑ t ∈ Finset.range (r + 1), phif p r (fun u => padicValNat p (cm m u)) t (l t) := by
  set β : ℕ → ℕ := fun u => padicValNat p (cm m u) with hβ
  have hnn : ∀ t ∈ Finset.range (r + 1), 0 ≤ phif p r β t (l t) := by
    intro t ht; rw [mem_range] at ht; exact phif_nonneg r β (by omega) _
  by_cases h0 : l 0 = 0
  · have : phif p r β 0 (l 0) = 3 * r := by simp [phif, h0]
    rw [← this]
    exact single_le_sum hnn (by simp)
  by_cases hbad : ∃ t ∈ Finset.range (r + 1), t ≠ 0 ∧ t ≠ r ∧ l t ≠ 0 ∧ ¬ p ^ t ∣ l t
  · obtain ⟨t, ht, ht0, htr, hlt, hdvd⟩ := hbad
    have : phif p r β t (l t) = 3 * r := by simp [phif, ht0, htr, hlt, hdvd]
    rw [← this]
    exact single_le_sum hnn ht
  by_cases hr' : ¬ p ^ r ∣ l r
  · have : phif p r β r (l r) = 3 * r := by
      have hr0 : r ≠ 0 := by omega
      simp [phif, hr0, hr']
    rw [← this]
    exact single_le_sum hnn (by simp)
  push_neg at hbad hr'
  -- the main case
  set S := (Finset.range r).filter (fun t => l t ≠ 0) with hS
  have hSsub : S ⊆ Finset.range (r + 1) := by
    intro t ht; rw [hS, mem_filter, mem_range] at ht; rw [mem_range]; omega
  have hS0 : 0 ∈ S := by rw [hS, mem_filter, mem_range]; exact ⟨by omega, h0⟩
  have hSlt : ∀ t ∈ S, t < r := by intro t ht; rw [hS, mem_filter, mem_range] at ht; exact ht.1
  have hSl : ∀ t ∈ S, l t ≠ 0 ∧ p ^ t ∣ l t := by
    intro t ht
    have ht' := ht
    rw [hS, mem_filter, mem_range] at ht'
    refine ⟨ht'.2, ?_⟩
    by_cases ht0 : t = 0
    · subst ht0; simp
    · exact hbad t (mem_range.2 (by omega)) ht0 (by omega) ht'.2
  have hSsum : p ^ r ∣ ∑ t ∈ S, l t := by
    rw [hS, sum_filter_ne_zero]
    rw [sum_range_succ] at hl
    have h1 : p ^ r ∣ ∑ t ∈ Finset.range r, l t + l r := by rw [hl]; exact dvd_mul_left _ _
    exact (Nat.dvd_add_left hr').1 h1
  have hβ' : ∀ u u', ¬ p ∣ u → ¬ p ∣ u' → padicValNat p (u + u') ≤ β u + β u' := by
    intro u u' hu hu'
    exact carry_lemma_cm p m u u' hm hu (Nat.pos_of_ne_zero (by rintro rfl; exact hu' (dvd_zero p)))
  have hcomb := comb_lemma r hr S hSlt hS0 l hSl hSsum β hβ'
  have hsub : ∑ t ∈ S, phif p r β t (l t) ≤ ∑ t ∈ Finset.range (r + 1), phif p r β t (l t) :=
    sum_le_sum_of_subset_of_nonneg hSsub (fun t ht _ => hnn t ht)
  have heq : ∑ t ∈ S, phif p r β t (l t) = ∑ t ∈ S, ψt p r β (l t) t := by
    apply sum_congr rfl
    intro t ht
    have h1 := hSl t ht
    have h2 := hSlt t ht
    by_cases ht0 : t = 0
    · subst ht0; simp [phif, h1.1]
    · have htr : t ≠ r := by omega
      simp [phif, ht0, htr, h1.1, h1.2]
  linarith

/- ### the main `p`-adic estimate -/

theorem PV_diff (h5 : 5 ≤ p) (m : ℕ) (hm : 2 ≤ m) (n r : ℕ) (hr : 1 ≤ r) :
    PV p (3 * r) (coeff (n * p ^ r) (ES (((n * p ^ r : ℕ) : ℚ_[p]) • Dc (p := p) m))
      - coeff (n * p ^ (r - 1)) (ES (((n * p ^ (r - 1) : ℕ) : ℚ_[p]) • Dc m))) := by
  rw [coeff_diff m n r hr, coeff_prod]
  apply PV_sum
  intro l hl
  rw [mem_finsuppAntidiag] at hl
  have := PV_prod (s := Finset.range (r + 1)) (k := fun t => phif p r (fun u => padicValNat p (cm m u)) t (l t))
    (f := fun t => coeff (l t) (Gf p m n r t))
    (fun t _ => PV_coeff_Gf h5 m hm n r hr t (l t))
  refine PV_mono this ?_
  have := sum_phif_ge (p := p) m hm n r hr l hl.1
  simpa using this


/- ### the case `m = 1`: auxiliary -/

lemma expSeq_one (k : ℕ) : expSeq (fun _ => (1 : ℚ_[p])) k = 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => exact expSeq_zero _
    | succ k =>
      rw [expSeq_succ]
      rw [sum_congr rfl (fun j hj => by rw [ih (k - j) (by rw [mem_range] at hj; omega), mul_one])]
      simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
      have : ((k : ℚ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      push_cast
      field_simp

lemma ES_Dc_one : ES (Dc (p := p) 1) = PowerSeries.mk 1 := by
  ext k
  rw [coeff_ES, coeff_mk, Pi.one_apply]
  rw [expSeq_congr (d := fun j => coeff j (Dc (p := p) 1)) (d' := fun _ => (1 : ℚ_[p]))]
  · exact expSeq_one k
  · intro j hj
    rw [coeff_Dc_of_ne _ (by omega), cm_one, Nat.cast_one]

lemma cm_two (N : ℕ) : cm 2 N = (2 * N).choose N := by
  rw [cm_eq_prod]; simp [prod_range_succ]

end Supercong

/- ## Section: Final (connection with the problem's definitions) -/

set_option linter.unusedSectionVars false

namespace Supercong
open PowerSeries

variable {p : ℕ} [hp : Fact p.Prime]

lemma coeff_of_log_gf_gen_eq (m k : ℕ) : coeff_of_log_gf_gen m k = cm m k := rfl

lemma gec_zero (d : ℕ → ℕ) : generalized_exp_coeff d 0 = 1 := by
  simp [generalized_exp_coeff]

lemma gec_succ (d : ℕ → ℕ) (k : ℕ) :
    generalized_exp_coeff d (k + 1)
      = (∑ j ∈ Finset.range (k + 1), d (j + 1) * generalized_exp_coeff d (k - j)) / (k + 1) := by
  rw [generalized_exp_coeff]
  simp only [Nat.add_sub_add_right]

/-- the ℕ-valued recursion computes `expSeq` provided the latter is integral. -/
theorem gec_eq_expSeq (d : ℕ → ℕ)
    (hint : ∀ k, ∃ z : ℤ, expSeq (fun j => (d j : ℚ)) k = z) (k : ℕ) :
    (generalized_exp_coeff d k : ℚ) = expSeq (fun j => (d j : ℚ)) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => rw [gec_zero, expSeq_zero]; simp
    | succ k =>
      obtain ⟨z, hz⟩ := hint (k + 1)
      have hnn : (0 : ℚ) ≤ z := by
        rw [← hz]; exact expSeq_nonneg _ (fun j => by positivity) _
      have hz0 : 0 ≤ z := by exact_mod_cast hnn
      set z' := z.toNat with hz'
      have hzz : (z' : ℤ) = z := Int.toNat_of_nonneg hz0
      have hzq : (z' : ℚ) = expSeq (fun j => (d j : ℚ)) (k + 1) := by
        rw [hz, ← hzz]; simp
      have hsum : ((∑ j ∈ Finset.range (k + 1), d (j + 1) * generalized_exp_coeff d (k - j) : ℕ) : ℚ)
          = (k + 1) * z' := by
        push_cast
        rw [Finset.sum_congr rfl (fun j _ => by rw [ih (k - j) (by omega)])]
        rw [hzq, expSeq_succ]
        have : ((k : ℚ) + 1) ≠ 0 := by positivity
        field_simp
      have hsumN : (∑ j ∈ Finset.range (k + 1), d (j + 1) * generalized_exp_coeff d (k - j)) = (k + 1) * z' := by
        exact_mod_cast hsum
      rw [gec_succ, hsumN, Nat.mul_div_cancel_left _ (Nat.succ_pos k), hzq]

/-- the main connection: `b_m_int m n` is the `n`-th coefficient of `ES (n • Dc m)`. -/
theorem b_m_int_cast (m n : ℕ) (hn : n ≠ 0) :
    ((b_m_int m n : ℤ) : ℚ_[p]) = coeff n (ES ((n : ℚ_[p]) • Dc (p := p) m)) := by
  unfold b_m_int
  rw [if_neg hn]
  simp only [coeff_of_log_gf_gen_eq]
  set d : ℕ → ℕ := fun k => n * cm m k with hd
  have hint : ∀ k, ∃ z : ℤ, expSeq (fun j => (d j : ℚ)) k = z := by
    intro k
    refine ⟨(expSeq (fun j => (d j : ℚ)) k).num, ?_⟩
    symm
    apply Rat.coe_int_num_of_den_eq_one
    apply rat_den_eq_one_of_padic
    intro ℓ hℓ
    rw [expSeq_rat_cast, hd]
    have := expSeq_eq_coeff_ES (p := ℓ) n m k
    simp only at this
    rw [this]
    exact norm_le_one_of_PV (IntS_ES_smul_Dc n m k)
  have h1 := gec_eq_expSeq d hint n
  have h2 : ((generalized_exp_coeff d n : ℤ) : ℚ_[p]) = ((generalized_exp_coeff d n : ℚ) : ℚ_[p]) := by
    push_cast; rfl
  rw [h2, h1, expSeq_rat_cast, hd]
  have := expSeq_eq_coeff_ES (p := p) n m n
  simp only at this
  exact this

theorem main_ge_two (h5 : 5 ≤ p) (m : ℕ) (hm : 2 ≤ m) (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    (p ^ (3 * r) : ℤ) ∣ b_m_int m (n * p ^ r) - b_m_int m (n * p ^ (r - 1)) := by
  rw [← PV_int_sub_iff]
  have h1 : n * p ^ r ≠ 0 := by positivity
  have h2 : n * p ^ (r - 1) ≠ 0 := by positivity
  rw [b_m_int_cast m _ h1, b_m_int_cast m _ h2]
  exact PV_diff h5 m hm n r hr

lemma b_one_eq (N : ℕ) (hN : N ≠ 0) :
    (2 : ℚ_[p]) * ((b_m_int 1 N : ℤ) : ℚ_[p]) = (cm 2 N : ℚ_[p]) := by
  rw [b_m_int_cast 1 N hN, Nat.cast_smul_eq_nsmul, ES_nsmul (constantCoeff_Dc 1), ES_Dc_one]
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rw [mk_one_pow_eq_mk_choose_add, coeff_mk, cm_two]
  have h := Nat.add_one_mul_choose_eq (2 * N' + 1) N'
  rw [show 2 * N' + 1 + 1 = 2 * (N' + 1) by ring] at h
  have h' : ((2 * (N' + 1) * (2 * N' + 1).choose N' : ℕ) : ℚ_[p])
      = (((2 * (N' + 1)).choose (N' + 1) * (N' + 1) : ℕ) : ℚ_[p]) := by rw [h]
  push_cast at h'
  have hN1 : ((N' : ℚ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N'
  rw [show N' + (N' + 1) = 2 * N' + 1 by ring]
  have : (2 : ℚ_[p]) * ((2 * N' + 1).choose N' : ℚ_[p]) * ((N' : ℚ_[p]) + 1)
      = ((2 * (N' + 1)).choose (N' + 1) : ℚ_[p]) * ((N' : ℚ_[p]) + 1) := by
    rw [← h']; ring
  exact mul_right_cancel₀ hN1 this

theorem main_one (h5 : 5 ≤ p) (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    (p ^ (3 * r) : ℤ) ∣ b_m_int 1 (n * p ^ r) - b_m_int 1 (n * p ^ (r - 1)) := by
  rw [← PV_int_sub_iff]
  have h1 := b_one_eq (p := p) (n * p ^ r) (by positivity)
  have h2 := b_one_eq (p := p) (n * p ^ (r - 1)) (by positivity)
  have h3 := cm_mul_p_sub h5 2 (n * p ^ (r - 1)) r hr (dvd_mul_left _ _)
  rw [show n * p ^ (r - 1) * p = n * p ^ r by
    rw [mul_assoc, ← pow_succ]; congr 2; omega] at h3
  have : ((b_m_int 1 (n * p ^ r) : ℤ) : ℚ_[p]) - ((b_m_int 1 (n * p ^ (r - 1)) : ℤ) : ℚ_[p])
      = ((cm 2 (n * p ^ r) : ℚ_[p]) - (cm 2 (n * p ^ (r - 1)) : ℚ_[p])) / 2 := by
    rw [← h1, ← h2]; ring
  rw [this]
  exact PV_two_inv_mul h5 (PV_mono h3 (by omega))

/- ### the final theorem -/

theorem general_supercongruence (m n r p : ℕ) (hp : Nat.Prime p)
    (hp5 : p ≥ 5) (hm : m ≥ 1) (hn : n ≥ 1) (hr : r ≥ 1) :
    b_m_int m (n * p ^ r) ≡ b_m_int m (n * p ^ (r - 1)) [ZMOD (p ^ (3 * r) : ℤ)] := by
  haveI := Fact.mk hp
  have hdvd : (p ^ (3 * r) : ℤ) ∣ b_m_int m (n * p ^ r) - b_m_int m (n * p ^ (r - 1)) := by
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · have : m = 1 := by omega
      subst this
      exact main_one hp5 n r hn hr
    · exact main_ge_two hp5 m hm2 n r hn hr
  exact (Int.modEq_iff_dvd.mpr hdvd).symm

end Supercong

/--
oeis_333042_conjecture_1:
More generally, for a positive integer $m$, set $A_m(x) = \exp( \sum_{n \ge 1} (m*n)!/(n!^m) * x^n/n )$
and define a sequence $\{b_m(n): n \ge 1\}$ by $b_m(n) := [x^n] A_m(x)^n$.
Then we conjecture that $b_m(n)$ is an integer sequence satisfying the supercongruences
$b_m(n p^r) \equiv b_m(n p^{r-1}) \pmod{p^{3r}}$ for prime $p \ge 5$ and all positive integers $m, n, r$.
-/
theorem general_supercongruence_conjecture (m n r p : ℕ) (hp : Nat.Prime p)
    (hp5 : p ≥ 5) (hm : m ≥ 1) (hn : n ≥ 1) (hr : r ≥ 1) :
    b_m_int m (n * p ^ r) ≡ b_m_int m (n * p ^ (r - 1)) [ZMOD (p ^ (3 * r) : ℤ)] :=
Supercong.general_supercongruence m n r p hp hp5 hm hn hr

theorem general_supercongruence_conjecture.disproof : ¬ (type_of% @general_supercongruence_conjecture) := sorry
