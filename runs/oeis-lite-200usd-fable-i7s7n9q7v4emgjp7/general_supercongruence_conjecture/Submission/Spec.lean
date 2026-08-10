/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

section

open Nat BigOperators Int

/-- The generalized coefficient $c_{m} (k) = \frac{(m k)!}{(k!)^m}$ in $\mathbb{N}$. -/
def coeff_of_log_gf_gen (m k : ℕ) : ℕ :=
  (m * k).factorial / (k.factorial ^ m)

/--
A generalized recursive definition for the coefficients of any exponential series $\exp(\sum d_k \frac{x^k}{k})$.
The coefficients $a_k$ satisfy $k \cdot a_k = \sum_{j=1}^k d_j \cdot a_{k-j}$.
This is a local helper function inside `b_m_int`.
-/
private noncomputable def generalized_exp_coeff (d : ℕ → ℕ) : ℕ → ℕ
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

end

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.style.copyright.formalConjectures false
set_option linter.style.moduleDocstring false
set_option linter.style.namespace false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.dupNamespace false
set_option maxHeartbeats 2000000

-- ===== Devel/D01.lean =====
/-! # D01: p-adic valuation interface `V`
`V p k q` means `v_p(q) ≥ k`, expressed via `padicNorm` (graceful at `q = 0`). -/

namespace Super

variable {p : ℕ} [hp : Fact p.Prime]

/-- `V p k q` : the `p`-adic valuation of `q` is at least `k`. -/
def V (p : ℕ) (k : ℤ) (q : ℚ) : Prop := padicNorm p q ≤ (p : ℚ) ^ (-k)

theorem one_lt_p : (1 : ℚ) < (p : ℚ) := by
  exact_mod_cast hp.out.one_lt

theorem p_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos

@[simp] theorem V_zero_val (k : ℤ) : V p k 0 := by
  unfold V
  rw [padicNorm.zero]
  have := p_pos (p := p) (hp := hp)
  positivity

theorem V_mono {k l : ℤ} {q : ℚ} (h : V p k q) (hle : l ≤ k) : V p l q := by
  refine le_trans h ?_
  exact zpow_le_zpow_right₀ (one_lt_p (p := p)).le (by omega)

theorem V_neg {k : ℤ} {q : ℚ} (h : V p k q) : V p k (-q) := by
  unfold V at *
  rwa [padicNorm.neg]

theorem V_add {k : ℤ} {a b : ℚ} (ha : V p k a) (hb : V p k b) : V p k (a + b) := by
  unfold V at *
  exact le_trans (padicNorm.nonarchimedean) (max_le ha hb)

theorem V_sub {k : ℤ} {a b : ℚ} (ha : V p k a) (hb : V p k b) : V p k (a - b) := by
  rw [sub_eq_add_neg]; exact V_add ha (V_neg hb)

theorem V_sum {ι : Type*} {k : ℤ} {s : Finset ι} {f : ι → ℚ}
    (h : ∀ i ∈ s, V p k (f i)) : V p k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using V_zero_val k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact V_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem V_mul {k l : ℤ} {a b : ℚ} (ha : V p k a) (hb : V p l b) : V p (k + l) (a * b) := by
  unfold V at *
  rw [padicNorm.mul, neg_add, zpow_add₀ (p_pos (p := p)).ne']
  exact mul_le_mul ha hb (padicNorm.nonneg b) (le_of_lt (by have := p_pos (p := p); positivity))

theorem V_prod {ι : Type*} {s : Finset ι} {f : ι → ℚ} {g : ι → ℤ}
    (h : ∀ i ∈ s, V p (g i) (f i)) : V p (∑ i ∈ s, g i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [V, padicNorm.one] using le_refl _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact V_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem V_int (z : ℤ) : V p 0 (z : ℚ) := by
  unfold V
  simpa using padicNorm.of_int z

theorem V_nat (n : ℕ) : V p 0 (n : ℚ) := by
  simpa using V_int (p := p) (n : ℤ)

theorem V_one : V p 0 (1 : ℚ) := by simpa using V_nat (p := p) 1

/-- Bridge to divisibility for integers. -/
theorem V_int_iff_dvd (t : ℕ) (z : ℤ) : V p t (z : ℚ) ↔ (p : ℤ) ^ t ∣ z := by
  unfold V
  rw [← padicNorm.dvd_iff_norm_le]
  push_cast
  tauto

theorem V_p_pow (t : ℕ) : V p t ((p : ℚ) ^ t) := by
  rw [show ((p:ℚ)^t) = (((p^t : ℤ) : ℚ)) by push_cast; ring]
  rw [V_int_iff_dvd]

theorem V_zpow_p (t : ℕ) : V p t ((p : ℚ) ^ (t : ℤ)) := by
  simpa [zpow_natCast] using V_p_pow (p := p) t

/-- valuation of a nonzero natural number: `V p (padicValNat p n) n`. -/
theorem V_padicValNat {n : ℕ} (hn : n ≠ 0) : V p (padicValNat p n) (n : ℚ) := by
  rw [show ((n:ℚ)) = (((n : ℤ)) : ℚ) by push_cast; ring, V_int_iff_dvd]
  exact_mod_cast pow_padicValNat_dvd (p := p) (n := n)

/-- `1/n` for `n` a nonzero natural: `V p (-v_p(n)) (1/n)`. -/
theorem V_inv_nat {n : ℕ} (hn : n ≠ 0) : V p (-(padicValNat p n : ℤ)) (1 / (n : ℚ)) := by
  unfold V
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  rw [one_div, padicNorm.eq_zpow_of_nonzero (by simpa using hnQ), neg_neg]
  rw [padicValRat.inv, padicValRat.of_nat]
  simp

theorem V_inv_nat_le {n : ℕ} {k : ℕ} (hn : n ≠ 0) (h : padicValNat p n ≤ k) :
    V p (-(k : ℤ)) (1 / (n : ℚ)) :=
  V_mono (V_inv_nat hn) (by omega)

/-- unit denominators: if `¬ p ∣ n` then `V p 0 (1/n)`. -/
theorem V_inv_unit {n : ℕ} (hn : n ≠ 0) (h : ¬ p ∣ n) : V p 0 (1 / (n : ℚ)) := by
  have := V_inv_nat (p := p) hn
  rwa [padicValNat.eq_zero_of_not_dvd h] at this

theorem V_div_nat {k : ℤ} {a : ℚ} {n : ℕ} (ha : V p k a) (hn : n ≠ 0) :
    V p (k - padicValNat p n) (a / n) := by
  rw [div_eq_mul_one_div, sub_eq_add_neg]
  exact V_mul ha (V_inv_nat hn)

theorem V_pow {k : ℤ} {a : ℚ} (ha : V p k a) (n : ℕ) : V p (n * k) (a ^ n) := by
  induction n with
  | zero => simpa using V_one (p := p)
  | succ n ih =>
    have h := V_mul ih ha
    rw [pow_succ]
    have he : ((n + 1 : ℕ) : ℤ) * k = (n : ℤ) * k + k := by push_cast; ring
    rw [he]
    exact h

theorem V_nsmul {k : ℤ} {a : ℚ} (n : ℕ) (ha : V p k a) : V p k ((n : ℚ) * a) := by
  simpa using V_mul (V_nat n) ha

/-- casting: an integer with `V p t` is divisible by `p^t`; specialized ℕ-version. -/
theorem V_nat_iff_dvd (t : ℕ) (n : ℕ) : V p t (n : ℚ) ↔ p ^ t ∣ n := by
  rw [show ((n:ℚ)) = ((n : ℤ) : ℚ) by push_cast; ring, V_int_iff_dvd]
  exact_mod_cast Int.natCast_dvd_natCast

theorem V_nat_sub_iff (t : ℕ) (a b : ℕ) : V p t ((a : ℚ) - b) ↔ (p : ℤ) ^ t ∣ (a - b : ℤ) := by
  rw [show ((a:ℚ) - b) = (((a - b : ℤ) : ℚ)) by push_cast; ring, V_int_iff_dvd]

end Super

-- ===== Devel/D02.lean =====
/-! # D02: exponentials of formal power series over ℚ

`expS F` is the exponential of a power series `F` (with the constant coefficient of `F`
ignored: only `coeff (j+1) F` enter the defining recursion).  It is characterized by
`IsExpOf F G`: `constantCoeff G = 1` and the derivative recursion
`(k+1) G_{k+1} = ∑_{j=0}^{k} ((j+1) F_{j+1}) G_{k-j}`. -/

namespace Super

open PowerSeries Finset

noncomputable section

/-- The coefficient recursion for the exponential of `F`. -/
def expC (F : ℚ⟦X⟧) : ℕ → ℚ
  | 0 => 1
  | (k+1) => (∑ j ∈ Finset.range (k+1),
      (((j+1 : ℕ) : ℚ) * coeff (j+1) F) * expC F (k - j)) / ((k+1 : ℕ) : ℚ)
  termination_by k => k
  decreasing_by omega

/-- Exponential of a power series (constant term of `F` is ignored). -/
def expS (F : ℚ⟦X⟧) : ℚ⟦X⟧ := mk (expC F)

/-- Characterizing predicate: `G = exp F` via the derivative recursion. -/
def IsExpOf (F G : ℚ⟦X⟧) : Prop :=
  constantCoeff G = 1 ∧
  ∀ k : ℕ, ((k+1 : ℕ) : ℚ) * coeff (k+1) G =
    ∑ j ∈ Finset.range (k+1), (((j+1 : ℕ) : ℚ) * coeff (j+1) F) * coeff (k - j) G

theorem isExpOf_expS (F : ℚ⟦X⟧) : IsExpOf F (expS F) := by
  constructor
  · rw [expS, constantCoeff_mk, expC]
  · intro k
    rw [expS, coeff_mk, expC]
    rw [mul_div_cancel₀]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [coeff_mk]
    · exact_mod_cast Nat.succ_ne_zero k

theorem IsExpOf.unique {F G H : ℚ⟦X⟧} (hG : IsExpOf F G) (hH : IsExpOf F H) : G = H := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [coeff_zero_eq_constantCoeff, hG.1, hH.1]
    | (k+1) =>
      have h1 := hG.2 k
      have h2 := hH.2 k
      have hne : ((k+1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      have : ((k+1 : ℕ) : ℚ) * coeff (k+1) G = ((k+1 : ℕ) : ℚ) * coeff (k+1) H := by
        rw [h1, h2]
        apply Finset.sum_congr rfl
        intro j hj
        rw [ih (k - j) (by omega)]
      exact mul_left_cancel₀ hne this

theorem IsExpOf.eq_expS {F G : ℚ⟦X⟧} (hG : IsExpOf F G) : G = expS F :=
  hG.unique (isExpOf_expS F) |>.symm ▸ rfl

/-- Derivative characterization of `IsExpOf`. -/
theorem isExpOf_iff_deriv (F G : ℚ⟦X⟧) :
    IsExpOf F G ↔ constantCoeff G = 1 ∧ d⁄dX ℚ G = d⁄dX ℚ F * G := by
  constructor
  · rintro ⟨h0, hrec⟩
    refine ⟨h0, ?_⟩
    ext k
    rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => coeff a (d⁄dX ℚ F) * coeff b G)]
    calc coeff (k+1) G * ((k:ℚ)+1) = ((k+1 : ℕ) : ℚ) * coeff (k+1) G := by push_cast; ring
    _ = ∑ j ∈ Finset.range (k+1), (((j+1 : ℕ) : ℚ) * coeff (j+1) F) * coeff (k - j) G := hrec k
    _ = ∑ j ∈ Finset.range (k+1), coeff j (d⁄dX ℚ F) * coeff (k - j) G := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [coeff_derivative]
        push_cast; ring
  · rintro ⟨h0, hD⟩
    refine ⟨h0, ?_⟩
    intro k
    have := congrArg (fun φ => coeff k φ) hD
    simp only at this
    rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => coeff a (d⁄dX ℚ F) * coeff b G)] at this
    calc ((k+1 : ℕ) : ℚ) * coeff (k+1) G = coeff (k+1) G * ((k:ℚ)+1) := by push_cast; ring
    _ = ∑ j ∈ Finset.range (k+1), coeff j (d⁄dX ℚ F) * coeff (k - j) G := this
    _ = ∑ j ∈ Finset.range (k+1), (((j+1 : ℕ) : ℚ) * coeff (j+1) F) * coeff (k - j) G := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [coeff_derivative]
        push_cast; ring

theorem IsExpOf.mul {F F' G G' : ℚ⟦X⟧} (h : IsExpOf F G) (h' : IsExpOf F' G') :
    IsExpOf (F + F') (G * G') := by
  rw [isExpOf_iff_deriv] at h h' ⊢
  refine ⟨by rw [map_mul, h.1, h'.1, mul_one], ?_⟩
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, h.2, h'.2, map_add]
  ring

theorem isExpOf_zero_one : IsExpOf (0 : ℚ⟦X⟧) 1 := by
  rw [isExpOf_iff_deriv]
  refine ⟨map_one _, ?_⟩
  rw [Derivation.map_one_eq_zero, map_zero, zero_mul]

theorem IsExpOf.pow {F G : ℚ⟦X⟧} (h : IsExpOf F G) (n : ℕ) : IsExpOf (n • F) (G ^ n) := by
  induction n with
  | zero => simpa using isExpOf_zero_one
  | succ n ih =>
    have := ih.mul h
    rwa [← pow_succ, ← succ_nsmul] at this

theorem expS_add (F F' : ℚ⟦X⟧) : expS (F + F') = expS F * expS F' :=
  (((isExpOf_expS F).mul (isExpOf_expS F')).eq_expS).symm

@[simp] theorem expS_zero : expS (0 : ℚ⟦X⟧) = 1 :=
  isExpOf_zero_one.eq_expS.symm

theorem expS_mul_expS_neg (F : ℚ⟦X⟧) : expS F * expS (-F) = 1 := by
  rw [← expS_add, add_neg_cancel, expS_zero]

theorem expS_nsmul (F : ℚ⟦X⟧) (n : ℕ) : expS (n • F) = expS F ^ n :=
  (((isExpOf_expS F).pow n).eq_expS).symm

theorem constantCoeff_expS (F : ℚ⟦X⟧) : constantCoeff (expS F) = 1 :=
  (isExpOf_expS F).1

/-- Reindexing a sum whose terms are supported on `j` with `t ∣ j+1`. -/
theorem sum_dilate {t : ℕ} (ht : t ≠ 0) (M : ℕ) (f : ℕ → ℚ)
    (hf : ∀ j, ¬ t ∣ (j+1) → f j = 0) :
    ∑ j ∈ Finset.range (t*M), f j = ∑ u ∈ Finset.range M, f (t*u + (t-1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    have : ∑ x ∈ Finset.range t, f (t*M + x) = f (t*M + (t-1)) := by
      apply Finset.sum_eq_single (t-1)
      · intro x hx hne
        apply hf
        intro hc
        have hx' : x < t := Finset.mem_range.mp hx
        have : t ∣ (x+1) := (Nat.dvd_add_right ⟨M, rfl⟩).mp hc
        have := Nat.le_of_dvd (by omega) this
        omega
      · intro hc
        exact absurd (Finset.mem_range.mpr (by omega)) hc
    rw [this]

/-- `expand` transfers the exponential recursion. -/
theorem IsExpOf.expand {F G : ℚ⟦X⟧} (h : IsExpOf F G) (t : ℕ) (ht : t ≠ 0) :
    IsExpOf (PowerSeries.expand t ht F) (PowerSeries.expand t ht G) := by
  obtain ⟨h0, hrec⟩ := h
  constructor
  · rw [constantCoeff_expand, h0]
  · intro k
    by_cases hdvd : t ∣ (k+1)
    · -- k+1 = t * M with M ≥ 1
      obtain ⟨M, hM⟩ := hdvd
      have hM0 : M ≠ 0 := by rintro rfl; omega
      have hL : coeff (k+1) (PowerSeries.expand t ht G) = coeff M G := by
        rw [hM, coeff_expand_mul]
      rw [hL]
      have hsupp : ∀ j, ¬ t ∣ (j+1) →
          (((j+1 : ℕ) : ℚ) * coeff (j+1) (PowerSeries.expand t ht F))
            * coeff (k - j) (PowerSeries.expand t ht G) = 0 := by
        intro j hj
        rw [coeff_expand_of_not_dvd t ht F hj, mul_zero, zero_mul]
      rw [show (k+1) = t*M from hM, sum_dilate ht M _ hsupp]
      have hstep : ∀ u ∈ Finset.range M,
          (((t*u + (t-1) + 1 : ℕ) : ℚ) * coeff (t*u + (t-1) + 1) (PowerSeries.expand t ht F))
            * coeff (k - (t*u + (t-1))) (PowerSeries.expand t ht G)
          = ((t : ℕ) : ℚ) * ((((u+1 : ℕ) : ℚ) * coeff (u+1) F) * coeff (M - 1 - u) G) := by
        intro u hu
        have hu' : u < M := Finset.mem_range.mp hu
        have e1 : t*u + (t-1) + 1 = t*(u+1) := by rw [Nat.mul_succ]; omega
        have e2 : k - (t*u + (t-1)) = t*(M - 1 - u) := by
          have h3 : M = u + 1 + (M - 1 - u) := by omega
          have h4 : t*M = t*u + t + t*(M - 1 - u) := by
            conv_lhs => rw [h3]
            ring
          omega
        rw [e1, e2, coeff_expand_mul, coeff_expand_mul]
        push_cast
        ring
      rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
      have hrecM := hrec (M-1)
      rw [show M - 1 + 1 = M by omega] at hrecM
      have : ∑ u ∈ Finset.range M,
          (((u+1 : ℕ) : ℚ) * coeff (u+1) F) * coeff (M - 1 - u) G
          = ((M : ℕ) : ℚ) * coeff M G := hrecM.symm
      rw [this]
      push_cast
      ring
    · -- t ∤ k+1: both sides vanish
      have hL : coeff (k+1) (PowerSeries.expand t ht G) = 0 :=
        coeff_expand_of_not_dvd t ht G hdvd
      rw [hL, mul_zero]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hj1 : t ∣ (j+1)
      · -- t ∣ j+1 ; then t ∤ k - j, so the G-factor vanishes
        have hj2 : ¬ t ∣ (k - j) := by
          intro hc
          apply hdvd
          have hjk : j < k+1 := Finset.mem_range.mp hj
          have : (j+1) + (k-j) = k+1 := by omega
          rw [← this]
          exact Nat.dvd_add hj1 hc
        rw [coeff_expand_of_not_dvd t ht G hj2, mul_zero]
      · rw [coeff_expand_of_not_dvd t ht F hj1, mul_zero, zero_mul]

theorem expand_expS (F : ℚ⟦X⟧) (t : ℕ) (ht : t ≠ 0) :
    PowerSeries.expand t ht (expS F) = expS (PowerSeries.expand t ht F) :=
  ((isExpOf_expS F).expand t ht).eq_expS

/-- Coefficients of `F^ℓ` vanish below degree `ℓ` when `F` has no constant term. -/
theorem coeff_pow_eq_zero {F : ℚ⟦X⟧} (hF : constantCoeff F = 0) {ℓ n : ℕ} (h : n < ℓ) :
    coeff n (F ^ ℓ) = 0 := by
  have hX : (X : ℚ⟦X⟧) ∣ F := X_dvd_iff.mpr hF
  have hXl : (X : ℚ⟦X⟧)^ℓ ∣ F^ℓ := pow_dvd_pow_of_dvd hX ℓ
  exact X_pow_dvd_iff.mp hXl n h

/-- Derivative of a power. -/
theorem deriv_pow (F : ℚ⟦X⟧) (ℓ : ℕ) :
    d⁄dX ℚ (F ^ (ℓ+1)) = ((ℓ+1 : ℕ) : ℚ) • (d⁄dX ℚ F * F ^ ℓ) := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    rw [pow_succ (a := F) (n := ℓ+1), Derivation.leibniz, ih]
    simp only [smul_eq_mul (α := ℚ⟦X⟧), smul_eq_C_mul, Nat.cast_add, Nat.cast_one, map_add,
      map_one]
    ring

/-- Coefficient version of the Euler identity for `F^{ℓ+1}`. -/
theorem coeff_succ_pow_succ (F : ℚ⟦X⟧) (ℓ k : ℕ) :
    ((k+1 : ℕ) : ℚ) * coeff (k+1) (F ^ (ℓ+1)) =
    ((ℓ+1 : ℕ) : ℚ) * ∑ j ∈ Finset.range (k+1),
      (((j+1 : ℕ) : ℚ) * coeff (j+1) F) * coeff (k - j) (F ^ ℓ) := by
  have h := congrArg (fun φ => coeff k φ) (deriv_pow F ℓ)
  simp only at h
  rw [coeff_derivative, map_smul, smul_eq_mul] at h
  have h2 : coeff k (d⁄dX ℚ F * F ^ ℓ) = ∑ j ∈ Finset.range (k+1),
      (((j+1 : ℕ) : ℚ) * coeff (j+1) F) * coeff (k - j) (F ^ ℓ) := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => coeff a (d⁄dX ℚ F) * coeff b (F ^ ℓ))]
    apply Finset.sum_congr rfl
    intro j hj
    rw [coeff_derivative]
    push_cast
    ring
  rw [h2] at h
  calc ((k+1 : ℕ) : ℚ) * coeff (k+1) (F ^ (ℓ+1))
      = coeff (k+1) (F ^ (ℓ+1)) * ((k : ℚ)+1) := by push_cast; ring
    _ = _ := h

/-- The explicit exponential-sum series satisfies the exponential recursion. -/
theorem isExpOf_expSum (F : ℚ⟦X⟧) (hF : constantCoeff F = 0) :
    IsExpOf F (mk fun n => ∑ ℓ ∈ Finset.range (n+1),
      ((Nat.factorial ℓ : ℚ))⁻¹ * coeff n (F ^ ℓ)) := by
  constructor
  · rw [constantCoeff_mk]
    simp
  · intro k
    rw [coeff_mk]
    calc ((k+1 : ℕ) : ℚ) * ∑ ℓ ∈ Finset.range (k+1+1),
          ((Nat.factorial ℓ : ℚ))⁻¹ * coeff (k+1) (F ^ ℓ)
        = ∑ ℓ ∈ Finset.range (k+2),
          ((Nat.factorial ℓ : ℚ))⁻¹ * (((k+1 : ℕ) : ℚ) * coeff (k+1) (F ^ ℓ)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ℓ _ => by ring
      _ = ∑ ℓ ∈ Finset.range (k+1),
          ((Nat.factorial (ℓ+1) : ℚ))⁻¹ * (((k+1 : ℕ) : ℚ) * coeff (k+1) (F ^ (ℓ+1))) := by
          rw [Finset.sum_range_succ']
          simp [coeff_one]
      _ = ∑ ℓ ∈ Finset.range (k+1), ((Nat.factorial ℓ : ℚ))⁻¹ *
            ∑ j ∈ Finset.range (k+1),
              (((j+1 : ℕ) : ℚ) * coeff (j+1) F) * coeff (k - j) (F ^ ℓ) := by
          apply Finset.sum_congr rfl
          intro ℓ _
          rw [coeff_succ_pow_succ]
          rw [Nat.factorial_succ]
          have h1 : ((ℓ+1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero ℓ
          have h2 : ((Nat.factorial ℓ : ℚ)) ≠ 0 := by
            exact_mod_cast (Nat.factorial_ne_zero ℓ)
          push_cast
          field_simp
      _ = ∑ ℓ ∈ Finset.range (k+1), ∑ j ∈ Finset.range (k+1),
            ((Nat.factorial ℓ : ℚ))⁻¹ *
              ((((j+1 : ℕ) : ℚ) * coeff (j+1) F) * coeff (k - j) (F ^ ℓ)) := by
          exact Finset.sum_congr rfl fun ℓ _ => by rw [Finset.mul_sum]
      _ = ∑ j ∈ Finset.range (k+1), ∑ ℓ ∈ Finset.range (k+1),
            ((Nat.factorial ℓ : ℚ))⁻¹ *
              ((((j+1 : ℕ) : ℚ) * coeff (j+1) F) * coeff (k - j) (F ^ ℓ)) :=
          Finset.sum_comm
      _ = ∑ j ∈ Finset.range (k+1), (((j+1 : ℕ) : ℚ) * coeff (j+1) F) *
            ∑ ℓ ∈ Finset.range (k+1),
              ((Nat.factorial ℓ : ℚ))⁻¹ * coeff (k - j) (F ^ ℓ) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ℓ _ => by ring
      _ = ∑ j ∈ Finset.range (k+1), (((j+1 : ℕ) : ℚ) * coeff (j+1) F) *
            ∑ ℓ ∈ Finset.range (k - j + 1),
              ((Nat.factorial ℓ : ℚ))⁻¹ * coeff (k - j) (F ^ ℓ) := by
          apply Finset.sum_congr rfl
          intro j hj
          congr 1
          symm
          apply Finset.sum_subset
          · intro x hx
            exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
          · intro ℓ _ hℓ'
            rw [Finset.mem_range, not_lt] at hℓ'
            rw [coeff_pow_eq_zero hF (by omega), mul_zero]
      _ = ∑ j ∈ Finset.range (k+1), (((j+1 : ℕ) : ℚ) * coeff (j+1) F) *
            coeff (k - j) (mk fun n => ∑ ℓ ∈ Finset.range (n+1),
              ((Nat.factorial ℓ : ℚ))⁻¹ * coeff n (F ^ ℓ)) := by
          exact Finset.sum_congr rfl fun j _ => by rw [coeff_mk]

/-- Explicit formula for the coefficients of `expS`. -/
theorem coeff_expS (F : ℚ⟦X⟧) (hF : constantCoeff F = 0) (n : ℕ) :
    coeff n (expS F) = ∑ ℓ ∈ Finset.range (n+1),
      ((Nat.factorial ℓ : ℚ))⁻¹ * coeff n (F ^ ℓ) := by
  rw [← (isExpOf_expSum F hF).eq_expS, coeff_mk]

end

end Super

-- ===== Devel/D03.lean =====
/-! # D03: p-adic valuation laws for harmonic-type sums

Main results (`p ≥ 5` prime, `w = v_p N`):
* `V_bernoulli`: `v_p(B_e) ≥ -1` (von Staudt bound);
* `V_bernoulli_zero`: `v_p(B_e) ≥ 0` when `(p-1) ∤ e` (partial von Staudt–Clausen);
* `P2_law`: `v_p(∑_{k<N, p∤k} 1/k²) ≥ w`;
* `H_law`: `v_p(∑_{k<N, p∤k} 1/k) ≥ 2w`. -/

namespace Super

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## Small helpers -/

theorem V_inv_int_unit {z : ℤ} (hz : z ≠ 0) (h : ¬ (p:ℤ) ∣ z) : V p 0 ((z:ℚ))⁻¹ := by
  unfold V
  rw [inv_eq_one_div, padicNorm.div, padicNorm.one]
  rw [(padicNorm.int_eq_one_iff (p := p) z).mpr h]
  norm_num

theorem V_inv_pow_unit {k : ℕ} (t : ℕ) (hk : ¬ p ∣ k) : V p 0 (((k:ℚ)^t))⁻¹ := by
  have hk0 : k ≠ 0 := by rintro rfl; exact hk (dvd_zero p)
  have : ((k:ℚ)^t) = (((k^t : ℕ) : ℤ) : ℚ) := by push_cast; ring
  rw [this]
  apply V_inv_int_unit
  · exact_mod_cast pow_ne_zero t hk0
  · rw [Int.natCast_dvd_natCast (m := p) (n := k^t)]
    intro hc
    exact hk (hp.out.dvd_of_dvd_pow hc)

theorem V_of_mul_nat_unit {c : ℕ} (hc : ¬ p ∣ c) {k : ℤ} {a : ℚ} (h : V p k ((c:ℚ) * a)) :
    V p k a := by
  have hc0 : c ≠ 0 := by rintro rfl; exact hc (dvd_zero p)
  have : a = ((c:ℚ))⁻¹ * ((c:ℚ) * a) := by
    field_simp
  rw [this]
  have h1 : V p 0 ((c:ℚ))⁻¹ := by
    have : ((c:ℚ))⁻¹ = (((c:ℕ):ℚ)^1)⁻¹ := by norm_num
    rw [this]; exact V_inv_pow_unit 1 hc
  simpa using V_mul h1 h

theorem V_div_p {k : ℤ} {a : ℚ} (h : V p k ((p:ℚ) * a)) : V p (k - 1) a := by
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : a = ((p:ℚ))⁻¹ * ((p:ℚ) * a) := by field_simp
  rw [this]
  have h1 : V p (-1) ((p:ℚ))⁻¹ := by
    have h3 := V_inv_nat (p := p) (n := p) hp.out.ne_zero
    rw [padicValNat.self hp.out.one_lt] at h3
    rwa [one_div] at h3
  have := V_mul h1 h
  rwa [show (-1) + k = k - 1 by ring] at this

/-- `v_p(d) + 1 ≤ d` for `d ≥ 1`. -/
theorem padicValNat_add_one_le {d : ℕ} (hd : 1 ≤ d) : padicValNat p d + 1 ≤ d := by
  have h1 : p ^ (padicValNat p d) ∣ d := pow_padicValNat_dvd
  have h2 : p ^ (padicValNat p d) ≤ d := Nat.le_of_dvd (by omega) h1
  have h3 : padicValNat p d < 2 ^ (padicValNat p d) := Nat.lt_two_pow_self
  have h4 : 2 ^ (padicValNat p d) ≤ p ^ (padicValNat p d) :=
    Nat.pow_le_pow_left hp.out.two_le _
  omega

/-- `v_p(d) + 2 ≤ d` for `d ≥ 2`, `p ≥ 3`. -/
theorem padicValNat_add_two_le (hp3 : 3 ≤ p) {d : ℕ} (hd : 2 ≤ d) :
    padicValNat p d + 2 ≤ d := by
  set v := padicValNat p d with hv
  rcases Nat.eq_zero_or_pos v with h0 | h1
  · omega
  · have h2 : p ^ v ≤ d := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    have h3 : 3 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp3 v
    have h4 : v + 2 ≤ 3 ^ v := by
      clear_value v
      clear hv h2 h3
      induction v with
      | zero => omega
      | succ v ih =>
        rcases Nat.eq_zero_or_pos v with rfl | hv1
        · norm_num
        · have := ih (by omega)
          have h5 : 3 ^ (v+1) = 3 * 3 ^ v := by ring
          omega
    omega

/-- `w + 1 ≤ p ^ w`. -/
theorem lt_pow_self' (w : ℕ) : w + 1 ≤ p ^ w := by
  have h3 : w < 2 ^ w := Nat.lt_two_pow_self
  have h4 : 2 ^ w ≤ p ^ w := Nat.pow_le_pow_left hp.out.two_le _
  omega

/-! ## Dilation of sums supported on multiples of `t` -/

theorem sum_dilate₀ {t : ℕ} (ht : t ≠ 0) (M : ℕ) (f : ℕ → ℚ)
    (hf : ∀ j, ¬ t ∣ j → f j = 0) :
    ∑ j ∈ Finset.range (t*M), f j = ∑ u ∈ Finset.range M, f (t*u) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    apply Finset.sum_eq_single 0
    · intro x hx hne
      apply hf
      intro hc
      have hx' : x < t := Finset.mem_range.mp hx
      have : t ∣ x := (Nat.dvd_add_right ⟨M, rfl⟩).mp hc
      have := Nat.le_of_dvd (by omega) this
      omega
    · intro hc
      exact absurd (Finset.mem_range.mpr (by omega)) hc

/-! ## Rearranged Faulhaber formula -/

theorem choose_id (e i : ℕ) (hi : i ≤ e) :
    (e+1).choose i * (e+1-i) = (e+1) * e.choose i := by
  have h := Nat.add_one_mul_choose_eq e (e-i)
  rw [Nat.choose_symm hi] at h
  rw [show e - i + 1 = e + 1 - i by omega] at h
  rw [Nat.choose_symm (show i ≤ e+1 by omega)] at h
  omega

theorem faulhaber' (n e : ℕ) :
    (∑ k ∈ Finset.range n, (k:ℚ)^e) =
    ∑ i ∈ Finset.range (e+1),
      bernoulli i * (e.choose i : ℚ) * (n:ℚ)^(e+1-i) / ((e+1-i : ℕ) : ℚ) := by
  rw [sum_range_pow]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ e := by have := Finset.mem_range.mp hi; omega
  have hne1 : ((e:ℚ)+1) ≠ 0 := by positivity
  have hne2 : ((e+1-i : ℕ) : ℚ) ≠ 0 := by
    have : 1 ≤ e+1-i := by omega
    exact_mod_cast (by omega : e+1-i ≠ 0)
  have hid : ((e+1).choose i : ℚ) * ((e+1-i : ℕ) : ℚ) = ((e:ℚ)+1) * (e.choose i : ℚ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) (choose_id e i hi')
  rw [div_eq_div_iff hne1 hne2]
  linear_combination (bernoulli i * (n:ℚ)^(e+1-i)) * hid

/-! ## The Bernoulli recursion at `n = p` -/

/-- `p·B_e = S_e(p) - ∑_{i<e} B_i C(e,i) p^{e+1-i}/(e+1-i)`. -/
theorem bernoulli_rec (e : ℕ) :
    (p:ℚ) * bernoulli e = (∑ k ∈ Finset.range p, (k:ℚ)^e) -
      ∑ i ∈ Finset.range e,
        bernoulli i * (e.choose i : ℚ) * (p:ℚ)^(e+1-i) / ((e+1-i : ℕ) : ℚ) := by
  have h := faulhaber' p e
  rw [Finset.sum_range_succ] at h
  have he : e+1-e = 1 := by omega
  rw [he] at h
  simp only [Nat.choose_self, Nat.cast_one, pow_one] at h
  rw [h]
  push_cast
  ring

/-- von Staudt bound: `v_p(B_e) ≥ -1` for all `e`. -/
theorem V_bernoulli (e : ℕ) : V p (-1) (bernoulli e) := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    have key : V p 0 ((p:ℚ) * bernoulli e) := by
      rw [bernoulli_rec]
      apply V_sub
      · have : (∑ k ∈ Finset.range p, (k:ℚ)^e)
            = (((∑ k ∈ Finset.range p, k^e : ℕ) : ℚ)) := by push_cast; ring
        rw [this]; exact V_nat _
      · apply V_sum
        intro i hi
        have hie : i < e := Finset.mem_range.mp hi
        set d := e+1-i with hd
        have hd1 : 1 ≤ d := by omega
        have hterm : bernoulli i * (e.choose i : ℚ) * (p:ℚ)^d / ((d : ℕ) : ℚ)
            = (bernoulli i * (e.choose i : ℚ) * (p:ℚ)^d) * (1 / ((d : ℕ) : ℚ)) := by
          ring
        rw [hterm]
        have h1 : V p (-1 + 0 + d) (bernoulli i * (e.choose i : ℚ) * (p:ℚ)^d) :=
          V_mul (V_mul (ih i hie) (V_nat _)) (V_p_pow d)
        have h2 : V p (-(padicValNat p d : ℤ)) (1 / ((d : ℕ) : ℚ)) :=
          V_inv_nat (by omega)
        have h3 := V_mul h1 h2
        apply V_mono h3
        have h4 := padicValNat_add_one_le (p := p) hd1
        omega
    have := V_div_p key
    simpa using this

/-- Modulo `p`: `p·B_e ≡ S_e(p)` (for `p ≥ 3`). -/
theorem V_pB_sub_S (hp3 : 3 ≤ p) (e : ℕ) :
    V p 1 ((p:ℚ) * bernoulli e - ∑ k ∈ Finset.range p, (k:ℚ)^e) := by
  rw [bernoulli_rec]
  rw [show ∀ a b : ℚ, a - b - a = -b from fun a b => by ring]
  apply V_neg
  apply V_sum
  intro i hi
  have hie : i < e := Finset.mem_range.mp hi
  set d := e+1-i with hd
  have hd2 : 2 ≤ d := by omega
  have hterm : bernoulli i * (e.choose i : ℚ) * (p:ℚ)^d / ((d : ℕ) : ℚ)
      = (bernoulli i * (e.choose i : ℚ) * (p:ℚ)^d) * (1 / ((d : ℕ) : ℚ)) := by
    ring
  rw [hterm]
  have h1 : V p (-1 + 0 + d) (bernoulli i * (e.choose i : ℚ) * (p:ℚ)^d) :=
    V_mul (V_mul (V_bernoulli i) (V_nat _)) (V_p_pow d)
  have h2 : V p (-(padicValNat p d : ℤ)) (1 / ((d : ℕ) : ℚ)) :=
    V_inv_nat (by omega)
  have h3 := V_mul h1 h2
  apply V_mono h3
  have h4 := padicValNat_add_two_le (p := p) hp3 hd2
  omega

/-! ## Power sums over a full period vanish mod p -/

theorem sum_univ_zmod_pow {e : ℕ} (he : e ≠ 0) (hnd : ¬ (p-1) ∣ e) :
    ∑ x : ZMod p, x ^ e = 0 := by
  classical
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have h1 : ∑ x : ZMod p, x ^ e = ∑ x ∈ Finset.univ \ {(0 : ZMod p)}, x ^ e := by
    rw [← Finset.sum_sdiff (Finset.subset_univ ({0} : Finset (ZMod p))),
      Finset.sum_singleton, zero_pow he, add_zero]
  have h2 : ∑ x ∈ Finset.univ \ {(0 : ZMod p)}, x ^ e = ∑ x : (ZMod p)ˣ, ((x : ZMod p)) ^ e := by
    refine Finset.sum_bij' (fun (a : ZMod p) (ha : a ∈ Finset.univ \ {(0 : ZMod p)}) =>
        Units.mk0 a (by simpa using (Finset.mem_sdiff.mp ha).2))
      (fun (u : (ZMod p)ˣ) _ => (u : ZMod p)) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact Finset.mem_univ _
    · intro u hu
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      simp [Units.ne_zero u]
    · intro a ha
      rfl
    · intro u hu
      exact Units.ext rfl
    · intro a ha
      rfl
  rw [h1, h2]
  have h3 := FiniteField.sum_pow_units (ZMod p) e
  rw [h3, if_neg]
  rwa [hcard]

theorem V_S_e {e : ℕ} (he : e ≠ 0) (hnd : ¬ (p-1) ∣ e) :
    V p 1 (∑ k ∈ Finset.range p, (k:ℚ)^e) := by
  have hcast : (∑ k ∈ Finset.range p, (k:ℚ)^e)
      = (((∑ k ∈ Finset.range p, k^e : ℕ) : ℚ)) := by push_cast; ring
  rw [hcast, show (1 : ℤ) = ((1 : ℕ) : ℤ) by norm_num, V_nat_iff_dvd, pow_one]
  have hzero : ((∑ k ∈ Finset.range p, k^e : ℕ) : ZMod p) = 0 := by
    push_cast
    have hswap : ∑ k ∈ Finset.range p, (k : ZMod p)^e = ∑ x : ZMod p, x ^ e := by
      apply Finset.sum_nbij' (fun k => ((k : ℕ) : ZMod p)) (fun x => x.val)
      · intro a ha; exact Finset.mem_univ _
      · intro x hx
        exact Finset.mem_range.mpr (ZMod.val_lt x)
      · intro a ha
        exact ZMod.val_cast_of_lt (Finset.mem_range.mp ha)
      · intro x hx
        exact ZMod.natCast_rightInverse x
      · intro a ha
        rfl
    rw [hswap, sum_univ_zmod_pow he hnd]
  exact (ZMod.natCast_eq_zero_iff _ p).mp hzero

/-- Partial von Staudt–Clausen: `v_p(B_e) ≥ 0` when `(p-1) ∤ e`, `e ≥ 1`, `p ≥ 3`. -/
theorem V_bernoulli_zero (hp3 : 3 ≤ p) {e : ℕ} (he : e ≠ 0) (hnd : ¬ (p-1) ∣ e) :
    V p 0 (bernoulli e) := by
  have h1 : V p 1 ((p:ℚ) * bernoulli e) := by
    have := V_add (V_pB_sub_S (p := p) hp3 e) (V_S_e (p := p) he hnd)
    simpa using this
  simpa using V_div_p h1

/-! ## The P2 law -/

theorem P2_law (hp5 : 5 ≤ p) {N : ℕ} (hN : N ≠ 0) :
    V p (padicValNat p N : ℤ)
      (∑ k ∈ (Finset.range N).filter (fun k => ¬ p ∣ k), ((k:ℚ)^2)⁻¹) := by
  set w := padicValNat p N with hw
  rcases Nat.eq_zero_or_pos w with hw0 | hw1
  · rw [hw0]
    apply V_sum
    intro k hk
    exact_mod_cast V_inv_pow_unit 2 (Finset.mem_filter.mp hk).2
  · -- main case: w ≥ 1
    have hpN : p ∣ N :=
      dvd_trans (dvd_pow_self p (by omega : w ≠ 0)) pow_padicValNat_dvd
    obtain ⟨N', hN'⟩ := hpN
    have hN'0 : N' ≠ 0 := by rintro rfl; simp at hN'; exact hN hN'
    set e := (p-1) * p^w - 2 with he
    have hpw : p ≤ p^w := by
      calc p = p^1 := (pow_one p).symm
      _ ≤ p^w := Nat.pow_le_pow_right (by omega) (by omega)
    have hbig : 20 ≤ (p-1) * p^w := by
      have h1 : 5 ≤ p^w := by omega
      have h2 : 4 ≤ p-1 := by omega
      calc (20 : ℕ) = 4 * 5 := by norm_num
      _ ≤ (p-1) * p^w := Nat.mul_le_mul h2 h1
    have he2 : e + 2 = (p-1) * p^w := by omega
    have hew : w + 1 ≤ e := by
      have h3 := lt_pow_self' (p := p) w
      have h2 : 4 ≤ p-1 := by omega
      have : 4 * (w+1) ≤ (p-1) * p^w := Nat.mul_le_mul h2 h3
      omega
    have he0 : e ≠ 0 := by omega
    -- Step 1: per-term Euler congruence
    have step1 : ∀ k ∈ (Finset.range N).filter (fun k => ¬ p ∣ k),
        V p ((w:ℤ)+1) (((k:ℚ)^2)⁻¹ - (k:ℚ)^e) := by
      intro k hk
      obtain ⟨hkr, hkd⟩ := Finset.mem_filter.mp hk
      have hk0 : k ≠ 0 := by rintro rfl; exact hkd (dvd_zero p)
      have hcop : Nat.Coprime k (p^(w+1)) :=
        Nat.Coprime.pow_right _
          (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hkd))
      have heuler := Nat.ModEq.pow_totient hcop
      have htot : Nat.totient (p^(w+1)) = p^w * (p-1) := by
        have h := Nat.totient_prime_pow hp.out (show 0 < w+1 by omega)
        simpa using h
      rw [htot] at heuler
      have hdvd : (p:ℤ)^(w+1) ∣ ((k:ℤ)^(e+2) - 1) := by
        have hd2 := heuler.symm.dvd
        push_cast at hd2
        rw [show e + 2 = p^w * (p-1) by rw [he2]; ring]
        exact_mod_cast hd2
      have hV : V p ((w:ℤ)+1) ((k:ℚ)^(e+2) - 1) := by
        have hcast : ((k:ℚ)^(e+2) - 1) = ((((k:ℤ)^(e+2) - 1 : ℤ)) : ℚ) := by push_cast; ring
        rw [hcast, show (w:ℤ)+1 = ((w+1 : ℕ) : ℤ) by push_cast; ring, V_int_iff_dvd]
        exact hdvd
      have hkQ : (k:ℚ) ≠ 0 := by exact_mod_cast hk0
      have hk2 : ((k:ℚ)^2) ≠ 0 := pow_ne_zero _ hkQ
      have hpow : ((k:ℚ)^2)⁻¹ * (k:ℚ)^(e+2) = (k:ℚ)^e := by
        rw [pow_add]
        calc ((k:ℚ)^2)⁻¹ * ((k:ℚ)^e * (k:ℚ)^2)
            = (k:ℚ)^e * (((k:ℚ)^2)⁻¹ * (k:ℚ)^2) := by ring
        _ = (k:ℚ)^e := by rw [inv_mul_cancel₀ hk2, mul_one]
      have hfact : ((k:ℚ)^2)⁻¹ - (k:ℚ)^e = -(((k:ℚ)^2)⁻¹ * ((k:ℚ)^(e+2) - 1)) := by
        rw [mul_sub, hpow, mul_one, neg_sub]
      rw [hfact]
      apply V_neg
      have := V_mul (V_inv_pow_unit 2 hkd) hV
      simpa using this
    -- Step 2: full power sum has valuation ≥ w
    have hS : V p (w:ℤ) (∑ k ∈ Finset.range N, (k:ℚ)^e) := by
      rw [faulhaber' N e, Finset.sum_range_succ]
      apply V_add
      · apply V_sum
        intro i hi
        have hie : i < e := Finset.mem_range.mp hi
        set d := e+1-i with hd
        have hd2 : 2 ≤ d := by omega
        have hterm : bernoulli i * (e.choose i : ℚ) * (N:ℚ)^d / ((d : ℕ) : ℚ)
            = ((bernoulli i * (e.choose i : ℚ)) * (N:ℚ)^d) * (1 / ((d : ℕ) : ℚ)) := by
          ring
        rw [hterm]
        have h1 : V p (-1 + 0) (bernoulli i * (e.choose i : ℚ)) :=
          V_mul (V_bernoulli i) (V_nat _)
        have hNd : V p ((d:ℕ) * (w:ℤ)) ((N:ℚ)^d) := V_pow (V_padicValNat hN) d
        have h2 := V_mul h1 hNd
        have h3 := V_mul h2 (V_inv_nat (p := p) (n := d) (by omega))
        apply V_mono h3
        have h4 := padicValNat_add_two_le (p := p) (by omega) hd2
        have h5 : padicValNat p d + 1 ≤ (d-1) * w := by
          have := Nat.mul_le_mul (show padicValNat p d + 1 ≤ d - 1 by omega)
            (show 1 ≤ w by omega)
          omega
        have h5' : (padicValNat p d : ℤ) + 1 ≤ ((d:ℤ)-1) * (w:ℤ) := by
          calc (padicValNat p d : ℤ) + 1 = ((padicValNat p d + 1 : ℕ) : ℤ) := by omega
          _ ≤ (((d-1) * w : ℕ) : ℤ) := by exact_mod_cast h5
          _ = ((d:ℤ)-1) * (w:ℤ) := by
              rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ d by omega)]
              norm_num
        linarith
      · -- top term: `B_e · N`
        rw [show e+1-e = 1 by omega]
        simp only [Nat.choose_self, Nat.cast_one, pow_one]
        have hnd : ¬ (p-1) ∣ e := by
          intro hdd
          have hd1 : (p-1) ∣ (p-1) * p^w := Dvd.intro _ rfl
          have hd2 : (p-1) ∣ 2 := by
            have := Nat.dvd_sub hd1 hdd
            rwa [show (p-1) * p^w - e = 2 by omega] at this
          have := Nat.le_of_dvd (by norm_num) hd2
          omega
        have hBe : V p 0 (bernoulli e) := V_bernoulli_zero (by omega) he0 hnd
        have h1 := V_mul hBe (V_padicValNat (p := p) hN)
        simpa using h1
    -- Step 3: restrict to `p ∤ k`
    have hdil : ∑ k ∈ (Finset.range N).filter (fun k => p ∣ k), (k:ℚ)^e
        = (p:ℚ)^e * ∑ j ∈ Finset.range N', (j:ℚ)^e := by
      rw [Finset.sum_filter, hN', sum_dilate₀ hp.out.ne_zero N'
        (fun k => if p ∣ k then (k:ℚ)^e else 0) (fun j hj => if_neg hj), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [if_pos (dvd_mul_right p u)]
      push_cast
      ring
    have hS' : V p (w:ℤ) (∑ k ∈ (Finset.range N).filter (fun k => ¬ p ∣ k), (k:ℚ)^e) := by
      have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range N)
        (fun k => p ∣ k) (fun k => (k:ℚ)^e)
      have heq : ∑ k ∈ (Finset.range N).filter (fun k => ¬ p ∣ k), (k:ℚ)^e
          = (∑ k ∈ Finset.range N, (k:ℚ)^e)
            - ∑ k ∈ (Finset.range N).filter (fun k => p ∣ k), (k:ℚ)^e := by
        rw [← hsplit]; ring
      rw [heq]
      apply V_sub hS
      rw [hdil]
      have h1 : V p (e:ℤ) ((p:ℚ)^e) := V_p_pow e
      have h2 : V p 0 (∑ j ∈ Finset.range N', (j:ℚ)^e) := by
        apply V_sum; intro j _
        rw [show ((j:ℚ)^e) = (((j^e : ℕ)):ℚ) by push_cast; ring]
        exact V_nat _
      have h3 := V_mul h1 h2
      apply V_mono h3
      omega
    -- combine
    have hfin : ∑ k ∈ (Finset.range N).filter (fun k => ¬ p ∣ k), ((k:ℚ)^2)⁻¹
        = (∑ k ∈ (Finset.range N).filter (fun k => ¬ p ∣ k), (((k:ℚ)^2)⁻¹ - (k:ℚ)^e))
          + ∑ k ∈ (Finset.range N).filter (fun k => ¬ p ∣ k), (k:ℚ)^e := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hfin]
    exact V_add (V_mono (V_sum step1) (by omega)) hS'

/-! ## The H law -/

theorem H_law (hp5 : 5 ≤ p) {N : ℕ} (hN : N ≠ 0) :
    V p (2 * (padicValNat p N : ℤ))
      (∑ k ∈ (Finset.range N).filter (fun k => ¬ p ∣ k), ((k:ℚ))⁻¹) := by
  set w := padicValNat p N with hw
  rcases Nat.eq_zero_or_pos w with hw0 | hw1
  · rw [hw0]
    have h0 : V p 0 (∑ k ∈ (Finset.range N).filter (fun k => ¬ p ∣ k), ((k:ℚ))⁻¹) :=
      V_sum (fun k hk => by
        simpa using V_inv_pow_unit (p := p) 1 (Finset.mem_filter.mp hk).2)
    exact V_mono h0 (by norm_num)
  · have hpN : p ∣ N :=
      dvd_trans (dvd_pow_self p (by omega : w ≠ 0)) pow_padicValNat_dvd
    set s := (Finset.range N).filter (fun k => ¬ p ∣ k) with hs
    have hmem : ∀ k ∈ s, k ≠ 0 ∧ k < N ∧ ¬ p ∣ k := by
      intro k hk
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hk
      exact ⟨fun h => h2 (h ▸ dvd_zero p), Finset.mem_range.mp h1, h2⟩
    have hstab : ∀ k ∈ s, N - k ∈ s := by
      intro k hk
      obtain ⟨hk0, hkN, hkd⟩ := hmem k hk
      rw [hs, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      intro hc
      apply hkd
      have h := Nat.dvd_sub hpN hc
      rwa [show N - (N-k) = k by omega] at h
    have hrefl : ∑ k ∈ s, (((N - k : ℕ)):ℚ)⁻¹ = ∑ k ∈ s, ((k:ℚ))⁻¹ := by
      apply Finset.sum_nbij' (fun k => N - k) (fun k => N - k)
      · exact hstab
      · exact hstab
      · intro k hk; obtain ⟨h1, h2, _⟩ := hmem k hk; omega
      · intro k hk; obtain ⟨h1, h2, _⟩ := hmem k hk; omega
      · intro k hk; rfl
    have h2H : (2:ℚ) * ∑ k ∈ s, ((k:ℚ))⁻¹
        = ∑ k ∈ s, (((k:ℚ))⁻¹ + (((N - k : ℕ)):ℚ)⁻¹) := by
      rw [Finset.sum_add_distrib, hrefl]
      ring
    have hpoint : ∀ k ∈ s, ((k:ℚ))⁻¹ + (((N - k : ℕ)):ℚ)⁻¹
        = -((N:ℚ) * ((k:ℚ)^2)⁻¹) - (N:ℚ)^2 * ((k:ℚ)^3)⁻¹
          - (N:ℚ)^3 * (((k:ℚ)^3 * ((k:ℚ) - (N:ℚ)))⁻¹) := by
      intro k hk
      obtain ⟨hk0, hkN, hkd⟩ := hmem k hk
      have hkQ : (k:ℚ) ≠ 0 := by exact_mod_cast hk0
      have hcast : (((N - k : ℕ)):ℚ) = (N:ℚ) - (k:ℚ) := by
        rw [Nat.cast_sub hkN.le]
      have hNk : (N:ℚ) - (k:ℚ) ≠ 0 := by
        intro hc
        have hkN2 : (k:ℚ) = (N:ℚ) := by linarith
        have : k = N := by exact_mod_cast hkN2
        omega
      have hkN' : (k:ℚ) - (N:ℚ) ≠ 0 := by
        intro hc; apply hNk; linarith
      rw [hcast]
      field_simp
      ring
    have hsplit3 : ∑ k ∈ s, (((k:ℚ))⁻¹ + (((N - k : ℕ)):ℚ)⁻¹)
        = -((N:ℚ) * ∑ k ∈ s, ((k:ℚ)^2)⁻¹) + (-((N:ℚ)^2 * ∑ k ∈ s, ((k:ℚ)^3)⁻¹))
          + (-((N:ℚ)^3 * ∑ k ∈ s, (((k:ℚ)^3 * ((k:ℚ) - (N:ℚ)))⁻¹))) := by
      rw [Finset.sum_congr rfl hpoint, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hP2 : V p (w:ℤ) (∑ k ∈ s, ((k:ℚ)^2)⁻¹) := P2_law hp5 hN
    have hS3 : V p 0 (∑ k ∈ s, ((k:ℚ)^3)⁻¹) := by
      apply V_sum
      intro k hk
      exact V_inv_pow_unit 3 (hmem k hk).2.2
    have hSmix : V p 0 (∑ k ∈ s, (((k:ℚ)^3 * ((k:ℚ) - (N:ℚ)))⁻¹)) := by
      apply V_sum
      intro k hk
      obtain ⟨hk0, hkN, hkd⟩ := hmem k hk
      rw [mul_inv]
      have h1 := V_inv_pow_unit (p := p) 3 hkd
      have h2 : V p 0 (((k:ℚ) - (N:ℚ)))⁻¹ := by
        have hz : ((k:ℤ) - (N:ℤ)) ≠ 0 := by
          intro hc
          have : (k:ℤ) = (N:ℤ) := by omega
          have : k = N := by exact_mod_cast this
          omega
        have hd : ¬ (p:ℤ) ∣ ((k:ℤ) - (N:ℤ)) := by
          intro hc
          apply hkd
          have hNd : (p:ℤ) ∣ (N:ℤ) := Int.natCast_dvd_natCast.mpr hpN
          have : (p:ℤ) ∣ (k:ℤ) := by
            have := dvd_add hc hNd
            rwa [sub_add_cancel] at this
          exact_mod_cast this
        have h3 := V_inv_int_unit (p := p) hz hd
        rwa [show (((k:ℤ) - (N:ℤ) : ℤ) : ℚ) = ((k:ℚ) - (N:ℚ)) by push_cast; ring] at h3
      simpa using V_mul h1 h2
    have hV2H : V p (2 * (w:ℤ)) ((2:ℚ) * ∑ k ∈ s, ((k:ℚ))⁻¹) := by
      rw [h2H, hsplit3]
      apply V_add
      apply V_add
      · apply V_neg
        have h1 := V_mul (V_padicValNat (p := p) hN) hP2
        apply V_mono h1
        omega
      · apply V_neg
        have h1 := V_mul (V_pow (V_padicValNat (p := p) hN) 2) hS3
        apply V_mono h1
        omega
      · apply V_neg
        have h1 := V_mul (V_pow (V_padicValNat (p := p) hN) 3) hSmix
        apply V_mono h1
        omega
    apply V_of_mul_nat_unit (p := p) (c := 2)
      (by intro h; have := Nat.le_of_dvd (by norm_num) h; omega)
    rwa [show (((2:ℕ)):ℚ) = (2:ℚ) by norm_num]

end Super

-- ===== Devel/D04.lean =====
/-! # D04: the Kazandzidis congruence

For `p ≥ 5` prime, `b ≥ 1`, `v ≥ 1` with `v ≤ v_p(bp)` and `v_p(cp) ≥ v`:
`binom((b+c)p, bp) / binom(b+c, b) ≡ 1 mod p^{3v}`  (`kaz_strong`);
and for every prime, the same mod `p^v` (`kaz_gauss`). -/

namespace Super

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## Factorial splitting -/

/-- Multiplicative dilation: only indices `j` with `t ∣ j+1` contribute. -/
theorem prod_dilate {t : ℕ} (ht : t ≠ 0) (M : ℕ) (f : ℕ → ℕ)
    (hf : ∀ j, ¬ t ∣ (j+1) → f j = 1) :
    ∏ j ∈ Finset.range (t*M), f j = ∏ u ∈ Finset.range M, f (t*u + (t-1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, Finset.prod_range_add, ih, Finset.prod_range_succ]
    congr 1
    apply Finset.prod_eq_single (t-1)
    · intro x hx hne
      apply hf
      intro hc
      have hx' : x < t := Finset.mem_range.mp hx
      have h1 : t ∣ (x+1) := (Nat.dvd_add_right ⟨M, rfl⟩).mp hc
      have := Nat.le_of_dvd (by omega) h1
      omega
    · intro hc
      exact absurd (Finset.mem_range.mpr (by omega)) hc

/-- The product of `1 ≤ k ≤ M` coprime to `p` (via an `if` over `range M`). -/
def Fcop (p M : ℕ) : ℕ := ∏ k ∈ Finset.range M, (if p ∣ (k+1) then 1 else (k+1))

theorem Fcop_pos (M : ℕ) : 0 < Fcop p M := by
  apply Finset.prod_pos
  intro k hk
  split <;> omega

theorem factorial_split (N : ℕ) : Nat.factorial (N*p) = p^N * Nat.factorial N * Fcop p (N*p) := by
  have h0 : Nat.factorial (N*p) = ∏ k ∈ Finset.range (N*p), (k+1) :=
    (Finset.prod_range_add_one_eq_factorial _).symm
  have h1 : ∀ k : ℕ, k + 1 =
      (if p ∣ (k+1) then (k+1) else 1) * (if p ∣ (k+1) then 1 else (k+1)) := by
    intro k
    split <;> omega
  have h2 : ∏ k ∈ Finset.range (N*p), (k+1)
      = (∏ k ∈ Finset.range (N*p), (if p ∣ (k+1) then (k+1) else 1)) * Fcop p (N*p) := by
    rw [Fcop, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => h1 k
  have h3 : ∏ k ∈ Finset.range (N*p), (if p ∣ (k+1) then (k+1) else 1)
      = p^N * Nat.factorial N := by
    rw [show N*p = p*N by ring, prod_dilate hp.out.ne_zero N _
      (fun j hj => if_neg hj)]
    have : ∀ u : ℕ, (if p ∣ (p*u + (p-1) + 1) then (p*u + (p-1) + 1) else 1) = p * (u+1) := by
      intro u
      have hpe : p*u + (p-1) + 1 = p*(u+1) := by
        have h5 : p*(u+1) = p*u + p := by ring
        have hp1 : 1 ≤ p := hp.out.pos
        omega
      rw [hpe, if_pos ⟨u+1, rfl⟩]
    rw [Finset.prod_congr rfl fun u _ => this u, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_range, Finset.prod_range_add_one_eq_factorial]
  rw [h0, h2, h3]

/-! ## The product formula for the binomial ratio -/

theorem choose_key (b c : ℕ) :
    ((b+c)*p).choose (b*p) * (Fcop p (b*p) * Fcop p (c*p))
      = (b+c).choose b * Fcop p ((b+c)*p) := by
  set a := b + c with ha
  have hD : 0 < p^a * (Nat.factorial b * Nat.factorial c) := by
    have := hp.out.pos
    positivity
  apply Nat.eq_of_mul_eq_mul_right hD
  have h1 : (a*p).choose (b*p) * Nat.factorial (b*p) * Nat.factorial (c*p)
      = Nat.factorial (a*p) := by
    have hle : b*p ≤ a*p := Nat.mul_le_mul_right p (by omega)
    have := Nat.choose_mul_factorial_mul_factorial hle
    rwa [show a*p - b*p = c*p by rw [ha, Nat.add_mul, Nat.add_sub_cancel_left]] at this
  have h2 : a.choose b * Nat.factorial b * Nat.factorial c = Nat.factorial a := by
    have := Nat.choose_mul_factorial_mul_factorial (show b ≤ a by omega)
    rwa [show a - b = c by omega] at this
  calc ((a*p).choose (b*p) * (Fcop p (b*p) * Fcop p (c*p))) * (p^a * (Nat.factorial b * Nat.factorial c))
      = (a*p).choose (b*p) * ((p^b * Nat.factorial b * Fcop p (b*p))
        * (p^c * Nat.factorial c * Fcop p (c*p))) := by
        rw [ha, pow_add]
        ring
    _ = (a*p).choose (b*p) * (Nat.factorial (b*p) * Nat.factorial (c*p)) := by
        rw [← factorial_split b, ← factorial_split c]
    _ = Nat.factorial (a*p) := by rw [← h1]; ring
    _ = p^a * Nat.factorial a * Fcop p (a*p) := factorial_split a
    _ = p^a * (a.choose b * Nat.factorial b * Nat.factorial c) * Fcop p (a*p) := by rw [h2]
    _ = (a.choose b * Fcop p (a*p)) * (p^a * (Nat.factorial b * Nat.factorial c)) := by ring

theorem Fcop_shift (b c : ℕ) :
    Fcop p ((b+c)*p) = Fcop p (c*p)
      * ∏ k ∈ Finset.range (b*p), (if p ∣ (k+1) then 1 else (c*p + k + 1)) := by
  rw [Fcop, show (b+c)*p = c*p + b*p by ring, Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  have hdvd : p ∣ (c*p + x + 1) ↔ p ∣ (x+1) := by
    rw [show c*p + x + 1 = c*p + (x+1) by ring]
    exact Nat.dvd_add_right ⟨c, mul_comm c p⟩
  by_cases hc : p ∣ (x+1)
  · rw [if_pos hc, if_pos (hdvd.mpr hc)]
  · rw [if_neg hc, if_neg (fun h => hc (hdvd.mp h))]

/-- The binomial ratio as a product of `1 + cp/j`. -/
theorem choose_ratio_eq (b c : ℕ) :
    ((((b+c)*p).choose (b*p)) : ℚ) = (((b+c).choose b) : ℚ) *
      ∏ k ∈ (Finset.range (b*p)).filter (fun k => ¬ p ∣ (k+1)),
        (1 + ((c:ℚ) * (p:ℚ)) / ((k+1 : ℕ) : ℚ)) := by
  have hFb : ((Fcop p (b*p) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Fcop_pos (p := p) (b*p)).ne'
  have hFc : ((Fcop p (c*p) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Fcop_pos (p := p) (c*p)).ne'
  have hkey : ((((b+c)*p).choose (b*p)) : ℚ) * (Fcop p (b*p) : ℚ) * (Fcop p (c*p) : ℚ)
      = (((b+c).choose b) : ℚ) * (Fcop p ((b+c)*p) : ℚ) := by
    have h := choose_key (p := p) b c
    have h' : (((b+c)*p).choose (b*p) * Fcop p (b*p) * Fcop p (c*p) : ℕ)
        = ((b+c).choose b * Fcop p ((b+c)*p) : ℕ) := by
      rw [mul_assoc]; exact h
    exact_mod_cast h'
  have hshift : ((Fcop p ((b+c)*p) : ℕ) : ℚ) = (Fcop p (c*p) : ℚ)
      * ∏ k ∈ Finset.range (b*p), (if p ∣ (k+1) then (1:ℚ) else (c*p + k + 1 : ℕ)) := by
    rw [Fcop_shift b c]
    push_cast
    congr 1
  -- per-factor: (if P then 1 else cp+k+1) = (if P then 1 else (1 + cp/(k+1))) * (if P then 1 else (k+1))
  have hsplitf : ∀ k : ℕ, (if p ∣ (k+1) then (1:ℚ) else (c*p + k + 1 : ℕ))
      = (if p ∣ (k+1) then (1:ℚ) else (1 + ((c:ℚ) * (p:ℚ)) / ((k+1 : ℕ) : ℚ)))
        * (if p ∣ (k+1) then (1:ℚ) else ((k+1 : ℕ) : ℚ)) := by
    intro k
    have hk1 : ((k+1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    by_cases hc : p ∣ (k+1)
    · simp [hc]
    · rw [if_neg hc, if_neg hc, if_neg hc]
      field_simp
      push_cast
      ring
  have hFb' : ((Fcop p (b*p) : ℕ) : ℚ)
      = ∏ k ∈ Finset.range (b*p), (if p ∣ (k+1) then (1:ℚ) else ((k+1 : ℕ) : ℚ)) := by
    rw [Fcop]
    push_cast
    apply Finset.prod_congr rfl
    intro x hx
    split <;> push_cast <;> ring
  have hprod : ∏ k ∈ Finset.range (b*p), (if p ∣ (k+1) then (1:ℚ) else (c*p + k + 1 : ℕ))
      = (∏ k ∈ Finset.range (b*p),
          (if p ∣ (k+1) then (1:ℚ) else (1 + ((c:ℚ) * (p:ℚ)) / ((k+1 : ℕ) : ℚ))))
        * (Fcop p (b*p) : ℚ) := by
    rw [hFb', ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => hsplitf k
  have hfilter : ∏ k ∈ Finset.range (b*p),
      (if p ∣ (k+1) then (1:ℚ) else (1 + ((c:ℚ) * (p:ℚ)) / ((k+1 : ℕ) : ℚ)))
      = ∏ k ∈ (Finset.range (b*p)).filter (fun k => ¬ p ∣ (k+1)),
          (1 + ((c:ℚ) * (p:ℚ)) / ((k+1 : ℕ) : ℚ)) := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro x hx
    by_cases hc : p ∣ (x+1)
    · rw [if_pos hc, if_neg (fun h => h hc)]
    · rw [if_neg hc, if_pos hc]
  -- combine
  have h1 : ((((b+c)*p).choose (b*p)) : ℚ) * (Fcop p (b*p) : ℚ) * (Fcop p (c*p) : ℚ)
      = ((((b+c).choose b) : ℚ) *
        ∏ k ∈ (Finset.range (b*p)).filter (fun k => ¬ p ∣ (k+1)),
          (1 + ((c:ℚ) * (p:ℚ)) / ((k+1 : ℕ) : ℚ)))
        * (Fcop p (b*p) : ℚ) * (Fcop p (c*p) : ℚ) := by
    rw [hkey, hshift, hprod, hfilter]
    ring
  have h2 := mul_right_cancel₀ hFc h1
  exact mul_right_cancel₀ hFb h2

/-! ## The valuation hierarchy for products of `1 + (small)` -/

theorem VP0 {s : Finset ℕ} {y : ℕ → ℚ} (hy : ∀ j ∈ s, V p 0 (y j)) :
    V p 0 (∏ j ∈ s, (1 + y j)) := by
  have h := V_prod (p := p) (s := s) (f := fun j => 1 + y j) (g := fun _ => 0)
    (fun j hj => V_add (V_one) (hy j hj))
  simpa using h

theorem VP1 {v : ℤ} (hv : 0 ≤ v) {s : Finset ℕ} {y : ℕ → ℚ}
    (hy : ∀ j ∈ s, V p v (y j)) :
    V p v ((∏ j ∈ s, (1 + y j)) - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using V_zero_val (p := p) v
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have key : (1 + y a) * (∏ j ∈ s, (1 + y j)) - 1
        = ((∏ j ∈ s, (1 + y j)) - 1) + y a * (∏ j ∈ s, (1 + y j)) := by ring
    rw [key]
    apply V_add (ih fun j hj => hy j (Finset.mem_insert_of_mem hj))
    have h1 := V_mul (hy a (Finset.mem_insert_self a s))
      (VP0 fun j hj => V_mono (hy j (Finset.mem_insert_of_mem hj)) hv)
    simpa using h1

theorem VP2 {v : ℤ} (hv : 0 ≤ v) {s : Finset ℕ} {y : ℕ → ℚ}
    (hy : ∀ j ∈ s, V p v (y j)) :
    V p (2*v) ((∏ j ∈ s, (1 + y j)) - 1 - ∑ j ∈ s, y j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using V_zero_val (p := p) (2*v)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have key : (1 + y a) * (∏ j ∈ s, (1 + y j)) - 1 - (y a + ∑ j ∈ s, y j)
        = ((∏ j ∈ s, (1 + y j)) - 1 - ∑ j ∈ s, y j)
          + y a * ((∏ j ∈ s, (1 + y j)) - 1) := by ring
    rw [key]
    apply V_add (ih fun j hj => hy j (Finset.mem_insert_of_mem hj))
    have h1 := V_mul (hy a (Finset.mem_insert_self a s))
      (VP1 hv fun j hj => hy j (Finset.mem_insert_of_mem hj))
    have : v + v = 2*v := by ring
    rwa [this] at h1

theorem VP3 {v : ℤ} (hv : 0 ≤ v) {s : Finset ℕ} {y : ℕ → ℚ}
    (hy : ∀ j ∈ s, V p v (y j)) :
    V p (3*v) ((∏ j ∈ s, (1 + y j)) - 1 - (∑ j ∈ s, y j)
      - (((∑ j ∈ s, y j)^2 - ∑ j ∈ s, (y j)^2)/2)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using V_zero_val (p := p) (3*v)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    have key : (1 + y a) * (∏ j ∈ s, (1 + y j)) - 1 - (y a + ∑ j ∈ s, y j)
        - (((y a + ∑ j ∈ s, y j)^2 - ((y a)^2 + ∑ j ∈ s, (y j)^2))/2)
        = ((∏ j ∈ s, (1 + y j)) - 1 - (∑ j ∈ s, y j)
            - (((∑ j ∈ s, y j)^2 - ∑ j ∈ s, (y j)^2)/2))
          + y a * ((∏ j ∈ s, (1 + y j)) - 1 - ∑ j ∈ s, y j) := by ring
    rw [key]
    apply V_add (ih fun j hj => hy j (Finset.mem_insert_of_mem hj))
    have h1 := V_mul (hy a (Finset.mem_insert_self a s))
      (VP2 hv fun j hj => hy j (Finset.mem_insert_of_mem hj))
    have : v + 2*v = 3*v := by ring
    rwa [this] at h1

/-! ## Reindexing between the two coprime-filter conventions -/

theorem reindex_shift (M : ℕ) (hM : p ∣ M) (g : ℕ → ℚ) :
    ∑ k ∈ (Finset.range M).filter (fun k => ¬ p ∣ (k+1)), g (k+1)
    = ∑ j ∈ (Finset.range M).filter (fun j => ¬ p ∣ j), g j := by
  apply Finset.sum_nbij' (fun k => k + 1) (fun j => j - 1)
  · intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hk
    have h1' := Finset.mem_range.mp h1
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · -- k+1 < M since k+1 ≤ M and p ∤ k+1 but p ∣ M
      rcases Nat.lt_or_ge (k+1) M with h | h
      · exact h
      · exfalso; apply h2; have : k + 1 = M := by omega
        rw [this]; exact hM
    · exact h2
  · intro j hj
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hj
    have h1' := Finset.mem_range.mp h1
    have hj0 : j ≠ 0 := by rintro rfl; exact h2 (dvd_zero p)
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · rw [show j - 1 + 1 = j by omega]; exact h2
  · intro k hk; omega
  · intro j hj
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hj
    have hj0 : j ≠ 0 := by rintro rfl; exact h2 (dvd_zero p)
    omega
  · intro k hk; rfl

/-! ## The Kazandzidis congruences -/

/-- Gauss-type congruence, valid for every prime `p`:
if `v_p(cp) ≥ v` then `binom((b+c)p, bp)/binom(b+c,b) ≡ 1 (mod p^v)`. -/
theorem kaz_gauss {b c v : ℕ} (hvc : V p (v:ℤ) ((c:ℚ) * (p:ℚ))) :
    V p (v:ℤ) ((((b+c)*p).choose (b*p) : ℚ) / (((b+c).choose b) : ℚ) - 1) := by
  have hch : (((b+c).choose b : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show b ≤ b+c by omega)).ne'
  have hdiv : (((b+c)*p).choose (b*p) : ℚ) / (((b+c).choose b) : ℚ)
      = ∏ k ∈ (Finset.range (b*p)).filter (fun k => ¬ p ∣ (k+1)),
        (1 + ((c:ℚ) * (p:ℚ)) / ((k+1 : ℕ) : ℚ)) := by
    rw [choose_ratio_eq b c, mul_comm, mul_div_assoc, div_self hch, mul_one]
  rw [hdiv]
  apply VP1 (by positivity)
  intro k hk
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hk
  rw [div_eq_mul_inv]
  have hinv : V p 0 (((k+1 : ℕ) : ℚ))⁻¹ := by
    have := V_inv_pow_unit (p := p) 1 h2
    simpa using this
  simpa using V_mul hvc hinv

/-- Kazandzidis-type congruence for `p ≥ 5`:
if moreover `v ≤ v_p(bp)` then the ratio is `1 (mod p^{3v})`. -/
theorem kaz_strong (hp5 : 5 ≤ p) {b c v : ℕ} (hb : 1 ≤ b)
    (hvb : v ≤ padicValNat p (b*p)) (hvc : V p (v:ℤ) ((c:ℚ) * (p:ℚ))) :
    V p (3*(v:ℤ)) ((((b+c)*p).choose (b*p) : ℚ) / (((b+c).choose b) : ℚ) - 1) := by
  have hbp : b * p ≠ 0 := by
    have := hp.out.pos; positivity
  have hpbp : p ∣ b*p := Dvd.intro_left b rfl
  have hch : (((b+c).choose b : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show b ≤ b+c by omega)).ne'
  have hdiv : (((b+c)*p).choose (b*p) : ℚ) / (((b+c).choose b) : ℚ)
      = ∏ k ∈ (Finset.range (b*p)).filter (fun k => ¬ p ∣ (k+1)),
        (1 + ((c:ℚ) * (p:ℚ)) / ((k+1 : ℕ) : ℚ)) := by
    rw [choose_ratio_eq b c, mul_comm, mul_div_assoc, div_self hch, mul_one]
  rw [hdiv]
  set s := (Finset.range (b*p)).filter (fun k => ¬ p ∣ (k+1)) with hs
  set y : ℕ → ℚ := fun k => ((c:ℚ) * (p:ℚ)) / ((k+1 : ℕ) : ℚ) with hy
  have hyV : ∀ k ∈ s, V p (v:ℤ) (y k) := by
    intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hk
    rw [hy]
    simp only
    rw [div_eq_mul_inv]
    have hinv : V p 0 (((k+1 : ℕ) : ℚ))⁻¹ := by
      have := V_inv_pow_unit (p := p) 1 h2
      simpa using this
    simpa using V_mul hvc hinv
  -- the three pieces
  have hE1 : V p (3*(v:ℤ)) (∑ k ∈ s, y k) := by
    have hfac : ∑ k ∈ s, y k
        = ((c:ℚ) * (p:ℚ)) * ∑ k ∈ s, (((k+1 : ℕ) : ℚ))⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hy]
      simp only
      rw [div_eq_mul_inv]
    have hHsum : ∑ k ∈ s, (((k+1 : ℕ) : ℚ))⁻¹
        = ∑ j ∈ (Finset.range (b*p)).filter (fun j => ¬ p ∣ j), ((j : ℚ))⁻¹ := by
      rw [hs]
      exact reindex_shift (b*p) hpbp (fun j => ((j:ℚ))⁻¹)
    rw [hfac, hHsum]
    have hH := H_law (p := p) hp5 hbp
    have h1 := V_mul hvc (V_mono hH (show 2*(v:ℤ) ≤ 2*((padicValNat p (b*p)):ℤ) by
      have : (v:ℤ) ≤ (padicValNat p (b*p) : ℤ) := by exact_mod_cast hvb
      omega))
    apply V_mono h1
    omega
  have hP2y : V p (3*(v:ℤ)) (∑ k ∈ s, (y k)^2) := by
    have hfac : ∑ k ∈ s, (y k)^2
        = ((c:ℚ) * (p:ℚ))^2 * ∑ k ∈ s, ((((k+1 : ℕ) : ℚ))^2)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hy]
      simp only
      rw [div_pow, div_eq_mul_inv]
    have hPsum : ∑ k ∈ s, ((((k+1 : ℕ) : ℚ))^2)⁻¹
        = ∑ j ∈ (Finset.range (b*p)).filter (fun j => ¬ p ∣ j), (((j : ℚ))^2)⁻¹ := by
      rw [hs]
      exact reindex_shift (b*p) hpbp (fun j => (((j:ℚ))^2)⁻¹)
    rw [hfac, hPsum]
    have hP := P2_law (p := p) hp5 hbp
    have h1 := V_mul (V_pow hvc 2) (V_mono hP (show (v:ℤ) ≤ ((padicValNat p (b*p)):ℤ) by
      exact_mod_cast hvb))
    apply V_mono h1
    omega
  have hE2 : V p (3*(v:ℤ)) (((∑ k ∈ s, y k)^2 - ∑ k ∈ s, (y k)^2)/2) := by
    have h2u : ¬ p ∣ 2 := by
      intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    have hinv2 : V p 0 (((2:ℕ):ℚ))⁻¹ := by
      have := V_inv_pow_unit (p := p) 1 h2u
      simpa using this
    have hsq : V p (3*(v:ℤ)) ((∑ k ∈ s, y k)^2 - ∑ k ∈ s, (y k)^2) := by
      apply V_sub ?_ hP2y
      have h1 := V_pow hE1 2
      apply V_mono h1
      have hv0 : (0:ℤ) ≤ (v:ℤ) := by positivity
      omega
    have hinv2' : V p 0 ((2:ℚ))⁻¹ := by
      rwa [show (((2:ℕ):ℚ)) = (2:ℚ) by norm_num] at hinv2
    rw [div_eq_mul_inv]
    have h3 := V_mul hsq hinv2'
    simpa using h3
  -- assemble
  have hVP3 := VP3 (p := p) (by positivity) hyV
  have hfin : (∏ k ∈ s, (1 + y k)) - 1
      = ((∏ k ∈ s, (1 + y k)) - 1 - (∑ k ∈ s, y k)
          - (((∑ k ∈ s, y k)^2 - ∑ k ∈ s, (y k)^2)/2))
        + (∑ k ∈ s, y k) + (((∑ k ∈ s, y k)^2 - ∑ k ∈ s, (y k)^2)/2) := by
    ring
  rw [hfin]
  exact V_add (V_add hVP3 hE1) hE2

end Super

-- ===== Devel/D05.lean =====
/-! # D05: the integers `c_m(k) = (mk)!/(k!)^m` and their `p`-adic valuations -/

namespace Super

open Finset

/-! ## `c` as a natural number -/

theorem pow_factorial_dvd (m k : ℕ) :
    (Nat.factorial k)^m ∣ Nat.factorial (m*k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : Nat.factorial (m*k) * Nat.factorial k ∣ Nat.factorial (m*k + k) :=
      Nat.factorial_mul_factorial_dvd_factorial_add _ _
    calc (Nat.factorial k)^(m+1) = (Nat.factorial k)^m * Nat.factorial k := by ring
    _ ∣ Nat.factorial (m*k) * Nat.factorial k := mul_dvd_mul_right ih _
    _ ∣ Nat.factorial ((m+1)*k) := by rwa [add_mul, one_mul]

/-- `c_m(k)` as a natural number. -/
def cN (m k : ℕ) : ℕ := Nat.factorial (m*k) / (Nat.factorial k)^m

theorem cN_mul_eq (m k : ℕ) : cN m k * (Nat.factorial k)^m = Nat.factorial (m*k) :=
  Nat.div_mul_cancel (pow_factorial_dvd m k)

theorem cN_pos (m k : ℕ) : 0 < cN m k := by
  rcases Nat.eq_zero_or_pos (cN m k) with h | h
  · exfalso
    have := cN_mul_eq m k
    rw [h, zero_mul] at this
    exact (Nat.factorial_ne_zero (m*k)) this.symm
  · exact h

/-- `c_m(k)` as a rational. -/
def cQ (m k : ℕ) : ℚ := ((Nat.factorial (m*k) : ℚ)) / ((Nat.factorial k : ℚ))^m

theorem cQ_eq_cast (m k : ℕ) : cQ m k = ((cN m k : ℕ) : ℚ) := by
  rw [cQ, eq_comm, eq_div_iff (by positivity)]
  exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) (cN_mul_eq m k)

/-- Product formula: `c_m(J) = ∏_{i=1}^{m-1} C((i+1)J, J)`. -/
theorem cQ_prod (m J : ℕ) :
    cQ m J = ∏ i ∈ Finset.Ico 1 m, ((((i+1)*J).choose J : ℕ) : ℚ) := by
  induction m with
  | zero => simp [cQ]
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [cQ, Nat.factorial_ne_zero]
    rw [Finset.prod_Ico_succ_top (a := 1) (b := m) (by omega), ← ih]
    have hch : (((m+1)*J).choose J) * Nat.factorial J * Nat.factorial (m*J)
        = Nat.factorial ((m+1)*J) := by
      have h := Nat.choose_mul_factorial_mul_factorial
        (show J ≤ (m+1)*J by nlinarith)
      rwa [show (m+1)*J - J = m*J by rw [add_mul, one_mul, Nat.add_sub_cancel]] at h
    rw [cQ, cQ]
    have hJ : ((Nat.factorial J : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero J
    have hmJ : ((Nat.factorial (m*J) : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (m*J)
    have hchQ : ((((m+1)*J).choose J : ℕ) : ℚ) * (Nat.factorial J : ℚ)
        * (Nat.factorial (m*J) : ℚ) = (Nat.factorial ((m+1)*J) : ℚ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) hch
    rw [← hchQ]
    field_simp
    ring

/-! ## Valuations -/

variable {p : ℕ} [hp : Fact p.Prime]

/-- `v_p(c_m(k))`. -/
def vc (p m k : ℕ) : ℕ := padicValNat p (cN m k)

theorem V_cQ (m k : ℕ) : V p ((vc p m k : ℤ)) (cQ m k) := by
  rw [cQ_eq_cast]
  exact V_padicValNat (cN_pos m k).ne'

theorem vc_add_eq (m k : ℕ) :
    vc p m k + m * padicValNat p (Nat.factorial k)
      = padicValNat p (Nat.factorial (m*k)) := by
  have h := congrArg (padicValNat p) (cN_mul_eq m k)
  rwa [padicValNat.mul (cN_pos m k).ne' (pow_ne_zero _ (Nat.factorial_ne_zero k)),
    padicValNat.pow _ (Nat.factorial_ne_zero k)] at h

/-- The digit-carry quantity at level `s`. -/
theorem dig_le (m k s : ℕ) : m * (k / p^s) ≤ (m*k) / p^s := by
  rw [Nat.le_div_iff_mul_le (pow_pos hp.out.pos s)]
  calc m * (k / p^s) * p^s = m * ((k/p^s) * p^s) := by ring
  _ ≤ m * k := Nat.mul_le_mul_left m (Nat.div_mul_le_self k _)

/-- Legendre: `v_p(c_m(k)) = ∑_{s ∈ Ico 1 b} ((mk)/p^s - m(k/p^s))` for large `b`. -/
theorem vc_eq_sum (m k : ℕ) {b : ℕ} (hb : Nat.log p (m*k) < b) :
    vc p m k = ∑ s ∈ Finset.Ico 1 b, ((m*k) / p^s - m * (k / p^s)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [vc, cN]
  have hbk : Nat.log p k < b := by
    calc Nat.log p k ≤ Nat.log p (m*k) := Nat.log_mono_right (Nat.le_mul_of_pos_left k hm)
    _ < b := hb
  have h1 := padicValNat_factorial (p := p) hb
  have h2 := padicValNat_factorial (p := p) hbk
  have h3 := vc_add_eq (p := p) m k
  rw [h1, h2] at h3
  have h4 : m * ∑ s ∈ Finset.Ico 1 b, k / p ^ s
      = ∑ s ∈ Finset.Ico 1 b, m * (k / p ^ s) := Finset.mul_sum _ _ _
  rw [h4] at h3
  have h5 : ∑ s ∈ Finset.Ico 1 b, (m*k) / p^s
      = ∑ s ∈ Finset.Ico 1 b, (((m*k) / p^s - m * (k / p^s)) + m * (k / p^s)) := by
    apply Finset.sum_congr rfl
    intro s _
    have := dig_le (p := p) m k s
    omega
  rw [h5, Finset.sum_add_distrib] at h3
  omega

/-- Partial-sum lower bound for `v_p(c_m(k))`. -/
theorem vc_ge (m k R : ℕ) :
    ∑ s ∈ Finset.Icc 1 R, ((m*k) / p^s - m * (k / p^s)) ≤ vc p m k := by
  set b := max (R+1) (Nat.log p (m*k) + 1) with hbdef
  have hb : Nat.log p (m*k) < b := by omega
  rw [vc_eq_sum (p := p) m k hb]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_Ico]
    omega
  · intro i _ _
    omega

/-- `v_p(c_m(pJ)) = v_p(c_m(J))`. -/
theorem vc_p_mul (m J : ℕ) : vc p m (p*J) = vc p m J := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [vc, cN]
  have h1 := vc_add_eq (p := p) m (p*J)
  have h2 := vc_add_eq (p := p) m J
  have h3 : padicValNat p (Nat.factorial (m*(p*J)))
      = padicValNat p (Nat.factorial (m*J)) + m*J := by
    rw [show m*(p*J) = p*(m*J) by ring]
    exact padicValNat_factorial_mul (m*J)
  have h4 : padicValNat p (Nat.factorial (p*J))
      = padicValNat p (Nat.factorial J) + J := padicValNat_factorial_mul J
  have h5 : m * padicValNat p (Nat.factorial (p*J))
      = m * padicValNat p (Nat.factorial J) + m*J := by
    rw [h4]; ring
  omega

/-- For `p ≥ 5` and `ℓ ≥ 1`: `4·v_p(ℓ!) + 1 ≤ ℓ`. -/
theorem factorial_val_bound (hp5 : 5 ≤ p) {ℓ : ℕ} (hl : 1 ≤ ℓ) :
    4 * padicValNat p (Nat.factorial ℓ) + 1 ≤ ℓ := by
  have h := sub_one_mul_padicValNat_factorial (p := p) ℓ
  have hS : 1 ≤ (p.digits ℓ).sum := by
    by_contra hS
    push_neg at hS
    have hS0 : (p.digits ℓ).sum = 0 := by omega
    have hgen : ∀ (L : List ℕ), L.sum = 0 → Nat.ofDigits p L = 0 := by
      intro L
      induction L with
      | nil => intro _; simp [Nat.ofDigits]
      | cons a L ih =>
        intro hL
        rw [List.sum_cons] at hL
        rw [Nat.ofDigits_cons, ih (by omega), show a = 0 by omega]
        simp
    have := Nat.ofDigits_digits p ℓ
    have hz := hgen _ hS0
    omega
  have hsum_le : (p.digits ℓ).sum ≤ ℓ := Nat.digit_sum_le p ℓ
  have h4 : 4 * padicValNat p (Nat.factorial ℓ) ≤ (p-1) * padicValNat p (Nat.factorial ℓ) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-! ## Per-level carry analysis for tuples -/

theorem dig_mod (m k S : ℕ) :
    (m * k)/p^S - m*(k/p^S) = (m * (k % p^S)) / p^S := by
  have hP : 0 < p^S := pow_pos hp.out.pos S
  have h1 : m*k = p^S * (m*(k/p^S)) + m*(k % p^S) := by
    conv_lhs => rw [show k = p^S * (k/p^S) + k % p^S from (Nat.div_add_mod k (p^S)).symm]
    ring
  have h2 : (m*k)/p^S = m*(k/p^S) + (m*(k % p^S))/p^S := by
    conv_lhs => rw [h1]
    rw [Nat.mul_add_div hP]
  rw [h2, Nat.add_sub_cancel_left]

theorem level_card_ne_one {S : ℕ} {s : Finset ℕ} {d : ℕ → ℕ}
    (hdvd : p^S ∣ ∑ t ∈ s, d t) :
    (s.filter (fun t => ¬ p^S ∣ d t)).card ≠ 1 := by
  classical
  intro hcard
  obtain ⟨t₀, ht₀⟩ := Finset.card_eq_one.mp hcard
  have ht₀mem : t₀ ∈ s ∧ ¬ p^S ∣ d t₀ := by
    have h : t₀ ∈ s.filter (fun t => ¬ p^S ∣ d t) := by
      rw [ht₀]; exact Finset.mem_singleton_self t₀
    exact Finset.mem_filter.mp h
  have hrest : p^S ∣ ∑ t ∈ s.erase t₀, d t := by
    apply Finset.dvd_sum
    intro t ht
    have hts : t ∈ s := Finset.mem_of_mem_erase ht
    have htne : t ≠ t₀ := Finset.ne_of_mem_erase ht
    by_contra hnd
    have h : t ∈ s.filter (fun t => ¬ p^S ∣ d t) := Finset.mem_filter.mpr ⟨hts, hnd⟩
    rw [ht₀] at h
    exact htne (Finset.mem_singleton.mp h)
  have hsum : ∑ t ∈ s, d t = d t₀ + ∑ t ∈ s.erase t₀, d t :=
    (Finset.add_sum_erase s d ht₀mem.1).symm
  apply ht₀mem.2
  rw [hsum] at hdvd
  have h := Nat.dvd_sub hdvd hrest
  rwa [Nat.add_sub_cancel] at h

theorem level_bound {S : ℕ} {s : Finset ℕ} {d : ℕ → ℕ} (m : ℕ)
    (hdvd : p^S ∣ ∑ t ∈ s, d t)
    (hL : 1 ≤ (s.filter (fun t => ¬ p^S ∣ d t)).card) :
    m + 1 ≤ (s.filter (fun t => ¬ p^S ∣ d t)).card
      + ∑ t ∈ s, ((m * d t)/p^S - m*(d t/p^S)) := by
  classical
  set P := p^S with hPdef
  have hP : 0 < P := pow_pos hp.out.pos S
  set u : ℕ → ℕ := fun t => d t % P with hu
  set L : ℕ := (s.filter (fun t => ¬ P ∣ d t)).card with hLdef
  have hu0 : ∀ t, P ∣ d t ↔ u t = 0 := by
    intro t
    rw [hu]
    exact ⟨fun h => Nat.mod_eq_zero_of_dvd h, fun h => Nat.dvd_of_mod_eq_zero h⟩
  have hsumu : P ∣ ∑ t ∈ s, u t := by
    have h1 : ∑ t ∈ s, d t = P * (∑ t ∈ s, d t / P) + ∑ t ∈ s, u t := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => (Nat.div_add_mod (d t) P).symm
    have h2 : P ∣ P * (∑ t ∈ s, d t / P) := Dvd.intro _ rfl
    rw [h1] at hdvd
    have h := Nat.dvd_sub hdvd h2
    rwa [Nat.add_sub_cancel_left] at h
  have hpos : 0 < ∑ t ∈ s, u t := by
    have hne : (s.filter (fun t => ¬ P ∣ d t)).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨t₁, ht₁⟩ := hne
    obtain ⟨ht₁s, ht₁d⟩ := Finset.mem_filter.mp ht₁
    apply Finset.sum_pos'
    · intro t _; omega
    · exact ⟨t₁, ht₁s, by
        have : u t₁ ≠ 0 := fun h => ht₁d ((hu0 t₁).mpr h)
        omega⟩
  have hκ : P ≤ ∑ t ∈ s, u t := Nat.le_of_dvd hpos hsumu
  have hT : ∑ t ∈ s, m * u t = P * (∑ t ∈ s, (m * u t)/P) + ∑ t ∈ s, (m * u t) % P := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => (Nat.div_add_mod _ _).symm
  have hTdvd : P ∣ ∑ t ∈ s, m * u t := by
    rw [show ∑ t ∈ s, m * u t = m * ∑ t ∈ s, u t from (Finset.mul_sum _ _ _).symm]
    exact Dvd.dvd.mul_left hsumu m
  have hRdvd : P ∣ ∑ t ∈ s, (m * u t) % P := by
    have h2 : P ∣ P * (∑ t ∈ s, (m*u t)/P) := Dvd.intro _ rfl
    rw [hT] at hTdvd
    have h := Nat.dvd_sub hTdvd h2
    rwa [Nat.add_sub_cancel_left] at h
  have hRle : ∑ t ∈ s, (m * u t) % P ≤ L * (P - 1) := by
    calc ∑ t ∈ s, (m * u t) % P
        = ∑ t ∈ s.filter (fun t => ¬ P ∣ d t), (m * u t) % P := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro t ht htn
          have hdt : P ∣ d t := by
            by_contra h; exact htn (Finset.mem_filter.mpr ⟨ht, h⟩)
          rw [(hu0 t).mp hdt]
          simp
      _ ≤ ∑ _t ∈ s.filter (fun t => ¬ P ∣ d t), (P - 1) := by
          apply Finset.sum_le_sum
          intro t _
          have := Nat.mod_lt (m * u t) hP
          omega
      _ = L * (P-1) := by rw [Finset.sum_const, smul_eq_mul]
  obtain ⟨τ, hτ⟩ := hRdvd
  have hτle : τ + 1 ≤ L := by
    by_contra hτ'
    push_neg at hτ'
    have h1 : L * P ≤ τ * P := Nat.mul_le_mul_right P (by omega)
    have h2 : L * P = L * (P-1) + L := by
      conv_lhs => rw [show P = (P-1) + 1 by omega]
      ring
    rw [hτ] at hRle
    have h3 : P * τ = τ * P := by ring
    omega
  have hQκ : m ≤ (∑ t ∈ s, (m * u t)/P) + τ := by
    have h1 : m * P ≤ m * ∑ t ∈ s, u t := Nat.mul_le_mul_left m hκ
    have h2 : ∑ t ∈ s, m * u t = m * ∑ t ∈ s, u t := (Finset.mul_sum _ _ _).symm
    have h3 : P * ((∑ t ∈ s, (m * u t)/P) + τ) = m * ∑ t ∈ s, u t := by
      rw [Nat.mul_add, ← hτ, ← hT, h2]
    have h4 : P * m ≤ P * ((∑ t ∈ s, (m * u t)/P) + τ) := by
      rw [h3]
      calc P * m = m * P := by ring
      _ ≤ m * ∑ t ∈ s, u t := h1
    exact Nat.le_of_mul_le_mul_left h4 hP
  have hdigsum : ∑ t ∈ s, ((m * d t)/P - m*(d t/P)) = ∑ t ∈ s, (m * u t)/P :=
    Finset.sum_congr rfl fun t _ => dig_mod m (d t) S
  rw [hdigsum]
  omega

theorem count_levels {R : ℕ} {s : Finset ℕ} {d : ℕ → ℕ}
    (h0 : ∀ t ∈ s, d t ≠ 0) (hnd : ∀ t ∈ s, ¬ p^R ∣ d t) :
    ∑ t ∈ s, (R - padicValNat p (d t))
      = ∑ S ∈ Finset.Icc 1 R, (s.filter (fun t => ¬ p^S ∣ d t)).card := by
  classical
  have hswap : ∑ S ∈ Finset.Icc 1 R, (s.filter (fun t => ¬ p^S ∣ d t)).card
      = ∑ t ∈ s, ∑ S ∈ Finset.Icc 1 R, (if ¬ p^S ∣ d t then 1 else 0) := by
    rw [← Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S _
    rw [Finset.card_filter]
  rw [hswap]
  apply Finset.sum_congr rfl
  intro t ht
  set a := padicValNat p (d t) with ha
  have hdvd_iff : ∀ S, p^S ∣ d t ↔ S ≤ a := fun S => padicValNat_dvd_iff_le (h0 t ht)
  have haR : a < R := by
    by_contra h
    push_neg at h
    exact hnd t ht ((hdvd_iff R).mpr h)
  have h2 : (Finset.Icc 1 R).filter (fun S => ¬ p^S ∣ d t) = Finset.Icc (a+1) R := by
    ext S
    rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc, hdvd_iff S]
    omega
  rw [← Finset.card_filter, h2, Nat.card_Icc]
  omega

/-! ## The two master tuple inequalities -/

/-- The F-inequality: tuples with at least two parts coprime to `p`. -/
theorem F_ineq (hp5 : 5 ≤ p) {m : ℕ} (hm : 3 ≤ m) {r : ℕ} (hr : 1 ≤ r)
    {s : Finset ℕ} {d : ℕ → ℕ}
    (h0 : ∀ t ∈ s, d t ≠ 0) (hnd : ∀ t ∈ s, ¬ p^r ∣ d t)
    (hsum : p^r ∣ ∑ t ∈ s, d t)
    (hcop : 2 ≤ (s.filter (fun t => ¬ p ∣ d t)).card) :
    3*r + padicValNat p (Nat.factorial s.card)
      ≤ (∑ t ∈ s, (r - padicValNat p (d t))) + ∑ t ∈ s, vc p m (d t) := by
  classical
  set ℓ := s.card with hℓ
  -- each level S ∈ [1,r] has ℓ'_S ≥ 2
  have hlev1 : ∀ S, 1 ≤ S →
      2 ≤ (s.filter (fun t => ¬ p^S ∣ d t)).card := by
    intro S hS
    calc 2 ≤ (s.filter (fun t => ¬ p ∣ d t)).card := hcop
    _ ≤ (s.filter (fun t => ¬ p^S ∣ d t)).card := by
        apply Finset.card_le_card
        intro t ht
        obtain ⟨hts, htd⟩ := Finset.mem_filter.mp ht
        exact Finset.mem_filter.mpr ⟨hts, fun hdt =>
          htd (dvd_trans (dvd_pow_self p (by omega : S ≠ 0)) hdt)⟩
  -- vc part: Σ_t vc ≥ Σ_S δ_S
  have hvc : ∑ S ∈ Finset.Icc 1 r, ∑ t ∈ s, ((m * d t)/p^S - m*(d t/p^S))
      ≤ ∑ t ∈ s, vc p m (d t) := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro t _
    exact vc_ge m (d t) r
  -- counting part
  have hcount := count_levels (p := p) h0 hnd
  -- per-level bounds
  have hdvdS : ∀ S ∈ Finset.Icc 1 r, p^S ∣ ∑ t ∈ s, d t := by
    intro S hS
    rw [Finset.mem_Icc] at hS
    exact dvd_trans (pow_dvd_pow p hS.2) hsum
  have hlev : ∀ S ∈ Finset.Icc 1 r, m + 1 ≤
      (s.filter (fun t => ¬ p^S ∣ d t)).card
        + ∑ t ∈ s, ((m * d t)/p^S - m*(d t/p^S)) := by
    intro S hS
    rw [Finset.mem_Icc] at hS
    exact level_bound m (hdvdS S (Finset.mem_Icc.mpr hS)) (by
      have := hlev1 S hS.1; omega)
  -- the top level S = r also has ℓ'_r = ℓ
  have htop : (s.filter (fun t => ¬ p^r ∣ d t)).card = ℓ := by
    rw [hℓ]
    congr 1
    apply Finset.filter_true_of_mem
    intro t ht
    exact hnd t ht
  -- combine
  have hsplit : Finset.Icc 1 r = insert r (Finset.Icc 1 (r-1)) := by
    ext S
    rw [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Icc]
    omega
  have hmain : (r-1)*(m+1) + max ℓ (m+1)
      ≤ ∑ S ∈ Finset.Icc 1 r, ((s.filter (fun t => ¬ p^S ∣ d t)).card
        + ∑ t ∈ s, ((m * d t)/p^S - m*(d t/p^S))) := by
    rw [hsplit, Finset.sum_insert (by rw [Finset.mem_Icc]; omega)]
    have hbot : (r-1)*(m+1) ≤ ∑ S ∈ Finset.Icc 1 (r-1),
        ((s.filter (fun t => ¬ p^S ∣ d t)).card
          + ∑ t ∈ s, ((m * d t)/p^S - m*(d t/p^S))) := by
      calc (r-1)*(m+1) = ∑ _S ∈ Finset.Icc 1 (r-1), (m+1) := by
            have hcard : (Finset.Icc 1 (r-1)).card = r-1 := by rw [Nat.card_Icc]; omega
            rw [Finset.sum_const, hcard, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun S hS => hlev S (by
            rw [Finset.mem_Icc] at hS ⊢; omega)
    have htopb : max ℓ (m+1) ≤ (s.filter (fun t => ¬ p^r ∣ d t)).card
        + ∑ t ∈ s, ((m * d t)/p^r - m*(d t/p^r)) := by
      apply max_le
      · rw [htop]; omega
      · exact hlev r (by rw [Finset.mem_Icc]; omega)
    omega
  have hsum_split : ∑ S ∈ Finset.Icc 1 r, ((s.filter (fun t => ¬ p^S ∣ d t)).card
      + ∑ t ∈ s, ((m * d t)/p^S - m*(d t/p^S)))
      = (∑ S ∈ Finset.Icc 1 r, (s.filter (fun t => ¬ p^S ∣ d t)).card)
        + ∑ S ∈ Finset.Icc 1 r, ∑ t ∈ s, ((m * d t)/p^S - m*(d t/p^S)) :=
    Finset.sum_add_distrib
  -- final arithmetic
  have hfac : 4 * padicValNat p (Nat.factorial ℓ) + 1 ≤ ℓ ∨ ℓ = 0 := by
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · right; exact h
    · left; exact factorial_val_bound hp5 h
  have hfac0 : ℓ = 0 → padicValNat p (Nat.factorial ℓ) = 0 := by
    intro h; rw [h]; simp [Nat.factorial]
  have hmul : 4*(r-1) ≤ (r-1)*(m+1) := by
    calc 4*(r-1) = (r-1)*4 := by ring
    _ ≤ (r-1)*(m+1) := Nat.mul_le_mul_left _ (by omega)
  have hmax1 : ℓ ≤ max ℓ (m+1) := le_max_left _ _
  have hmax2 : m+1 ≤ max ℓ (m+1) := le_max_right _ _
  omega

/-- The K-inequality: tuples at level `r-1` with a distinguished slot carrying
the Kazandzidis bonus `3(1 + v_p(d t₀))`. -/
theorem K_ineq (hp5 : 5 ≤ p) {m : ℕ} (hm : 3 ≤ m) {r' : ℕ} (hr' : 1 ≤ r')
    {s : Finset ℕ} {d : ℕ → ℕ}
    (h0 : ∀ t ∈ s, d t ≠ 0) (hnd : ∀ t ∈ s, ¬ p^r' ∣ d t)
    (hsum : p^r' ∣ ∑ t ∈ s, d t)
    {t₀ : ℕ} (ht₀ : t₀ ∈ s) :
    3*(r'+1) + padicValNat p (Nat.factorial s.card)
      ≤ (∑ t ∈ s, (r' - padicValNat p (d t))) + (∑ t ∈ s, vc p m (d t))
        + (3 + 3 * padicValNat p (d t₀)) := by
  classical
  set ℓ := s.card with hℓ
  set a₀ := padicValNat p (d t₀) with ha₀
  have ha₀r : a₀ < r' := by
    by_contra h
    push_neg at h
    exact hnd t₀ ht₀ ((padicValNat_dvd_iff_le (h0 t₀ ht₀)).mpr h)
  -- levels S ∈ [a₀+1, r'] have ℓ'_S ≥ 1 (witness t₀), hence ≥ 2
  have hlev1 : ∀ S, a₀ + 1 ≤ S →
      1 ≤ (s.filter (fun t => ¬ p^S ∣ d t)).card := by
    intro S hS
    apply Finset.card_pos.mpr
    refine ⟨t₀, Finset.mem_filter.mpr ⟨ht₀, ?_⟩⟩
    rw [padicValNat_dvd_iff_le (h0 t₀ ht₀)]
    omega
  have hvc : ∑ S ∈ Finset.Icc (a₀+1) r', ∑ t ∈ s, ((m * d t)/p^S - m*(d t/p^S))
      ≤ ∑ t ∈ s, vc p m (d t) := by
    calc ∑ S ∈ Finset.Icc (a₀+1) r', ∑ t ∈ s, ((m * d t)/p^S - m*(d t/p^S))
        ≤ ∑ S ∈ Finset.Icc 1 r', ∑ t ∈ s, ((m * d t)/p^S - m*(d t/p^S)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro S hS
            rw [Finset.mem_Icc] at hS ⊢
            omega
          · intro i _ _
            positivity
      _ ≤ ∑ t ∈ s, vc p m (d t) := by
          rw [Finset.sum_comm]
          apply Finset.sum_le_sum
          intro t _
          exact vc_ge m (d t) r'
  have hcount := count_levels (p := p) h0 hnd
  have hcount_ge : ∑ S ∈ Finset.Icc (a₀+1) r', (s.filter (fun t => ¬ p^S ∣ d t)).card
      ≤ ∑ t ∈ s, (r' - padicValNat p (d t)) := by
    rw [hcount]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro S hS
      rw [Finset.mem_Icc] at hS ⊢
      omega
    · intro i _ _
      positivity
  have hdvdS : ∀ S ∈ Finset.Icc (a₀+1) r', p^S ∣ ∑ t ∈ s, d t := by
    intro S hS
    rw [Finset.mem_Icc] at hS
    exact dvd_trans (pow_dvd_pow p hS.2) hsum
  have hlev : ∀ S ∈ Finset.Icc (a₀+1) r', m + 1 ≤
      (s.filter (fun t => ¬ p^S ∣ d t)).card
        + ∑ t ∈ s, ((m * d t)/p^S - m*(d t/p^S)) := by
    intro S hS
    have hS' := Finset.mem_Icc.mp hS
    exact level_bound m (hdvdS S hS) (hlev1 S hS'.1)
  have htop : (s.filter (fun t => ¬ p^r' ∣ d t)).card = ℓ := by
    rw [hℓ]
    congr 1
    apply Finset.filter_true_of_mem
    intro t ht
    exact hnd t ht
  have hsplit : Finset.Icc (a₀+1) r' = insert r' (Finset.Icc (a₀+1) (r'-1)) := by
    ext S
    rw [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Icc]
    omega
  have hmain : (r'-1-a₀)*(m+1) + max ℓ (m+1)
      ≤ ∑ S ∈ Finset.Icc (a₀+1) r', ((s.filter (fun t => ¬ p^S ∣ d t)).card
        + ∑ t ∈ s, ((m * d t)/p^S - m*(d t/p^S))) := by
    rw [hsplit, Finset.sum_insert (by rw [Finset.mem_Icc]; omega)]
    have hbot : (r'-1-a₀)*(m+1) ≤ ∑ S ∈ Finset.Icc (a₀+1) (r'-1),
        ((s.filter (fun t => ¬ p^S ∣ d t)).card
          + ∑ t ∈ s, ((m * d t)/p^S - m*(d t/p^S))) := by
      calc (r'-1-a₀)*(m+1) = ∑ _S ∈ Finset.Icc (a₀+1) (r'-1), (m+1) := by
            have hcard : (Finset.Icc (a₀+1) (r'-1)).card = r'-1-a₀ := by
              rw [Nat.card_Icc]; omega
            rw [Finset.sum_const, hcard, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun S hS => hlev S (by
            rw [Finset.mem_Icc] at hS ⊢; omega)
    have htopb : max ℓ (m+1) ≤ (s.filter (fun t => ¬ p^r' ∣ d t)).card
        + ∑ t ∈ s, ((m * d t)/p^r' - m*(d t/p^r')) := by
      apply max_le
      · rw [htop]; omega
      · exact hlev r' (by rw [Finset.mem_Icc]; omega)
    omega
  have hsum_split : ∑ S ∈ Finset.Icc (a₀+1) r', ((s.filter (fun t => ¬ p^S ∣ d t)).card
      + ∑ t ∈ s, ((m * d t)/p^S - m*(d t/p^S)))
      = (∑ S ∈ Finset.Icc (a₀+1) r', (s.filter (fun t => ¬ p^S ∣ d t)).card)
        + ∑ S ∈ Finset.Icc (a₀+1) r', ∑ t ∈ s, ((m * d t)/p^S - m*(d t/p^S)) :=
    Finset.sum_add_distrib
  have hfac : 4 * padicValNat p (Nat.factorial ℓ) + 1 ≤ ℓ ∨ ℓ = 0 := by
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · right; exact h
    · left; exact factorial_val_bound hp5 h
  have hfac0 : ℓ = 0 → padicValNat p (Nat.factorial ℓ) = 0 := by
    intro h; rw [h]; simp [Nat.factorial]
  have hmul : 4*(r'-1-a₀) ≤ (r'-1-a₀)*(m+1) := by
    calc 4*(r'-1-a₀) = (r'-1-a₀)*4 := by ring
    _ ≤ (r'-1-a₀)*(m+1) := Nat.mul_le_mul_left _ (by omega)
  have hmax1 : ℓ ≤ max ℓ (m+1) := le_max_left _ _
  have hmax2 : m+1 ≤ max ℓ (m+1) := le_max_right _ _
  omega

/-! ## The Kazandzidis relation for `c_m` -/

theorem cQ_ne_zero (m J : ℕ) : cQ m J ≠ 0 := by
  rw [cQ_eq_cast]
  exact_mod_cast (cN_pos m J).ne'

theorem cQ_pJ_over (m J : ℕ) :
    cQ m (p*J) = cQ m J * ∏ i ∈ Finset.Ico 1 m,
      ((((J + i*J)*p).choose (J*p) : ℚ) / (((J + i*J).choose J : ℚ))) := by
  rw [cQ_prod m (p*J), cQ_prod m J, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
  have hch : (((J + i*J).choose J : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show J ≤ J + i*J by omega)).ne'
  have he1 : (i+1)*(p*J) = (J + i*J)*p := by ring
  have he2 : p*J = J*p := by ring
  have he3 : (i+1)*J = J + i*J := by ring
  rw [he1, he2, he3, mul_comm ((((J + i*J).choose J : ℕ)) : ℚ), div_mul_cancel₀ _ hch]

theorem rel_strong (hp5 : 5 ≤ p) (m J : ℕ) (hJ : J ≠ 0) :
    V p ((vc p m J : ℤ) + (3 + 3*(padicValNat p J : ℤ)))
      (cQ m (p*J) - cQ m J) := by
  set κ := padicValNat p J with hκ
  set y : ℕ → ℚ := fun i =>
    (((J + i*J)*p).choose (J*p) : ℚ) / (((J + i*J).choose J : ℚ)) - 1 with hy
  have hyV : ∀ i ∈ Finset.Ico 1 m, V p ((3*(κ+1) : ℕ) : ℤ) (y i) := by
    intro i hi
    have hvb : κ+1 ≤ padicValNat p (J*p) := by
      rw [padicValNat.mul hJ hp.out.ne_zero, padicValNat.self hp.out.one_lt]
    have hvc : V p ((κ+1 : ℕ) : ℤ) (((i*J : ℕ):ℚ) * (p:ℚ)) := by
      have hc : ((i*J : ℕ):ℚ) * (p:ℚ) = ((i*J*p : ℕ) : ℚ) := by push_cast; ring
      rw [hc, V_nat_iff_dvd]
      have h1 : p^κ ∣ J := pow_padicValNat_dvd
      have h2 : p^(κ+1) ∣ J*p := by
        rw [pow_succ]
        exact mul_dvd_mul h1 dvd_rfl
      have h3 : J*p ∣ i*J*p := ⟨i, by ring⟩
      exact dvd_trans h2 h3
    have h := kaz_strong (p := p) hp5 (b := J) (c := i*J) (v := κ+1)
      (by omega) hvb hvc
    rw [hy]
    simp only
    have hexp : (3*((κ+1 : ℕ)):ℤ) = ((3*(κ+1) : ℕ) : ℤ) := by push_cast; ring
    rw [← hexp]
    exact h
  have hprod : cQ m (p*J) - cQ m J
      = cQ m J * ((∏ i ∈ Finset.Ico 1 m, (1 + y i)) - 1) := by
    have h1 : ∀ i ∈ Finset.Ico 1 m, (1 : ℚ) + y i
        = (((J + i*J)*p).choose (J*p) : ℚ) / (((J + i*J).choose J : ℚ)) := by
      intro i _
      rw [hy]
      ring
    rw [mul_sub, mul_one, Finset.prod_congr rfl h1, ← cQ_pJ_over m J]
  rw [hprod]
  have h1 := V_mul (V_cQ (p := p) m J) (VP1 (by positivity) hyV)
  apply V_mono h1
  push_cast
  omega

theorem rel_gauss (m J : ℕ) (hJ : J ≠ 0) :
    V p ((vc p m J : ℤ) + (1 + (padicValNat p J : ℤ)))
      (cQ m (p*J) - cQ m J) := by
  set κ := padicValNat p J with hκ
  set y : ℕ → ℚ := fun i =>
    (((J + i*J)*p).choose (J*p) : ℚ) / (((J + i*J).choose J : ℚ)) - 1 with hy
  have hyV : ∀ i ∈ Finset.Ico 1 m, V p ((κ+1 : ℕ) : ℤ) (y i) := by
    intro i hi
    have hvc : V p ((κ+1 : ℕ) : ℤ) (((i*J : ℕ):ℚ) * (p:ℚ)) := by
      have hc : ((i*J : ℕ):ℚ) * (p:ℚ) = ((i*J*p : ℕ) : ℚ) := by push_cast; ring
      rw [hc, V_nat_iff_dvd]
      have h1 : p^κ ∣ J := pow_padicValNat_dvd
      have h2 : p^(κ+1) ∣ J*p := by
        rw [pow_succ]
        exact mul_dvd_mul h1 dvd_rfl
      have h3 : J*p ∣ i*J*p := ⟨i, by ring⟩
      exact dvd_trans h2 h3
    have h := kaz_gauss (p := p) (b := J) (c := i*J) (v := κ+1) hvc
    rw [hy]
    simp only
    exact h
  have hprod : cQ m (p*J) - cQ m J
      = cQ m J * ((∏ i ∈ Finset.Ico 1 m, (1 + y i)) - 1) := by
    have h1 : ∀ i ∈ Finset.Ico 1 m, (1 : ℚ) + y i
        = (((J + i*J)*p).choose (J*p) : ℚ) / (((J + i*J).choose J : ℚ)) := by
      intro i _
      rw [hy]
      ring
    rw [mul_sub, mul_one, Finset.prod_congr rfl h1, ← cQ_pJ_over m J]
  rw [hprod]
  have h1 := V_mul (V_cQ (p := p) m J) (VP1 (by positivity) hyV)
  apply V_mono h1
  push_cast
  omega

end Super

-- ===== Devel/D06.lean =====
namespace Super

open Finset PowerSeries

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## Coefficient-wise valuation bounds -/

theorem V_coeff_mul {c d : ℤ} {G H : ℚ⟦X⟧} (hG : ∀ j, V p c (coeff j G))
    (hH : ∀ j, V p d (coeff j H)) (j : ℕ) : V p (c + d) (coeff j (G * H)) := by
  rw [coeff_mul]
  apply V_sum
  intro x hx
  exact V_mul (hG x.1) (hH x.2)

theorem V_coeff_one {j : ℕ} : V p 0 (coeff j (1 : ℚ⟦X⟧)) := by
  rcases eq_or_ne j 0 with rfl | hj
  · simpa [coeff_zero_eq_constantCoeff] using V_one (p := p)
  · rw [coeff_one, if_neg hj]
    exact V_zero_val _

theorem V_coeff_pow {c : ℤ} {Φ : ℚ⟦X⟧} (hΦ : ∀ j, V p c (coeff j Φ)) (ℓ : ℕ) (j : ℕ) :
    V p (ℓ * c) (coeff j (Φ ^ ℓ)) := by
  induction ℓ generalizing j with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact V_coeff_one
  | succ ℓ ih =>
    rw [pow_succ]
    have h := V_coeff_mul (c := (ℓ : ℤ) * c) (d := c) (fun i => ih i) hΦ j
    have harith : ((ℓ+1 : ℕ) : ℤ) * c = (ℓ : ℕ) * c + c := by push_cast; ring
    rw [harith]
    exact h

/-- valuation of factorial is at most `ℓ - 1`. -/
theorem padicValNat_factorial_le {ℓ : ℕ} (hl : 1 ≤ ℓ) :
    padicValNat p ℓ.factorial ≤ ℓ - 1 := by
  have h := sub_one_mul_padicValNat_factorial (p := p) ℓ
  have hS : 1 ≤ (p.digits ℓ).sum := by
    by_contra hS
    push_neg at hS
    have hS0 : (p.digits ℓ).sum = 0 := by omega
    have hgen : ∀ (L : List ℕ), L.sum = 0 → Nat.ofDigits p L = 0 := by
      intro L
      induction L with
      | nil => intro _; simp [Nat.ofDigits]
      | cons a L ih =>
        intro hL
        rw [List.sum_cons] at hL
        rw [Nat.ofDigits_cons, ih (by omega), show a = 0 by omega]
        simp
    have := Nat.ofDigits_digits p ℓ
    have hz := hgen _ hS0
    omega
  have h2 : 2 ≤ p := hp.out.two_le
  have h3 : padicValNat p ℓ.factorial ≤ (p-1) * padicValNat p ℓ.factorial :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- Tail coefficients of the exponential of a series all of whose coefficients have
valuation at least `c ≥ 1` again have valuation at least `c`. -/
theorem exp_tail {c : ℤ} (hc : 1 ≤ c) {Φ : ℚ⟦X⟧} (hΦ0 : constantCoeff Φ = 0)
    (hΦ : ∀ j, V p c (coeff j Φ)) {j : ℕ} (hj : j ≠ 0) : V p c (coeff j (expS Φ)) := by
  rw [coeff_expS Φ hΦ0 j]
  apply V_sum
  intro ℓ hℓ
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ1
  · rw [pow_zero, coeff_one, if_neg hj, mul_zero]
    exact V_zero_val _
  · have h1 : V p (-(padicValNat p ℓ.factorial : ℤ)) ((ℓ.factorial : ℚ))⁻¹ := by
      have := V_inv_nat (p := p) (n := ℓ.factorial) ℓ.factorial_ne_zero
      rwa [one_div] at this
    have h2 := V_coeff_pow hΦ ℓ j
    have h3 := V_mul h1 h2
    apply V_mono h3
    show c ≤ -(padicValNat p ℓ.factorial : ℤ) + (ℓ : ℤ) * c
    have h4 : (padicValNat p ℓ.factorial : ℤ) ≤ (ℓ : ℤ) - 1 := by
      have := padicValNat_factorial_le (p := p) hℓ1
      omega
    nlinarith [h4, hc, show (1 : ℤ) ≤ (ℓ : ℤ) from by exact_mod_cast hℓ1]

/-! ## Fermat's little theorem for `p`-integral rationals -/

theorem not_dvd_den {a : ℚ} (ha : V p 0 a) : ¬ p ∣ a.den := by
  intro hdvd
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Rat.den_ofNat] at hdvd
    exact hp.out.one_lt.ne' (Nat.eq_one_of_dvd_one hdvd |>.symm ▸ rfl)
  have hden0 : a.den ≠ 0 := a.den_nz
  -- numerator is coprime to p
  have hnum : ¬ (p : ℤ) ∣ a.num := by
    intro hnd
    have h1 : p ∣ a.num.natAbs := by
      rwa [Int.natCast_dvd_natCast.symm, Int.dvd_natAbs]
    have := Nat.Coprime.eq_one_of_dvd (a.reduced.coprime_dvd_left h1) hdvd
    exact hp.out.one_lt.ne' this
  have hvnum : padicValInt p a.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
  have hvden : 1 ≤ padicValNat p a.den := by
    have := (padicValNat_dvd_iff_le (p := p) hden0 (n := 1)).mp (by simpa using hdvd)
    exact this
  have hval : padicValRat p a ≤ -1 := by
    rw [padicValRat_def, hvnum]
    omega
  have hnorm : padicNorm p a = (p : ℚ) ^ (-padicValRat p a) :=
    padicNorm.eq_zpow_of_nonzero ha0
  have hbig : (1 : ℚ) < padicNorm p a := by
    rw [hnorm]
    exact one_lt_zpow₀ (one_lt_p (p := p)) (by omega)
  have := ha
  rw [V] at this
  simp only [neg_zero, zpow_zero] at this
  linarith

theorem fermat_rat {a : ℚ} (ha : V p 0 a) : V p 1 (a ^ p - a) := by
  set s : ℤ := a.num with hs
  set t : ℕ := a.den with ht
  have ht0 : t ≠ 0 := a.den_nz
  have hpt : ¬ p ∣ t := not_dvd_den ha
  have htQ : ((t : ℚ)) ≠ 0 := by exact_mod_cast ht0
  -- key algebraic identity
  have hkey : a ^ p - a = ((s ^ p - s * (t : ℤ) ^ (p-1) : ℤ) : ℚ) * ((t : ℚ) ^ p)⁻¹ := by
    have hnd : ((s : ℚ)) / ((t : ℚ)) = a := by
      rw [hs, ht]; exact_mod_cast Rat.num_div_den a
    have htp : ((t:ℚ))^p ≠ 0 := pow_ne_zero _ htQ
    rw [← hnd, div_pow, ← div_eq_mul_inv]
    rw [div_sub_div _ _ htp htQ, div_eq_div_iff (by positivity) htp]
    push_cast
    have hexp : (t:ℚ)^p = (t:ℚ)^(p-1) * (t:ℚ) := by
      rw [← pow_succ]
      congr 1
      have := hp.out.two_le
      omega
    rw [hexp]
    ring
  rw [hkey]
  have h1 : V p 1 ((s ^ p - s * (t : ℤ) ^ (p-1) : ℤ) : ℚ) := by
    have hd : (p : ℤ) ^ 1 ∣ (s ^ p - s * (t : ℤ) ^ (p-1)) := by
      rw [pow_one]
      have hz : ((s ^ p - s * (t : ℤ) ^ (p-1) : ℤ) : ZMod p) = 0 := by
        push_cast
        have hzs : ((s : ZMod p)) ^ p = (s : ZMod p) := ZMod.pow_card _
        have hzt : ((t : ZMod p)) ^ (p - 1) = 1 := by
          apply ZMod.pow_card_sub_one_eq_one
          intro hcon
          exact hpt ((ZMod.natCast_eq_zero_iff t p).mp hcon)
        rw [hzs, hzt]
        ring
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz
    have := (V_int_iff_dvd (p := p) 1 _).mpr hd
    simpa using this
  have h2 : V p 0 (((t : ℚ) ^ p)⁻¹) := V_inv_pow_unit p hpt
  have := V_mul h1 h2
  simpa using this

/-! ## Truncations and the Frobenius congruence -/

/-- Truncation of a power series to degrees `< M`, as a power series. -/
def truncS (M : ℕ) (F : ℚ⟦X⟧) : ℚ⟦X⟧ := mk fun j => if j < M then coeff j F else 0

@[simp] theorem coeff_truncS (M : ℕ) (F : ℚ⟦X⟧) (j : ℕ) :
    coeff j (truncS M F) = if j < M then coeff j F else 0 := coeff_mk _ _

theorem truncS_zero (F : ℚ⟦X⟧) : truncS 0 F = 0 := by
  ext j
  simp

theorem truncS_succ (M : ℕ) (F : ℚ⟦X⟧) :
    truncS (M+1) F = truncS M F + monomial M (coeff M F) := by
  ext j
  rw [map_add, coeff_truncS, coeff_truncS, coeff_monomial]
  rcases lt_trichotomy j M with h | rfl | h
  · rw [if_pos (by omega), if_pos h, if_neg (by omega), add_zero]
  · rw [if_pos (by omega), if_neg (by omega), if_pos rfl, zero_add]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), add_zero]

theorem V_coeff_truncS {M : ℕ} {F : ℚ⟦X⟧} (hF : ∀ j, j < M → V p 0 (coeff j F)) (j : ℕ) :
    V p 0 (coeff j (truncS M F)) := by
  rw [coeff_truncS]
  split
  · exact hF j (by assumption)
  · exact V_zero_val _

/-- Frobenius congruence for truncated series with `p`-integral coefficients:
`A(x)^p ≡ A(x^p) (mod p)` coefficientwise. -/
theorem frob_trunc {F : ℚ⟦X⟧} (M : ℕ) (hF : ∀ j, j < M → V p 0 (coeff j F)) :
    ∀ i, V p 1 (coeff i ((truncS M F) ^ p
      - PowerSeries.expand p hp.out.ne_zero (truncS M F))) := by
  induction M with
  | zero =>
    intro i
    rw [truncS_zero, zero_pow hp.out.ne_zero, map_zero, sub_zero, map_zero]
    exact V_zero_val _
  | succ M ih =>
    intro i
    set A : ℚ⟦X⟧ := truncS M F with hA
    set a : ℚ := coeff M F with ha
    set B : ℚ⟦X⟧ := monomial M a with hB
    have hVa : V p 0 a := hF M (by omega)
    have hAcoeff : ∀ j, V p 0 (coeff j A) := V_coeff_truncS (fun j hj => hF j (by omega))
    have hBcoeff : ∀ j, V p 0 (coeff j B) := by
      intro j
      rw [hB, coeff_monomial]
      split
      · exact hVa
      · exact V_zero_val _
    have hp2 : 2 ≤ p := hp.out.two_le
    -- the binomial expansion, with the extreme terms singled out
    have hkey : (truncS (M+1) F) ^ p - PowerSeries.expand p hp.out.ne_zero (truncS (M+1) F)
        = (A ^ p - PowerSeries.expand p hp.out.ne_zero A)
          + (monomial (p*M) (a ^ p - a)
          + ∑ t ∈ Finset.Ico 1 p, A ^ t * B ^ (p - t) * ((p.choose t : ℕ) : ℚ⟦X⟧)) := by
      rw [truncS_succ, ← hA, ← ha, ← hB, add_pow, map_add]
      have hEB : PowerSeries.expand p hp.out.ne_zero B = monomial (p*M) a := by
        rw [hB, expand_monomial]
      have hBp : B ^ p = monomial (p*M) (a ^ p) := by
        rw [hB, monomial_pow, mul_comm]
      have hsplit : ∑ t ∈ Finset.range (p+1), A ^ t * B ^ (p - t) * ((p.choose t : ℕ) : ℚ⟦X⟧)
          = B ^ p + (∑ t ∈ Finset.Ico 1 p, A ^ t * B ^ (p - t) * ((p.choose t : ℕ) : ℚ⟦X⟧))
            + A ^ p := by
        rw [Finset.sum_range_succ, Finset.range_eq_Ico,
          Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < p)]
        simp
      rw [hsplit, hEB, hBp]
      have hmono : monomial (p*M) (a ^ p) - monomial (p*M) a = monomial (p*M) (a ^ p - a) := by
        rw [← map_sub]
      rw [← hmono]
      ring
    rw [hkey, map_add, map_add]
    apply V_add
    · exact ih (fun j hj => hF j (by omega)) i
    apply V_add
    · rw [coeff_monomial]
      split
      · exact fermat_rat hVa
      · exact V_zero_val _
    · rw [map_sum]
      apply V_sum
      intro t hht
      obtain ⟨u, hu⟩ : p ∣ p.choose t := by
        rw [Finset.mem_Ico] at hht
        exact hp.out.dvd_choose_self (by omega) (by omega)
      have hcoeffmul : ∀ j, V p 0 (coeff j (A ^ t * B ^ (p - t))) := by
        intro j
        have h1 := V_coeff_pow hAcoeff t
        have h2 := V_coeff_pow hBcoeff (p - t)
        have := V_coeff_mul (c := (t : ℤ) * 0) (d := ((p - t : ℕ) : ℤ) * 0) h1 h2 j
        simpa using this
      have hc : coeff i (A ^ t * B ^ (p - t) * ((p.choose t : ℕ) : ℚ⟦X⟧))
          = coeff i (A ^ t * B ^ (p - t)) * ((p.choose t : ℕ) : ℚ) := by
        rw [(map_natCast (C : ℚ →+* ℚ⟦X⟧) (p.choose t)).symm, mul_comm, ← smul_eq_C_mul,
          map_smul, smul_eq_mul]
        ring
      rw [hc, hu]
      have h3 : ((p * u : ℕ) : ℚ) = (p : ℚ) * (u : ℚ) := by push_cast; ring
      rw [h3]
      have h4 := V_mul (V_mul (hcoeffmul i) (V_p_pow (p := p) 1)) (V_nat (p := p) u)
      apply V_mono _ (show (1:ℤ) ≤ 0 + 1 + 0 by omega)
      rw [pow_one] at h4
      convert h4 using 1
      ring

/-! ## Coefficients of powers only depend on low-order coefficients -/

theorem coeff_pow_congr {F G : ℚ⟦X⟧} {k : ℕ} (h : ∀ j, j ≤ k → coeff j F = coeff j G)
    (e : ℕ) : ∀ j, j ≤ k → coeff j (F ^ e) = coeff j (G ^ e) := by
  induction e with
  | zero => intro j hj; rfl
  | succ e ih =>
    intro j hj
    rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_antidiagonal] at hx
    rw [ih x.1 (by omega), h x.2 (by omega)]

/-- Extraction of the top coefficient from the `p`-th power of a truncation. -/
theorem coeff_trunc_pow_key {E : ℚ⟦X⟧} (hE0 : constantCoeff E = 1) {k : ℕ} (hk : 0 < k) :
    coeff k ((truncS (k+1) E) ^ p)
      = coeff k ((truncS k E) ^ p) + (p : ℚ) * coeff k E := by
  have hp2 : 2 ≤ p := hp.out.two_le
  set A : ℚ⟦X⟧ := truncS k E with hA
  set a : ℚ := coeff k E with ha
  rw [truncS_succ, ← hA, ← ha, add_pow]
  rw [map_sum]
  -- split the sum: t = p gives A^p, t = p-1 gives p * a, the rest vanish at degree k
  have hsplit : Finset.range (p+1) = insert p (insert (p-1) (Finset.range (p-1))) := by
    ext t
    simp only [Finset.mem_range, Finset.mem_insert]
    omega
  rw [hsplit, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_range]; omega),
    Finset.sum_insert (by simp only [Finset.mem_range]; omega)]
  have hterm : ∀ t, coeff k (A ^ t * (monomial k a) ^ (p - t) * ((p.choose t : ℕ) : ℚ⟦X⟧))
      = coeff k (A ^ t * monomial ((p-t)*k) (a ^ (p-t))) * ((p.choose t : ℕ) : ℚ) := by
    intro t
    rw [(map_natCast (C : ℚ →+* ℚ⟦X⟧) (p.choose t)).symm, mul_comm, ← smul_eq_C_mul,
      map_smul, smul_eq_mul, monomial_pow]
    ring
  -- t = p term
  have hTp : coeff k (A ^ p * (monomial k a) ^ (p - p) * ((p.choose p : ℕ) : ℚ⟦X⟧))
      = coeff k (A ^ p) := by
    rw [Nat.sub_self, pow_zero, mul_one, Nat.choose_self]
    simp
  -- t = p - 1 term
  have hTp1 : coeff k (A ^ (p-1) * (monomial k a) ^ (p - (p-1)) * ((p.choose (p-1) : ℕ) : ℚ⟦X⟧))
      = (p : ℚ) * a := by
    rw [hterm]
    have h1 : p - (p - 1) = 1 := by omega
    rw [h1, pow_one, one_mul]
    have h2 : coeff k (A ^ (p-1) * monomial k a) = coeff 0 (A ^ (p-1)) * a := by
      rw [coeff_mul]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => coeff x (A ^ (p-1)) * coeff y (monomial k a))]
      rw [Finset.sum_range_succ']
      have hz : ∀ x ∈ Finset.range k,
          coeff (x+1) (A ^ (p-1)) * coeff (k - (x+1)) (monomial k a) = 0 := by
        intro x hx
        rw [Finset.mem_range] at hx
        rw [coeff_monomial, if_neg (by omega), mul_zero]
      rw [Finset.sum_eq_zero hz, zero_add, Nat.sub_zero, coeff_monomial, if_pos rfl]
    rw [h2]
    have h3 : coeff 0 (A ^ (p-1)) = 1 := by
      rw [coeff_zero_eq_constantCoeff, map_pow]
      have h4 : constantCoeff A = 1 := by
        rw [hA]
        have := coeff_truncS k E 0
        rw [if_pos hk] at this
        rw [← coeff_zero_eq_constantCoeff, this, coeff_zero_eq_constantCoeff, hE0]
      rw [h4, one_pow]
    rw [h3, one_mul]
    have h5 : p.choose (p-1) = p := by
      have h6 := Nat.choose_symm (show p - 1 ≤ p by omega)
      rw [show p - (p-1) = 1 by omega, Nat.choose_one_right] at h6
      omega
    rw [h5]
    ring
  -- remaining terms vanish
  have hrest : ∀ t ∈ Finset.range (p-1),
      coeff k (A ^ t * (monomial k a) ^ (p - t) * ((p.choose t : ℕ) : ℚ⟦X⟧)) = 0 := by
    intro t hht
    rw [Finset.mem_range] at hht
    rw [hterm]
    have hz : coeff k (A ^ t * monomial ((p-t)*k) (a ^ (p-t))) = 0 := by
      rw [coeff_mul]
      apply Finset.sum_eq_zero
      intro x hx
      rw [Finset.mem_antidiagonal] at hx
      rw [coeff_monomial, if_neg, mul_zero]
      have : 2 * k ≤ (p - t) * k := by
        apply Nat.mul_le_mul_right
        omega
      omega
    rw [hz, zero_mul]
  rw [Finset.sum_eq_zero hrest, add_zero, hTp, hTp1, ha]

/-! ## Dwork's integrality lemma -/

theorem dwork {F : ℚ⟦X⟧} (hF0 : constantCoeff F = 0)
    (hH : ∀ j, V p 1 (coeff j ((p : ℕ) • F - PowerSeries.expand p hp.out.ne_zero F)))
    (k : ℕ) : V p 0 (coeff k (expS F)) := by
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h1 : coeff 0 (expS F) = 1 := by
      rw [coeff_zero_eq_constantCoeff, constantCoeff_expS]
    rw [h1]
    exact V_one
  · set E : ℚ⟦X⟧ := expS F with hE
    set Δ : ℚ⟦X⟧ := (p : ℕ) • F - PowerSeries.expand p hp.out.ne_zero F with hΔ
    have hΔ0 : constantCoeff Δ = 0 := by
      rw [hΔ, map_sub, constantCoeff_expand, map_nsmul, hF0, smul_zero, sub_zero]
    have hkey : E ^ p = PowerSeries.expand p hp.out.ne_zero E * expS Δ := by
      rw [hE, expand_expS, ← expS_add, ← expS_nsmul]
      congr 1
      rw [hΔ]
      abel
    set A : ℚ⟦X⟧ := truncS k E with hA
    have hAfrob := frob_trunc (p := p) k (fun j hj => IH j hj)
    have hEtail : ∀ j, j ≠ 0 → V p 1 (coeff j (expS Δ)) :=
      fun j hj => exp_tail le_rfl hΔ0 hH hj
    -- LHS computation
    have hagree : ∀ j, j ≤ k → coeff j (truncS (k+1) E) = coeff j E := by
      intro j hj
      rw [coeff_truncS, if_pos (by omega)]
    have c1 : coeff k (E ^ p) = coeff k ((truncS (k+1) E) ^ p) :=
      (coeff_pow_congr hagree p k le_rfl).symm
    have c2 : coeff k ((truncS (k+1) E) ^ p)
        = coeff k (A ^ p) + (p : ℚ) * coeff k E :=
      coeff_trunc_pow_key (by rw [hE, constantCoeff_expS]) hk
    -- RHS computation
    have c3 : coeff k (E ^ p) = (∑ i ∈ Finset.range k,
          coeff i (PowerSeries.expand p hp.out.ne_zero E) * coeff (k - i) (expS Δ))
        + coeff k (PowerSeries.expand p hp.out.ne_zero E) := by
      rw [hkey, coeff_mul]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun x y => coeff x (PowerSeries.expand p hp.out.ne_zero E) * coeff y (expS Δ))]
      rw [Finset.sum_range_succ, Nat.sub_self]
      have h1 : coeff 0 (expS Δ) = 1 := by
        rw [coeff_zero_eq_constantCoeff, constantCoeff_expS]
      rw [h1, mul_one]
    -- top coefficients of expansions agree
    have c4 : coeff k (PowerSeries.expand p hp.out.ne_zero E)
        = coeff k (PowerSeries.expand p hp.out.ne_zero A) := by
      rw [coeff_expand, coeff_expand]
      split
      · rename_i hdvd
        rw [hA, coeff_truncS, if_pos]
        exact Nat.div_lt_self hk hp.out.one_lt
      · rfl
    have heq : (p : ℚ) * coeff k E = (∑ i ∈ Finset.range k,
          coeff i (PowerSeries.expand p hp.out.ne_zero E) * coeff (k - i) (expS Δ))
        - coeff k (A ^ p - PowerSeries.expand p hp.out.ne_zero A) := by
      rw [map_sub]
      have := c1.symm.trans c3
      rw [c2] at this
      rw [c4] at this
      linarith
    have hV : V p 1 ((p : ℚ) * coeff k E) := by
      rw [heq]
      apply V_sub
      · apply V_sum
        intro i hi
        rw [Finset.mem_range] at hi
        have h1 : V p 0 (coeff i (PowerSeries.expand p hp.out.ne_zero E)) := by
          rw [coeff_expand]
          split
          · rename_i hdvd
            exact IH (i / p) (by
              calc i / p ≤ i := Nat.div_le_self i p
              _ < k := hi)
          · exact V_zero_val _
        have h2 : V p 1 (coeff (k - i) (expS Δ)) := hEtail (k - i) (by omega)
        have := V_mul h1 h2
        simpa using this
      · exact hAfrob k
    have := V_div_p (p := p) hV
    simpa using this

end

end Super

-- ===== Devel/D07.lean =====
namespace Super

open Finset PowerSeries

noncomputable section

/-! ## The logarithmic generating series -/

/-- `Lser m t = ∑_{k ≥ 1} c_m(k t) x^k / k`. -/
def Lser (m t : ℕ) : ℚ⟦X⟧ := mk fun k => if k = 0 then 0 else cQ m (k*t) / k

@[simp] theorem coeff_Lser (m t k : ℕ) :
    coeff k (Lser m t) = if k = 0 then 0 else cQ m (k*t) / k := coeff_mk _ _

theorem constantCoeff_Lser (m t : ℕ) : constantCoeff (Lser m t) = 0 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_Lser, if_pos rfl]

variable {p : ℕ} [hp : Fact p.Prime]

/-- Dwork's hypothesis for `N • Lser m t`, via the Gauss congruence for `c_m`. -/
theorem dwork_hyp_L (m t N : ℕ) (ht : t ≠ 0) (j : ℕ) :
    V p 1 (coeff j ((p : ℕ) • ((N : ℕ) • Lser m t)
      - PowerSeries.expand p hp.out.ne_zero ((N : ℕ) • Lser m t))) := by
  rw [map_sub, map_nsmul, map_nsmul, coeff_expand, coeff_Lser]
  rcases eq_or_ne j 0 with rfl | hj
  · rw [if_pos rfl, if_pos (dvd_zero p), Nat.zero_div, map_nsmul, coeff_Lser, if_pos rfl]
    simp
  rw [if_neg hj]
  by_cases hdvd : p ∣ j
  · obtain ⟨J, hJ⟩ := hdvd
    have hJ0 : J ≠ 0 := by rintro rfl; omega
    have hp0 : (0:ℕ) < p := hp.out.pos
    rw [if_pos ⟨J, hJ⟩, map_nsmul, coeff_Lser, hJ, Nat.mul_div_cancel_left J hp0,
      if_neg hJ0]
    have hJt : J * t ≠ 0 := Nat.mul_ne_zero hJ0 ht
    have halg : (p : ℕ) • ((N : ℕ) • (cQ m (p*J*t) / (p*J : ℕ)))
        - (N : ℕ) • (cQ m (J*t) / (J : ℕ))
        = ((N : ℚ) * (1 / (J : ℕ))) * (cQ m (p*(J*t)) - cQ m (J*t)) := by
      have hpJ : ((p*J : ℕ) : ℚ) = (p:ℚ) * (J:ℚ) := by push_cast; ring
      have hpQ : (p:ℚ) ≠ 0 := by
        exact_mod_cast hp.out.ne_zero
      have hJQ : (J:ℚ) ≠ 0 := by exact_mod_cast hJ0
      rw [nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, hpJ]
      rw [show p*(J*t) = p*J*t by ring]
      field_simp
    rw [halg]
    have h1 : V p (-(padicValNat p J : ℤ)) ((N : ℚ) * (1 / (J : ℕ))) :=
      V_nsmul N (V_inv_nat hJ0)
    have h2 := rel_gauss (p := p) m (J*t) hJt
    have h3 := V_mul h1 h2
    apply V_mono h3
    show (1:ℤ) ≤ -(padicValNat p J : ℤ) + ((vc p m (J*t) : ℤ) + (1 + (padicValNat p (J*t) : ℤ)))
    have h4 : padicValNat p J ≤ padicValNat p (J*t) := by
      rw [padicValNat.mul hJ0 ht]
      omega
    omega
  · rw [if_neg hdvd, sub_zero, nsmul_eq_mul, nsmul_eq_mul]
    have hpj : ¬ p ∣ j := hdvd
    have halg : (p : ℚ) * ((N : ℚ) * (cQ m (j*t) / (j:ℕ)))
        = (p : ℚ) * ((N : ℚ) * (cQ m (j*t) * (1 / (j:ℕ)))) := by
      rw [mul_one_div]
    rw [halg]
    have h1 : V p 1 ((p:ℚ)) := by
      have := V_p_pow (p := p) 1
      rwa [pow_one] at this
    have h2 : V p 0 ((N:ℚ)) := V_nat N
    have h3 : V p 0 (cQ m (j*t)) := by
      rw [cQ_eq_cast]
      exact V_nat _
    have h4 : V p 0 (1 / (j:ℕ)) := V_inv_unit hj hpj
    have h5 := V_mul h1 (V_mul h2 (V_mul h3 h4))
    simpa using h5

/-- `p`-integrality of the coefficients of `exp(N ∑ c_m(kt) x^k/k)`. -/
theorem integral_expS_NL (m t N : ℕ) (ht : t ≠ 0) (k : ℕ) :
    V p 0 (coeff k (expS ((N : ℕ) • Lser m t))) := by
  apply dwork
  · rw [map_nsmul, constantCoeff_Lser, smul_zero]
  · exact dwork_hyp_L m t N ht

/-! ## Integrality of inverses -/

theorem V_coeff_inv {G H : ℚ⟦X⟧} (hGH : G * H = 1) (hG0 : constantCoeff G = 1)
    (hG : ∀ j, V p 0 (coeff j G)) (j : ℕ) : V p 0 (coeff j H) := by
  induction j using Nat.strong_induction_on with
  | _ j IH =>
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h1 : constantCoeff G * constantCoeff H = 1 := by
      rw [← map_mul, hGH, map_one]
    rw [hG0, one_mul] at h1
    rw [coeff_zero_eq_constantCoeff, h1]
    exact V_one
  · have h1 : coeff j (G * H) = 0 := by
      rw [hGH, coeff_one, if_neg (by omega)]
    rw [coeff_mul] at h1
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun x y => coeff x G * coeff y H)] at h1
    rw [Finset.sum_range_succ'] at h1
    have h2 : coeff 0 G * coeff (j - 0) H = coeff j H := by
      rw [coeff_zero_eq_constantCoeff, hG0, one_mul, Nat.sub_zero]
    rw [h2] at h1
    have h3 : coeff j H
        = -(∑ i ∈ Finset.range j, coeff (i+1) G * coeff (j - (i+1)) H) := by
      linarith
    rw [h3]
    apply V_neg
    apply V_sum
    intro i hi
    rw [Finset.mem_range] at hi
    have := V_mul (hG (i+1)) (IH (j - (i+1)) (by omega))
    simpa using this

/-! ## From all-primes integrality to integers -/

theorem den_eq_one_of_all_primes {x : ℚ} (h : ∀ q : ℕ, q.Prime → padicNorm q x ≤ 1) :
    x.den = 1 := by
  by_contra hden
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hden
  haveI : Fact q.Prime := ⟨hq⟩
  have hV : V q 0 x := by
    rw [V]
    simpa using h q hq
  exact not_dvd_den hV hqd

theorem exists_int_of_all_primes {x : ℚ} (h : ∀ q : ℕ, q.Prime → padicNorm q x ≤ 1) :
    ∃ z : ℤ, x = (z : ℚ) := by
  refine ⟨x.num, ?_⟩
  have hd := den_eq_one_of_all_primes h
  exact ((Rat.den_eq_one_iff x).mp hd).symm

/-! ## Nonnegativity of exponential coefficients -/

theorem coeff_expS_nonneg {F : ℚ⟦X⟧} (hF : ∀ j, 0 ≤ coeff j F) (k : ℕ) :
    0 ≤ coeff k (expS F) := by
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [coeff_zero_eq_constantCoeff, constantCoeff_expS]
    exact zero_le_one
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hrec := (isExpOf_expS F).2 k'
    have hpos : (0:ℚ) < ((k'+1 : ℕ) : ℚ) := by positivity
    have hsum : 0 ≤ ∑ j ∈ Finset.range (k'+1),
        (((j+1 : ℕ) : ℚ) * coeff (j+1) F) * coeff (k' - j) (expS F) := by
      apply Finset.sum_nonneg
      intro j hj
      rw [Finset.mem_range] at hj
      apply mul_nonneg
      · apply mul_nonneg (by positivity) (hF (j+1))
      · exact IH (k' - j) (by omega)
    nlinarith [hrec]

/-- The coefficients of `exp(N ∑_k c_m(kt) x^k/k)` are natural numbers. -/
theorem coeff_expS_NL_nat (m t N : ℕ) (ht : t ≠ 0) (k : ℕ) :
    ∃ b : ℕ, coeff k (expS ((N : ℕ) • Lser m t)) = (b : ℚ) := by
  have hall : ∀ q : ℕ, q.Prime → padicNorm q (coeff k (expS ((N : ℕ) • Lser m t))) ≤ 1 := by
    intro q hq
    haveI : Fact q.Prime := ⟨hq⟩
    have := integral_expS_NL (p := q) m t N ht k
    rw [V] at this
    simpa using this
  obtain ⟨z, hz⟩ := exists_int_of_all_primes hall
  have hnn : 0 ≤ coeff k (expS ((N : ℕ) • Lser m t)) := by
    apply coeff_expS_nonneg
    intro j
    rw [map_nsmul, coeff_Lser, nsmul_eq_mul]
    split
    · simp
    · have h1 : (0:ℚ) ≤ cQ m (j*t) := by
        rw [cQ_eq_cast]
        positivity
      positivity
  refine ⟨z.toNat, ?_⟩
  rw [hz]
  have hz0 : 0 ≤ z := by
    rw [hz] at hnn
    exact_mod_cast hnn
  have h7 : ((z.toNat : ℤ) : ℚ) = (z : ℚ) := by rw [Int.toNat_of_nonneg hz0]
  exact_mod_cast h7.symm

end

end Super

-- ===== Devel/D08.lean =====
namespace Super

open Finset PowerSeries

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## The correction series `Pser` -/

/-- Coefficients of the correction series at level `ρ`. -/
def Pc (p m n ρ : ℕ) (u : ℕ) : ℚ :=
  if p^ρ ∣ u then 0 else (n : ℚ) * (p:ℚ)^ρ * cQ m u / u

/-- The correction series `n • (p^ρ • L₀ - expand_{p^ρ} L_ρ)`. -/
def Pser (p m n ρ : ℕ) : ℚ⟦X⟧ := mk (Pc p m n ρ)

@[simp] theorem coeff_Pser (m n ρ u : ℕ) :
    coeff u (Pser p m n ρ) = Pc p m n ρ u := coeff_mk _ _

theorem Pc_zero (m n ρ : ℕ) : Pc p m n ρ 0 = 0 := if_pos (dvd_zero _)

theorem constantCoeff_Pser (m n ρ : ℕ) : constantCoeff (Pser p m n ρ) = 0 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_Pser, Pc_zero]

/-- The splitting of the base logarithmic series. -/
theorem L_split (m n ρ : ℕ) :
    ((n * p^ρ : ℕ) • Lser m 1)
      = Pser p m n ρ + PowerSeries.expand (p^ρ) (pow_ne_zero ρ hp.out.ne_zero)
          ((n:ℕ) • Lser m (p^ρ)) := by
  have hpρ : (0:ℕ) < p^ρ := pow_pos hp.out.pos ρ
  ext u
  rw [map_nsmul, map_add, coeff_Pser, coeff_expand, coeff_Lser, nsmul_eq_mul]
  rcases eq_or_ne u 0 with rfl | hu
  · rw [if_pos rfl, mul_zero, Pc_zero, if_pos (dvd_zero _), Nat.zero_div, map_nsmul,
      coeff_Lser, if_pos rfl, smul_zero, add_zero]
  rw [if_neg hu, Pc]
  by_cases hdvd : p^ρ ∣ u
  · obtain ⟨w, hw⟩ := hdvd
    have hw0 : w ≠ 0 := by rintro rfl; omega
    rw [if_pos ⟨w, hw⟩, if_pos ⟨w, hw⟩, map_nsmul, coeff_Lser, hw,
      Nat.mul_div_cancel_left w hpρ, if_neg hw0, nsmul_eq_mul, zero_add]
    have hwQ : ((w:ℚ)) ≠ 0 := by exact_mod_cast hw0
    have hpQ : ((p:ℚ)) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    rw [show (p^ρ * w) * 1 = p^ρ * w from mul_one _, show w * p^ρ = p^ρ * w by ring]
    push_cast
    field_simp
  · rw [if_neg hdvd, if_neg hdvd, add_zero, mul_one]
    have huQ : ((u:ℚ)) ≠ 0 := by exact_mod_cast hu
    push_cast
    field_simp

/-- Master identity: `exp((n p^ρ) L₀) = exp(n P_ρ) · exp(n L_ρ)(x^{p^ρ})`. -/
theorem master_identity (m n ρ : ℕ) :
    expS ((n * p^ρ : ℕ) • Lser m 1)
      = expS (Pser p m n ρ) * PowerSeries.expand (p^ρ) (pow_ne_zero ρ hp.out.ne_zero)
          (expS ((n:ℕ) • Lser m (p^ρ))) := by
  rw [L_split (p := p) m n ρ, expS_add, expand_expS]

/-! ## Valuation bounds for the coefficients of `Pser` -/

theorem V_Pc {m n ρ u : ℕ} (hu : ¬ p^ρ ∣ u) :
    V p ((ρ : ℤ) - padicValNat p u + vc p m u) (Pc p m n ρ u) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ dvd_zero _)
  rw [Pc, if_neg hu]
  have h1 := V_nsmul (p := p) n (V_mul (V_p_pow (p := p) ρ)
    (V_mul (V_cQ (p := p) m u) (V_inv_nat (p := p) hu0)))
  have h2 : (n : ℚ) * ((p:ℚ)^ρ * (cQ m u * (1 / (u:ℚ))))
      = (n : ℚ) * (p:ℚ)^ρ * cQ m u / u := by
    field_simp
  rw [h2] at h1
  apply V_mono h1
  omega

/-- Value of `Pc` at level `r` on an argument `p·J`. -/
theorem V_Pc_high {m n r J : ℕ} (hr : 1 ≤ r) (hJ : ¬ p^(r-1) ∣ J) :
    V p (((r-1 : ℕ) : ℤ) - padicValNat p J + vc p m J) (Pc p m n r (p * J)) := by
  have hJ0 : J ≠ 0 := fun h => hJ (h ▸ dvd_zero _)
  have hnd : ¬ p^r ∣ p * J := by
    intro hcon
    apply hJ
    obtain ⟨c, hc⟩ := hcon
    refine ⟨c, ?_⟩
    have hpr : p^r = p * p^(r-1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpr] at hc
    have := hp.out.pos
    have h2 : p * J = p * (p^(r-1) * c) := by rw [hc]; ring
    exact Nat.eq_of_mul_eq_mul_left this h2
  have h1 := V_Pc (p := p) (m := m) (n := n) hnd
  have hval : padicValNat p (p * J) = 1 + padicValNat p J := by
    rw [padicValNat.mul hp.out.ne_zero hJ0, padicValNat.self hp.out.one_lt]
  have hvc : vc p m (p * J) = vc p m J := vc_p_mul m J
  apply V_mono h1
  rw [hval, hvc]
  omega

/-- Difference bound via the strong Kazandzidis relation. -/
theorem V_Pc_diff (hp5 : 5 ≤ p) {m n r J : ℕ} (hr : 1 ≤ r) (hJ : ¬ p^(r-1) ∣ J) :
    V p ((((r-1 : ℕ) : ℤ) - padicValNat p J + vc p m J)
        + (3 + 3 * (padicValNat p J : ℤ)))
      (Pc p m n r (p * J) - Pc p m n (r-1) J) := by
  have hJ0 : J ≠ 0 := fun h => hJ (h ▸ dvd_zero _)
  have hJQ : ((J:ℚ)) ≠ 0 := by exact_mod_cast hJ0
  have hpQ : ((p:ℚ)) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hnd : ¬ p^r ∣ p * J := by
    intro hcon
    apply hJ
    obtain ⟨c, hc⟩ := hcon
    refine ⟨c, ?_⟩
    have hpr : p^r = p * p^(r-1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpr] at hc
    have := hp.out.pos
    have h2 : p * J = p * (p^(r-1) * c) := by rw [hc]; ring
    exact Nat.eq_of_mul_eq_mul_left this h2
  -- explicit values
  have hvalhigh : Pc p m n r (p * J) = (n:ℚ) * (p:ℚ)^(r-1) * cQ m (p*J) / J := by
    rw [Pc, if_neg hnd]
    have hpr : (p:ℚ)^r = (p:ℚ) * (p:ℚ)^(r-1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hcast : ((p * J : ℕ) : ℚ) = (p:ℚ) * (J:ℚ) := by push_cast; ring
    rw [hpr, hcast]
    field_simp
  have hvallow : Pc p m n (r-1) J = (n:ℚ) * (p:ℚ)^(r-1) * cQ m J / J := by
    rw [Pc, if_neg hJ]
  have hdiff : Pc p m n r (p * J) - Pc p m n (r-1) J
      = (n:ℚ) * ((p:ℚ)^(r-1) * ((1/(J:ℚ)) * (cQ m (p*J) - cQ m J))) := by
    rw [hvalhigh, hvallow]
    field_simp
  rw [hdiff]
  have h1 := V_nsmul (p := p) n (V_mul (V_p_pow (p := p) (r-1))
    (V_mul (V_inv_nat (p := p) hJ0) (rel_strong (p := p) hp5 m J hJ0)))
  apply V_mono h1
  omega

/-! ## Telescoping product difference bound -/

theorem V_prod_sub_prod {a b : ℕ → ℚ} {w δ : ℕ → ℤ} :
    ∀ (s : Finset ℕ) (c : ℤ),
      (∀ i ∈ s, V p (w i) (a i)) → (∀ i ∈ s, V p (w i) (b i)) →
      (∀ i ∈ s, V p (w i + δ i) (a i - b i)) →
      (∀ i ∈ s, c ≤ (∑ t ∈ s, w t) + δ i) →
      V p c (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by
  intro s
  induction s using Finset.cons_induction with
  | empty =>
    intro c _ _ _ _
    simpa using V_zero_val (p := p) c
  | cons x s hx ih =>
    intro c ha hb hd hc
    rw [Finset.prod_cons, Finset.prod_cons]
    have key : a x * ∏ i ∈ s, a i - b x * ∏ i ∈ s, b i
        = a x * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a x - b x) * ∏ i ∈ s, b i := by
      ring
    rw [key]
    apply V_add
    · have h1 : V p (c - w x) (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by
        apply ih (c - w x) (fun i hi => ha i (Finset.mem_cons_of_mem hi))
          (fun i hi => hb i (Finset.mem_cons_of_mem hi))
          (fun i hi => hd i (Finset.mem_cons_of_mem hi))
        intro i hi
        have := hc i (Finset.mem_cons_of_mem hi)
        rw [Finset.sum_cons] at this
        omega
      have h2 := V_mul (ha x (Finset.mem_cons_self x s)) h1
      apply V_mono h2
      omega
    · have h1 := V_mul (hd x (Finset.mem_cons_self x s))
        (V_prod (fun i hi => hb i (Finset.mem_cons_of_mem hi)))
      apply V_mono h1
      have := hc x (Finset.mem_cons_self x s)
      rw [Finset.sum_cons] at this
      omega

end

end Super

-- ===== Devel/D09.lean =====
namespace Super

open Finset PowerSeries

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

/-- The per-power valuation bound for the difference of tuple sums at
consecutive levels. -/
theorem KL_ell (hp5 : 5 ≤ p) {m : ℕ} (hm : 3 ≤ m) {r : ℕ} (hr : 1 ≤ r)
    (n j : ℕ) (hj : j ≠ 0) (ℓ : ℕ) :
    V p (3*(r:ℤ) + (padicValNat p ℓ.factorial : ℤ))
      (coeff (p^r * j) ((Pser p m n r)^ℓ)
        - coeff (p^(r-1) * j) ((Pser p m n (r-1))^ℓ)) := by
  set K := p^r * j with hK
  set K' := p^(r-1) * j with hK'
  set U : Finset (ℕ →₀ ℕ) := finsuppAntidiag (range ℓ) K with hU
  set U' : Finset (ℕ →₀ ℕ) := finsuppAntidiag (range ℓ) K' with hU'
  -- rewrite coefficients as tuple sums
  have hT : coeff K ((Pser p m n r)^ℓ)
      = ∑ l ∈ U, ∏ i ∈ range ℓ, Pc p m n r (l i) := by
    rw [coeff_pow]
    exact Finset.sum_congr rfl fun l _ => Finset.prod_congr rfl fun i _ => by
      rw [coeff_Pser]
  have hT' : coeff K' ((Pser p m n (r-1))^ℓ)
      = ∑ l ∈ U', ∏ i ∈ range ℓ, Pc p m n (r-1) (l i) := by
    rw [coeff_pow]
    exact Finset.sum_congr rfl fun l _ => Finset.prod_congr rfl fun i _ => by
      rw [coeff_Pser]
  -- restrict to good tuples
  have hTg : ∑ l ∈ U, ∏ i ∈ range ℓ, Pc p m n r (l i)
      = ∑ l ∈ U.filter (fun l => ∀ i ∈ range ℓ, ¬ p^r ∣ l i),
          ∏ i ∈ range ℓ, Pc p m n r (l i) := by
    symm
    apply Finset.sum_filter_of_ne
    intro l hl hne i hi hdvd
    exact hne (Finset.prod_eq_zero hi (by rw [Pc, if_pos hdvd]))
  have hTg' : ∑ l ∈ U', ∏ i ∈ range ℓ, Pc p m n (r-1) (l i)
      = ∑ l ∈ U'.filter (fun l => ∀ i ∈ range ℓ, ¬ p^(r-1) ∣ l i),
          ∏ i ∈ range ℓ, Pc p m n (r-1) (l i) := by
    symm
    apply Finset.sum_filter_of_ne
    intro l hl hne i hi hdvd
    exact hne (Finset.prod_eq_zero hi (by rw [Pc, if_pos hdvd]))
  set cnum : (ℕ →₀ ℕ) → ℕ := fun l => ((range ℓ).filter (fun i => ¬ p ∣ l i)).card
    with hcnum
  -- split good tuples by the number of parts coprime to p
  have hsplit : ∑ l ∈ U.filter (fun l => ∀ i ∈ range ℓ, ¬ p^r ∣ l i),
        ∏ i ∈ range ℓ, Pc p m n r (l i)
      = ∑ l ∈ (U.filter (fun l => ∀ i ∈ range ℓ, ¬ p^r ∣ l i)).filter
            (fun l => 2 ≤ cnum l), ∏ i ∈ range ℓ, Pc p m n r (l i)
        + ∑ l ∈ (U.filter (fun l => ∀ i ∈ range ℓ, ¬ p^r ∣ l i)).filter
            (fun l => ¬ 2 ≤ cnum l), ∏ i ∈ range ℓ, Pc p m n r (l i) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- tuples with cnum ≤ 1 have all parts divisible by p
  have hparity : (U.filter (fun l => ∀ i ∈ range ℓ, ¬ p^r ∣ l i)).filter
        (fun l => ¬ 2 ≤ cnum l)
      = (U.filter (fun l => ∀ i ∈ range ℓ, ¬ p^r ∣ l i)).filter
        (fun l => ∀ i ∈ range ℓ, p ∣ l i) := by
    ext l
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hlU, hlgood⟩, hc⟩
      refine ⟨⟨hlU, hlgood⟩, ?_⟩
      by_contra hcon
      push_neg at hcon
      obtain ⟨i₀, hi₀, hnd₀⟩ := hcon
      have hi₀f : i₀ ∈ (range ℓ).filter (fun i => ¬ p ∣ l i) :=
        Finset.mem_filter.mpr ⟨hi₀, hnd₀⟩
      have hcard1 : cnum l = 1 := by
        have h1 : 0 < ((range ℓ).filter (fun i => ¬ p ∣ l i)).card :=
          Finset.card_pos.mpr ⟨i₀, hi₀f⟩
        have h2 : cnum l = ((range ℓ).filter (fun i => ¬ p ∣ l i)).card := rfl
        omega
      obtain ⟨i₁, hi₁⟩ := Finset.card_eq_one.mp hcard1
      have hi₀eq : i₀ = i₁ := by
        have := hi₁ ▸ hi₀f
        simpa using this
      subst hi₀eq
      -- sum over range ℓ splits; p divides everything except l i₀
      have hsum : ∑ i ∈ range ℓ, l i = K := (Finset.mem_finsuppAntidiag.mp hlU).1
      have hsplit2 : ∑ i ∈ (range ℓ).filter (fun i => ¬ p ∣ l i), l i
          + ∑ i ∈ (range ℓ).filter (fun i => ¬ ¬ p ∣ l i), l i
          = ∑ i ∈ range ℓ, l i := Finset.sum_filter_add_sum_filter_not _ _ _
      have h2 : ∑ i ∈ (range ℓ).filter (fun i => ¬ p ∣ l i), l i = l i₀ := by
        rw [hi₁, Finset.sum_singleton]
      have h3 : p ∣ ∑ i ∈ (range ℓ).filter (fun i => ¬ ¬ p ∣ l i), l i := by
        apply Finset.dvd_sum
        intro i hi
        have := (Finset.mem_filter.mp hi).2
        rwa [not_not] at this
      have h4 : p ∣ K := by
        rw [hK]
        exact Dvd.dvd.mul_right (dvd_pow_self p (by omega : r ≠ 0)) j
      apply hnd₀
      rw [h2] at hsplit2
      obtain ⟨c3, hc3⟩ := h3
      obtain ⟨c4, hc4⟩ := h4
      have h5 : l i₀ = p * c4 - p * c3 := by omega
      rw [h5]
      exact Nat.dvd_sub (Dvd.intro c4 rfl) (Dvd.intro c3 rfl)
    · rintro ⟨⟨hlU, hlgood⟩, hall⟩
      refine ⟨⟨hlU, hlgood⟩, ?_⟩
      have hzero : cnum l = 0 := by
        rw [hcnum]
        simp only
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i hi
        rw [not_not]
        exact hall i hi
      omega
  -- the F-part: tuples with at least two coprime parts
  have hFpart : V p (3*(r:ℤ) + (padicValNat p ℓ.factorial : ℤ))
      (∑ l ∈ (U.filter (fun l => ∀ i ∈ range ℓ, ¬ p^r ∣ l i)).filter
        (fun l => 2 ≤ cnum l), ∏ i ∈ range ℓ, Pc p m n r (l i)) := by
    apply V_sum
    intro l hl
    obtain ⟨hl1, hlc⟩ := Finset.mem_filter.mp hl
    obtain ⟨hlU, hlgood⟩ := Finset.mem_filter.mp hl1
    have hlsum : ∑ i ∈ range ℓ, l i = K := (Finset.mem_finsuppAntidiag.mp hlU).1
    have h0 : ∀ i ∈ range ℓ, l i ≠ 0 := by
      intro i hi hzero
      exact hlgood i hi (hzero ▸ dvd_zero _)
    have hvlt : ∀ i ∈ range ℓ, padicValNat p (l i) < r := by
      intro i hi
      by_contra hcon
      push_neg at hcon
      exact hlgood i hi ((padicValNat_dvd_iff_le (h0 i hi)).mpr hcon)
    have hfac : ∀ i ∈ range ℓ, V p ((r:ℤ) - padicValNat p (l i) + vc p m (l i))
        (Pc p m n r (l i)) := fun i hi => V_Pc (hlgood i hi)
    have h1 := V_prod (g := fun i => (r:ℤ) - padicValNat p (l i) + vc p m (l i)) hfac
    apply V_mono h1
    have hFi := F_ineq (p := p) hp5 hm hr (s := range ℓ) (d := ⇑l)
      h0 hlgood (by rw [hlsum, hK]; exact dvd_mul_right _ _) hlc
    rw [Finset.card_range] at hFi
    have hcast : ∀ i ∈ range ℓ, (r:ℤ) - padicValNat p (l i) + vc p m (l i)
        = ((r - padicValNat p (l i) : ℕ) : ℤ) + ((vc p m (l i) : ℕ) : ℤ) := by
      intro i hi
      have := hvlt i hi
      omega
    rw [Finset.sum_congr rfl hcast, Finset.sum_add_distrib, ← Nat.cast_sum, ← Nat.cast_sum]
    omega
  -- the K-part: bijection with level r-1 tuples
  have hbij : ∑ l ∈ (U.filter (fun l => ∀ i ∈ range ℓ, ¬ p^r ∣ l i)).filter
        (fun l => ∀ i ∈ range ℓ, p ∣ l i), ∏ i ∈ range ℓ, Pc p m n r (l i)
      = ∑ l' ∈ U'.filter (fun l => ∀ i ∈ range ℓ, ¬ p^(r-1) ∣ l i),
          ∏ i ∈ range ℓ, Pc p m n r (p * l' i) := by
    apply Finset.sum_nbij' (fun l => Finsupp.mapRange (· / p) (Nat.zero_div p) l)
      (fun l' => p • l')
    · -- forward membership
      intro l hl
      obtain ⟨hl1, hall⟩ := Finset.mem_filter.mp hl
      obtain ⟨hlU, hlgood⟩ := Finset.mem_filter.mp hl1
      obtain ⟨hlsum, hlsupp⟩ := Finset.mem_finsuppAntidiag.mp hlU
      refine Finset.mem_filter.mpr ⟨Finset.mem_finsuppAntidiag.mpr ⟨?_, ?_⟩, ?_⟩
      · -- sum
        have h1 : p * (∑ i ∈ range ℓ, (Finsupp.mapRange (· / p) (Nat.zero_div p) l) i)
            = p * K' := by
          rw [Finset.mul_sum]
          have h2 : ∀ i ∈ range ℓ, p * ((Finsupp.mapRange (· / p) (Nat.zero_div p) l) i)
              = l i := by
            intro i hi
            rw [Finsupp.mapRange_apply]
            exact Nat.mul_div_cancel' (hall i hi)
          rw [Finset.sum_congr rfl h2, hlsum, hK, hK']
          have h3 : p * p^(r-1) = p^r := by
            rw [← pow_succ']
            congr 1
            omega
          rw [← h3]
          ring
        exact Nat.eq_of_mul_eq_mul_left hp.out.pos h1
      · -- support
        exact (Finsupp.support_mapRange).trans hlsupp
      · -- goodness at level r-1
        intro i hi hdvd
        apply hlgood i hi
        rw [Finsupp.mapRange_apply] at hdvd
        obtain ⟨c, hc⟩ := hdvd
        refine ⟨c, ?_⟩
        have h3 : p * (l i / p) = l i := Nat.mul_div_cancel' (hall i hi)
        have h4 : p^r = p * p^(r-1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [h4]
        rw [← h3, hc]
        ring
    · -- backward membership
      intro l' hl'
      obtain ⟨hl'U, hl'good⟩ := Finset.mem_filter.mp hl'
      obtain ⟨hl'sum, hl'supp⟩ := Finset.mem_finsuppAntidiag.mp hl'U
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_finsuppAntidiag.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
      · -- sum
        have h1 : ∀ i ∈ range ℓ, (p • l') i = p * l' i := by
          intro i hi
          rw [Finsupp.smul_apply, smul_eq_mul]
        rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, hl'sum, hK, hK']
        have h3 : p * p^(r-1) = p^r := by
          rw [← pow_succ']
          congr 1
          omega
        rw [← h3]
        ring
      · -- support
        exact (Finsupp.support_smul).trans hl'supp
      · -- goodness at level r
        intro i hi hdvd
        apply hl'good i hi
        rw [Finsupp.smul_apply, smul_eq_mul] at hdvd
        have h4 : p^r = p * p^(r-1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [h4] at hdvd
        obtain ⟨c, hc⟩ := hdvd
        refine ⟨c, ?_⟩
        exact Nat.eq_of_mul_eq_mul_left hp.out.pos (by rw [hc]; ring)
      · -- all parts divisible by p
        intro i hi
        rw [Finsupp.smul_apply, smul_eq_mul]
        exact Dvd.intro _ rfl
    · -- left inverse
      intro l hl
      obtain ⟨hl1, hall⟩ := Finset.mem_filter.mp hl
      obtain ⟨hlU, hlgood⟩ := Finset.mem_filter.mp hl1
      obtain ⟨hlsum, hlsupp⟩ := Finset.mem_finsuppAntidiag.mp hlU
      ext i
      rw [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
      by_cases hi : i ∈ range ℓ
      · exact Nat.mul_div_cancel' (hall i hi)
      · have h5 : l i = 0 := by
          by_contra hcon
          exact hi (hlsupp (Finsupp.mem_support_iff.mpr hcon))
        rw [h5, Nat.zero_div, mul_zero]
    · -- right inverse
      intro l' hl'
      ext i
      rw [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul]
      exact Nat.mul_div_cancel_left _ hp.out.pos
    · -- summand equality
      intro l hl
      obtain ⟨hl1, hall⟩ := Finset.mem_filter.mp hl
      apply Finset.prod_congr rfl
      intro i hi
      rw [Finsupp.mapRange_apply, Nat.mul_div_cancel' (hall i hi)]
  -- the K-part valuation bound
  have hKpart : V p (3*(r:ℤ) + (padicValNat p ℓ.factorial : ℤ))
      (∑ l' ∈ U'.filter (fun l => ∀ i ∈ range ℓ, ¬ p^(r-1) ∣ l i),
        ((∏ i ∈ range ℓ, Pc p m n r (p * l' i))
          - ∏ i ∈ range ℓ, Pc p m n (r-1) (l' i))) := by
    apply V_sum
    intro l' hl'
    obtain ⟨hl'U, hl'good⟩ := Finset.mem_filter.mp hl'
    obtain ⟨hl'sum, hl'supp⟩ := Finset.mem_finsuppAntidiag.mp hl'U
    -- rule out r = 1 (no good tuples at level 0)
    rcases Nat.lt_or_ge r 2 with hr1 | hr2
    · exfalso
      have hreq : r = 1 := by omega
      rcases Nat.eq_zero_or_pos ℓ with rfl | hℓpos
      · -- ℓ = 0 : empty sum can't equal K' ≠ 0
        rw [Finset.range_zero, Finset.sum_empty] at hl'sum
        rw [hK'] at hl'sum
        have h6 : p^(r-1)*j ≠ 0 :=
          Nat.mul_ne_zero (pow_pos hp.out.pos _).ne' hj
        omega
      · exact hl'good 0 (Finset.mem_range.mpr hℓpos)
          (by rw [hreq]; simpa using one_dvd _)
    -- now r ≥ 2
    have h0 : ∀ i ∈ range ℓ, l' i ≠ 0 := by
      intro i hi hzero
      exact hl'good i hi (hzero ▸ dvd_zero _)
    have hvlt : ∀ i ∈ range ℓ, padicValNat p (l' i) < r - 1 := by
      intro i hi
      by_contra hcon
      push_neg at hcon
      exact hl'good i hi ((padicValNat_dvd_iff_le (h0 i hi)).mpr hcon)
    apply V_prod_sub_prod (a := fun i => Pc p m n r (p * l' i))
      (b := fun i => Pc p m n (r-1) (l' i))
      (w := fun i => ((r-1 : ℕ) : ℤ) - padicValNat p (l' i) + vc p m (l' i))
      (δ := fun i => 3 + 3 * (padicValNat p (l' i) : ℤ))
    · exact fun i hi => V_Pc_high hr (hl'good i hi)
    · exact fun i hi => V_Pc (hl'good i hi)
    · exact fun i hi => V_Pc_diff hp5 hr (hl'good i hi)
    · -- the K_ineq condition
      intro i hi
      have hKi := K_ineq (p := p) hp5 hm (r' := r-1) (by omega)
        (s := range ℓ) (d := ⇑l') h0 hl'good
        (by rw [hl'sum, hK']; exact dvd_mul_right _ _) (t₀ := i) hi
      rw [Finset.card_range] at hKi
      have hcast : ∀ t ∈ range ℓ,
          ((r-1 : ℕ) : ℤ) - padicValNat p (l' t) + vc p m (l' t)
          = (((r-1) - padicValNat p (l' t) : ℕ) : ℤ) + ((vc p m (l' t) : ℕ) : ℤ) := by
        intro t ht
        have := hvlt t ht
        omega
      rw [Finset.sum_congr rfl hcast, Finset.sum_add_distrib, ← Nat.cast_sum, ← Nat.cast_sum]
      have hrw : 3 * ((r-1) + 1) = 3 * r := by omega
      rw [hrw] at hKi
      omega
  -- assemble
  rw [hT, hT', hTg, hTg', hsplit, hparity, hbij]
  have hfinal : ∑ l ∈ (U.filter (fun l => ∀ i ∈ range ℓ, ¬ p^r ∣ l i)).filter
        (fun l => 2 ≤ cnum l), ∏ i ∈ range ℓ, Pc p m n r (l i)
      + ∑ l' ∈ U'.filter (fun l => ∀ i ∈ range ℓ, ¬ p^(r-1) ∣ l i),
          ∏ i ∈ range ℓ, Pc p m n r (p * l' i)
      - ∑ l ∈ U'.filter (fun l => ∀ i ∈ range ℓ, ¬ p^(r-1) ∣ l i),
          ∏ i ∈ range ℓ, Pc p m n (r-1) (l i)
      = ∑ l ∈ (U.filter (fun l => ∀ i ∈ range ℓ, ¬ p^r ∣ l i)).filter
          (fun l => 2 ≤ cnum l), ∏ i ∈ range ℓ, Pc p m n r (l i)
        + ∑ l' ∈ U'.filter (fun l => ∀ i ∈ range ℓ, ¬ p^(r-1) ∣ l i),
            ((∏ i ∈ range ℓ, Pc p m n r (p * l' i))
              - ∏ i ∈ range ℓ, Pc p m n (r-1) (l' i)) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hfinal]
  exact V_add hFpart hKpart

end

end Super

-- ===== Devel/D10.lean =====
namespace Super

open Finset PowerSeries

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## The KL ingredient -/

theorem KL (hp5 : 5 ≤ p) {m : ℕ} (hm : 3 ≤ m) {r : ℕ} (hr : 1 ≤ r) (n j : ℕ) :
    V p (3*(r:ℤ)) (coeff (p^r * j) (expS (Pser p m n r))
      - coeff (p^(r-1) * j) (expS (Pser p m n (r-1)))) := by
  rcases eq_or_ne j 0 with rfl | hj
  · have h1 : constantCoeff (expS (Pser p m n r)) = 1 := constantCoeff_expS _
    have h2 : constantCoeff (expS (Pser p m n (r-1))) = 1 := constantCoeff_expS _
    rw [mul_zero, mul_zero, coeff_zero_eq_constantCoeff, h1, h2, sub_self]
    exact V_zero_val _
  · rw [coeff_expS _ (constantCoeff_Pser _ _ _) _,
      coeff_expS _ (constantCoeff_Pser _ _ _) _]
    have hle : p^(r-1)*j + 1 ≤ p^r*j + 1 := by
      have h1 : p^(r-1) ≤ p^r := Nat.pow_le_pow_right hp.out.pos (by omega)
      have h2 : p^(r-1)*j ≤ p^r*j := Nat.mul_le_mul_right j h1
      omega
    have hsub : ∑ ℓ ∈ range (p^(r-1)*j + 1),
          ((Nat.factorial ℓ : ℚ))⁻¹ * coeff (p^(r-1)*j) ((Pser p m n (r-1)) ^ ℓ)
        = ∑ ℓ ∈ range (p^r*j + 1),
          ((Nat.factorial ℓ : ℚ))⁻¹ * coeff (p^(r-1)*j) ((Pser p m n (r-1)) ^ ℓ) := by
      apply Finset.sum_subset (Finset.range_subset_range.mpr hle)
      intro ℓ hℓ hnot
      rw [Finset.mem_range] at hℓ
      rw [Finset.mem_range, not_lt] at hnot
      rw [coeff_pow_eq_zero (constantCoeff_Pser _ _ _) (by omega), mul_zero]
    rw [hsub, ← Finset.sum_sub_distrib]
    apply V_sum
    intro ℓ hℓ
    rw [← mul_sub]
    have hf : V p (-(padicValNat p ℓ.factorial : ℤ)) ((ℓ.factorial : ℚ))⁻¹ := by
      have := V_inv_nat (p := p) ℓ.factorial_ne_zero
      rwa [one_div] at this
    have h1 := V_mul hf (KL_ell hp5 hm hr n j hj ℓ)
    apply V_mono h1
    omega

/-! ## The LV ingredient -/

theorem LV (hp5 : 5 ≤ p) (m : ℕ) {r : ℕ} (hr : 1 ≤ r) (n : ℕ) (i : ℕ) :
    V p (3*(r:ℤ)) (coeff i (expS ((n:ℕ) • Lser m (p^r)))
      - coeff i (expS ((n:ℕ) • Lser m (p^(r-1))))) := by
  set D : ℚ⟦X⟧ := (n:ℕ) • Lser m (p^r) - (n:ℕ) • Lser m (p^(r-1)) with hD
  have hD0 : constantCoeff D = 0 := by
    rw [hD, map_sub, map_nsmul, map_nsmul, constantCoeff_Lser, constantCoeff_Lser]
    simp
  have hDco : ∀ k, V p (3*(r:ℤ)) (coeff k D) := by
    intro k
    rw [hD, map_sub, map_nsmul, map_nsmul, coeff_Lser, coeff_Lser]
    rcases eq_or_ne k 0 with rfl | hk
    · rw [if_pos rfl, if_pos rfl]
      simpa using V_zero_val (p := p) _
    · rw [if_neg hk, if_neg hk, nsmul_eq_mul, nsmul_eq_mul]
      set J := k * p^(r-1) with hJ
      have hJ0 : J ≠ 0 := Nat.mul_ne_zero hk (pow_pos hp.out.pos _).ne'
      have hidx : k * p^r = p * J := by
        rw [hJ]
        have h1 : p^r = p * p^(r-1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [h1]
        ring
      have hkQ : ((k:ℚ)) ≠ 0 := by exact_mod_cast hk
      have halg : (n:ℚ) * (cQ m (k*p^r)/(k:ℚ)) - (n:ℚ) * (cQ m (k*p^(r-1))/(k:ℚ))
          = (n:ℚ) * ((1/(k:ℚ)) * (cQ m (p*J) - cQ m J)) := by
        rw [hidx, hJ]
        field_simp
      rw [halg]
      have h1 := V_nsmul (p := p) n (V_mul (V_inv_nat (p := p) hk)
        (rel_strong (p := p) hp5 m J hJ0))
      apply V_mono h1
      have hvJ : padicValNat p J = padicValNat p k + (r-1) := by
        rw [hJ, padicValNat.mul hk (pow_pos hp.out.pos _).ne',
          padicValNat.prime_pow]
      omega
  have hsplit : (n:ℕ) • Lser m (p^r) = (n:ℕ) • Lser m (p^(r-1)) + D := by
    rw [hD]
    abel
  have heq : coeff i (expS ((n:ℕ) • Lser m (p^r)))
        - coeff i (expS ((n:ℕ) • Lser m (p^(r-1))))
      = coeff i (expS ((n:ℕ) • Lser m (p^(r-1))) * (expS D - 1)) := by
    rw [← map_sub]
    congr 1
    rw [mul_sub, mul_one, ← expS_add, ← hsplit]
  rw [heq]
  have htail : ∀ jj, V p (3*(r:ℤ)) (coeff jj (expS D - 1)) := by
    intro jj
    rw [map_sub]
    rcases eq_or_ne jj 0 with rfl | hjj
    · rw [coeff_zero_eq_constantCoeff, constantCoeff_expS, map_one, sub_self]
      exact V_zero_val _
    · rw [coeff_one, if_neg hjj, sub_zero]
      exact exp_tail (by omega) hD0 hDco hjj
  have hint : ∀ jj, V p 0 (coeff jj (expS ((n:ℕ) • Lser m (p^(r-1))))) :=
    integral_expS_NL m (p^(r-1)) n (pow_pos hp.out.pos _).ne'
  have := V_coeff_mul hint htail i
  simpa using this

/-! ## Integrality of the coefficients of `expS (Pser)` -/

theorem V_coeff_div {G H W : ℚ⟦X⟧} (hGH : G * H = W) (hG0 : constantCoeff G = 1)
    (hG : ∀ j, V p 0 (coeff j G)) (hW : ∀ j, V p 0 (coeff j W)) (j : ℕ) :
    V p 0 (coeff j H) := by
  induction j using Nat.strong_induction_on with
  | _ j IH =>
  have h1 : coeff j W = ∑ i ∈ Finset.range (j+1), coeff i G * coeff (j - i) H := by
    rw [← hGH, coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => coeff x G * coeff y H)]
  rw [Finset.sum_range_succ'] at h1
  have h2 : coeff 0 G * coeff (j - 0) H = coeff j H := by
    rw [coeff_zero_eq_constantCoeff, hG0, one_mul, Nat.sub_zero]
  rw [h2] at h1
  have h3 : coeff j H
      = coeff j W - ∑ i ∈ Finset.range j, coeff (i+1) G * coeff (j - (i+1)) H := by
    linarith
  rw [h3]
  apply V_sub (hW j)
  apply V_sum
  intro i hi
  rw [Finset.mem_range] at hi
  have := V_mul (hG (i+1)) (IH (j - (i+1)) (by omega))
  simpa using this

theorem INT_E (m n ρ k : ℕ) : V p 0 (coeff k (expS (Pser p m n ρ))) := by
  have hpρ : (p^ρ : ℕ) ≠ 0 := (pow_pos hp.out.pos _).ne'
  apply V_coeff_div
    (G := PowerSeries.expand (p^ρ) (pow_ne_zero ρ hp.out.ne_zero)
      (expS ((n:ℕ) • Lser m (p^ρ))))
    (W := expS ((n * p^ρ : ℕ) • Lser m 1))
  · rw [mul_comm]
    exact (master_identity (p := p) m n ρ).symm
  · rw [constantCoeff_expand, constantCoeff_expS]
  · intro jj
    rw [coeff_expand]
    split
    · exact integral_expS_NL m (p^ρ) n hpρ _
    · exact V_zero_val _
  · intro jj
    exact integral_expS_NL m 1 (n * p^ρ) one_ne_zero jj

/-! ## The boundary convolution formula -/

theorem coeff_mul_expand {t : ℕ} (ht : t ≠ 0) (E A : ℚ⟦X⟧) (n : ℕ) :
    coeff (n*t) (E * PowerSeries.expand t ht A)
      = ∑ w ∈ range (n+1), coeff (n*t - t*w) E * coeff w A := by
  rw [coeff_mul]
  have hswap : ∑ x ∈ Finset.antidiagonal (n*t),
        coeff x.1 E * coeff x.2 (PowerSeries.expand t ht A)
      = ∑ x ∈ Finset.antidiagonal (n*t),
        coeff x.2 E * coeff x.1 (PowerSeries.expand t ht A) := by
    rw [← Finset.Nat.sum_antidiagonal_swap
      (f := fun x => coeff x.2 E * coeff x.1 (PowerSeries.expand t ht A))]
    apply Finset.sum_congr rfl
    intro x hx
    rfl
  rw [hswap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun u v => coeff v E * coeff u (PowerSeries.expand t ht A))]
  have hzero : ∀ u, ¬ t ∣ u →
      coeff (n*t - u) E * coeff u (PowerSeries.expand t ht A) = 0 := by
    intro u hu
    rw [coeff_expand_of_not_dvd t ht A hu, mul_zero]
  have hext : ∑ u ∈ range (n*t + 1),
        coeff (n*t - u) E * coeff u (PowerSeries.expand t ht A)
      = ∑ u ∈ range (t * (n+1)),
        coeff (n*t - u) E * coeff u (PowerSeries.expand t ht A) := by
    apply Finset.sum_subset
    · apply Finset.range_subset_range.mpr
      have h0 : 0 < t := Nat.pos_of_ne_zero ht
      have h1 : t*(n+1) = n*t + t := by ring
      omega
    · intro u hu hnot
      rw [Finset.mem_range] at hu
      rw [Finset.mem_range, not_lt] at hnot
      apply hzero
      intro hdvd
      obtain ⟨c, hc⟩ := hdvd
      -- n*t < u < t*(n+1), u = t*c : impossible
      have h1 : n < c := by
        by_contra hcon
        push_neg at hcon
        have : u ≤ n * t := by
          rw [hc]
          calc t * c ≤ t * n := Nat.mul_le_mul_left t hcon
          _ = n * t := by ring
        omega
      have h2 : u ≥ t * (n+1) := by
        rw [hc]
        exact Nat.mul_le_mul_left t h1
      omega
  rw [hext, sum_dilate₀ ht (n+1) _ (fun u hu => hzero u hu)]
  apply Finset.sum_congr rfl
  intro w hw
  rw [coeff_expand_mul]

/-! ## The main congruence, for `m ≥ 3` -/

theorem main_m3 (hp5 : 5 ≤ p) {m : ℕ} (hm : 3 ≤ m) {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    V p (3*(r:ℤ))
      (coeff (n * p^r) (expS ((n * p^r : ℕ) • Lser m 1))
        - coeff (n * p^(r-1)) (expS ((n * p^(r-1) : ℕ) • Lser m 1))) := by
  have hb : ∀ ρ : ℕ, coeff (n * p^ρ) (expS ((n * p^ρ : ℕ) • Lser m 1))
      = ∑ w ∈ range (n+1),
          coeff (n*p^ρ - p^ρ*w) (expS (Pser p m n ρ))
            * coeff w (expS ((n:ℕ) • Lser m (p^ρ))) := by
    intro ρ
    rw [master_identity (p := p) m n ρ,
      coeff_mul_expand (pow_ne_zero ρ hp.out.ne_zero)]
  rw [hb r, hb (r-1), ← Finset.sum_sub_distrib]
  apply V_sum
  intro w hw
  have halg : ∀ a b c d : ℚ, a * b - c * d = (a - c) * b + c * (b - d) := by
    intro a b c d
    ring
  rw [halg]
  apply V_add
  · -- KL × INT-A
    have hidx : ∀ ρ : ℕ, n*p^ρ - p^ρ*w = p^ρ*(n-w) := by
      intro ρ
      rw [Nat.mul_sub]
      ring_nf
    rw [hidx r, hidx (r-1)]
    have h1 := V_mul (KL hp5 hm hr n (n-w))
      (integral_expS_NL m (p^r) n (pow_pos hp.out.pos _).ne' w)
    simpa using h1
  · -- INT-E × LV
    have h1 := V_mul (INT_E m n (r-1) (n*p^(r-1) - p^(r-1)*w)) (LV hp5 m hr n w)
    simpa using h1

end

end Super

-- ===== Devel/D11.lean =====
namespace Super

open Finset PowerSeries

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## The shared Kazandzidis difference lemma -/

theorem choose_diff (hp5 : 5 ≤ p) {r n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n)
    (i : ℕ) :
    V p (3*(r:ℤ)) ((((1+i)*(n*p^r)).choose (n*p^r) : ℚ)
      - (((1+i)*(n*p^(r-1))).choose (n*p^(r-1)) : ℚ)) := by
  set b := n*p^(r-1) with hb
  have hb1 : 1 ≤ b := by
    have := pow_pos hp.out.pos (r-1)
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hbp : b * p = n * p^r := by
    rw [hb, mul_assoc, ← pow_succ]
    congr 2
    omega
  have hvb : r ≤ padicValNat p (b*p) := by
    rw [hbp, padicValNat.mul (by omega) (pow_pos hp.out.pos r).ne',
      padicValNat.prime_pow]
    omega
  have hvc : V p ((r:ℕ):ℤ) (((i*b : ℕ):ℚ) * (p:ℚ)) := by
    have hcast : ((i*b : ℕ):ℚ) * (p:ℚ) = ((i*b*p : ℕ) : ℚ) := by push_cast; ring
    rw [hcast, V_nat_iff_dvd]
    refine ⟨i*n, ?_⟩
    have h5 : i*b*p = (b*p)*i := by ring
    rw [h5, hbp]
    ring
  have hk := kaz_strong (p := p) hp5 hb1 hvb hvc
  have hC0 : (((b+i*b).choose b : ℕ):ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show b ≤ b+i*b by omega)).ne'
  have h2 := V_mul hk (V_nat (p := p) ((b+i*b).choose b))
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hC0, add_zero] at h2
  have he1 : (b+i*b)*p = (1+i)*(n*p^r) := by
    rw [← hbp]
    ring
  have he2 : b + i*b = (1+i)*(n*p^(r-1)) := by
    rw [hb]
    ring
  have he3 : b*p = n*p^r := hbp
  rw [he1, he2, he3] at h2
  rw [← hb] at h2
  exact h2

/-! ## The `m = 1` closed form -/

/-- The geometric series `1/(1-X)`. -/
def c1S : ℚ⟦X⟧ := mk fun _ => (1:ℚ)

@[simp] theorem coeff_c1S (k : ℕ) : coeff k c1S = 1 := coeff_mk _ _

theorem constantCoeff_c1S : constantCoeff c1S = 1 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_c1S]

theorem c1S_eq : c1S = 1 + X * c1S := by
  ext k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [coeff_c1S, map_add, coeff_one, if_pos rfl, coeff_zero_eq_constantCoeff,
      map_mul, constantCoeff_X, zero_mul, add_zero]
  · obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩
    rw [coeff_c1S, map_add, coeff_one, if_neg (by omega), coeff_succ_X_mul, coeff_c1S]
    norm_num

theorem cQ_one (k : ℕ) : cQ 1 k = 1 := by
  rw [cQ, one_mul, pow_one]
  exact div_self (by exact_mod_cast k.factorial_ne_zero)

theorem d_c1S : d⁄dX ℚ c1S = c1S^2 := by
  ext k
  rw [coeff_derivative, coeff_c1S, pow_two, coeff_mul]
  have h1 : ∀ x ∈ Finset.antidiagonal k, coeff x.1 c1S * coeff x.2 c1S = 1 := by
    intro x hx
    rw [coeff_c1S, coeff_c1S, mul_one]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.Nat.card_antidiagonal]
  push_cast
  ring

theorem dL1 (N : ℕ) : d⁄dX ℚ ((N:ℕ) • Lser 1 1) = (N:ℕ) • c1S := by
  ext k
  rw [coeff_derivative, map_nsmul, map_nsmul, coeff_Lser, coeff_c1S, if_neg (by omega)]
  rw [nsmul_eq_mul, nsmul_eq_mul, mul_one]
  rw [cQ_one]
  have hk1 : ((k+1 : ℕ):ℚ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

theorem expS_m1 {N : ℕ} (hN : 1 ≤ N) : expS ((N:ℕ) • Lser 1 1) = c1S ^ N := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M+1 := ⟨N-1, by omega⟩
  symm
  apply IsExpOf.eq_expS
  rw [isExpOf_iff_deriv]
  constructor
  · rw [map_pow, constantCoeff_c1S, one_pow]
  · rw [dL1, deriv_pow, d_c1S, nsmul_eq_mul, smul_eq_C_mul,
      ← map_natCast (C : ℚ →+* ℚ⟦X⟧) (M+1)]
    ring

theorem coeff_c1S_pow (j k : ℕ) : coeff k (c1S^(j+1)) = (((j + k).choose k : ℕ) : ℚ) := by
  have hrel : ∀ j' : ℕ, c1S^(j'+1) = c1S^j' + X * c1S^(j'+1) := by
    intro j'
    have h := c1S_eq
    calc c1S^(j'+1) = c1S^j' * c1S := by rw [pow_succ]
    _ = c1S^j' * (1 + X * c1S) := by rw [← h]
    _ = c1S^j' + X * (c1S^j' * c1S) := by ring
    _ = c1S^j' + X * c1S^(j'+1) := by rw [← pow_succ]
  induction j generalizing k with
  | zero =>
    rw [pow_one, coeff_c1S, Nat.zero_add, Nat.choose_self, Nat.cast_one]
  | succ j ihj =>
    induction k with
    | zero =>
      rw [coeff_zero_eq_constantCoeff, map_pow, constantCoeff_c1S, one_pow,
        Nat.add_zero, Nat.choose_zero_right, Nat.cast_one]
    | succ k ihk =>
      rw [hrel (j+1)]
      rw [map_add, coeff_succ_X_mul, ihj (k+1), ihk]
      have : (j + (k+1)).choose (k+1) + (j + 1 + k).choose k
          = (j + 1 + (k+1)).choose (k+1) := by
        have h1 : j + 1 + (k+1) = (j + k + 1) + 1 := by omega
        have h2 : j + (k+1) = j + k + 1 := by omega
        have h3 : j + 1 + k = j + k + 1 := by omega
        rw [h1, h2, h3]
        conv_rhs => rw [Nat.choose_succ_succ]
        simp only [Nat.succ_eq_add_one]
        omega
      rw [← this]
      push_cast
      ring

theorem b1_closed {M : ℕ} (hM : 1 ≤ M) :
    coeff M (expS ((M:ℕ) • Lser 1 1)) = (((2*M).choose M : ℕ) : ℚ) / 2 := by
  rw [expS_m1 hM]
  obtain ⟨M', rfl⟩ : ∃ M', M = M'+1 := ⟨M-1, by omega⟩
  rw [coeff_c1S_pow]
  have hnat : (2*(M'+1)).choose (M'+1) = 2 * ((M' + (M'+1)).choose (M'+1)) := by
    have h1 : 2*(M'+1) = (2*M'+1) + 1 := by omega
    rw [h1, Nat.choose_succ_succ]
    have h2 : (2*M'+1).choose M' = (2*M'+1).choose (M'+1) := by
      have h3 := Nat.choose_symm (show M'+1 ≤ 2*M'+1 by omega)
      rw [show 2*M'+1 - (M'+1) = M' by omega] at h3
      exact h3
    have h4 : M' + (M'+1) = 2*M'+1 := by omega
    rw [h4, h2]
    simp only [Nat.succ_eq_add_one]
    omega
  rw [eq_div_iff (by norm_num : (2:ℚ) ≠ 0)]
  rw [show ((((2*(M'+1)).choose (M'+1) : ℕ)) : ℚ) = ((2 * ((M' + (M'+1)).choose (M'+1)) : ℕ) : ℚ) by rw [← hnat]]
  push_cast
  ring

theorem main_m1 (hp5 : 5 ≤ p) {r : ℕ} (hr : 1 ≤ r) {n : ℕ} (hn : 1 ≤ n) :
    V p (3*(r:ℤ))
      (coeff (n * p^r) (expS ((n * p^r : ℕ) • Lser 1 1))
        - coeff (n * p^(r-1)) (expS ((n * p^(r-1) : ℕ) • Lser 1 1))) := by
  have hM1 : 1 ≤ n * p^r := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (pow_pos hp.out.pos r).ne')
  have hM2 : 1 ≤ n * p^(r-1) := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (pow_pos hp.out.pos (r-1)).ne')
  rw [b1_closed hM1, b1_closed hM2, div_sub_div_same]
  have h2 : V p 0 (1 / ((2:ℕ):ℚ)) := V_inv_unit (by omega)
    (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  have hd := choose_diff (p := p) hp5 hr hn 1
  have h3 := V_mul hd h2
  rw [add_zero] at h3
  have halg : ((((2*(n*p^r)).choose (n*p^r) : ℕ) : ℚ)
        - (((2*(n*p^(r-1))).choose (n*p^(r-1)) : ℕ) : ℚ)) / 2
      = ((((1+1)*(n*p^r)).choose (n*p^r) : ℚ)
        - (((1+1)*(n*p^(r-1))).choose (n*p^(r-1)) : ℚ)) * (1/((2:ℕ):ℚ)) := by
    rw [show (1+1)*(n*p^r) = 2*(n*p^r) from by ring,
        show (1+1)*(n*p^(r-1)) = 2*(n*p^(r-1)) from by ring]
    push_cast
    ring
  rw [halg]
  exact h3

end

end Super

-- ===== Devel/D12.lean =====
namespace Super

open Finset PowerSeries

noncomputable section

variable {p : ℕ}

/-! ## The Catalan and central binomial series -/

def CatQ : ℚ⟦X⟧ := mk fun k => (catalan k : ℚ)

def fSer : ℚ⟦X⟧ := mk fun k => (Nat.centralBinom k : ℚ)

def hSer : ℚ⟦X⟧ := mk fun k => (Nat.centralBinom (k+1) : ℚ)

def Rser (j : ℕ) : ℚ⟦X⟧ := mk fun k => (((2*k+j).choose k : ℕ) : ℚ)

@[simp] theorem coeff_CatQ (k : ℕ) : coeff k CatQ = (catalan k : ℚ) := coeff_mk _ _
@[simp] theorem coeff_fSer (k : ℕ) : coeff k fSer = (Nat.centralBinom k : ℚ) := coeff_mk _ _
@[simp] theorem coeff_hSer (k : ℕ) : coeff k hSer = (Nat.centralBinom (k+1) : ℚ) := coeff_mk _ _
@[simp] theorem coeff_Rser (j k : ℕ) : coeff k (Rser j) = (((2*k+j).choose k : ℕ) : ℚ) :=
  coeff_mk _ _

theorem constantCoeff_CatQ : constantCoeff CatQ = 1 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_CatQ, catalan_zero, Nat.cast_one]

theorem CatQ_eq : CatQ = 1 + X * CatQ^2 := by
  ext k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [coeff_CatQ, catalan_zero, map_add, coeff_one, if_pos rfl,
      coeff_zero_eq_constantCoeff, map_mul, constantCoeff_X, zero_mul, add_zero,
      Nat.cast_one]
  · obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩
    rw [coeff_CatQ, map_add, coeff_one, if_neg (by omega), coeff_succ_X_mul, zero_add]
    rw [pow_two, coeff_mul, catalan_succ']
    push_cast
    apply Finset.sum_congr rfl
    intro x hx
    rw [coeff_CatQ, coeff_CatQ]

theorem one_sub_ne_zero : (1 - 2*X*CatQ : ℚ⟦X⟧) ≠ 0 := by
  intro h
  have h1 : constantCoeff (1 - 2*X*CatQ : ℚ⟦X⟧) = 1 := by
    rw [map_sub, map_one, map_mul, map_mul, constantCoeff_X, mul_zero, zero_mul,
      sub_zero]
  rw [h, map_zero] at h1
  norm_num at h1

theorem one_sub4_ne_zero : (1 - 4*X : ℚ⟦X⟧) ≠ 0 := by
  intro h
  have h1 : constantCoeff (1 - 4*X : ℚ⟦X⟧) = 1 := by
    rw [map_sub, map_one, map_mul, constantCoeff_X, mul_zero, sub_zero]
  rw [h, map_zero] at h1
  norm_num at h1

theorem hCu : CatQ - X*CatQ^2 = 1 := by
  linear_combination CatQ_eq

theorem key1 : (1 - 2*X*CatQ : ℚ⟦X⟧)^2 = 1 - 4*X := by
  linear_combination (-4*(X : ℚ⟦X⟧)) * CatQ_eq

/-! ## Derivative relations -/

theorem dCat_rel : (d⁄dX ℚ CatQ) * (1 - 2*X*CatQ) = CatQ^2 := by
  have h := congrArg (d⁄dX ℚ) CatQ_eq
  rw [map_add, Derivation.map_one_eq_zero, zero_add, Derivation.leibniz,
    smul_eq_mul, smul_eq_mul, deriv_pow, derivative_X, mul_one] at h
  rw [smul_eq_C_mul, map_natCast (C : ℚ →+* ℚ⟦X⟧) (1+1)] at h
  -- h : d CatQ = X * (↑(1+1) * (d CatQ * CatQ^1)) + CatQ^2
  have h2 : ((1+1 : ℕ) : ℚ⟦X⟧) = 2 := by norm_num
  rw [h2, pow_one] at h
  linear_combination h

theorem fS_ODE : (1 - 4*X) * d⁄dX ℚ fSer = 2 * fSer := by
  have hexp : (1 - 4*X) * d⁄dX ℚ fSer
      = d⁄dX ℚ fSer - (4:ℚ) • (X * d⁄dX ℚ fSer) := by
    rw [smul_eq_C_mul, map_ofNat]
    ring
  have h2S : (2 : ℚ⟦X⟧) * fSer = (2:ℚ) • fSer := by
    rw [smul_eq_C_mul, map_ofNat]
  rw [hexp, h2S]
  ext k
  rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, coeff_derivative,
    coeff_fSer]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hX0 : coeff 0 (X * d⁄dX ℚ fSer) = 0 := by
      rw [coeff_zero_eq_constantCoeff, map_mul, constantCoeff_X, zero_mul]
    rw [hX0, mul_zero, sub_zero, coeff_fSer]
    have h1 : Nat.centralBinom 1 = 2 := by
      rw [Nat.centralBinom_eq_two_mul_choose]
      norm_num
    have h0 : Nat.centralBinom 0 = 1 := Nat.centralBinom_zero
    rw [h1, h0]
    norm_num
  · obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩
    simp only [coeff_succ_X_mul, coeff_derivative, coeff_fSer]
    have h := Nat.succ_mul_centralBinom_succ (k'+1)
    have hcast : (((k'+1+1) * Nat.centralBinom (k'+1+1) : ℕ) : ℚ)
        = ((2*(2*(k'+1)+1) * Nat.centralBinom (k'+1) : ℕ) : ℚ) :=
      congrArg (Nat.cast : ℕ → ℚ) h
    push_cast at hcast ⊢
    linear_combination hcast

/-! ## The key relation `fSer * (1 - 2X·Cat) = 1` -/

theorem du_zero : d⁄dX ℚ (fSer * (1 - 2*X*CatQ)) = 0 := by
  have hd2X : d⁄dX ℚ (2*X : ℚ⟦X⟧) = 2 := by
    rw [two_mul, map_add, derivative_X]
    norm_num
  have hdu : d⁄dX ℚ (fSer * (1 - 2*X*CatQ))
      = fSer * (-(2*X*(d⁄dX ℚ CatQ)) - 2*CatQ)
        + (1 - 2*X*CatQ) * d⁄dX ℚ fSer := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    congr 1
    rw [map_sub, Derivation.map_one_eq_zero, zero_sub]
    rw [show (2*X*CatQ : ℚ⟦X⟧) = (2*X)*CatQ from rfl, Derivation.leibniz,
      smul_eq_mul, smul_eq_mul, hd2X]
    ring
  have e1 : (1 - 4*X) * d⁄dX ℚ fSer = 2 * fSer := fS_ODE
  have hz : (1-4*X) * ((1-2*X*CatQ) * d⁄dX ℚ (fSer * (1 - 2*X*CatQ))) = 0 := by
    rw [hdu]
    linear_combination ((1-2*X*CatQ)^2) * e1 + (-(2*X*fSer*(1-4*X))) * dCat_rel
      + (2*fSer) * key1 + (-(2*fSer*(1-4*X))) * hCu
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd h one_sub4_ne_zero
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' one_sub_ne_zero
  · exact h'

theorem key2 : fSer * (1 - 2*X*CatQ) = 1 := by
  ext k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [coeff_zero_eq_constantCoeff, map_mul, map_sub, map_one, map_mul, map_mul,
      constantCoeff_X, mul_zero, zero_mul, sub_zero, mul_one]
    rw [← coeff_zero_eq_constantCoeff, coeff_fSer, Nat.centralBinom_zero, Nat.cast_one]
  · obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩
    have h1 : coeff k' (d⁄dX ℚ (fSer * (1 - 2*X*CatQ))) = 0 := by
      rw [du_zero, map_zero]
    rw [coeff_derivative] at h1
    have h2 : ((k' : ℚ) + 1) ≠ 0 := by positivity
    have h3 : coeff (k'+1) (fSer * (1 - 2*X*CatQ)) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h h2
    rw [h3, coeff_one, if_neg (by omega)]

/-! ## The ballot-number identification -/

theorem hRpascal (j : ℕ) : Rser (j+1) = Rser j + X * Rser (j+2) := by
  ext k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [coeff_Rser, map_add, coeff_Rser, coeff_zero_eq_constantCoeff, map_mul,
      constantCoeff_X, zero_mul, add_zero]
    norm_num
  · obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩
    rw [coeff_Rser, map_add, coeff_Rser, coeff_succ_X_mul, coeff_Rser]
    have h1 : 2*(k'+1)+(j+1) = (2*k'+j+2)+1 := by omega
    have h2 : 2*(k'+1)+j = 2*k'+j+2 := by omega
    have h3 : 2*k'+(j+2) = 2*k'+j+2 := by omega
    rw [h1, h2, h3]
    have h4 := Nat.choose_succ_succ (2*k'+j+2) k'
    push_cast [h4]
    ring

theorem hL3 (j : ℕ) : fSer*CatQ^(j+1) = fSer*CatQ^j + X*(fSer*CatQ^(j+2)) := by
  linear_combination (fSer*CatQ^j) * CatQ_eq

theorem base0 : fSer * CatQ^0 = Rser 0 := by
  rw [pow_zero, mul_one]
  ext k
  rw [coeff_fSer, coeff_Rser, Nat.centralBinom_eq_two_mul_choose, Nat.add_zero]

theorem base1 : fSer * CatQ^1 = Rser 1 := by
  have hf2 : fSer = 1 + 2*(X*(fSer*CatQ)) := by
    linear_combination key2
  ext k
  rw [pow_one, coeff_Rser]
  have h5 := congrArg (fun φ => coeff (k+1) φ) hf2
  simp only [map_add, coeff_one, if_neg (Nat.succ_ne_zero k), zero_add] at h5
  rw [coeff_fSer] at h5
  have h6 : coeff (k+1) (2*(X*(fSer*CatQ))) = 2 * coeff k (fSer*CatQ) := by
    have h7 : (2 : ℚ⟦X⟧) * (X*(fSer*CatQ)) = (2:ℚ) • (X*(fSer*CatQ)) := by
      rw [smul_eq_C_mul, map_ofNat]
    rw [h7, map_smul, smul_eq_mul, coeff_succ_X_mul]
  rw [h6] at h5
  -- ℕ identity: centralBinom (k+1) = 2 * (2k+1).choose k
  have hnat : Nat.centralBinom (k+1) = 2 * ((2*k+1).choose k) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    have e1 : 2*(k+1) = (2*k+1)+1 := by omega
    rw [e1, Nat.choose_succ_succ]
    have e2 : (2*k+1).choose (k+1) = (2*k+1).choose k := by
      have h3 := Nat.choose_symm (show k+1 ≤ 2*k+1 by omega)
      rw [show 2*k+1 - (k+1) = k by omega] at h3
      exact h3.symm
    rw [e2]
    omega
  rw [hnat] at h5
  push_cast at h5
  linarith

theorem hLR (j : ℕ) : fSer*CatQ^j = Rser j := by
  have hpair : ∀ j : ℕ, fSer*CatQ^j = Rser j ∧ fSer*CatQ^(j+1) = Rser (j+1) := by
    intro j
    induction j with
    | zero => exact ⟨base0, base1⟩
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have h1 : X*(fSer*CatQ^(j+2)) = X*(Rser (j+2)) := by
        linear_combination (-1 : ℚ⟦X⟧)*(hL3 j) + (hRpascal j) + ih.2 - ih.1
      exact mul_left_cancel₀ X_ne_zero h1
  exact (hpair j).1

theorem hCR (j : ℕ) : CatQ^j = Rser j - 2*(X * Rser (j+1)) := by
  have h1 : CatQ^j = fSer*CatQ^j - 2*(X*(fSer*CatQ^(j+1))) := by
    calc CatQ^j = CatQ^j * (fSer*(1-2*X*CatQ)) := by rw [key2, mul_one]
    _ = fSer*CatQ^j - 2*(X*(fSer*(CatQ^j*CatQ))) := by ring
    _ = fSer*CatQ^j - 2*(X*(fSer*CatQ^(j+1))) := by rw [← pow_succ]
  rw [h1, hLR j, hLR (j+1)]

/-! ## Exponential identification for `m = 2` -/

theorem cQ_two (k : ℕ) : cQ 2 k = (Nat.centralBinom k : ℚ) := by
  rw [cQ]
  have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2*k by omega)
  rw [show 2*k - k = k by omega] at h
  have hcast : ((2*k).factorial : ℚ) = ((2*k).choose k : ℚ) * (k.factorial : ℚ)
      * (k.factorial : ℚ) := by exact_mod_cast h.symm
  rw [hcast, Nat.centralBinom_eq_two_mul_choose]
  have hf : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

theorem hXh : X * hSer = fSer - 1 := by
  ext k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [map_sub, coeff_fSer, coeff_one, if_pos rfl, Nat.centralBinom_zero,
      coeff_zero_eq_constantCoeff, map_mul, constantCoeff_X, zero_mul]
    norm_num
  · obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩
    rw [coeff_succ_X_mul, coeff_hSer, map_sub, coeff_fSer, coeff_one,
      if_neg (by omega), sub_zero]

theorem key3 : 2 * (d⁄dX ℚ CatQ) = hSer * CatQ := by
  have h1 : (X * (2*(d⁄dX ℚ CatQ))) * (1-2*X*CatQ)
      = (X*(hSer*CatQ)) * (1-2*X*CatQ) := by
    linear_combination (2*(X:ℚ⟦X⟧)) * dCat_rel + (-(CatQ*(1-2*X*CatQ))) * hXh
      + (-CatQ) * key2
  have h2 := mul_right_cancel₀ one_sub_ne_zero h1
  exact mul_left_cancel₀ X_ne_zero h2

theorem dL2 (N : ℕ) : d⁄dX ℚ ((N:ℕ) • Lser 2 1) = (N:ℕ) • hSer := by
  ext k
  rw [coeff_derivative, map_nsmul, map_nsmul, coeff_Lser, coeff_hSer,
    if_neg (by omega)]
  rw [nsmul_eq_mul, nsmul_eq_mul, mul_one, cQ_two]
  have hk1 : ((k+1 : ℕ):ℚ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

theorem expS_m2 {N : ℕ} (hN : 1 ≤ N) : expS ((N:ℕ) • Lser 2 1) = CatQ ^ (2*N) := by
  obtain ⟨M, hM⟩ : ∃ M, 2*N = M+1 := ⟨2*N-1, by omega⟩
  symm
  apply IsExpOf.eq_expS
  rw [isExpOf_iff_deriv]
  constructor
  · rw [map_pow, constantCoeff_CatQ, one_pow]
  · rw [dL2, hM, deriv_pow, nsmul_eq_mul, smul_eq_C_mul,
      map_natCast (C : ℚ →+* ℚ⟦X⟧) (M+1)]
    -- goal : ↑(M+1) * (d CatQ * CatQ^M) = ↑N * hSer * CatQ^(M+1)
    have hcast : ((M+1 : ℕ) : ℚ⟦X⟧) = 2*((N:ℕ) : ℚ⟦X⟧) := by
      rw [show (M+1 : ℕ) = 2*N from hM.symm]
      push_cast
      ring
    rw [hcast]
    have h3 : ((N:ℕ) : ℚ⟦X⟧) * hSer * CatQ^(M+1)
        = ((N:ℕ) : ℚ⟦X⟧) * ((hSer * CatQ) * CatQ^M) := by
      ring
    rw [h3, ← key3]
    ring

theorem b2_closed {M : ℕ} (hM : 1 ≤ M) :
    coeff M (expS ((M:ℕ) • Lser 2 1)) = (((4*M).choose M : ℕ) : ℚ) / 2 := by
  rw [expS_m2 hM, hCR (2*M)]
  obtain ⟨M', rfl⟩ : ∃ M', M = M'+1 := ⟨M-1, by omega⟩
  have h6 : coeff (M'+1) (2*(X * Rser (2*(M'+1)+1)))
      = 2 * coeff M' (Rser (2*(M'+1)+1)) := by
    have h7 : (2 : ℚ⟦X⟧) * (X * Rser (2*(M'+1)+1))
        = (2:ℚ) • (X * Rser (2*(M'+1)+1)) := by
      rw [smul_eq_C_mul, map_ofNat]
    rw [h7, map_smul, smul_eq_mul, coeff_succ_X_mul]
  rw [map_sub, h6, coeff_Rser, coeff_Rser]
  have e1 : 2*(M'+1)+2*(M'+1) = 4*(M'+1) := by omega
  have e2 : 2*M'+(2*(M'+1)+1) = 4*(M'+1)-1 := by omega
  rw [e1, e2]
  -- ℕ identity : 4 * C(4M-1, M-1) = C(4M, M)
  have hnat : 4 * ((4*(M'+1)-1).choose M') = (4*(M'+1)).choose (M'+1) := by
    have h := Nat.add_one_mul_choose_eq (4*(M'+1)-1) M'
    -- (4M-1+1) * C(4M-1, M') = C(4M, M'+1) * (M'+1)
    rw [show 4*(M'+1)-1+1 = 4*(M'+1) by omega] at h
    have h8 : (M'+1) * (4 * ((4*(M'+1)-1).choose M'))
        = (M'+1) * ((4*(M'+1)).choose (M'+1)) := by
      calc (M'+1) * (4 * ((4*(M'+1)-1).choose M'))
          = (4*(M'+1)) * ((4*(M'+1)-1).choose M') := by ring
      _ = (4*(M'+1)).choose (M'+1) * (M'+1) := h
      _ = (M'+1) * ((4*(M'+1)).choose (M'+1)) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h8
  have hcastn : (((4*(M'+1)-1).choose M' : ℕ) : ℚ)
      = (((4*(M'+1)).choose (M'+1) : ℕ) : ℚ) / 4 := by
    have h9 : ((4 * ((4*(M'+1)-1).choose M') : ℕ) : ℚ)
        = (((4*(M'+1)).choose (M'+1) : ℕ) : ℚ) := congrArg (Nat.cast : ℕ → ℚ) hnat
    push_cast at h9
    rw [eq_div_iff (by norm_num : (4:ℚ) ≠ 0)]
    linarith
  rw [hcastn]
  ring

theorem main_m2 (hp5 : 5 ≤ p) [hp : Fact p.Prime] {r : ℕ} (hr : 1 ≤ r) {n : ℕ}
    (hn : 1 ≤ n) :
    V p (3*(r:ℤ))
      (coeff (n * p^r) (expS ((n * p^r : ℕ) • Lser 2 1))
        - coeff (n * p^(r-1)) (expS ((n * p^(r-1) : ℕ) • Lser 2 1))) := by
  have hM1 : 1 ≤ n * p^r := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (pow_pos hp.out.pos r).ne')
  have hM2 : 1 ≤ n * p^(r-1) := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (pow_pos hp.out.pos (r-1)).ne')
  rw [b2_closed hM1, b2_closed hM2, div_sub_div_same]
  have h2 : V p 0 (1 / ((2:ℕ):ℚ)) := V_inv_unit (by omega)
    (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  have hd := choose_diff (p := p) hp5 hr hn 3
  have h3 := V_mul hd h2
  rw [add_zero] at h3
  have halg : ((((4*(n*p^r)).choose (n*p^r) : ℕ) : ℚ)
        - (((4*(n*p^(r-1))).choose (n*p^(r-1)) : ℕ) : ℚ)) / 2
      = ((((1+3)*(n*p^r)).choose (n*p^r) : ℚ)
        - (((1+3)*(n*p^(r-1))).choose (n*p^(r-1)) : ℚ)) * (1/((2:ℕ):ℚ)) := by
    rw [show (1+3)*(n*p^r) = 4*(n*p^r) from by ring,
        show (1+3)*(n*p^(r-1)) = 4*(n*p^(r-1)) from by ring]
    push_cast
    ring
  rw [halg]
  exact h3

end

end Super

-- ===== Devel/D13.lean =====
namespace Super

open Finset PowerSeries

noncomputable section

variable {p : ℕ}

/-! ## The natural-number recursion (mirror of `generalized_exp_coeff`) -/

noncomputable def gec (d : ℕ → ℕ) : ℕ → ℕ
| 0 => 1
| k' + 1 =>
  let k := k' + 1
  (Finset.sum (Finset.range k) fun j =>
    (d (j + 1)) * (gec d (k - (j + 1)))) / k

theorem gec_zero (d : ℕ → ℕ) : gec d 0 = 1 := by rw [gec]

theorem gec_succ (d : ℕ → ℕ) (k' : ℕ) :
    gec d (k' + 1)
      = (Finset.sum (Finset.range (k' + 1)) fun j =>
          (d (j + 1)) * (gec d (k' + 1 - (j + 1)))) / (k' + 1) := by
  rw [gec]

/-! ## Identification with the coefficients of `expS (N • Lser m 1)` -/

theorem gec_eq_coeff (m N k : ℕ) :
    ((gec (fun i => N * cN m i) k : ℕ) : ℚ)
      = coeff k (expS ((N : ℕ) • Lser m 1)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 =>
      rw [gec_zero, coeff_zero_eq_constantCoeff, constantCoeff_expS, Nat.cast_one]
    | k' + 1 =>
      obtain ⟨b, hb⟩ := coeff_expS_NL_nat m 1 N one_ne_zero (k' + 1)
      have hrec := (isExpOf_expS ((N : ℕ) • Lser m 1)).2 k'
      have hterm : ∀ j ∈ Finset.range (k' + 1),
          (((j + 1 : ℕ) : ℚ) * coeff (j + 1) ((N : ℕ) • Lser m 1))
              * coeff (k' - j) (expS ((N : ℕ) • Lser m 1))
          = (((N * cN m (j + 1)) * gec (fun i => N * cN m i) (k' + 1 - (j + 1)) : ℕ) : ℚ) := by
        intro j hj
        have hj1 : (j : ℕ) + 1 ≠ 0 := Nat.succ_ne_zero j
        rw [map_nsmul, nsmul_eq_mul, coeff_Lser, if_neg hj1,
          show (j + 1) * 1 = j + 1 from Nat.mul_one _]
        have hlt : k' - j < k' + 1 := by omega
        rw [← ih (k' - j) hlt]
        rw [show k' + 1 - (j + 1) = k' - j from by omega]
        have hne : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        rw [cQ_eq_cast]
        push_cast
        field_simp
      rw [Finset.sum_congr rfl hterm, ← Nat.cast_sum, hb] at hrec
      have hS : (∑ j ∈ Finset.range (k' + 1),
          (N * cN m (j + 1)) * gec (fun i => N * cN m i) (k' + 1 - (j + 1)))
          = (k' + 1) * b := by exact_mod_cast hrec.symm
      have hdiv : gec (fun i => N * cN m i) (k' + 1) = b := by
        rw [gec_succ]
        simp only at hS ⊢
        rw [hS, Nat.mul_div_cancel_left _ (Nat.succ_pos k')]
      rw [hdiv, hb]

/-! ## Combining the three regimes `m = 1`, `m = 2`, `m ≥ 3` -/

theorem main_all (hp5 : 5 ≤ p) [hp : Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {r : ℕ} (hr : 1 ≤ r) {n : ℕ} (hn : 1 ≤ n) :
    V p (3 * (r : ℤ))
      (coeff (n * p ^ r) (expS ((n * p ^ r : ℕ) • Lser m 1))
        - coeff (n * p ^ (r - 1)) (expS ((n * p ^ (r - 1) : ℕ) • Lser m 1))) := by
  by_cases h1 : m = 1
  · subst h1; exact main_m1 hp5 hr hn
  by_cases h2 : m = 2
  · subst h2; exact main_m2 hp5 hr hn
  · exact main_m3 hp5 (by omega) hr n

theorem final_int (hp5 : 5 ≤ p) [hp : Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {r : ℕ} (hr : 1 ≤ r) {n : ℕ} (hn : 1 ≤ n) :
    (p : ℤ) ^ (3 * r) ∣
      (gec (fun i => (n * p ^ r) * cN m i) (n * p ^ r) : ℤ)
        - (gec (fun i => (n * p ^ (r - 1)) * cN m i) (n * p ^ (r - 1)) : ℤ) := by
  have h := main_all hp5 hm hr hn
  rw [← gec_eq_coeff m (n * p ^ r) (n * p ^ r),
    ← gec_eq_coeff m (n * p ^ (r - 1)) (n * p ^ (r - 1))] at h
  rw [show ((gec (fun i => n * p ^ r * cN m i) (n * p ^ r) : ℕ) : ℚ)
        - ((gec (fun i => n * p ^ (r - 1) * cN m i) (n * p ^ (r - 1)) : ℕ) : ℚ)
      = (((gec (fun i => n * p ^ r * cN m i) (n * p ^ r) : ℤ)
        - (gec (fun i => n * p ^ (r - 1) * cN m i) (n * p ^ (r - 1)) : ℤ) : ℤ) : ℚ)
      from by push_cast; ring] at h
  rw [show (3 * (r : ℤ)) = ((3 * r : ℕ) : ℤ) from by push_cast; ring] at h
  exact (V_int_iff_dvd _ _).mp h

/-! ## Mirror of `b_m_int` and the final statement -/

noncomputable def bI (m n : ℕ) : ℤ :=
  if n = 0 then 0
  else
    let d (k : ℕ) : ℕ := n * cN m k
    (gec d n : ℤ)

theorem spec_final (m n r p : ℕ) (hp : Nat.Prime p)
    (hp5 : p ≥ 5) (hm : m ≥ 1) (hn : n ≥ 1) (hr : r ≥ 1) :
    bI m (n * p ^ r) ≡ bI m (n * p ^ (r - 1)) [ZMOD (p ^ (3 * r) : ℤ)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hz1 : n * p ^ r ≠ 0 :=
    Nat.mul_ne_zero (by omega) (pow_pos hp.pos r).ne'
  have hz2 : n * p ^ (r - 1) ≠ 0 :=
    Nat.mul_ne_zero (by omega) (pow_pos hp.pos (r - 1)).ne'
  rw [bI, bI, if_neg hz1, if_neg hz2]
  rw [Int.modEq_iff_dvd]
  have h := final_int (p := p) hp5 hm hr hn
  have h' := (dvd_neg.mpr h)
  rw [neg_sub] at h'
  convert h' using 2

/-! ## Rehearsal of the final assembly glue (a verbatim copy of the
`generalized_exp_coeff` recursion, proved equal to `gec`). -/

private noncomputable def gec2 (d : ℕ → ℕ) : ℕ → ℕ
| 0 => 1
| k' + 1 =>
  let k := k' + 1
  (Finset.sum (Finset.range k) fun j =>
    (d (j + 1)) * (gec2 d (k - (j + 1)))) / k

private def cLogGF (m k : ℕ) : ℕ := (m * k).factorial / (k.factorial ^ m)

theorem gec2_eq (d : ℕ → ℕ) (k : ℕ) : gec2 d k = gec d k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => rw [gec2, gec_zero]
    | k' + 1 =>
      rw [gec2, gec_succ]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih (k' + 1 - (j + 1)) (by omega)]

theorem cLogGF_eq : cLogGF = cN := by
  funext m k
  rfl

private noncomputable def bI2 (m n : ℕ) : ℤ :=
  if n = 0 then 0
  else
    let d (k : ℕ) : ℕ := n * cLogGF m k
    (gec2 d n : ℤ)

theorem bI2_eq : bI2 = bI := by
  funext m n
  rw [bI2, bI, cLogGF_eq]
  by_cases h : n = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    show ((gec2 (fun k => n * cN m k) n : ℤ)) = ((gec (fun k => n * cN m k) n : ℤ))
    rw [gec2_eq]

theorem spec_final2 (m n r p : ℕ) (hp : Nat.Prime p)
    (hp5 : p ≥ 5) (hm : m ≥ 1) (hn : n ≥ 1) (hr : r ≥ 1) :
    bI2 m (n * p ^ r) ≡ bI2 m (n * p ^ (r - 1)) [ZMOD (p ^ (3 * r) : ℤ)] := by
  rw [bI2_eq]
  exact spec_final m n r p hp hp5 hm hn hr

end

end Super

private theorem generalized_exp_coeff_eq_gec (d : ℕ → ℕ) (k : ℕ) :
    generalized_exp_coeff d k = Super.gec d k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => rw [generalized_exp_coeff, Super.gec_zero]
    | k' + 1 =>
      rw [generalized_exp_coeff, Super.gec_succ]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih (k' + 1 - (j + 1)) (by omega)]

private theorem coeff_of_log_gf_gen_eq : coeff_of_log_gf_gen = Super.cN := by
  funext m k
  rfl

private theorem b_m_int_eq : b_m_int = Super.bI := by
  funext m n
  rw [b_m_int, Super.bI, coeff_of_log_gf_gen_eq]
  by_cases h : n = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    show ((generalized_exp_coeff (fun k => n * Super.cN m k) n : ℤ))
      = ((Super.gec (fun k => n * Super.cN m k) n : ℤ))
    rw [generalized_exp_coeff_eq_gec]

section
open Nat BigOperators Int

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
by
  rw [b_m_int_eq]
  exact Super.spec_final m n r p hp hp5 hm hn hr

end
