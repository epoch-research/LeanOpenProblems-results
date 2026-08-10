import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The sequence $a(n)$ defined by
$$a(n) = \frac{1}{n} \sum_{k = 0}^n (n+2k) \binom{n+k-1}{k}^3$$
for $n \ge 1$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- Calculate the numerator sum S in ℕ
    -- We use binomial(n+k-1, n-1) which is equal to binomial(n+k-1, k)
    -- This makes the dependency on 'n - 1' explicit for the lower index.
    let S : ℕ := Finset.sum (range (n + 1)) fun k =>
      (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3

    -- Division is exact since a(n) is an integer sequence.
    S / n

section A361883Proof

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace A361883

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => ℚ_[p]

/-- Abbreviation for `(p:ℝ)⁻¹`; all norm bounds are stated as powers of `q`. -/
noncomputable def q (p : ℕ) : ℝ := (p:ℝ)⁻¹

lemma q_pos : 0 < q p := by
  have h : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.out.pos
  exact inv_pos.mpr h

lemma q_nonneg : 0 ≤ q p := (q_pos (p := p)).le

lemma q_le_one : q p ≤ 1 := by
  have h1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.out.one_lt.le
  simpa [q] using inv_le_one_of_one_le₀ h1

lemma q_pow_nonneg (e : ℕ) : 0 ≤ q p ^ e := pow_nonneg q_nonneg e

lemma q_pow_le_one (e : ℕ) : q p ^ e ≤ 1 :=
  pow_le_one₀ q_nonneg q_le_one

lemma q_pow_le_q_pow {e f : ℕ} (h : e ≤ f) : q p ^ f ≤ q p ^ e :=
  pow_le_pow_of_le_one q_nonneg q_le_one h

lemma q_pow_eq_zpow (e : ℕ) : q p ^ e = (p:ℝ) ^ (-(e:ℤ)) := by
  rw [zpow_neg, zpow_natCast, q, inv_pow]

lemma norm_p_pow_eq (e : ℕ) : ‖((p:K))^e‖ = q p ^ e := by
  rw [norm_pow, Padic.norm_p, q]

/-- Norm of a natural number cast is at most 1. -/
lemma norm_nat_le_one (m : ℕ) : ‖(m : K)‖ ≤ 1 := by
  simpa using Padic.norm_int_le_one (p := p) (m : ℤ)

lemma norm_nat_eq_one {m : ℕ} (h : ¬ p ∣ m) : ‖(m : K)‖ = 1 :=
  Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr h)

lemma nat_cast_ne_zero {m : ℕ} (h : m ≠ 0) : (m : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr h

lemma norm_nat_pos {m : ℕ} (h : m ≠ 0) : 0 < ‖(m : K)‖ :=
  norm_pos_iff.mpr (nat_cast_ne_zero h)

/-- If `p^e ∣ m` then `‖m‖ ≤ q^e`. -/
lemma norm_nat_le_pow {m e : ℕ} (h : p ^ e ∣ m) : ‖(m : K)‖ ≤ q p ^ e := by
  rw [q_pow_eq_zpow]
  have : ((p:ℤ) ^ e) ∣ (m : ℤ) := by exact_mod_cast h
  simpa using (Padic.norm_int_le_pow_iff_dvd (m : ℤ) e).mpr this

/-- Exact norm of `m * p^e` when `p ∤ m`. -/
lemma norm_nat_mul_pow {m e : ℕ} (h : ¬ p ∣ m) : ‖((m * p ^ e : ℕ) : K)‖ = q p ^ e := by
  push_cast
  rw [norm_mul, norm_nat_eq_one h, one_mul, norm_p_pow_eq]

lemma norm_two_eq_one (hp5 : 5 ≤ p) : ‖(2 : K)‖ = 1 := by
  have h : ¬ p ∣ 2 := fun hd => absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)
  have := norm_nat_eq_one (p := p) (m := 2) h
  simpa using this

lemma norm_three_eq_one (hp5 : 5 ≤ p) : ‖(3 : K)‖ = 1 := by
  have h : ¬ p ∣ 3 := fun hd => absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)
  have := norm_nat_eq_one (p := p) (m := 3) h
  simpa using this

lemma norm_int_le_pow_iff {z : ℤ} {e : ℕ} : ‖(z : K)‖ ≤ q p ^ e ↔ ((p:ℤ) ^ e) ∣ z := by
  rw [q_pow_eq_zpow]
  simpa using Padic.norm_int_le_pow_iff_dvd z e

/-- Ultrametric sum bound. -/
lemma norm_sum_le' {ι : Type*} {s : Finset ι} {f : ι → K} {C : ℝ} (h0 : 0 ≤ C)
    (h : ∀ i ∈ s, ‖f i‖ ≤ C) : ‖∑ i ∈ s, f i‖ ≤ C :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 h

lemma norm_add_le_max' (x y : K) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := Padic.nonarchimedean x y

lemma norm_sub_le_max' (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg] using Padic.nonarchimedean x (-y)



/-- First-order bound: `‖∏ (1 + x i) - 1‖ ≤ δ` when all `‖x i‖ ≤ δ ≤ 1`. -/
lemma norm_prod_one_add_sub_one_le {ι : Type*} {s : Finset ι} {x : ι → K} {δ : ℝ}
    (hδ1 : δ ≤ 1) (hδ0 : 0 ≤ δ) (hx : ∀ i ∈ s, ‖x i‖ ≤ δ) :
    ‖(∏ i ∈ s, (1 + x i)) - 1‖ ≤ δ := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using hδ0
  | cons a s ha ih =>
    have hxa : ‖x a‖ ≤ δ := hx a (Finset.mem_cons_self a s)
    have ih' : ‖(∏ i ∈ s, (1 + x i)) - 1‖ ≤ δ :=
      ih (fun i hi => hx i (Finset.mem_cons_of_mem hi))
    have h1a : ‖1 + x a‖ ≤ 1 := by
      refine (norm_add_le_max' 1 (x a)).trans ?_
      simp only [norm_one]
      exact max_le le_rfl (hxa.trans hδ1)
    have key : (∏ i ∈ Finset.cons a s ha, (1 + x i)) - 1
        = (1 + x a) * ((∏ i ∈ s, (1 + x i)) - 1) + x a := by
      rw [Finset.prod_cons]; ring
    rw [key]
    refine (norm_add_le_max' _ _).trans (max_le ?_ hxa)
    rw [norm_mul]
    calc ‖1 + x a‖ * ‖(∏ i ∈ s, (1 + x i)) - 1‖ ≤ 1 * δ :=
          mul_le_mul h1a ih' (norm_nonneg _) zero_le_one
    _ = δ := one_mul δ

/-- The product `∏ (1 + x i)` has norm at most 1 when all `‖x i‖ ≤ δ ≤ 1`. -/
lemma norm_prod_one_add_le_one {ι : Type*} {s : Finset ι} {x : ι → K} {δ : ℝ}
    (hδ1 : δ ≤ 1) (hδ0 : 0 ≤ δ) (hx : ∀ i ∈ s, ‖x i‖ ≤ δ) :
    ‖∏ i ∈ s, (1 + x i)‖ ≤ 1 := by
  have h := norm_prod_one_add_sub_one_le hδ1 hδ0 hx
  calc ‖∏ i ∈ s, (1 + x i)‖ = ‖((∏ i ∈ s, (1 + x i)) - 1) + 1‖ := by ring_nf
  _ ≤ max ‖(∏ i ∈ s, (1 + x i)) - 1‖ ‖(1:K)‖ := norm_add_le_max' _ _
  _ ≤ 1 := by simp only [norm_one]; exact max_le (h.trans hδ1) le_rfl

/-- Second-order expansion of `∏ (1 + x i)`:
`∏ (1 + x i) = 1 + S + (S² - Q)/2 + O(δ³)` where `S = ∑ x i` and `Q = ∑ (x i)²`. -/
lemma norm_prod_one_add_expand {ι : Type*} {s : Finset ι} {x : ι → K} {δ : ℝ}
    (hδ1 : δ ≤ 1) (hδ0 : 0 ≤ δ) (h2 : ‖(2 : K)‖ = 1) (hx : ∀ i ∈ s, ‖x i‖ ≤ δ) :
    ‖(∏ i ∈ s, (1 + x i)) -
      (1 + (∑ i ∈ s, x i) + ((∑ i ∈ s, x i)^2 - ∑ i ∈ s, (x i)^2)/2)‖ ≤ δ^3 := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using pow_nonneg hδ0 3
  | cons a s ha ih =>
    have hxa : ‖x a‖ ≤ δ := hx a (Finset.mem_cons_self a s)
    have hxs : ∀ i ∈ s, ‖x i‖ ≤ δ := fun i hi => hx i (Finset.mem_cons_of_mem hi)
    have ih' := ih hxs
    set P := ∏ i ∈ s, (1 + x i) with hP
    set S := ∑ i ∈ s, x i with hS
    set Q := ∑ i ∈ s, (x i)^2 with hQ
    have hSn : ‖S‖ ≤ δ := norm_sum_le' hδ0 hxs
    have hQn : ‖Q‖ ≤ δ^2 := by
      refine norm_sum_le' (by positivity) (fun i hi => ?_)
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hxs i hi) 2
    have h1a : ‖1 + x a‖ ≤ 1 := by
      refine (norm_add_le_max' 1 (x a)).trans ?_
      simp only [norm_one]
      exact max_le le_rfl (hxa.trans hδ1)
    have key : (∏ i ∈ Finset.cons a s ha, (1 + x i)) -
        (1 + (∑ i ∈ Finset.cons a s ha, x i) +
          ((∑ i ∈ Finset.cons a s ha, x i)^2 - ∑ i ∈ Finset.cons a s ha, (x i)^2)/2)
        = (1 + x a) * (P - (1 + S + (S^2 - Q)/2)) + x a * ((S^2 - Q)/2) := by
      rw [Finset.prod_cons, Finset.sum_cons, Finset.sum_cons, ← hP, ← hS, ← hQ]
      ring
    rw [key]
    refine (norm_add_le_max' _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖1 + x a‖ * ‖P - (1 + S + (S^2 - Q)/2)‖ ≤ 1 * δ^3 :=
            mul_le_mul h1a ih' (norm_nonneg _) zero_le_one
      _ = δ^3 := one_mul _
    · rw [norm_mul, norm_div, h2, div_one]
      have hsq : ‖S^2 - Q‖ ≤ δ^2 := by
        refine (norm_sub_le_max' _ _).trans (max_le ?_ hQn)
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hSn 2
      calc ‖x a‖ * ‖S^2 - Q‖ ≤ δ * δ^2 :=
            mul_le_mul hxa hsq (norm_nonneg _) hδ0
      _ = δ^3 := by ring

/-- `‖X³ - 1‖ ≤ ‖X - 1‖` when `‖X‖ ≤ 1`. -/
lemma norm_cube_sub_one_le {X : K} (h : ‖X‖ ≤ 1) : ‖X^3 - 1‖ ≤ ‖X - 1‖ := by
  have key : X^3 - 1 = (X - 1) * (X^2 + X + 1) := by ring
  rw [key, norm_mul]
  have h2 : ‖X^2 + X + 1‖ ≤ 1 := by
    refine (norm_add_le_max' _ _).trans (max_le ((norm_add_le_max' _ _).trans (max_le ?_ h)) ?_)
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) h
    · simp
  calc ‖X - 1‖ * ‖X^2 + X + 1‖ ≤ ‖X - 1‖ * 1 :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  _ = ‖X - 1‖ := mul_one _

/-- Difference of inverse squares: if `x, y` are unit-norm and `‖x - y‖ ≤ ε` then
`‖1/x² - 1/y²‖ ≤ ε`. -/
lemma norm_inv_sq_sub_inv_sq {x y : K} {ε : ℝ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ‖x - y‖ ≤ ε) : ‖1/x^2 - 1/y^2‖ ≤ ε := by
  have hx0 : x ≠ 0 := by intro h; rw [h] at hx; simp at hx
  have hy0 : y ≠ 0 := by intro h; rw [h] at hy; simp at hy
  have key : 1/x^2 - 1/y^2 = ((y - x) * (y + x)) / (x^2 * y^2) := by
    field_simp; ring
  rw [key, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, hx, hy]
  have hyx : ‖y - x‖ ≤ ε := by rwa [← norm_neg, neg_sub]
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hyx
  have hsum : ‖y + x‖ ≤ 1 := by
    refine (norm_add_le_max' _ _).trans ?_
    rw [hx, hy]; simp
  simp only [one_pow, mul_one, div_one]
  calc ‖y - x‖ * ‖y + x‖ ≤ ε * 1 := mul_le_mul hyx hsum (norm_nonneg _) hε0
  _ = ε := mul_one _

/- ### Binomial coefficients as products -/

/-- `C(m+j, j) = ∏_{i=1}^{j} (m+i)/i` in `K`. -/
lemma choose_eq_prod (m j : ℕ) :
    (((m + j).choose j : ℕ) : K) = ∏ i ∈ Finset.Icc 1 j, (((m + i : ℕ) : K) / ((i : ℕ) : K)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.prod_Icc_succ_top (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero j)), ← ih]
    have hnat : (m + j + 1) * (m + j).choose j = (m + j + 1).choose (j + 1) * (j + 1) :=
      Nat.succ_mul_choose_eq (m + j) j
    have key : (((m + j + 1 : ℕ)) : K) * (((m + j).choose j : ℕ) : K)
        = (((m + j + 1).choose (j + 1) : ℕ) : K) * (((j + 1 : ℕ)) : K) := by
      exact_mod_cast hnat
    have hB : (((j + 1 : ℕ)) : K) ≠ 0 := nat_cast_ne_zero (Nat.succ_ne_zero j)
    have hgoal : (((m + (j + 1)).choose (j + 1) : ℕ) : K)
        = (((m + j).choose j : ℕ) : K) * ((((m + (j + 1) : ℕ)) : K) / (((j + 1 : ℕ)) : K)) := by
      rw [mul_div_assoc', eq_div_iff hB]
      have h1 : m + (j + 1) = m + j + 1 := by omega
      rw [h1]
      linear_combination -key
    exact hgoal

/-- The set of `i ∈ [1, k]` not divisible by `p`. -/
def Iset (p k : ℕ) : Finset ℕ := (Finset.Icc 1 k).filter (fun i => ¬ (p ∣ i))

/-- The product `E = ∏_{1 ≤ i ≤ k, p ∤ i} (1 + N/i)`. -/
noncomputable def Ebig (p : ℕ) [Fact p.Prime] (N k : ℕ) : ℚ_[p] :=
  ∏ i ∈ Iset p k, (1 + (N : ℚ_[p]) / (i : ℚ_[p]))

lemma mem_Iset {k i : ℕ} : i ∈ Iset p k ↔ (1 ≤ i ∧ i ≤ k ∧ ¬ (p ∣ i)) := by
  simp [Iset, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-- Key splitting: if `N = p * M` then `C(N+k, k) = C(M + k/p, k/p) * Ebig p N k`. -/
lemma choose_split {N M k : ℕ} (hNM : N = p * M) :
    (((N + k).choose k : ℕ) : K) = (((M + k / p).choose (k / p) : ℕ) : K) * Ebig p N k := by
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hppos : 0 < p := Nat.pos_of_ne_zero hp0
  have hp0' : (p : K) ≠ 0 := nat_cast_ne_zero hp0
  rw [choose_eq_prod N k, choose_eq_prod M (k / p)]
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 k) (fun i => p ∣ i)]
  have himg : (Finset.Icc 1 k).filter (fun i => p ∣ i)
      = (Finset.Icc 1 (k / p)).image (fun i => p * i) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, c, rfl⟩
      have hc1 : 1 ≤ c := by
        rcases Nat.eq_zero_or_pos c with rfl | hc
        · omega
        · exact hc
      have hc2 : c ≤ k / p := by
        rw [Nat.le_div_iff_mul_le hppos, mul_comm]
        exact h2
      exact ⟨c, ⟨hc1, hc2⟩, rfl⟩
    · rintro ⟨c, ⟨h1, h2⟩, rfl⟩
      have h2' : c * p ≤ k := (Nat.le_div_iff_mul_le hppos).mp h2
      have h1' : 1 ≤ p * c := Nat.mul_pos hppos h1
      exact ⟨⟨h1', by rw [mul_comm]; exact h2'⟩, ⟨c, rfl⟩⟩
  rw [himg, Finset.prod_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hppos h)]
  have hfac : ∀ i ∈ Finset.Icc 1 (k / p),
      ((N + p * i : ℕ) : K) / ((p * i : ℕ) : K) = ((M + i : ℕ) : K) / ((i : ℕ) : K) := by
    intro i hi
    simp only [Finset.mem_Icc] at hi
    subst hNM
    push_cast
    rw [← mul_add (p : K) (M : K) (i : K)]
    rw [mul_div_mul_left _ _ hp0']
  rw [Finset.prod_congr rfl hfac]
  have hE : ∏ i ∈ (Finset.Icc 1 k).filter (fun i => ¬ p ∣ i), (((N + i : ℕ) : K) / ((i : ℕ) : K))
      = Ebig p N k := by
    unfold Ebig Iset
    refine Finset.prod_congr rfl (fun i hi => ?_)
    simp only [Finset.mem_filter, Finset.mem_Icc] at hi
    have hi0 : (i : K) ≠ 0 := nat_cast_ne_zero (by omega)
    push_cast
    field_simp
    ring
  rw [hE]

/-- Each factor `N/i` in `Ebig` has norm `‖N‖`. -/
lemma norm_factor_le {N k : ℕ} {δ : ℝ} (hN : ‖(N : K)‖ ≤ δ) :
    ∀ i ∈ Iset p k, ‖(N : K) / (i : K)‖ ≤ δ := by
  intro i hi
  rw [mem_Iset] at hi
  rw [norm_div, norm_nat_eq_one hi.2.2, div_one]
  exact hN

lemma norm_Ebig_sub_one_le {N k : ℕ} {δ : ℝ} (hδ1 : δ ≤ 1) (hδ0 : 0 ≤ δ)
    (hN : ‖(N : K)‖ ≤ δ) : ‖Ebig p N k - 1‖ ≤ δ := by
  unfold Ebig
  exact norm_prod_one_add_sub_one_le hδ1 hδ0 (norm_factor_le (k := k) hN)

lemma norm_Ebig_le_one {N k : ℕ} : ‖Ebig p N k‖ ≤ 1 := by
  unfold Ebig
  exact norm_prod_one_add_le_one (norm_nat_le_one N) (norm_nonneg _)
    (norm_factor_le (k := k) le_rfl)

lemma norm_Ebig_cube_sub_one_le {N k : ℕ} : ‖(Ebig p N k)^3 - 1‖ ≤ ‖(N : K)‖ :=
  (norm_cube_sub_one_le norm_Ebig_le_one).trans
    (norm_Ebig_sub_one_le (norm_nat_le_one N) (norm_nonneg _) le_rfl)

/- ### Wolstenholme-type lemmas -/

/-- The reduced residues in `[0, p^β)`. -/
def Rset (p β : ℕ) : Finset ℕ := (Finset.range (p^β)).filter (fun u => ¬ (p ∣ u))

lemma mem_Rset {β u : ℕ} : u ∈ Rset p β ↔ (u < p^β ∧ ¬ (p ∣ u)) := by
  simp [Rset, Finset.mem_filter, Finset.mem_range]

/-- The fundamental sum `Gs β w = ∑_{p ∤ u, 0 < u < p^β} 1/(u + p^β w)²`. -/
noncomputable def Gs (p : ℕ) [Fact p.Prime] (β w : ℕ) : ℚ_[p] :=
  ∑ u ∈ Rset p β, (1 : ℚ_[p]) / (((u + p^β * w : ℕ)) : ℚ_[p])^2

lemma p_pow_pos (β : ℕ) : 0 < p ^ β := pow_pos hp.out.pos β

lemma p_ne_two (hp5 : 5 ≤ p) : p ≠ 2 := by omega

lemma not_dvd_shift {β u w : ℕ} (hβ : 1 ≤ β) (hu : ¬ p ∣ u) : ¬ p ∣ (u + p^β * w) := by
  intro h
  apply hu
  have hq : p ∣ p^β * w := (dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hβ)).mul_right w
  exact (Nat.dvd_add_right hq).mp (by rwa [add_comm] at h)

/-- Lemma U: the sum of inverse squares over the reduced residues mod `p^β`
has norm at most `q^β`. -/
lemma norm_sum_inv_sq_le (hp5 : 5 ≤ p) {β : ℕ} (hβ : 1 ≤ β) :
    ‖∑ u ∈ Rset p β, (1 : K) / ((u : ℕ) : K)^2‖ ≤ q p ^ β := by
  classical
  set Q := p ^ β with hQdef
  have hQpos : 0 < Q := p_pow_pos β
  have hpdvdQ : p ∣ Q := dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hβ)
  have hQodd : Odd Q := (Nat.Prime.odd_of_ne_two hp.out (p_ne_two hp5)).pow
  have h2c : 2 * ((Q+1)/2) = Q + 1 := by obtain ⟨m, hm⟩ := hQodd; omega
  set c := (Q+1)/2 with hcdef
  set σ := fun u => (2*u) % Q with hσdef
  set σ' := fun u => (c*u) % Q with hσ'def
  -- p does not divide 2, 3, c
  have hpnot2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hpnotc : ¬ p ∣ c := by
    intro h
    have h2cd : p ∣ Q + 1 := h2c ▸ (h.mul_left 2)
    have : p ∣ 1 := (Nat.dvd_add_right hpdvdQ).mp h2cd
    have := Nat.le_of_dvd (by norm_num) this
    omega
  -- membership
  have hmemσ : ∀ u ∈ Rset p β, σ u ∈ Rset p β := by
    intro u hu
    rw [mem_Rset] at hu ⊢
    refine ⟨Nat.mod_lt _ hQpos, ?_⟩
    intro hd
    have hd2u : p ∣ 2*u := by
      rw [← Nat.div_add_mod (2*u) Q]
      exact Dvd.dvd.add (Dvd.dvd.mul_right hpdvdQ _) hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd2u with h | h
    · exact hpnot2 h
    · exact hu.2 h
  have hmemσ' : ∀ u ∈ Rset p β, σ' u ∈ Rset p β := by
    intro u hu
    rw [mem_Rset] at hu ⊢
    refine ⟨Nat.mod_lt _ hQpos, ?_⟩
    intro hd
    have hdcu : p ∣ c*u := by
      rw [← Nat.div_add_mod (c*u) Q]
      exact Dvd.dvd.add (Dvd.dvd.mul_right hpdvdQ _) hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hdcu with h | h
    · exact hpnotc h
    · exact hu.2 h
  -- inverses
  have hleft : ∀ u ∈ Rset p β, σ' (σ u) = u := by
    intro u hu
    rw [mem_Rset] at hu
    have e1 : c * ((2*u) % Q) % Q = (c*(2*u)) % Q := ((Nat.mod_modEq (2*u) Q).mul_left c)
    have e2 : c*(2*u) = u + Q * u := by
      rw [← mul_assoc, mul_comm c 2, h2c]; ring
    have : σ' (σ u) = u % Q := by
      show c * ((2*u) % Q) % Q = u % Q
      rw [e1, e2, Nat.add_mul_mod_self_left]
    rw [this, Nat.mod_eq_of_lt hu.1]
  have hright : ∀ u ∈ Rset p β, σ (σ' u) = u := by
    intro u hu
    rw [mem_Rset] at hu
    have e1 : 2 * ((c*u) % Q) % Q = (2*(c*u)) % Q := ((Nat.mod_modEq (c*u) Q).mul_left 2)
    have e2 : 2*(c*u) = u + Q * u := by
      rw [← mul_assoc, h2c]; ring
    have : σ (σ' u) = u % Q := by
      show 2 * ((c*u) % Q) % Q = u % Q
      rw [e1, e2, Nat.add_mul_mod_self_left]
    rw [this, Nat.mod_eq_of_lt hu.1]
  -- reindexing
  set T := ∑ u ∈ Rset p β, (1 : K) / ((u : ℕ) : K)^2 with hTdef
  have reindex : ∑ u ∈ Rset p β, (1 : K) / ((σ u : ℕ) : K)^2 = T :=
    Finset.sum_nbij' σ σ' hmemσ hmemσ' hleft hright (fun a _ => rfl)
  -- termwise difference bound
  have hdiff : ∀ u ∈ Rset p β,
      ‖(1:K)/((σ u : ℕ) : K)^2 - (1:K)/(((2*u : ℕ)) : K)^2‖ ≤ q p ^ β := by
    intro u hu
    have huR := hu
    rw [mem_Rset] at huR
    have hσu := hmemσ u hu
    rw [mem_Rset] at hσu
    have h2u : ¬ p ∣ (2*u) := by
      intro h
      rcases (Nat.Prime.dvd_mul hp.out).mp h with h | h
      · exact hpnot2 h
      · exact huR.2 h
    refine norm_inv_sq_sub_inv_sq (norm_nat_eq_one hσu.2) (norm_nat_eq_one h2u) ?_
    have hsplit : 2*u = Q * (2*u/Q) + σ u := (Nat.div_add_mod (2*u) Q).symm
    have hc : ((σ u : ℕ) : K) - ((2*u : ℕ) : K) = -(((Q*(2*u/Q) : ℕ)) : K) := by
      have hcast := congrArg (fun t : ℕ => (t : K)) hsplit
      push_cast at hcast ⊢
      linear_combination -hcast
    rw [hc, norm_neg]
    exact norm_nat_le_pow (hQdef ▸ dvd_mul_right Q (2*u/Q))
  -- the (2u) sum equals (1/4) T
  have hsum2 : ∑ u ∈ Rset p β, (1:K)/(((2*u : ℕ)) : K)^2 = 1/(2:K)^2 * T := by
    rw [hTdef, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [mem_Rset] at hu
    have hu0 : ((u : ℕ) : K) ≠ 0 := nat_cast_ne_zero (fun h => hu.2 (h ▸ dvd_zero p))
    have h20 : (2 : K) ≠ 0 := two_ne_zero
    push_cast
    field_simp
  -- put it together
  have hkey : T * (1 - 1/(2:K)^2)
      = ∑ u ∈ Rset p β, ((1:K)/((σ u : ℕ) : K)^2 - (1:K)/(((2*u : ℕ)) : K)^2) := by
    rw [Finset.sum_sub_distrib, reindex, hsum2]
    ring
  have herr : ‖∑ u ∈ Rset p β, ((1:K)/((σ u : ℕ) : K)^2 - (1:K)/(((2*u : ℕ)) : K)^2)‖
      ≤ q p ^ β := norm_sum_le' (q_pow_nonneg β) hdiff
  have hnorm34 : ‖(1:K) - 1/(2:K)^2‖ = 1 := by
    have h1 : (1:K) - 1/(2:K)^2 = (3:K)/(2:K)^2 := by
      have h20 : (2 : K) ≠ 0 := two_ne_zero
      field_simp
      norm_num
    rw [h1, norm_div, norm_pow, norm_two_eq_one hp5, norm_three_eq_one hp5]
    norm_num
  calc ‖T‖ = ‖T * (1 - 1/(2:K)^2)‖ := by rw [norm_mul, hnorm34, mul_one]
  _ ≤ q p ^ β := hkey ▸ herr

/-- Lemma G: `‖Gs β w‖ ≤ q^β` for all `w`. -/
lemma norm_Gs_le (hp5 : 5 ≤ p) {β : ℕ} (hβ : 1 ≤ β) (w : ℕ) : ‖Gs p β w‖ ≤ q p ^ β := by
  have hdecomp : Gs p β w = (∑ u ∈ Rset p β, ((1:K)/(((u + p^β*w : ℕ)) : K)^2 -
      (1:K)/((u : ℕ) : K)^2)) + ∑ u ∈ Rset p β, (1:K)/((u : ℕ) : K)^2 := by
    rw [Finset.sum_sub_distrib]
    unfold Gs
    ring
  rw [hdecomp]
  refine (norm_add_le_max' _ _).trans (max_le ?_ (norm_sum_inv_sq_le hp5 hβ))
  refine norm_sum_le' (q_pow_nonneg β) (fun u hu => ?_)
  rw [mem_Rset] at hu
  refine norm_inv_sq_sub_inv_sq (norm_nat_eq_one (not_dvd_shift hβ hu.2))
    (norm_nat_eq_one hu.2) ?_
  have hc : (((u + p^β*w : ℕ)) : K) - ((u : ℕ) : K) = (((p^β*w : ℕ)) : K) := by
    push_cast
    ring
  rw [hc]
  exact norm_nat_le_pow (dvd_mul_right (p^β) w)

/-- W2: `‖∑_{i ∈ Iset (b p^β)} 1/i²‖ ≤ q^β`. -/
lemma norm_S2_le (hp5 : 5 ≤ p) {b β : ℕ} (hβ : 1 ≤ β) :
    ‖∑ i ∈ Iset p (b * p^β), (1:K)/((i : ℕ) : K)^2‖ ≤ q p ^ β := by
  classical
  have hQpos : 0 < p ^ β := p_pow_pos β
  have hpdvdQ : p ∣ p^β := dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hβ)
  have hsplit : ∑ i ∈ Iset p (b * p^β), (1:K)/((i : ℕ) : K)^2
      = ∑ x ∈ (Finset.range b) ×ˢ (Rset p β), (1:K)/(((x.2 + p^β * x.1 : ℕ)) : K)^2 := by
    refine Finset.sum_nbij' (fun i => (i / p^β, i % p^β)) (fun x => x.2 + p^β * x.1)
      ?_ ?_ ?_ ?_ ?_
    · intro i hi
      rw [mem_Iset] at hi
      obtain ⟨h1, h2, h3⟩ := hi
      have hiltB : i < b * p^β := by
        rcases Nat.lt_or_ge i (b * p^β) with h | h
        · exact h
        · exfalso
          have : i = b * p^β := le_antisymm h2 h
          exact h3 (this ▸ (hpdvdQ.mul_left b))
      simp only [Finset.mem_product, Finset.mem_range, mem_Rset]
      refine ⟨?_, Nat.mod_lt _ hQpos, ?_⟩
      · exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hiltB)
      · intro hd
        apply h3
        rw [← Nat.div_add_mod i (p^β)]
        exact Dvd.dvd.add (hpdvdQ.mul_right _) hd
    · intro x hx
      simp only [Finset.mem_product, Finset.mem_range, mem_Rset] at hx
      obtain ⟨hc, hu, hnd⟩ := hx
      rw [mem_Iset]
      refine ⟨?_, ?_, ?_⟩
      · have hx2 : 1 ≤ x.2 :=
          Nat.pos_of_ne_zero (fun h0 => hnd (by rw [h0]; exact dvd_zero p))
        exact le_trans hx2 (Nat.le_add_right _ _)
      · have h1 : x.2 + p^β * x.1 < p^β * (x.1 + 1) := by
          have hexp : p^β * (x.1+1) = p^β * x.1 + p^β := by ring
          omega
        have h2 : p^β * (x.1 + 1) ≤ p^β * b := Nat.mul_le_mul_left _ (by omega)
        calc x.2 + p^β * x.1 ≤ p^β * (x.1+1) := le_of_lt h1
        _ ≤ p^β * b := h2
        _ = b * p^β := Nat.mul_comm _ _
      · exact not_dvd_shift hβ hnd
    · intro i hi
      show i % p^β + p^β * (i / p^β) = i
      exact Nat.mod_add_div i (p^β)
    · intro x hx
      simp only [Finset.mem_product, Finset.mem_range, mem_Rset] at hx
      obtain ⟨hc, hu, hnd⟩ := hx
      have h1 : (x.2 + p^β * x.1) / p^β = x.1 := by
        rw [Nat.add_mul_div_left _ _ hQpos, Nat.div_eq_of_lt hu]
        omega
      have h2 : (x.2 + p^β * x.1) % p^β = x.2 := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]
      simp only [h1, h2]
    · intro i hi
      show (1:K)/((i : ℕ) : K)^2 = (1:K)/(((i % p^β + p^β * (i / p^β) : ℕ)) : K)^2
      rw [Nat.mod_add_div i (p^β)]
  rw [hsplit, Finset.sum_product]
  refine norm_sum_le' (q_pow_nonneg β) (fun c _ => ?_)
  exact norm_Gs_le hp5 hβ c

/-- W1: `‖∑_{i ∈ Iset (b p^β)} 1/i‖ ≤ q^(2β)`. -/
lemma norm_S1_le (hp5 : 5 ≤ p) {b β : ℕ} (hβ : 1 ≤ β) :
    ‖∑ i ∈ Iset p (b * p^β), (1:K)/((i : ℕ) : K)‖ ≤ q p ^ (2*β) := by
  classical
  set B := b * p^β with hBdef
  have hpdvdQ : p ∣ p^β := dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hβ)
  have hpdvdB : p ∣ B := hpdvdQ.mul_left b
  have hQBdvd : p^β ∣ B := Dvd.intro_left b rfl
  have hBnorm : ‖(B : K)‖ ≤ q p ^ β := norm_nat_le_pow hQBdvd
  -- facts about elements of Iset p B
  have hmem : ∀ i ∈ Iset p B, 1 ≤ i ∧ i ≤ B ∧ ¬ p ∣ i := fun i hi => mem_Iset.mp hi
  have hrefl_mem : ∀ i ∈ Iset p B, B - i ∈ Iset p B := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hmem i hi
    rw [mem_Iset]
    have hiB : i ≠ B := fun h => h3 (h ▸ hpdvdB)
    have hnd : ¬ p ∣ (B - i) := by
      intro hd
      apply h3
      have hsum : B - i + i = B := Nat.sub_add_cancel h2
      have hdvd : p ∣ B - i + i := by rw [hsum]; exact hpdvdB
      exact (Nat.dvd_add_right hd).mp hdvd
    refine ⟨by omega, by omega, hnd⟩
  -- reflection identity
  have hreflect : ∑ i ∈ Iset p B, (1:K)/(((B - i : ℕ)) : K) = ∑ i ∈ Iset p B, (1:K)/((i : ℕ) : K) := by
    refine Finset.sum_nbij' (fun i => B - i) (fun i => B - i) hrefl_mem hrefl_mem ?_ ?_ ?_
    · intro i hi
      obtain ⟨h1, h2, h3⟩ := hmem i hi
      show B - (B - i) = i
      omega
    · intro i hi
      obtain ⟨h1, h2, h3⟩ := hmem i hi
      show B - (B - i) = i
      omega
    · intro i hi
      rfl
  -- the doubled sum
  have hdouble : (2:K) * (∑ i ∈ Iset p B, (1:K)/((i : ℕ) : K))
      = (B : K) * ∑ i ∈ Iset p B, (1:K)/(((i : ℕ) : K) * (((B - i : ℕ)) : K)) := by
    calc (2:K) * (∑ i ∈ Iset p B, (1:K)/((i : ℕ) : K))
        = (∑ i ∈ Iset p B, (1:K)/((i : ℕ) : K)) + ∑ i ∈ Iset p B, (1:K)/(((B - i : ℕ)) : K) := by
          rw [hreflect]; ring
    _ = ∑ i ∈ Iset p B, ((1:K)/((i : ℕ) : K) + (1:K)/(((B - i : ℕ)) : K)) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ i ∈ Iset p B, (B : K) * ((1:K)/(((i : ℕ) : K) * (((B - i : ℕ)) : K))) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          obtain ⟨h1, h2, h3⟩ := hmem i hi
          obtain ⟨h1', h2', h3'⟩ := hmem _ (hrefl_mem i hi)
          have hi0 : ((i : ℕ) : K) ≠ 0 := nat_cast_ne_zero (by omega)
          have hBi0 : (((B - i : ℕ)) : K) ≠ 0 := nat_cast_ne_zero (by omega)
          have hcast : (((B - i : ℕ)) : K) = (B : K) - ((i:ℕ) : K) := by
            push_cast [Nat.cast_sub h2]
            ring
          have hBi0' : (B : K) - ((i:ℕ) : K) ≠ 0 := hcast ▸ hBi0
          rw [hcast]
          field_simp
          ring
    _ = (B : K) * ∑ i ∈ Iset p B, (1:K)/(((i : ℕ) : K) * (((B - i : ℕ)) : K)) := by
          rw [Finset.mul_sum]
  -- bound on the paired sum
  have hpair : ‖∑ i ∈ Iset p B, (1:K)/(((i : ℕ) : K) * (((B - i : ℕ)) : K))‖ ≤ q p ^ β := by
    have hdecomp : ∑ i ∈ Iset p B, (1:K)/(((i : ℕ) : K) * (((B - i : ℕ)) : K))
        = (∑ i ∈ Iset p B, ((1:K)/(((i : ℕ) : K) * (((B - i : ℕ)) : K)) + (1:K)/((i : ℕ) : K)^2))
          - ∑ i ∈ Iset p B, (1:K)/((i : ℕ) : K)^2 := by
      rw [Finset.sum_add_distrib]
      ring
    rw [hdecomp]
    refine (norm_sub_le_max' _ _).trans (max_le ?_ ?_)
    · refine norm_sum_le' (q_pow_nonneg β) (fun i hi => ?_)
      obtain ⟨h1, h2, h3⟩ := hmem i hi
      obtain ⟨h1', h2', h3'⟩ := hmem _ (hrefl_mem i hi)
      have hi0 : ((i : ℕ) : K) ≠ 0 := nat_cast_ne_zero (by omega)
      have hBi0 : (((B - i : ℕ)) : K) ≠ 0 := nat_cast_ne_zero (by omega)
      have hcast : (((B - i : ℕ)) : K) = (B : K) - ((i:ℕ) : K) := by
        push_cast [Nat.cast_sub h2]
        ring
      have hkey : (1:K)/(((i : ℕ) : K) * (((B - i : ℕ)) : K)) + (1:K)/((i : ℕ) : K)^2
          = (B : K) * (1 / (((i : ℕ) : K)^2 * (((B - i : ℕ)) : K))) := by
        field_simp
        rw [hcast]
        ring
      rw [hkey, norm_mul]
      calc ‖(B:K)‖ * ‖1 / (((i : ℕ) : K)^2 * (((B - i : ℕ)) : K))‖
          ≤ q p ^ β * 1 := by
            refine mul_le_mul hBnorm ?_ (norm_nonneg _) (q_pow_nonneg β)
            rw [norm_div, norm_mul, norm_pow, norm_nat_eq_one h3, norm_nat_eq_one h3']
            simp
      _ = q p ^ β := mul_one _
    · rw [hBdef]
      exact norm_S2_le hp5 hβ
  -- conclude
  have h2n : ‖(2:K)‖ = 1 := norm_two_eq_one hp5
  have : ‖(2:K) * (∑ i ∈ Iset p B, (1:K)/((i : ℕ) : K))‖ ≤ q p ^ (2*β) := by
    rw [hdouble, norm_mul]
    calc ‖(B:K)‖ * ‖∑ i ∈ Iset p B, (1:K)/(((i : ℕ) : K) * (((B - i : ℕ)) : K))‖
        ≤ q p ^ β * q p ^ β :=
          mul_le_mul hBnorm hpair (norm_nonneg _) (q_pow_nonneg β)
    _ = q p ^ (2*β) := by rw [← pow_add]; ring_nf
  rwa [norm_mul, h2n, one_mul] at this
/- ### Part 2: the descent machinery -/

/-- The auxiliary sums `Xs m β = ∑_{j < m} C(m+j, j)³ Gs β (m+j)`. -/
noncomputable def Xs (p : ℕ) [Fact p.Prime] (m β : ℕ) : ℚ_[p] :=
  ∑ j ∈ Finset.range m, (((m+j).choose j : ℕ) : ℚ_[p])^3 * Gs p β (m+j)

/-- Endpoint bound: `‖Xs m β‖ ≤ q^β` for any `m`. -/
lemma norm_Xs_le (hp5 : 5 ≤ p) {β : ℕ} (hβ : 1 ≤ β) (m : ℕ) :
    ‖Xs p m β‖ ≤ q p ^ β := by
  refine norm_sum_le' (q_pow_nonneg β) (fun j _ => ?_)
  rw [norm_mul, norm_pow]
  calc ‖(((m+j).choose j : ℕ) : K)‖^3 * ‖Gs p β (m+j)‖ ≤ 1^3 * (q p ^ β) := by
        refine mul_le_mul ?_ (norm_Gs_le hp5 hβ _) (norm_nonneg _) (by norm_num)
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_nat_le_one _) 3
  _ = q p ^ β := by norm_num

/-- Exact identity: summing `Gs β` over a block of `p` consecutive arguments gives
`Gs (β+1)`. -/
lemma sum_Gs_eq {β : ℕ} (hβ : 1 ≤ β) (W : ℕ) :
    ∑ t ∈ Finset.range p, Gs p β (p*W + t) = Gs p (β+1) W := by
  classical
  have hQpos : 0 < p ^ β := p_pow_pos β
  have hppos : 0 < p := hp.out.pos
  unfold Gs
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun x => x.2 + p^β * x.1) (fun u => (u / p^β, u % p^β))
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range, mem_Rset] at hx ⊢
    obtain ⟨ht, hu, hnd⟩ := hx
    constructor
    · calc x.2 + p^β * x.1 < p^β * (x.1 + 1) := by
            have hexp : p^β * (x.1+1) = p^β * x.1 + p^β := by ring
            omega
      _ ≤ p^β * p := Nat.mul_le_mul_left _ (by omega)
      _ = p^(β+1) := by rw [pow_succ]
    · exact not_dvd_shift hβ hnd
  · intro u hu
    rw [mem_Rset] at hu
    obtain ⟨hlt, hnd⟩ := hu
    simp only [Finset.mem_product, Finset.mem_range, mem_Rset]
    refine ⟨?_, Nat.mod_lt _ hQpos, ?_⟩
    · have : u < p^β * p := by rw [← pow_succ]; exact hlt
      exact Nat.div_lt_of_lt_mul this
    · intro hd
      apply hnd
      rw [← Nat.div_add_mod u (p^β)]
      exact Dvd.dvd.add ((dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hβ)).mul_right _) hd
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range, mem_Rset] at hx
    obtain ⟨ht, hu, hnd⟩ := hx
    have h1 : (x.2 + p^β * x.1) / p^β = x.1 := by
      rw [Nat.add_mul_div_left _ _ hQpos, Nat.div_eq_of_lt hu]
      omega
    have h2 : (x.2 + p^β * x.1) % p^β = x.2 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]
    simp only [h1, h2]
  · intro u hu
    show u % p^β + p^β * (u / p^β) = u
    exact Nat.mod_add_div u (p^β)
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range, mem_Rset] at hx
    obtain ⟨ht, hu, hnd⟩ := hx
    have harg : x.2 + p^β * (p * W + x.1) = (x.2 + p^β * x.1) + p^(β+1) * W := by
      ring
    rw [harg]

/-- Reindex a sum over `range (p*m)` as a double sum. -/
lemma sum_range_pmul {α : Type*} [AddCommMonoid α] (m : ℕ) (f : ℕ → α) :
    ∑ j ∈ Finset.range (p*m), f j
      = ∑ x ∈ (Finset.range m) ×ˢ (Finset.range p), f (p * x.1 + x.2) := by
  classical
  have hppos : 0 < p := hp.out.pos
  refine Finset.sum_nbij' (fun j => (j / p, j % p)) (fun x => p * x.1 + x.2) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_range] at hj
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.div_lt_of_lt_mul hj, Nat.mod_lt _ hppos⟩
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range] at hx
    rw [Finset.mem_range]
    calc p * x.1 + x.2 < p * x.1 + p := by omega
    _ = p * (x.1 + 1) := by ring
    _ ≤ p * m := Nat.mul_le_mul_left _ (by omega)
  · intro j hj
    show p * (j / p) + j % p = j
    exact Nat.div_add_mod j p
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range] at hx
    have h1 : (p * x.1 + x.2) / p = x.1 := by
      rw [Nat.mul_add_div hppos, Nat.div_eq_of_lt hx.2]
      omega
    have h2 : (p * x.1 + x.2) % p = x.2 := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hx.2]
    simp only [h1, h2]
  · intro j hj
    rw [Nat.div_add_mod j p]

/-- The chain step: `Xs (p*m) β` is close to `Xs m (β+1)`. -/
lemma norm_Xs_chain (hp5 : 5 ≤ p) {β : ℕ} (hβ : 1 ≤ β) (m : ℕ) :
    ‖Xs p (p*m) β - Xs p m (β+1)‖ ≤ ‖((p*m : ℕ) : K)‖ * q p ^ β := by
  classical
  have hsplit : ∀ x : ℕ × ℕ, x ∈ (Finset.range m) ×ˢ (Finset.range p) →
      (((p*m + (p * x.1 + x.2)).choose (p * x.1 + x.2) : ℕ) : K)
        = (((m + x.1).choose x.1 : ℕ) : K) * Ebig p (p*m) (p * x.1 + x.2) := by
    intro x hx
    simp only [Finset.mem_product, Finset.mem_range] at hx
    have hdiv : (p * x.1 + x.2) / p = x.1 := by
      rw [Nat.mul_add_div hp.out.pos, Nat.div_eq_of_lt hx.2]
      omega
    have := choose_split (p := p) (N := p*m) (M := m) (k := p * x.1 + x.2) rfl
    rwa [hdiv] at this
  -- rewrite Xs (p*m) β as a double sum
  have hXpm : Xs p (p*m) β = ∑ x ∈ (Finset.range m) ×ˢ (Finset.range p),
      ((((m + x.1).choose x.1 : ℕ) : K) * Ebig p (p*m) (p * x.1 + x.2))^3
        * Gs p β (p*m + (p * x.1 + x.2)) := by
    unfold Xs
    rw [sum_range_pmul m (fun j => (((p*m+j).choose j : ℕ) : K)^3 * Gs p β (p*m+j))]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [hsplit x hx]
  -- the main term: with E replaced by 1
  have hmain : ∑ x ∈ (Finset.range m) ×ˢ (Finset.range p),
      ((((m + x.1).choose x.1 : ℕ) : K))^3 * Gs p β (p*m + (p * x.1 + x.2))
        = Xs p m (β+1) := by
    rw [Finset.sum_product]
    unfold Xs
    refine Finset.sum_congr rfl (fun l hl => ?_)
    dsimp only
    rw [← Finset.mul_sum]
    congr 1
    have harg : ∀ t, p*m + (p * l + t) = p * (m + l) + t := fun t => by ring
    calc ∑ t ∈ Finset.range p, Gs p β (p*m + (p * l + t))
        = ∑ t ∈ Finset.range p, Gs p β (p * (m + l) + t) := by
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [harg t]
    _ = Gs p (β+1) (m + l) := sum_Gs_eq hβ (m + l)
  -- the difference
  have hdiff : Xs p (p*m) β - Xs p m (β+1)
      = ∑ x ∈ (Finset.range m) ×ˢ (Finset.range p),
        ((((m + x.1).choose x.1 : ℕ) : K))^3 * Gs p β (p*m + (p * x.1 + x.2))
          * ((Ebig p (p*m) (p * x.1 + x.2))^3 - 1) := by
    rw [hXpm, ← hmain, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    ring
  rw [hdiff]
  refine norm_sum_le' (mul_nonneg (norm_nonneg _) (q_pow_nonneg β)) (fun x hx => ?_)
  rw [norm_mul, norm_mul, norm_pow]
  calc ‖(((m + x.1).choose x.1 : ℕ) : K)‖^3 * ‖Gs p β (p*m + (p * x.1 + x.2))‖
        * ‖(Ebig p (p*m) (p * x.1 + x.2))^3 - 1‖
      ≤ 1^3 * (q p ^ β) * ‖((p*m : ℕ) : K)‖ := by
        refine mul_le_mul (mul_le_mul ?_ (norm_Gs_le hp5 hβ _) (norm_nonneg _) (by norm_num))
          norm_Ebig_cube_sub_one_le (norm_nonneg _)
          (mul_nonneg (by norm_num) (q_pow_nonneg β))
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_nat_le_one _) 3
  _ = ‖((p*m : ℕ) : K)‖ * q p ^ β := by ring

/-- Descent: `‖Xs (n p^b) β‖ ≤ q^(b+β)` when `p ∤ n`. -/
lemma norm_Xs_desc (hp5 : 5 ≤ p) {n : ℕ} (hn : ¬ p ∣ n) :
    ∀ b β : ℕ, 1 ≤ β → ‖Xs p (n*p^b) β‖ ≤ q p ^ (b+β) := by
  intro b
  induction b with
  | zero =>
    intro β hβ
    have h0 : n * p^0 = n := by simp
    rw [zero_add, h0]
    exact norm_Xs_le hp5 hβ n
  | succ b ih =>
    intro β hβ
    have hnpb : n * p^(b+1) = p * (n * p^b) := by ring
    have hnorm : ‖((p * (n * p^b) : ℕ) : K)‖ = q p ^ (b+1) := by
      rw [show p * (n * p^b) = n * p^(b+1) from by ring]
      exact norm_nat_mul_pow hn
    have hchain := norm_Xs_chain hp5 hβ (n * p^b)
    have hih := ih (β+1) (by omega)
    have hXpm : Xs p (n*p^(b+1)) β = Xs p (p * (n * p^b)) β := by rw [hnpb]
    rw [hXpm]
    have hdec : Xs p (p * (n * p^b)) β
        = (Xs p (p * (n * p^b)) β - Xs p (n * p^b) (β+1)) + Xs p (n * p^b) (β+1) := by
      ring
    rw [hdec]
    refine (norm_add_le_max' _ _).trans (max_le ?_ ?_)
    · calc ‖Xs p (p * (n * p^b)) β - Xs p (n * p^b) (β+1)‖
          ≤ ‖((p * (n * p^b) : ℕ) : K)‖ * q p ^ β := hchain
      _ = q p ^ (b+1) * q p ^ β := by rw [hnorm]
      _ = q p ^ ((b+1)+β) := by rw [← pow_add]
    · calc ‖Xs p (n * p^b) (β+1)‖ ≤ q p ^ (b+(β+1)) := hih
      _ = q p ^ ((b+1)+β) := by ring_nf
/- ### Part 2 assembly -/

/-- Reindex a sum over non-multiples of `p` in `[0, pM]` as a double sum. -/
lemma sum_filter_not_dvd {M : ℕ} (f : ℕ → K) :
    ∑ k ∈ (Finset.range (p*M + 1)).filter (fun k => ¬ p ∣ k), f k
      = ∑ x ∈ (Finset.range M) ×ˢ (Rset p 1), f (p * x.1 + x.2) := by
  classical
  have hppos : 0 < p := hp.out.pos
  refine Finset.sum_nbij' (fun k => (k/p, k%p)) (fun x => p*x.1 + x.2) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hlt, hnd⟩ := hk
    have hkpM : k ≠ p * M := by
      intro h
      exact hnd (h ▸ Dvd.intro M rfl)
    have hklt : k < p * M := by omega
    simp only [Finset.mem_product, Finset.mem_range, mem_Rset, pow_one]
    refine ⟨?_, Nat.mod_lt _ hppos, ?_⟩
    · exact Nat.div_lt_of_lt_mul hklt
    · intro hd
      apply hnd
      rw [← Nat.div_add_mod k p]
      exact Dvd.dvd.add (Dvd.intro _ rfl) hd
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range, mem_Rset, pow_one] at hx
    obtain ⟨hj, hs, hnd⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · have h1 : p * x.1 + x.2 < p * (x.1 + 1) := by
        have hexp : p * (x.1+1) = p * x.1 + p := by ring
        omega
      have h2 : p * (x.1+1) ≤ p * M := Nat.mul_le_mul_left _ (by omega)
      omega
    · intro hd
      apply hnd
      exact (Nat.dvd_add_right (Dvd.intro _ rfl)).mp hd
  · intro k hk
    show p * (k / p) + k % p = k
    exact Nat.div_add_mod k p
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range, mem_Rset, pow_one] at hx
    have h1 : (p * x.1 + x.2) / p = x.1 := by
      rw [Nat.mul_add_div hppos, Nat.div_eq_of_lt hx.2.1]
      omega
    have h2 : (p * x.1 + x.2) % p = x.2 := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hx.2.1]
    simp only [h1, h2]
  · intro k hk
    rw [Nat.div_add_mod k p]

/-- Part 2: the sum over `p ∤ k` has norm at most `q^(3r)`. -/
lemma PT2_bound (hp5 : 5 ≤ p) {n r : ℕ} (hn : ¬ p ∣ n) (hn0 : 0 < n) (hr : 1 ≤ r) :
    ‖∑ k ∈ (Finset.range (n*p^r + 1)).filter (fun k => ¬ p ∣ k),
        (((n*p^r + 2*k : ℕ)) : K) * ((((n*p^r + k - 1).choose k : ℕ)) : K)^3
          / (((n*p^r : ℕ)) : K)‖ ≤ q p ^ (3*r) := by
  classical
  set N := n * p^r with hNdef
  set M := n * p^(r-1) with hMdef
  have hr' : r - 1 + 1 = r := by omega
  have hppow : p^(r-1) * p = p^r := by rw [← pow_succ, hr']
  have hNM : N = p * M := by
    rw [hNdef, hMdef, ← hppow]
    ring
  have hN0 : N ≠ 0 := by
    have : 0 < p^r := p_pow_pos r
    positivity
  have hN0' : (N : K) ≠ 0 := nat_cast_ne_zero hN0
  have hNnorm : ‖(N : K)‖ ≤ q p ^ r := by
    rw [hNdef]
    exact norm_nat_le_pow (Dvd.dvd.mul_left dvd_rfl n)
  have hpdvdN : p ∣ N := hNM ▸ Dvd.intro M rfl
  -- basic facts for k with p ∤ k
  have hNk : ∀ k : ℕ, ¬ p ∣ k → ¬ p ∣ (N + k) := by
    intro k hk hd
    exact hk ((Nat.dvd_add_right hpdvdN).mp hd)
  -- Reindex
  have hidx : (Finset.range (N+1)).filter (fun k => ¬ p ∣ k)
      = (Finset.range (p*M+1)).filter (fun k => ¬ p ∣ k) := by rw [← hNM]
  rw [hidx, sum_filter_not_dvd]
  -- names for the pieces
  set F : ℕ → K := fun k => (((N + 2*k : ℕ)) : K) * ((((N + k - 1).choose k : ℕ)) : K)^3
    / ((N : ℕ) : K) with hFdef
  -- the target of the comparison
  set Xv := Xs p M 1 with hXdef
  have hXnorm : ‖Xv‖ ≤ q p ^ r := by
    rw [hXdef, hMdef]
    have := norm_Xs_desc hp5 hn (r-1) 1 le_rfl
    rwa [hr'] at this
  -- per-term canonical form
  have hterm : ∀ x ∈ (Finset.range M) ×ˢ (Rset p 1),
      F (p * x.1 + x.2) = (((N + 2*(p*x.1+x.2) : ℕ)) : K) * ((N:K))^2
          * ((((M + x.1).choose x.1 : ℕ)) : K)^3 * (Ebig p N (p*x.1+x.2))^3
          / (((N + (p*x.1+x.2) : ℕ)) : K)^3 := by
    intro x hx
    simp only [Finset.mem_product, Finset.mem_range, mem_Rset, pow_one] at hx
    obtain ⟨hj, hs, hnd⟩ := hx
    set k := p * x.1 + x.2 with hkdef
    have hknd : ¬ p ∣ k := by
      intro hd
      exact hnd ((Nat.dvd_add_right (Dvd.intro _ rfl)).mp hd)
    have hNknd : ¬ p ∣ (N + k) := hNk k hknd
    have hNk0 : (((N + k : ℕ)) : K) ≠ 0 := by
      intro h
      have := norm_nat_eq_one (p := p) hNknd
      rw [h] at this
      simp at this
    -- step 1 : C(N+k-1, k) * (N+k) = C(N+k, k) * N
    have hnat : (N+k-1).choose k * (N+k) = (N+k).choose k * N := by
      have h0 := Nat.choose_mul_succ_eq (N+k-1) k
      have e1 : N+k-1+1 = N+k := by omega
      rw [e1] at h0
      have e2 : N+k-k = N := by omega
      rw [e2] at h0
      exact h0
    have hcast1 : ((((N + k - 1).choose k : ℕ)) : K) * (((N + k : ℕ)) : K)
        = ((((N + k).choose k : ℕ)) : K) * (N : K) := by
      exact_mod_cast hnat
    -- step 2 : split the binomial
    have hdiv : k / p = x.1 := by
      rw [hkdef, Nat.mul_add_div hp.out.pos, Nat.div_eq_of_lt hs]
      omega
    have hsplit := choose_split (p := p) (N := N) (M := M) (k := k) hNM
    rw [hdiv] at hsplit
    -- combine
    have hC : ((((N + k - 1).choose k : ℕ)) : K)
        = (N : K) * (((((M + x.1).choose x.1 : ℕ)) : K) * Ebig p N k) / (((N + k : ℕ)) : K) := by
      rw [← hsplit]
      field_simp
      linear_combination hcast1
    rw [hFdef]
    simp only
    rw [hC]
    field_simp
  -- the comparison sum
  have hXsum : (2:K) * ((N:K))^2 * Xv = ∑ x ∈ (Finset.range M) ×ˢ (Rset p 1),
      (2:K) * ((N:K))^2 * ((((M + x.1).choose x.1 : ℕ)) : K)^3
        / (((N + (p*x.1+x.2) : ℕ)) : K)^2 := by
    rw [hXdef]
    unfold Xs Gs
    rw [Finset.mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have harg : s + p^1 * (M + j) = N + (p*j + s) := by
      rw [pow_one, hNM]
      ring
    rw [harg]
    field_simp
  -- the difference, term by term
  have hdiff : ∀ x ∈ (Finset.range M) ×ˢ (Rset p 1),
      ‖F (p*x.1+x.2) - (2:K) * ((N:K))^2 * ((((M + x.1).choose x.1 : ℕ)) : K)^3
        / (((N + (p*x.1+x.2) : ℕ)) : K)^2‖ ≤ q p ^ (3*r) := by
    intro x hx
    rw [hterm x hx]
    simp only [Finset.mem_product, Finset.mem_range, mem_Rset, pow_one] at hx
    obtain ⟨hj, hs, hnd⟩ := hx
    set k := p * x.1 + x.2 with hkdef
    have hknd : ¬ p ∣ k := by
      intro hd
      exact hnd ((Nat.dvd_add_right (Dvd.intro _ rfl)).mp hd)
    have hNknd : ¬ p ∣ (N + k) := hNk k hknd
    have hNknorm : ‖(((N + k : ℕ)) : K)‖ = 1 := norm_nat_eq_one hNknd
    have hNk0 : (((N + k : ℕ)) : K) ≠ 0 := by
      intro h
      rw [h] at hNknorm
      simp at hNknorm
    set Y := (((N + k : ℕ)) : K) with hYdef
    set C := ((((M + x.1).choose x.1 : ℕ)) : K) with hCdef
    set E := Ebig p N k with hEdef
    -- algebraic identity
    have h2Y : (((N + 2*k : ℕ)) : K) = 2*Y - (N:K) := by
      rw [hYdef]
      push_cast
      ring
    have hkey : (((N + 2*k : ℕ)) : K) * ((N:K))^2 * C^3 * E^3 / Y^3
        - (2:K) * ((N:K))^2 * C^3 / Y^2
        = (((N + 2*k : ℕ)) : K) * ((N:K))^2 * C^3 * (E^3 - 1) / Y^3
          - ((N:K))^3 * C^3 / Y^3 := by
      rw [h2Y]
      field_simp
      ring
    rw [hkey]
    -- norms
    have hCnorm : ‖C‖ ≤ 1 := norm_nat_le_one _
    have hEnorm : ‖E^3 - 1‖ ≤ ‖(N:K)‖ := norm_Ebig_cube_sub_one_le
    have hN2k : ‖(((N + 2*k : ℕ)) : K)‖ ≤ 1 := norm_nat_le_one _
    have hq3r : (q p)^(3*r) = ((q p)^r)^3 := by rw [← pow_mul]; ring_nf
    refine (norm_sub_le_max' _ _).trans (max_le ?_ ?_)
    · rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, hYdef, hNknorm]
      simp only [one_pow, div_one]
      calc ‖(((N + 2*k : ℕ)) : K)‖ * ‖(N:K)‖^2 * ‖C‖^3 * ‖E^3-1‖
          ≤ 1 * (q p ^ r)^2 * 1^3 * (q p ^ r) := by
            refine mul_le_mul (mul_le_mul (mul_le_mul hN2k ?_ (by positivity) zero_le_one)
              ?_ (by positivity) ?_) (hEnorm.trans hNnorm) (norm_nonneg _) ?_
            · exact pow_le_pow_left₀ (norm_nonneg _) hNnorm 2
            · exact pow_le_pow_left₀ (norm_nonneg _) hCnorm 3
            · exact mul_nonneg zero_le_one (pow_nonneg (q_pow_nonneg r) 2)
            · exact mul_nonneg (mul_nonneg zero_le_one (pow_nonneg (q_pow_nonneg r) 2))
                (by norm_num)
      _ = q p ^ (3*r) := by
            rw [← pow_mul]
            ring_nf
    · rw [norm_div, norm_mul, norm_pow, norm_pow, norm_pow, hYdef, hNknorm]
      simp only [one_pow, div_one]
      calc ‖(N:K)‖^3 * ‖C‖^3 ≤ (q p ^ r)^3 * 1^3 := by
            refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hNnorm 3)
              (pow_le_pow_left₀ (norm_nonneg _) hCnorm 3) (by positivity)
              (pow_nonneg (q_pow_nonneg r) 3)
      _ = q p ^ (3*r) := by
            rw [← pow_mul]
            ring_nf
  -- put everything together
  have hfinal : ∑ x ∈ (Finset.range M) ×ˢ (Rset p 1), F (p*x.1+x.2)
      = (∑ x ∈ (Finset.range M) ×ˢ (Rset p 1),
          (F (p*x.1+x.2) - (2:K) * ((N:K))^2 * ((((M + x.1).choose x.1 : ℕ)) : K)^3
            / (((N + (p*x.1+x.2) : ℕ)) : K)^2))
        + (2:K) * ((N:K))^2 * Xv := by
    rw [hXsum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    ring
  rw [hfinal]
  refine (norm_add_le_max' _ _).trans (max_le ?_ ?_)
  · exact norm_sum_le' (q_pow_nonneg _) hdiff
  · rw [norm_mul, norm_mul, norm_pow, norm_two_eq_one hp5, one_mul]
    calc ‖(N:K)‖^2 * ‖Xv‖ ≤ (q p ^ r)^2 * (q p ^ r) := by
          refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hNnorm 2) hXnorm
            (norm_nonneg _) (by positivity)
    _ = q p ^ (3*r) := by
          rw [← pow_mul]
          ring_nf
/- ### Part 1: the refined bound on `Ebig - 1` -/

lemma q_lt_one : q p < 1 := by
  have h1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.out.one_lt
  rw [q]
  exact inv_lt_one_of_one_lt₀ h1

lemma q_pow_lt_q_pow {a b : ℕ} (h : a < b) : q p ^ b < q p ^ a :=
  pow_lt_pow_right_of_lt_one₀ q_pos q_lt_one h

lemma q_pow_ne_q_pow {a b : ℕ} (h : a ≠ b) : q p ^ a ≠ q p ^ b := by
  rcases Nat.lt_or_ge a b with hab | hab
  · exact (q_pow_lt_q_pow hab).ne'
  · have : b < a := by omega
    exact (q_pow_lt_q_pow this).ne

/-- Refined second-order bound on `Ebig p N (p*(j''*p^u)) - 1` where `p ∤ j''`. -/
lemma norm_R_sub_one (hp5 : 5 ≤ p) {N ρ : ℕ} (hN : ‖(N : K)‖ ≤ q p ^ (ρ+1)) {j'' u : ℕ}
    (hj'' : ¬ p ∣ j'') :
    ‖Ebig p N (p * (j'' * p^u)) - 1‖
      ≤ q p ^ (3 + min (ρ + 2*u) (min (2*ρ + u) (3*ρ))) := by
  classical
  set k := p * (j'' * p^u) with hkdef
  have hk : k = j'' * p^(u+1) := by rw [hkdef]; ring
  set em := min (ρ + 2*u) (min (2*ρ + u) (3*ρ)) with hemdef
  set δ : ℝ := q p ^ (ρ+1) with hδdef
  have hδ0 : 0 ≤ δ := q_pow_nonneg _
  have hδ1 : δ ≤ 1 := q_pow_le_one _
  have hx : ∀ i ∈ Iset p k, ‖(N : K)/(i : K)‖ ≤ δ := norm_factor_le hN
  -- the sums S₁ and S₂
  set S1 := ∑ i ∈ Iset p k, (1:K)/((i : ℕ) : K) with hS1def
  set S2 := ∑ i ∈ Iset p k, (1:K)/((i : ℕ) : K)^2 with hS2def
  have hS1 : ‖S1‖ ≤ q p ^ (2*(u+1)) := by
    rw [hS1def, hk]
    exact norm_S1_le hp5 (by omega)
  have hS2 : ‖S2‖ ≤ q p ^ (u+1) := by
    rw [hS2def, hk]
    exact norm_S2_le hp5 (by omega)
  -- expansion
  have hexp := norm_prod_one_add_expand (s := Iset p k) (x := fun i => (N : K)/(i : K))
    hδ1 hδ0 (norm_two_eq_one hp5) hx
  set S := ∑ i ∈ Iset p k, (N : K)/((i : ℕ) : K) with hSdef
  set Q := ∑ i ∈ Iset p k, ((N : K)/((i : ℕ) : K))^2 with hQdef
  have hSfac : S = (N : K) * S1 := by
    rw [hSdef, hS1def, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_one_div]
  have hQfac : Q = (N : K)^2 * S2 := by
    rw [hQdef, hS2def, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [div_pow, mul_one_div]
  -- individual bounds
  have hSnorm : ‖S‖ ≤ q p ^ (3 + (ρ + 2*u)) := by
    rw [hSfac, norm_mul]
    calc ‖(N:K)‖ * ‖S1‖ ≤ q p ^ (ρ+1) * q p ^ (2*(u+1)) :=
          mul_le_mul hN hS1 (norm_nonneg _) (q_pow_nonneg _)
    _ = q p ^ (3 + (ρ + 2*u)) := by rw [← pow_add]; ring_nf
  have hQnorm : ‖Q‖ ≤ q p ^ (3 + (2*ρ + u)) := by
    rw [hQfac, norm_mul, norm_pow]
    calc ‖(N:K)‖^2 * ‖S2‖ ≤ (q p ^ (ρ+1))^2 * q p ^ (u+1) := by
          refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hN 2) hS2 (norm_nonneg _) ?_
          exact pow_nonneg (q_pow_nonneg _) 2
    _ = q p ^ (3 + (2*ρ + u)) := by rw [← pow_mul, ← pow_add]; ring_nf
  have hS2norm : ‖S^2‖ ≤ q p ^ (3 + (ρ + 2*u)) := by
    rw [norm_pow]
    calc ‖S‖^2 ≤ (q p ^ (3 + (ρ + 2*u)))^2 :=
          pow_le_pow_left₀ (norm_nonneg _) hSnorm 2
    _ ≤ q p ^ (3 + (ρ + 2*u)) * 1 := by
          rw [pow_two]
          exact mul_le_mul_of_nonneg_left (q_pow_le_one _) (q_pow_nonneg _)
    _ = q p ^ (3 + (ρ + 2*u)) := mul_one _
  -- min exponent inequalities
  have hm1 : q p ^ (3 + (ρ + 2*u)) ≤ q p ^ (3 + em) :=
    q_pow_le_q_pow (by omega)
  have hm2 : q p ^ (3 + (2*ρ + u)) ≤ q p ^ (3 + em) :=
    q_pow_le_q_pow (by omega)
  have hm3 : δ^3 ≤ q p ^ (3 + em) := by
    rw [hδdef, ← pow_mul]
    exact q_pow_le_q_pow (by omega)
  -- assemble
  have hdecomp : Ebig p N k - 1
      = ((∏ i ∈ Iset p k, (1 + (N : K)/((i : ℕ) : K))) - (1 + S + (S^2 - Q)/2))
        + S + (S^2 - Q)/2 := by
    unfold Ebig
    ring
  calc ‖Ebig p N k - 1‖
      ≤ max ‖((∏ i ∈ Iset p k, (1 + (N : K)/((i : ℕ) : K))) - (1 + S + (S^2 - Q)/2)) + S‖
          ‖(S^2 - Q)/2‖ := by rw [hdecomp]; exact norm_add_le_max' _ _
  _ ≤ q p ^ (3 + em) := by
      refine max_le ((norm_add_le_max' _ _).trans (max_le ?_ ?_)) ?_
      · exact hexp.trans hm3
      · exact hSnorm.trans hm1
      · rw [norm_div, norm_two_eq_one hp5, div_one]
        refine (norm_sub_le_max' _ _).trans (max_le ?_ ?_)
        · exact hS2norm.trans hm1
        · exact hQnorm.trans hm2

/-- Kummer-type norm bound: `‖C(M+j, j)‖ * ‖j‖ ≤ ‖M+j‖`. -/
lemma norm_choose_mul_le {M j : ℕ} (hj : 1 ≤ j) :
    ‖((((M+j).choose j : ℕ)) : K)‖ * ‖((j : ℕ) : K)‖ ≤ ‖(((M+j : ℕ)) : K)‖ := by
  have hnat : (M+j) * ((M+j-1).choose (j-1)) = ((M+j).choose j) * j := by
    have h0 := Nat.succ_mul_choose_eq (M+j-1) (j-1)
    simp only [Nat.succ_eq_add_one] at h0
    have e1 : M+j-1+1 = M+j := by omega
    have e2 : j-1+1 = j := by omega
    rw [e1, e2] at h0
    exact h0
  have hcast : (((M+j : ℕ)) : K) * ((((M+j-1).choose (j-1) : ℕ)) : K)
      = ((((M+j).choose j : ℕ)) : K) * ((j : ℕ) : K) := by
    exact_mod_cast hnat
  calc ‖((((M+j).choose j : ℕ)) : K)‖ * ‖((j : ℕ) : K)‖
      = ‖((((M+j).choose j : ℕ)) : K) * ((j : ℕ) : K)‖ := (norm_mul _ _).symm
  _ = ‖(((M+j : ℕ)) : K) * ((((M+j-1).choose (j-1) : ℕ)) : K)‖ := by rw [hcast]
  _ = ‖(((M+j : ℕ)) : K)‖ * ‖((((M+j-1).choose (j-1) : ℕ)) : K)‖ := norm_mul _ _
  _ ≤ ‖(((M+j : ℕ)) : K)‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_nat_le_one _) (norm_nonneg _)
  _ = ‖(((M+j : ℕ)) : K)‖ := mul_one _
/- ### Part 1: term identity and bound -/

/-- `C(A+k-1, k) = A * C(A+k, k) / (A+k)` in `K`, for `A ≥ 1`. -/
lemma choose_pred_eq {A k : ℕ} (hA : 0 < A) :
    ((((A + k - 1).choose k : ℕ)) : K)
      = (A : K) * ((((A+k).choose k : ℕ)) : K) / (((A + k : ℕ)) : K) := by
  have hnat : (A+k-1).choose k * (A+k) = (A+k).choose k * A := by
    have h0 := Nat.choose_mul_succ_eq (A+k-1) k
    have e1 : A+k-1+1 = A+k := by omega
    rw [e1] at h0
    have e2 : A+k-k = A := by omega
    rw [e2] at h0
    exact h0
  have hAk0 : (((A + k : ℕ)) : K) ≠ 0 := nat_cast_ne_zero (by omega)
  rw [eq_div_iff hAk0]
  exact_mod_cast hnat.trans (Nat.mul_comm _ _)

/-- The Part 1 term identity. -/
lemma PT1_term_eq (hp5 : 5 ≤ p) {M j : ℕ} (hM0 : 0 < M) (hj : 1 ≤ j) :
    (((p*M + 2*(p*j) : ℕ)) : K) * ((((p*M + p*j - 1).choose (p*j) : ℕ)) : K)^3
        / (((p*M : ℕ)) : K)
      - (((M + 2*j : ℕ)) : K) * ((((M + j - 1).choose j : ℕ)) : K)^3 / ((M : ℕ) : K)
    = (((M + 2*j : ℕ)) : K) * ((M : ℕ) : K)^2 * ((((M+j).choose j : ℕ)) : K)^3
        * ((Ebig p (p*M) (p*j))^3 - 1) / (((M + j : ℕ)) : K)^3 := by
  have hp0 : (0:ℕ) < p := hp.out.pos
  have hpM0 : 0 < p * M := Nat.mul_pos hp0 hM0
  have hCN := choose_pred_eq (p := p) (A := p*M) (k := p*j) hpM0
  have hCM := choose_pred_eq (p := p) (A := M) (k := j) hM0
  have hdiv : (p*j) / p = j := Nat.mul_div_cancel_left j hp0
  have hsplit := choose_split (p := p) (N := p*M) (M := M) (k := p*j) rfl
  rw [hdiv] at hsplit
  rw [hCN, hCM, hsplit]
  -- cast simplifications
  have hc1 : (((p*M + 2*(p*j) : ℕ)) : K) = (p : K) * (((M + 2*j : ℕ)) : K) := by
    push_cast; ring
  have hc2 : (((p*M + p*j : ℕ)) : K) = (p : K) * (((M + j : ℕ)) : K) := by
    push_cast; ring
  have hc3 : (((p*M : ℕ)) : K) = (p : K) * ((M : ℕ) : K) := by
    push_cast; ring
  rw [hc1, hc2, hc3]
  have hp0' : (p : K) ≠ 0 := nat_cast_ne_zero (by omega)
  have hM0' : ((M : ℕ) : K) ≠ 0 := nat_cast_ne_zero (by omega)
  have hMj0' : (((M + j : ℕ)) : K) ≠ 0 := nat_cast_ne_zero (by omega)
  field_simp


/-- Bounding a product of four nonnegative reals. -/
lemma prod4_le {a b c d A B C D : ℝ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) (hd : d ≤ D)
    (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C) :
    a*b*c*d ≤ A*B*C*D := by
  have h1 : a*b ≤ A*B := mul_le_mul ha hb hb0 hA0
  have h2 : a*b*c ≤ A*B*C := mul_le_mul h1 hc hc0 (mul_nonneg hA0 hB0)
  exact mul_le_mul h2 hd hd0 (mul_nonneg (mul_nonneg hA0 hB0) hC0)

/-- The Part 1 termwise bound. -/
lemma PT1_term_bound (hp5 : 5 ≤ p) {n ρ j : ℕ} (hn : ¬ p ∣ n) (hj : 1 ≤ j) :
    ‖(((n*p^ρ + 2*j : ℕ)) : K) * (((n*p^ρ : ℕ)) : K)^2
        * ((((n*p^ρ+j).choose j : ℕ)) : K)^3
        * ((Ebig p (p*(n*p^ρ)) (p*j))^3 - 1) / (((n*p^ρ + j : ℕ)) : K)^3‖
      ≤ q p ^ (3 + 3*ρ) := by
  classical
  set M := n * p^ρ with hMdef
  have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h => hn (h ▸ dvd_zero p))
  have hM0 : 0 < M := by
    have := p_pow_pos (p := p) ρ
    exact Nat.mul_pos hn0 this
  -- factor j
  obtain ⟨u, j'', hj''nd, hjeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.one_le_iff_ne_zero.mp hj) p hp.out.ne_one
  have hjeq' : j = j'' * p^u := by rw [hjeq]; ring
  -- exact norms
  have hMnorm : ‖((M : ℕ) : K)‖ = q p ^ ρ := by
    rw [hMdef]; exact norm_nat_mul_pow hn
  have hjnorm : ‖((j : ℕ) : K)‖ = q p ^ u := by
    rw [hjeq']; exact norm_nat_mul_pow hj''nd
  have h2j''nd : ¬ p ∣ (2 * j'') := by
    intro h
    rcases (Nat.Prime.dvd_mul hp.out).mp h with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · exact hj''nd h
  have h2jnorm : ‖((2*j : ℕ) : K)‖ = q p ^ u := by
    have : 2*j = (2*j'') * p^u := by rw [hjeq']; ring
    rw [this]; exact norm_nat_mul_pow h2j''nd
  -- bound on E³ - 1
  have hNnorm : ‖(((p*M : ℕ)) : K)‖ ≤ q p ^ (ρ+1) := by
    have hcast : (((p*M : ℕ)) : K) = (p:K) * ((M:ℕ):K) := by push_cast; ring
    rw [hcast, norm_mul, Padic.norm_p, hMnorm]
    rw [_root_.pow_succ']
    apply mul_le_mul_of_nonneg_right ?_ (q_pow_nonneg ρ)
    exact le_of_eq rfl
  have hjarg : p * j = p * (j'' * p^u) := by rw [hjeq']
  have hE1 : ‖Ebig p (p*M) (p*j) - 1‖
      ≤ q p ^ (3 + min (ρ + 2*u) (min (2*ρ + u) (3*ρ))) := by
    rw [hjarg]
    exact norm_R_sub_one hp5 hNnorm hj''nd
  have hE3 : ‖(Ebig p (p*M) (p*j))^3 - 1‖
      ≤ q p ^ (3 + min (ρ + 2*u) (min (2*ρ + u) (3*ρ))) :=
    (norm_cube_sub_one_le norm_Ebig_le_one).trans hE1
  -- generic norm pieces
  have hC1 : ‖((((M+j).choose j : ℕ)) : K)‖ ≤ 1 := norm_nat_le_one _
  have hMj0 : (((M + j : ℕ)) : K) ≠ 0 := nat_cast_ne_zero (by omega)
  have hτpos : 0 < ‖(((M + j : ℕ)) : K)‖ := norm_pos_iff.mpr hMj0
  have hcastMj : (((M + j : ℕ)) : K) = ((M:ℕ) : K) + ((j:ℕ) : K) := by push_cast; ring
  have hcastM2j : (((M + 2*j : ℕ)) : K) = ((M:ℕ) : K) + ((2*j:ℕ) : K) := by push_cast; ring
  -- expand the norm of the whole expression
  rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, hMnorm]
  rw [div_le_iff₀ (pow_pos hτpos 3)]
  rcases lt_trichotomy u ρ with hu | hu | hu
  · -- case u < ρ : ‖M+j‖ = ‖M+2j‖ = q^u
    have hem : min (ρ + 2*u) (min (2*ρ + u) (3*ρ)) = ρ + 2*u := by omega
    rw [hem] at hE3
    have hne : ‖((M:ℕ) : K)‖ ≠ ‖((j:ℕ) : K)‖ := by
      rw [hMnorm, hjnorm]; exact q_pow_ne_q_pow (by omega)
    have hne2 : ‖((M:ℕ) : K)‖ ≠ ‖((2*j:ℕ) : K)‖ := by
      rw [hMnorm, h2jnorm]; exact q_pow_ne_q_pow (by omega)
    have hMj : ‖(((M + j : ℕ)) : K)‖ = q p ^ u := by
      rw [hcastMj, Padic.add_eq_max_of_ne hne, hMnorm, hjnorm]
      exact max_eq_right (q_pow_le_q_pow (by omega))
    have hM2j : ‖(((M + 2*j : ℕ)) : K)‖ = q p ^ u := by
      rw [hcastM2j, Padic.add_eq_max_of_ne hne2, hMnorm, h2jnorm]
      exact max_eq_right (q_pow_le_q_pow (by omega))
    rw [hMj, hM2j]
    have hstep : q p ^ u * (q p ^ ρ)^2 * ‖((((M+j).choose j : ℕ)) : K)‖^3
          * ‖(Ebig p (p*M) (p*j))^3 - 1‖
        ≤ q p ^ u * (q p ^ ρ)^2 * 1^3 * q p ^ (3 + (ρ + 2*u)) :=
      prod4_le le_rfl le_rfl (pow_le_pow_left₀ (norm_nonneg _) hC1 3) hE3
        (pow_nonneg (q_pow_nonneg ρ) 2) (pow_nonneg (norm_nonneg _) 3) (norm_nonneg _)
        (q_pow_nonneg u) (pow_nonneg (q_pow_nonneg ρ) 2) (by norm_num)
    refine hstep.trans (le_of_eq ?_)
    rw [one_pow, mul_one, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  · -- case u = ρ : Kummer bound
    have hem : min (ρ + 2*u) (min (2*ρ + u) (3*ρ)) = 3*ρ := by omega
    rw [hem] at hE3
    set τ := ‖(((M + j : ℕ)) : K)‖ with hτdef
    have hM2j : ‖(((M + 2*j : ℕ)) : K)‖ ≤ q p ^ ρ := by
      rw [hcastM2j]
      refine (norm_add_le_max' _ _).trans (max_le (le_of_eq hMnorm) ?_)
      rw [h2jnorm, hu]
    have hChoose : ‖((((M+j).choose j : ℕ)) : K)‖ ≤ τ / q p ^ ρ := by
      rw [le_div_iff₀ (pow_pos q_pos ρ)]
      have := norm_choose_mul_le (p := p) (M := M) (j := j) hj
      rwa [hjnorm, hu] at this
    have hstep : ‖(((M + 2*j : ℕ)) : K)‖ * (q p ^ ρ)^2 * ‖((((M+j).choose j : ℕ)) : K)‖^3
          * ‖(Ebig p (p*M) (p*j))^3 - 1‖
        ≤ q p ^ ρ * (q p ^ ρ)^2 * (τ / q p ^ ρ)^3 * q p ^ (3 + 3*ρ) :=
      prod4_le hM2j le_rfl (pow_le_pow_left₀ (norm_nonneg _) hChoose 3) hE3
        (pow_nonneg (q_pow_nonneg ρ) 2) (pow_nonneg (norm_nonneg _) 3) (norm_nonneg _)
        (q_pow_nonneg ρ) (pow_nonneg (q_pow_nonneg ρ) 2)
        (pow_nonneg (div_nonneg (norm_nonneg _) (q_pow_nonneg ρ)) 3)
    refine hstep.trans (le_of_eq ?_)
    have hqρ : (q p ^ ρ : ℝ) ≠ 0 := (pow_pos q_pos ρ).ne'
    field_simp
  · -- case ρ < u : ‖M+j‖ = ‖M+2j‖ = q^ρ
    have hem : min (ρ + 2*u) (min (2*ρ + u) (3*ρ)) = 3*ρ := by omega
    rw [hem] at hE3
    have hne : ‖((M:ℕ) : K)‖ ≠ ‖((j:ℕ) : K)‖ := by
      rw [hMnorm, hjnorm]; exact q_pow_ne_q_pow (by omega)
    have hne2 : ‖((M:ℕ) : K)‖ ≠ ‖((2*j:ℕ) : K)‖ := by
      rw [hMnorm, h2jnorm]; exact q_pow_ne_q_pow (by omega)
    have hMj : ‖(((M + j : ℕ)) : K)‖ = q p ^ ρ := by
      rw [hcastMj, Padic.add_eq_max_of_ne hne, hMnorm, hjnorm]
      exact max_eq_left (q_pow_le_q_pow (by omega))
    have hM2j : ‖(((M + 2*j : ℕ)) : K)‖ = q p ^ ρ := by
      rw [hcastM2j, Padic.add_eq_max_of_ne hne2, hMnorm, h2jnorm]
      exact max_eq_left (q_pow_le_q_pow (by omega))
    rw [hMj, hM2j]
    have hstep : q p ^ ρ * (q p ^ ρ)^2 * ‖((((M+j).choose j : ℕ)) : K)‖^3
          * ‖(Ebig p (p*M) (p*j))^3 - 1‖
        ≤ q p ^ ρ * (q p ^ ρ)^2 * 1^3 * q p ^ (3 + 3*ρ) :=
      prod4_le le_rfl le_rfl (pow_le_pow_left₀ (norm_nonneg _) hC1 3) hE3
        (pow_nonneg (q_pow_nonneg ρ) 2) (pow_nonneg (norm_nonneg _) 3) (norm_nonneg _)
        (q_pow_nonneg ρ) (pow_nonneg (q_pow_nonneg ρ) 2) (by norm_num)
    refine hstep.trans (le_of_eq ?_)
    rw [one_pow, mul_one, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega

/-- Part 1: the difference of the two sums over multiples of `p` is small. -/
lemma PT1_bound (hp5 : 5 ≤ p) {n r : ℕ} (hn : ¬ p ∣ n) (hr : 1 ≤ r) :
    ‖∑ j ∈ Finset.range (n*p^(r-1) + 1),
        ((((n*p^r + 2*(p*j) : ℕ)) : K) * ((((n*p^r + p*j - 1).choose (p*j) : ℕ)) : K)^3
            / (((n*p^r : ℕ)) : K)
          - (((n*p^(r-1) + 2*j : ℕ)) : K) * ((((n*p^(r-1) + j - 1).choose j : ℕ)) : K)^3
            / (((n*p^(r-1) : ℕ)) : K))‖
      ≤ q p ^ (3*r) := by
  classical
  set M := n * p^(r-1) with hMdef
  have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h => hn (h ▸ dvd_zero p))
  have hM0 : 0 < M := by
    have := p_pow_pos (p := p) (r-1)
    exact Nat.mul_pos hn0 this
  have hr' : r - 1 + 1 = r := by omega
  have hppow : p^(r-1) * p = p^r := by rw [← pow_succ, hr']
  have hNM : n*p^r = p * M := by
    rw [hMdef, ← hppow]; ring
  have hexp : (3:ℕ)*r = 3 + 3*(r-1) := by omega
  rw [hNM, hexp]
  refine norm_sum_le' (q_pow_nonneg _) (fun j hj => ?_)
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · -- j = 0 : both terms equal 1
    have hpM0 : (0:ℕ) < p * M := Nat.mul_pos hp.out.pos hM0
    have h1 : (((p*M + 2*(p*0) : ℕ)) : K) * ((((p*M + p*0 - 1).choose (p*0) : ℕ)) : K)^3
        / (((p*M : ℕ)) : K) = 1 := by
      simp only [Nat.mul_zero, Nat.add_zero, Nat.choose_zero_right]
      rw [Nat.cast_one, one_pow, mul_one]
      exact div_self (nat_cast_ne_zero (by omega))
    have h2 : (((M + 2*0 : ℕ)) : K) * ((((M + 0 - 1).choose 0 : ℕ)) : K)^3
        / (((M : ℕ)) : K) = 1 := by
      simp only [Nat.mul_zero, Nat.add_zero, Nat.choose_zero_right]
      rw [Nat.cast_one, one_pow, mul_one]
      exact div_self (nat_cast_ne_zero (by omega))
    rw [h1, h2, sub_self, norm_zero]
    exact q_pow_nonneg _
  · rw [PT1_term_eq hp5 hM0 hjpos]
    have := PT1_term_bound (p := p) hp5 (n := n) (ρ := r-1) (j := j) hn hjpos
    rw [← hMdef] at this
    exact this
/- ### Integrality of `a` and the final assembly -/

/-- The `ℕ`-level identity `(A+k-1).choose k * (A+k) = (A+k).choose k * A`. -/
lemma choose_pred_nat {A k : ℕ} (hA : 0 < A) :
    (A+k-1).choose k * (A+k) = (A+k).choose k * A := by
  have h0 := Nat.choose_mul_succ_eq (A+k-1) k
  have e1 : A+k-1+1 = A+k := by omega
  rw [e1] at h0
  have e2 : A+k-k = A := by omega
  rw [e2] at h0
  exact h0

/-- The symmetric form of the binomial coefficient in the definition of `a`. -/
lemma choose_symm_a {n k : ℕ} (hn : 0 < n) :
    (n + k - 1).choose (n - 1) = (n + k - 1).choose k := by
  have h1 : n - 1 ≤ n + k - 1 := by omega
  have h2 := Nat.choose_symm h1
  have h3 : n + k - 1 - (n - 1) = k := by omega
  rw [h3] at h2
  exact h2.symm

/-- The divisibility `n ∣ S n` giving integrality of `a`. -/
lemma S_eq_n_mul (n : ℕ) (hn : 0 < n) :
    (Finset.sum (Finset.range (n + 1)) fun k => (n + 2 * k) * ((n + k - 1).choose k) ^ 3)
      = n * ((Finset.sum (Finset.range (n + 1)) fun k =>
            ((n+k).choose k) * ((n + k - 1).choose k)^2)
          + (Finset.sum (Finset.range n) fun k =>
            ((n+k).choose k) * ((n + k).choose (k+1))^2)) := by
  have hsplit : ∀ k : ℕ, (n + 2 * k) * ((n + k - 1).choose k) ^ 3
      = (n + k) * ((n + k - 1).choose k) ^ 3 + k * ((n + k - 1).choose k) ^ 3 := by
    intro k
    ring
  rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib]
  have hA : (Finset.sum (Finset.range (n + 1)) fun k => (n + k) * ((n + k - 1).choose k) ^ 3)
      = n * (Finset.sum (Finset.range (n + 1)) fun k =>
        ((n+k).choose k) * ((n + k - 1).choose k)^2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have h1 : (n + k) * ((n + k - 1).choose k) ^ 3
        = ((n + k - 1).choose k * (n+k)) * ((n + k - 1).choose k) ^ 2 := by ring
    rw [h1, choose_pred_nat hn]
    ring
  have hB : (Finset.sum (Finset.range (n + 1)) fun k => k * ((n + k - 1).choose k) ^ 3)
      = n * (Finset.sum (Finset.range n) fun k =>
        ((n+k).choose k) * ((n + k).choose (k+1))^2) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.zero_mul, Nat.add_zero, zero_mul, add_zero]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have e1 : n + (k+1) - 1 = n + k := by omega
    rw [e1]
    have h2 : (n + k).choose (k+1) * (k+1) = (n+k).choose k * n := by
      have := Nat.choose_succ_right_eq (n+k) k
      have e2 : n + k - k = n := by omega
      rw [e2] at this
      exact this
    have h1 : (k + 1) * ((n + k).choose (k+1)) ^ 3
        = ((n + k).choose (k+1) * (k+1)) * ((n + k).choose (k+1)) ^ 2 := by ring
    rw [h1, h2]
    ring
  rw [hA, hB, ← Nat.mul_add]

/-- `a n` as a `p`-adic sum. -/
lemma a_cast (m : ℕ) (hm : 0 < m) :
    ((a m : ℕ) : K) = ∑ k ∈ Finset.range (m + 1),
      (((m + 2 * k : ℕ)) : K) * ((((m + k - 1).choose k : ℕ)) : K)^3 / ((m : ℕ) : K) := by
  have hm' : m ≠ 0 := by omega
  have ha : a m = (Finset.sum (Finset.range (m + 1)) fun k =>
      (m + 2 * k) * ((m + k - 1).choose (m - 1)) ^ 3) / m := by
    unfold a
    rw [if_neg hm']
  have hsymm : (Finset.sum (Finset.range (m + 1)) fun k =>
      (m + 2 * k) * ((m + k - 1).choose (m - 1)) ^ 3)
      = (Finset.sum (Finset.range (m + 1)) fun k =>
      (m + 2 * k) * ((m + k - 1).choose k) ^ 3) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [choose_symm_a hm]
  rw [hsymm] at ha
  rw [S_eq_n_mul m hm] at ha
  rw [Nat.mul_div_cancel_left _ hm] at ha
  -- now the K-side
  have hm0 : ((m : ℕ) : K) ≠ 0 := nat_cast_ne_zero hm'
  rw [← Finset.sum_div]
  rw [eq_div_iff hm0]
  have hcastS : ((Finset.sum (Finset.range (m + 1)) fun k =>
        (m + 2 * k) * ((m + k - 1).choose k) ^ 3 : ℕ) : K)
      = ∑ k ∈ Finset.range (m+1),
          (((m + 2*k : ℕ)) : K) * ((((m + k - 1).choose k : ℕ)) : K)^3 := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    push_cast
    ring
  have hSnat : (Finset.sum (Finset.range (m + 1)) fun k =>
      (m + 2 * k) * ((m + k - 1).choose k) ^ 3) = a m * m := by
    rw [ha, S_eq_n_mul m hm]
    ring
  rw [← hcastS]
  exact_mod_cast congrArg (fun t : ℕ => (t : K)) hSnat.symm
/-- The intermediate supercongruence for `p ∤ n`. -/
theorem main_congruence (hp5 : 5 ≤ p) {n r : ℕ} (hn : ¬ p ∣ n) (hr : 1 ≤ r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  classical
  have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h => hn (h ▸ dvd_zero p))
  set N := n * p^r with hNdef
  set M := n * p^(r-1) with hMdef
  have hM0 : 0 < M := Nat.mul_pos hn0 (p_pow_pos (p := p) (r-1))
  have hN0 : 0 < N := Nat.mul_pos hn0 (p_pow_pos (p := p) r)
  have hr' : r - 1 + 1 = r := by omega
  have hppow : p^(r-1) * p = p^r := by rw [← pow_succ, hr']
  have hNM : N = p * M := by rw [hNdef, hMdef, ← hppow]; ring
  -- the p-adic estimate
  have hkey : ‖((a N : ℕ) : K) - ((a M : ℕ) : K)‖ ≤ q p ^ (3*r) := by
    rw [a_cast N hN0, a_cast M hM0]
    -- split the sum over range (N+1) into multiples of p and the rest
    set F : ℕ → K := fun k =>
      (((N + 2 * k : ℕ)) : K) * ((((N + k - 1).choose k : ℕ)) : K)^3 / ((N : ℕ) : K) with hFdef
    have hFsplit : ∑ k ∈ Finset.range (N + 1), F k
        = (∑ k ∈ (Finset.range (N+1)).filter (fun k => p ∣ k), F k)
          + ∑ k ∈ (Finset.range (N+1)).filter (fun k => ¬ p ∣ k), F k :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have himg : (Finset.range (N+1)).filter (fun k => p ∣ k)
        = (Finset.range (M+1)).image (fun j => p * j) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hlt, c, rfl⟩
        refine ⟨c, ?_, rfl⟩
        have : p * c ≤ N := by omega
        rw [hNM] at this
        have := Nat.le_of_mul_le_mul_left this hp.out.pos
        omega
      · rintro ⟨c, hc, rfl⟩
        constructor
        · have : c ≤ M := by omega
          have h2 : p * c ≤ p * M := Nat.mul_le_mul_left _ this
          rw [← hNM] at h2
          omega
        · exact ⟨c, rfl⟩
    have hmul : ∑ k ∈ (Finset.range (N+1)).filter (fun k => p ∣ k), F k
        = ∑ j ∈ Finset.range (M+1), F (p * j) := by
      rw [himg, Finset.sum_image]
      intro a _ b _ h
      exact Nat.eq_of_mul_eq_mul_left hp.out.pos h
    rw [hFsplit, hmul]
    have hrearr : (∑ j ∈ Finset.range (M+1), F (p * j))
        + (∑ k ∈ (Finset.range (N+1)).filter (fun k => ¬ p ∣ k), F k)
        - ∑ j ∈ Finset.range (M + 1),
            (((M + 2 * j : ℕ)) : K) * ((((M + j - 1).choose j : ℕ)) : K)^3 / ((M : ℕ) : K)
        = (∑ j ∈ Finset.range (M+1), (F (p * j)
            - (((M + 2 * j : ℕ)) : K) * ((((M + j - 1).choose j : ℕ)) : K)^3 / ((M : ℕ) : K)))
          + ∑ k ∈ (Finset.range (N+1)).filter (fun k => ¬ p ∣ k), F k := by
      rw [Finset.sum_sub_distrib]
      ring
    rw [hrearr]
    refine (norm_add_le_max' _ _).trans (max_le ?_ ?_)
    · -- Part 1
      have h1 := PT1_bound (p := p) hp5 (n := n) (r := r) hn hr
      rw [← hNdef, ← hMdef] at h1
      exact h1
    · -- Part 2
      have h2 := PT2_bound (p := p) hp5 (n := n) (r := r) hn hn0 hr
      rw [← hNdef] at h2
      exact h2
  -- convert the p-adic estimate to a `Nat.ModEq`
  have hint : ((p : ℤ) ^ (3*r)) ∣ ((a N : ℤ) - (a M : ℤ)) := by
    rw [← norm_int_le_pow_iff]
    have hcast : (((a N : ℤ) - (a M : ℤ) : ℤ) : K) = ((a N : ℕ) : K) - ((a M : ℕ) : K) := by
      push_cast
      ring
    rw [hcast]
    exact hkey
  refine (Nat.modEq_iff_dvd (n := p ^ (3*r)) (a := a N) (b := a M)).mpr ?_
  push_cast
  rw [show ((a M : ℤ) - (a N : ℤ)) = -((a N : ℤ) - (a M : ℤ)) from by ring]
  exact dvd_neg.mpr hint

end A361883

open A361883 in
/-- The final supercongruence, for arbitrary `n`. -/
theorem a_supercongruence {p n r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- write n = p^s * n' with p ∤ n'
  obtain ⟨s, n', hn', hneq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.ne_one
  have h1 : n * p ^ r = n' * p ^ (r + s) := by
    rw [hneq, pow_add]
    ring
  have h2 : n * p ^ (r - 1) = n' * p ^ ((r + s) - 1) := by
    rw [hneq]
    have e1 : (r + s) - 1 = (r - 1) + s := by omega
    rw [e1, pow_add]
    ring
  have hmain := main_congruence (p := p) hp5 (n := n') (r := r + s) hn' (by omega)
  rw [← h1, ← h2] at hmain
  exact hmain.of_dvd (pow_dvd_pow p (by omega))


end A361883Proof

/--
The central binomial coefficients $u(n) := \binom{2n}{n}$ satisfy the supercongruences
$u(n \cdot p^r) \equiv u(n \cdot p^{r-1}) \pmod{p^{3r}}$ for positive integers $n$ and $r$
and all primes $p \ge 5$. We conjecture that the present sequence $a(n)$ satisfies the same congruences.
-/
theorem oeis_361883_conjecture_0 {p n r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] :=
  a_supercongruence hp hp5 hn hr
