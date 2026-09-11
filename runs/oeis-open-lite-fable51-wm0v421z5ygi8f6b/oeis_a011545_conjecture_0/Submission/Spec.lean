import FormalConjectures.Util.ProblemImports

open Real Int

/--
A011545: $a(n)$ is the integer whose decimal digits are the first $n+1$ decimal digits of $\pi$.
This is equivalent to $a(n) = \lfloor \pi \cdot 10^n \rfloor$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The calculation is $\lfloor \pi \cdot 10^n \rfloor$.
  -- We use Real.floor, which returns an Int, and convert it to a natural number.
  (floor (Real.pi * (10 : ℝ) ^ n.cast)).toNat

/- ### Partial result: the conjecture holds for all `n ≤ 9999`.

The general statement is equivalent to the assertion that the decimal expansion of π
never contains a run of ≈ `n` nines starting at digit `n+1` (Galperin's billiard
conjecture), which is open (see the reduction further below). Here we certify it for all
`n ≤ 9999`:
* 10000 digits of π are proved from Machin's formula `π = 16 arctan(1/5) − 4 arctan(1/239)`;
  the alternating series is bounded by its partial sums, which are evaluated in fixed-point
  integer arithmetic (with explicit ±1 truncation error per term) by the kernel via
  `decide +kernel`, using balanced-tree summation to keep the evaluation depth small;
* the per-`n` check is reduced (via `aux_bound`) to a Boolean inequality between natural
  numbers, again checked by the kernel for all `n < 2^14`. -/

section PartialResult
open Finset

/-- Truncated term `⌊10^E / (a^(2i+1) (2i+1))⌋`. -/
def trm (a E i : ℕ) : ℕ := 10 ^ E / (a ^ (2 * i + 1) * (2 * i + 1))

/-- Signed lower-bound term (zero beyond `m`). -/
def lowT (a E m i : ℕ) : ℤ :=
  if i < m then (if i % 2 = 0 then (trm a E i : ℤ) else -((trm a E i : ℤ) + 1)) else 0

/-- Signed upper-bound term (zero beyond `m`). -/
def uppT (a E m i : ℕ) : ℤ :=
  if i < m then (if i % 2 = 0 then (trm a E i : ℤ) + 1 else -(trm a E i : ℤ)) else 0

/-- Balanced-tree summation `∑_{i < 2^d} f (lo + i)`, kernel-friendly. -/
def tree (f : ℕ → ℤ) : ℕ → ℕ → ℤ
  | lo, 0 => f lo
  | lo, d + 1 => tree f lo d + tree f (lo + 2 ^ d) d

lemma tree_eq (f : ℕ → ℤ) (lo d : ℕ) : tree f lo d = ∑ i ∈ range (2 ^ d), f (lo + i) := by
  induction d generalizing lo with
  | zero => simp [tree]
  | succ d ih =>
    rw [tree, ih, ih, pow_succ, mul_two, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_assoc]

lemma sum_range_of_vanish (f : ℕ → ℤ) (m M : ℕ) (hm : m ≤ M) (hf : ∀ i, m ≤ i → f i = 0) :
    ∑ i ∈ range M, f i = ∑ i ∈ range m, f i := by
  symm
  apply Finset.sum_subset (Finset.range_mono hm)
  intro i hi hni
  simp only [Finset.mem_range, not_lt] at hi hni
  exact hf i hni

lemma tree_lowT (a E m d : ℕ) (hm : m ≤ 2 ^ d) :
    tree (lowT a E m) 0 d = ∑ i ∈ range m, lowT a E m i := by
  rw [tree_eq]
  simp only [zero_add]
  exact sum_range_of_vanish _ m _ hm fun i hi => by simp [lowT, not_lt.2 hi]

lemma tree_uppT (a E m d : ℕ) (hm : m ≤ 2 ^ d) :
    tree (uppT a E m) 0 d = ∑ i ∈ range m, uppT a E m i := by
  rw [tree_eq]
  simp only [zero_add]
  exact sum_range_of_vanish _ m _ hm fun i hi => by simp [uppT, not_lt.2 hi]

/-- The real value of the `i`-th series term, scaled by `10^E`. -/
lemma trm_bounds (a E i : ℕ) (ha : 0 < a) :
    (trm a E i : ℝ) ≤ 10 ^ E * ((1 / (a : ℝ)) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) ∧
    10 ^ E * ((1 / (a : ℝ)) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) < (trm a E i : ℝ) + 1 := by
  set q : ℕ := a ^ (2 * i + 1) * (2 * i + 1) with hq
  have hqpos : 0 < q := by positivity
  have hqpos' : (0 : ℝ) < q := by exact_mod_cast hqpos
  have h1 : trm a E i * q ≤ 10 ^ E := Nat.div_mul_le_self _ _
  have h2 : 10 ^ E < trm a E i * q + q := Nat.lt_div_mul_add hqpos
  have h1' : (trm a E i : ℝ) * q ≤ 10 ^ E := by exact_mod_cast h1
  have h2' : (10 : ℝ) ^ E < trm a E i * q + q := by exact_mod_cast h2
  have e : (10 : ℝ) ^ E * ((1 / (a : ℝ)) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) = 10 ^ E / q := by
    rw [hq]; push_cast
    have : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    rw [one_div, inv_pow]
    field_simp
  rw [e]
  constructor
  · rw [le_div_iff₀ hqpos']; exact h1'
  · rw [div_lt_iff₀ hqpos']; linarith

lemma lowT_le (a E m i : ℕ) (ha : 0 < a) (hi : i < m) :
    (lowT a E m i : ℝ) ≤ 10 ^ E * ((-1) ^ i * ((1 / (a : ℝ)) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ))) := by
  obtain ⟨b1, b2⟩ := trm_bounds a E i ha
  push_cast at b1 b2
  simp only [lowT, if_pos hi]
  rcases Nat.even_or_odd i with he | ho
  · rw [if_pos (Nat.even_iff.1 he), he.neg_one_pow]; push_cast; linarith
  · rw [if_neg (by rw [Nat.odd_iff.1 ho]; norm_num), ho.neg_one_pow]; push_cast; linarith

lemma le_uppT (a E m i : ℕ) (ha : 0 < a) (hi : i < m) :
    10 ^ E * ((-1) ^ i * ((1 / (a : ℝ)) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ))) ≤ (uppT a E m i : ℝ) := by
  obtain ⟨b1, b2⟩ := trm_bounds a E i ha
  push_cast at b1 b2
  simp only [uppT, if_pos hi]
  rcases Nat.even_or_odd i with he | ho
  · rw [if_pos (Nat.even_iff.1 he), he.neg_one_pow]; push_cast; linarith
  · rw [if_neg (by rw [Nat.odd_iff.1 ho]; norm_num), ho.neg_one_pow]; push_cast; linarith

lemma sum_lowT_le (a E m : ℕ) (ha : 0 < a) :
    ((∑ i ∈ range m, lowT a E m i : ℤ) : ℝ) ≤
      10 ^ E * ∑ i ∈ range m, (-1) ^ i * ((1 / (a : ℝ)) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) := by
  rw [Finset.mul_sum]; push_cast
  refine Finset.sum_le_sum fun i hi => ?_
  have := lowT_le a E m i ha (Finset.mem_range.1 hi)
  push_cast at this
  exact this

lemma le_sum_uppT (a E m : ℕ) (ha : 0 < a) :
    10 ^ E * ∑ i ∈ range m, (-1) ^ i * ((1 / (a : ℝ)) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) ≤
      ((∑ i ∈ range m, uppT a E m i : ℤ) : ℝ) := by
  rw [Finset.mul_sum]; push_cast
  refine Finset.sum_le_sum fun i hi => ?_
  have := le_uppT a E m i ha (Finset.mem_range.1 hi)
  push_cast at this
  exact this

/-- Alternating-series bounds for `arctan` on `[0, 1)`. -/
lemma arctan_partial_sum_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    (∑ i ∈ range (2 * k), (-1) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ))) ≤ arctan x ∧
    arctan x ≤ ∑ i ∈ range (2 * k + 1), (-1) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) := by
  have hs := Real.hasSum_arctan (x := x) (by rwa [Real.norm_eq_abs, abs_of_nonneg hx0])
  set f : ℕ → ℝ := fun i => x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ) with hf
  have hs' : HasSum (fun i => (-1) ^ i * f i) (arctan x) := by
    convert hs using 1
    ext i
    simp only [hf]
    rw [mul_div_assoc]
  have ht := hs'.tendsto_sum_nat
  have hanti : Antitone f := by
    intro i j hij
    simp only [hf]
    have hpow : x ^ (2 * j + 1) ≤ x ^ (2 * i + 1) :=
      pow_le_pow_of_le_one hx0 hx1.le (by omega)
    have hden : ((2 * i + 1 : ℕ) : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hpos : (0 : ℝ) < ((2 * i + 1 : ℕ) : ℝ) := by positivity
    exact div_le_div₀ (by positivity) hpow hpos hden
  exact ⟨hanti.alternating_series_le_tendsto ht k, hanti.tendsto_le_alternating_series ht k⟩

/-- Machin's formula. -/
theorem machin : π = 16 * arctan (1 / 5) - 4 * arctan (1 / 239) := by
  have h1 : 2 * arctan (1 / 5 : ℝ) = arctan (5 / 12) := by
    rw [two_mul_arctan (by norm_num) (by norm_num)]; norm_num
  have h2 : 2 * arctan (5 / 12 : ℝ) = arctan (120 / 119) := by
    rw [two_mul_arctan (by norm_num) (by norm_num)]; norm_num
  have h3 : arctan (120 / 119 : ℝ) + arctan (-(1 / 239)) = arctan 1 := by
    rw [arctan_add (by norm_num)]; norm_num
  rw [arctan_neg, arctan_one] at h3
  linarith

/-- Lower bound on `10^E · π` from kernel-computable integers. -/
theorem low_le_pi (E k₁ k₂ d₁ d₂ : ℕ) (h₁ : 2 * k₁ ≤ 2 ^ d₁) (h₂ : 2 * k₂ + 1 ≤ 2 ^ d₂) :
    ((16 * tree (lowT 5 E (2 * k₁)) 0 d₁ - 4 * tree (uppT 239 E (2 * k₂ + 1)) 0 d₂ : ℤ) : ℝ) ≤
      10 ^ E * π := by
  rw [tree_lowT _ _ _ _ h₁, tree_uppT _ _ _ _ h₂]
  have a1 := sum_lowT_le 5 E (2 * k₁) (by norm_num)
  have a2 := le_sum_uppT 239 E (2 * k₂ + 1) (by norm_num)
  have b1 := (arctan_partial_sum_bounds (1 / 5) (by norm_num) (by norm_num) k₁).1
  have b2 := (arctan_partial_sum_bounds (1 / 239) (by norm_num) (by norm_num) k₂).2
  push_cast at a1 a2 b1 b2 ⊢
  rw [machin]
  have hE : (0 : ℝ) ≤ 10 ^ E := by positivity
  nlinarith [mul_le_mul_of_nonneg_left b1 hE, mul_le_mul_of_nonneg_left b2 hE]

/-- Upper bound on `10^E · π` from kernel-computable integers. -/
theorem pi_le_upp (E k₁ k₂ d₁ d₂ : ℕ) (h₁ : 2 * k₁ + 1 ≤ 2 ^ d₁) (h₂ : 2 * k₂ ≤ 2 ^ d₂) :
    10 ^ E * π ≤
      ((16 * tree (uppT 5 E (2 * k₁ + 1)) 0 d₁ - 4 * tree (lowT 239 E (2 * k₂)) 0 d₂ : ℤ) : ℝ) := by
  rw [tree_lowT _ _ _ _ h₂, tree_uppT _ _ _ _ h₁]
  have a1 := le_sum_uppT 5 E (2 * k₁ + 1) (by norm_num)
  have a2 := sum_lowT_le 239 E (2 * k₂) (by norm_num)
  have b1 := (arctan_partial_sum_bounds (1 / 5) (by norm_num) (by norm_num) k₁).2
  have b2 := (arctan_partial_sum_bounds (1 / 239) (by norm_num) (by norm_num) k₂).1
  push_cast at a1 a2 b1 b2 ⊢
  rw [machin]
  have hE : (0 : ℝ) ≤ 10 ^ E := by positivity
  nlinarith [mul_le_mul_of_nonneg_left b1 hE, mul_le_mul_of_nonneg_left b2 hE]

/-- From integer certificates, deduce `P / 10^D < π < (P+1) / 10^D`. -/
theorem pi_bounds_of_cert (P D E k₁ k₂ d₁ d₂ : ℕ) (hDE : D ≤ E)
    (h₁ : 2 * k₁ + 1 ≤ 2 ^ d₁) (h₂ : 2 * k₂ + 1 ≤ 2 ^ d₂)
    (hlo : (P : ℤ) * 10 ^ (E - D) <
      16 * tree (lowT 5 E (2 * k₁)) 0 d₁ - 4 * tree (uppT 239 E (2 * k₂ + 1)) 0 d₂)
    (hhi : 16 * tree (uppT 5 E (2 * k₁ + 1)) 0 d₁ - 4 * tree (lowT 239 E (2 * k₂)) 0 d₂ <
      ((P : ℤ) + 1) * 10 ^ (E - D)) :
    (P : ℝ) / 10 ^ D < π ∧ π < ((P : ℝ) + 1) / 10 ^ D := by
  have l := low_le_pi E k₁ k₂ d₁ d₂ (by omega) h₂
  have u := pi_le_upp E k₁ k₂ d₁ d₂ h₁ (by omega)
  have hlo' : (P : ℝ) * 10 ^ (E - D) <
      ((16 * tree (lowT 5 E (2 * k₁)) 0 d₁ - 4 * tree (uppT 239 E (2 * k₂ + 1)) 0 d₂ : ℤ) : ℝ) := by
    exact_mod_cast hlo
  have hhi' : ((16 * tree (uppT 5 E (2 * k₁ + 1)) 0 d₁ - 4 * tree (lowT 239 E (2 * k₂)) 0 d₂ : ℤ) : ℝ) <
      ((P : ℝ) + 1) * 10 ^ (E - D) := by
    exact_mod_cast hhi
  have hsplit : (10 : ℝ) ^ E = 10 ^ D * 10 ^ (E - D) := by
    rw [← pow_add, Nat.add_sub_cancel' hDE]
  have hD : (0 : ℝ) < 10 ^ D := by positivity
  have hED : (0 : ℝ) < 10 ^ (E - D) := by positivity
  constructor
  · rw [div_lt_iff₀ hD]
    have : (P : ℝ) * 10 ^ (E - D) < 10 ^ D * 10 ^ (E - D) * π := by rw [← hsplit]; linarith
    nlinarith
  · rw [lt_div_iff₀ hD]
    have : 10 ^ D * 10 ^ (E - D) * π < ((P : ℝ) + 1) * 10 ^ (E - D) := by rw [← hsplit]; linarith
    nlinarith

/-! ### Per-`n` certificate, kernel-checkable as a balanced tree of Booleans -/

/-- The per-`n` condition (trivially `true` for `n = 0` and `n ≥ D`). -/
def chk (P D n : ℕ) : Bool :=
  n == 0 || D ≤ n || (P + 1) * (10 ^ (2 * n) + 1) ≤ (P / 10 ^ (D - n) + 1) * 10 ^ (n + D)

/-- Balanced-tree conjunction `∀ i < 2^d, f (lo + i)`. -/
def allT (f : ℕ → Bool) : ℕ → ℕ → Bool
  | lo, 0 => f lo
  | lo, d + 1 => allT f lo d && allT f (lo + 2 ^ d) d

lemma allT_true (f : ℕ → Bool) (lo d : ℕ) (h : allT f lo d = true) :
    ∀ i, i < 2 ^ d → f (lo + i) = true := by
  induction d generalizing lo with
  | zero =>
    intro i hi
    have : i = 0 := by simpa using hi
    subst this
    simpa [allT] using h
  | succ d ih =>
    intro i hi
    simp only [allT, Bool.and_eq_true] at h
    rcases lt_or_ge i (2 ^ d) with hlt | hge
    · exact ih lo h.1 i hlt
    · have := ih _ h.2 (i - 2 ^ d) (by rw [pow_succ] at hi; omega)
      rwa [add_assoc, Nat.add_sub_cancel' hge] at this

lemma chk_spec (P D n : ℕ) (h : chk P D n = true) (h1 : 1 ≤ n) (h2 : n < D) :
    (P + 1) * (10 ^ (2 * n) + 1) ≤ (P / 10 ^ (D - n) + 1) * 10 ^ (n + D) := by
  simp only [chk, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · omega
  · omega
  · exact h

lemma arctan_ge_div (x : ℝ) (hx : 0 ≤ x) : x / (1 + x ^ 2) ≤ arctan x := by
  have hθ : 0 ≤ arctan x := arctan_nonneg.2 hx
  have hs := Real.sin_arctan x
  have hc := Real.cos_arctan x
  have e : x / (1 + x ^ 2) = sin (arctan x) * cos (arctan x) := by
    rw [hs, hc, div_mul_div_comm, mul_one, Real.mul_self_sqrt (by positivity)]
  have hsin_le : sin (arctan x) ≤ arctan x := Real.sin_le hθ
  have hcos_le : cos (arctan x) ≤ 1 := Real.cos_le_one _
  have hcos_nn : 0 ≤ cos (arctan x) := by rw [hc]; positivity
  rw [e]
  calc sin (arctan x) * cos (arctan x) ≤ arctan x * cos (arctan x) :=
        mul_le_mul_of_nonneg_right hsin_le hcos_nn
    _ ≤ arctan x * 1 := mul_le_mul_of_nonneg_left hcos_le hθ
    _ = arctan x := mul_one _

/-- Generic certificate: given bounds `plo < π < phi` and an integer `K` with
`K - 1 ≤ plo·10ⁿ` and `phi·(10²ⁿ + 1) ≤ K·10ⁿ`, the interval `(π·10ⁿ, π/arctan(10⁻ⁿ))`
contains no integer. -/
lemma aux_bound (n : ℕ) (K : ℤ) (plo phi : ℝ) (hlo : plo < π) (hhi : π < phi)
    (hK1 : (K : ℝ) - 1 ≤ plo * 10 ^ n)
    (hK2 : phi * ((10 : ℝ) ^ (2 * n) + 1) ≤ K * 10 ^ n) :
    ¬ ∃ (k : ℤ), (Real.pi * (10 : ℝ) ^ n < k) ∧
      (k < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n)) := by
  rintro ⟨k, h1, h2⟩
  have h10 : (0 : ℝ) < 10 ^ n := by positivity
  have hx : (0 : ℝ) < 1 / 10 ^ n := by positivity
  have harc : 0 < arctan (1 / (10 : ℝ) ^ n) := arctan_pos.2 hx
  have hlow := arctan_ge_div (1 / (10 : ℝ) ^ n) hx.le
  have h3 : (k : ℝ) * arctan (1 / 10 ^ n) < π := by rwa [lt_div_iff₀ harc] at h2
  have hk_pos : (0 : ℝ) < k := by nlinarith [pi_pos]
  have h4 : (k : ℝ) * ((1 / 10 ^ n) / (1 + (1 / 10 ^ n) ^ 2)) < π :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hlow hk_pos.le) h3
  have e : (1 / (10 : ℝ) ^ n) / (1 + (1 / 10 ^ n) ^ 2) = 10 ^ n / (10 ^ (2 * n) + 1) := by
    have h2n : (10 : ℝ) ^ (2 * n) = (10 ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [h2n]; field_simp
  rw [e] at h4
  have h5 : (k : ℝ) * 10 ^ n < π * (10 ^ (2 * n) + 1) := by
    have hpos : (0 : ℝ) < 10 ^ (2 * n) + 1 := by positivity
    rwa [mul_div_assoc', div_lt_iff₀ hpos] at h4
  have hKlo : ((K : ℝ) - 1) < k := by nlinarith
  have hKhi : (k : ℝ) * 10 ^ n < K * 10 ^ n := by
    have : (0:ℝ) < 10 ^ (2 * n) + 1 := by positivity
    nlinarith
  have hKhi' : (k : ℝ) < K := lt_of_mul_lt_mul_right hKhi h10.le
  have i1 : K - 1 < k := by exact_mod_cast hKlo
  have i2 : k < K := by exact_mod_cast hKhi'
  omega

/-- Main assembly: from `P/10^D < π < (P+1)/10^D` and the Boolean certificate tree of depth `d`,
the conjecture holds for all `n < min D (2^d)`. -/
theorem conj_of_cert (D P d : ℕ)
    (hlo : ((P : ℝ) / 10 ^ D) < π) (hhi : π < ((P : ℝ) + 1) / 10 ^ D)
    (hcert : allT (chk P D) 0 d = true)
    (n : ℕ) (hnD : n < D) (hnd : n < 2 ^ d) :
    ¬ ∃ (k : ℤ), (Real.pi * (10 : ℝ) ^ n < k) ∧
      (k < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n)) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    rintro ⟨k, h1, h2⟩
    rw [pow_zero, mul_one] at h1
    rw [pow_zero, one_div_one, arctan_one] at h2
    have hpi4 : π / (π / 4) = 4 := by field_simp
    rw [hpi4] at h2
    have h3 : (3 : ℝ) < k := pi_gt_three.trans h1
    have i1 : (3 : ℤ) < k := by exact_mod_cast h3
    have i2 : k < (4 : ℤ) := by exact_mod_cast h2
    omega
  · set Q : ℕ := P / 10 ^ (D - n) with hQ
    have hc : (P + 1) * (10 ^ (2 * n) + 1) ≤ (Q + 1) * 10 ^ (n + D) :=
      chk_spec P D n (by simpa using allT_true _ 0 d hcert n hnd) hpos hnD
    apply aux_bound n ((Q + 1 : ℕ) : ℤ) ((P : ℝ) / 10 ^ D) (((P : ℝ) + 1) / 10 ^ D) hlo hhi
    · have hdiv : Q * 10 ^ (D - n) ≤ P := Nat.div_mul_le_self P (10 ^ (D - n))
      have hdiv' : (Q : ℝ) * 10 ^ (D - n) ≤ P := by exact_mod_cast hdiv
      have hsplit : (10 : ℝ) ^ D = 10 ^ (D - n) * 10 ^ n := by
        rw [← pow_add, Nat.sub_add_cancel hnD.le]
      have hpos' : (0 : ℝ) < 10 ^ (D - n) := by positivity
      have hposn : (0 : ℝ) < 10 ^ n := by positivity
      push_cast
      rw [hsplit, div_mul_eq_mul_div, mul_comm ((10:ℝ) ^ (D - n)), ← div_div,
        mul_div_cancel_right₀ _ hposn.ne', le_div_iff₀ hpos']
      linarith
    · have hc' : ((P : ℝ) + 1) * (10 ^ (2 * n) + 1) ≤ ((Q : ℝ) + 1) * 10 ^ (n + D) := by
        exact_mod_cast hc
      have hposD : (0 : ℝ) < 10 ^ D := by positivity
      push_cast
      rw [div_mul_eq_mul_div, div_le_iff₀ hposD]
      rw [pow_add] at hc'
      linarith


/-- The first 10001 significant digits of π as an integer: `piP / 10^10000 < π < (piP+1) / 10^10000`. -/
def piP : ℕ := 31415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679821480865132823066470938446095505822317253594081284811174502841027019385211055596446229489549303819644288109756659334461284756482337867831652712019091456485669234603486104543266482133936072602491412737245870066063155881748815209209628292540917153643678925903600113305305488204665213841469519415116094330572703657595919530921861173819326117931051185480744623799627495673518857527248912279381830119491298336733624406566430860213949463952247371907021798609437027705392171762931767523846748184676694051320005681271452635608277857713427577896091736371787214684409012249534301465495853710507922796892589235420199561121290219608640344181598136297747713099605187072113499999983729780499510597317328160963185950244594553469083026425223082533446850352619311881710100031378387528865875332083814206171776691473035982534904287554687311595628638823537875937519577818577805321712268066130019278766111959092164201989380952572010654858632788659361533818279682303019520353018529689957736225994138912497217752834791315155748572424541506959508295331168617278558890750983817546374649393192550604009277016711390098488240128583616035637076601047101819429555961989467678374494482553797747268471040475346462080466842590694912933136770289891521047521620569660240580381501935112533824300355876402474964732639141992726042699227967823547816360093417216412199245863150302861829745557067498385054945885869269956909272107975093029553211653449872027559602364806654991198818347977535663698074265425278625518184175746728909777727938000816470600161452491921732172147723501414419735685481613611573525521334757418494684385233239073941433345477624168625189835694855620992192221842725502542568876717904946016534668049886272327917860857843838279679766814541009538837863609506800642251252051173929848960841284886269456042419652850222106611863067442786220391949450471237137869609563643719172874677646575739624138908658326459958133904780275900994657640789512694683983525957098258226205224894077267194782684826014769909026401363944374553050682034962524517493996514314298091906592509372216964615157098583874105978859597729754989301617539284681382686838689427741559918559252459539594310499725246808459872736446958486538367362226260991246080512438843904512441365497627807977156914359977001296160894416948685558484063534220722258284886481584560285060168427394522674676788952521385225499546667278239864565961163548862305774564980355936345681743241125150760694794510965960940252288797108931456691368672287489405601015033086179286809208747609178249385890097149096759852613655497818931297848216829989487226588048575640142704775551323796414515237462343645428584447952658678210511413547357395231134271661021359695362314429524849371871101457654035902799344037420073105785390621983874478084784896833214457138687519435064302184531910484810053706146806749192781911979399520614196634287544406437451237181921799983910159195618146751426912397489409071864942319615679452080951465502252316038819301420937621378559566389377870830390697920773467221825625996615014215030680384477345492026054146659252014974428507325186660021324340881907104863317346496514539057962685610055081066587969981635747363840525714591028970641401109712062804390397595156771577004203378699360072305587631763594218731251471205329281918261861258673215791984148488291644706095752706957220917567116722910981690915280173506712748583222871835209353965725121083579151369882091444210067510334671103141267111369908658516398315019701651511685171437657618351556508849099898599823873455283316355076479185358932261854896321329330898570642046752590709154814165498594616371802709819943099244889575712828905923233260972997120844335732654893823911932597463667305836041428138830320382490375898524374417029132765618093773444030707469211201913020330380197621101100449293215160842444859637669838952286847831235526582131449576857262433441893039686426243410773226978028073189154411010446823252716201052652272111660396665573092547110557853763466820653109896526918620564769312570586356620185581007293606598764861179104533488503461136576867532494416680396265797877185560845529654126654085306143444318586769751456614068007002378776591344017127494704205622305389945613140711270004078547332699390814546646458807972708266830634328587856983052358089330657574067954571637752542021149557615814002501262285941302164715509792592309907965473761255176567513575178296664547791745011299614890304639947132962107340437518957359614589019389713111790429782856475032031986915140287080859904801094121472213179476477726224142548545403321571853061422881375850430633217518297986622371721591607716692547487389866549494501146540628433663937900397692656721463853067360965712091807638327166416274888800786925602902284721040317211860820419000422966171196377921337575114959501566049631862947265473642523081770367515906735023507283540567040386743513622224771589150495309844489333096340878076932599397805419341447377441842631298608099888687413260472156951623965864573021631598193195167353812974167729478672422924654366800980676928238280689964004824354037014163149658979409243237896907069779422362508221688957383798623001593776471651228935786015881617557829735233446042815126272037343146531977774160319906655418763979293344195215413418994854447345673831624993419131814809277771038638773431772075456545322077709212019051660962804909263601975988281613323166636528619326686336062735676303544776280350450777235547105859548702790814356240145171806246436267945612753181340783303362542327839449753824372058353114771199260638133467768796959703098339130771098704085913374641442822772634659470474587847787201927715280731767907707157213444730605700733492436931138350493163128404251219256517980694113528013147013047816437885185290928545201165839341965621349143415956258658655705526904965209858033850722426482939728584783163057777560688876446248246857926039535277348030480290058760758251047470916439613626760449256274204208320856611906254543372131535958450687724602901618766795240616342522577195429162991930645537799140373404328752628889639958794757291746426357455254079091451357111369410911939325191076020825202618798531887705842972591677813149699009019211697173727847684726860849003377024242916513005005168323364350389517029893922334517220138128069650117844087451960121228599371623130171144484640903890644954440061986907548516026327505298349187407866808818338510228334508504860825039302133219715518430635455007668282949304137765527939751754613953984683393638304746119966538581538420568533862186725233402830871123282789212507712629463229563989898935821167456270102183564622013496715188190973038119800497340723961036854066431939509790190699639552453005450580685501956730229219139339185680344903982059551002263535361920419947455385938102343955449597783779023742161727111723643435439478221818528624085140066604433258885698670543154706965747458550332323342107301545940516553790686627333799585115625784322988273723198987571415957811196358330059408730681216028764962867446047746491599505497374256269010490377819868359381465741268049256487985561453723478673303904688383436346553794986419270563872931748723320837601123029911367938627089438799362016295154133714248928307220126901475466847653576164773794675200490757155527819653621323926406160136358155907422020203187277605277219005561484255518792530343513984425322341576233610642506390497500865627109535919465897514131034822769306247435363256916078154781811528436679570611086153315044521274739245449454236828860613408414863776700961207151249140430272538607648236341433462351897576645216413767969031495019108575984423919862916421939949072362346468441173940326591840443780513338945257423995082965912285085558215725031071257012668302402929525220118726767562204154205161841634847565169998116141010029960783869092916030288400269104140792886215078424516709087000699282120660418371806535567252532567532861291042487761825829765157959847035622262934860034158722980534989650226291748788202734209222245339856264766914905562842503912757710284027998066365825488926488025456610172967026640765590429099456815065265305371829412703369313785178609040708667114965583434347693385781711386455873678123014587687126603489139095620099393610310291616152881384379099042317473363948045759314931405297634757481193567091101377517210080315590248530906692037671922033229094334676851422144773793937517034436619910403375111735471918550464490263655128162288244625759163330391072253837421821408835086573917715096828874782656995995744906617583441375223970968340800535598491754173818839994469748676265516582765848358845314277568790029095170283529716344562129640435231176006651012412006597558512761785838292041974844236080071930457618932349229279650198751872127267507981255470958904556357921221033346697499235630254947802490114195212382815309114079073860251522742995818072471625916685451333123948049470791191532673430282441860414263639548000448002670496248201792896476697583183271314251702969234889627668440323260927524960357996469256504936818360900323809293459588970695365349406034021665443755890045632882250545255640564482465151875471196218443965825337543885690941130315095261793780029741207665147939425902989695946995565761218656196733786236256125216320862869222103274889218654364802296780705765615144632046927906821207388377814233562823608963208068222468012248261177185896381409183903673672220888321513755600372798394004152970028783076670944474560134556417254370906979396122571429894671543578468788614445812314593571984922528471605049221242470141214780573455105008019086996033027634787081081754501193071412233908663938339529425786905076431006383519834389341596131854347546495569781038293097164651438407007073604112373599843452251610507027056235266012764848308407611830130527932054274628654036036745328651057065874882256981579367897669742205750596834408697350201410206723585020072452256326513410559240190274216248439140359989535394590944070469120914093870012645600162374288021092764579310657922955249887275846101264836999892256959688159205600101655256375678

set_option maxRecDepth 100000 in
theorem piP_lo : (piP : ℤ) * 10 ^ (10020 - 10000) <
    16 * tree (lowT 5 10020 (2 * 3600)) 0 13 - 4 * tree (uppT 239 10020 (2 * 1060 + 1)) 0 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem piP_hi :
    16 * tree (uppT 5 10020 (2 * 3600 + 1)) 0 13 - 4 * tree (lowT 239 10020 (2 * 1060)) 0 12 <
    ((piP : ℤ) + 1) * 10 ^ (10020 - 10000) := by
  decide +kernel

/-- 10000 certified decimal digits of π. -/
theorem pi_bounds_d10000 : (piP : ℝ) / 10 ^ 10000 < π ∧ π < ((piP : ℝ) + 1) / 10 ^ 10000 :=
  pi_bounds_of_cert piP 10000 10020 3600 1060 13 12 (by norm_num) (by norm_num) (by norm_num)
    piP_lo piP_hi

set_option maxRecDepth 100000 in
theorem piP_cert : allT (chk piP 10000) 0 14 = true := by decide +kernel

/-- The conjecture holds for every `n ≤ 9999`. -/
theorem conjecture_le_9999 (n : ℕ) (hn : n ≤ 9999) :
    ¬ ∃ (k : ℤ),
      (Real.pi * (10 : ℝ) ^ n.cast < k.cast) ∧
      (k.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast)) := by
  simp only [Nat.cast_id]
  exact conj_of_cert 10000 piP 14 pi_bounds_d10000.1 pi_bounds_d10000.2 piP_cert n
    (by omega) (by norm_num; omega)

end PartialResult

/- ### The reduction to a digit condition on π

We formalize the (folklore) equivalence between the conjecture and a statement about the
decimal digits of π: for `n ≥ 1`, the conjecture fails at `n` iff `⌈π·10ⁿ⌉ < π/arctan(10⁻ⁿ)`,
and quantitatively the gap `⌈π·10ⁿ⌉ − π·10ⁿ` (which is `1 − fract(π·10ⁿ)`) must then be
`< π·10ⁿ/(3·10²ⁿ − 1) ≈ (π/3)·10⁻ⁿ`; conversely a gap `< π(1/3 − 1/500)·10⁻ⁿ` forces failure.
Thus the conjecture asks that π never has a run of ≈ `n` nines starting at digit `n + 1`. -/

open Finset in
/-- Cubic/quintic Taylor bounds for `arctan` on `[0, 1)`. -/
lemma arctan_taylor_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x - x ^ 3 / 3 ≤ arctan x ∧ arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5 := by
  have hs := Real.hasSum_arctan (x := x) (by rwa [Real.norm_eq_abs, abs_of_nonneg hx0])
  set f : ℕ → ℝ := fun i => x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ) with hf
  have hs' : HasSum (fun i => (-1) ^ i * f i) (arctan x) := by
    convert hs using 1
    ext i
    simp only [hf]
    rw [mul_div_assoc]
  have ht := hs'.tendsto_sum_nat
  have hanti : Antitone f := by
    intro i j hij
    simp only [hf]
    have hx1' : x ≤ 1 := hx1.le
    have hpow : x ^ (2 * j + 1) ≤ x ^ (2 * i + 1) :=
      pow_le_pow_of_le_one hx0 hx1' (by omega)
    have hden : ((2 * i + 1 : ℕ) : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hpos : (0 : ℝ) < ((2 * i + 1 : ℕ) : ℝ) := by positivity
    exact div_le_div₀ (by positivity) hpow hpos hden
  have h1 := hanti.alternating_series_le_tendsto ht 1
  have h2 := hanti.tendsto_le_alternating_series ht 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hf] at h1 h2
  norm_num at h1 h2
  constructor <;> linarith

/-- `π · 10ⁿ` is never an integer. -/
lemma pi_mul_pow_ten_ne_int (n : ℕ) (k : ℤ) : Real.pi * (10 : ℝ) ^ n ≠ k := by
  have h : Irrational (Real.pi * ((10 ^ n : ℕ) : ℝ)) :=
    irrational_pi.mul_natCast (by positivity)
  have : Real.pi * (10 : ℝ) ^ n = Real.pi * ((10 ^ n : ℕ) : ℝ) := by push_cast; ring
  rw [this]
  exact h.ne_int k

/-- The conjecture at `n` is equivalent to `π / arctan(10⁻ⁿ) ≤ ⌈π · 10ⁿ⌉`. -/
theorem conjecture_iff_ceil (n : ℕ) :
    (¬ ∃ (k : ℤ), (Real.pi * (10 : ℝ) ^ n < k) ∧
        (k < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n))) ↔
      Real.pi / Real.arctan (1 / (10 : ℝ) ^ n) ≤ (⌈Real.pi * (10 : ℝ) ^ n⌉ : ℝ) := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    apply h
    refine ⟨⌈Real.pi * (10 : ℝ) ^ n⌉, ?_, hlt⟩
    exact lt_of_le_of_ne (Int.le_ceil _) (pi_mul_pow_ten_ne_int n _)
  · rintro h ⟨k, h1, h2⟩
    have : (⌈Real.pi * (10 : ℝ) ^ n⌉ : ℝ) ≤ k := by exact_mod_cast Int.ceil_le.2 h1.le
    linarith

/-- **Necessary condition for failure.** If the interval contains an integer `k` (`n ≥ 1`), then
`k − π·10ⁿ < π·10ⁿ / (3·10²ⁿ − 1) ≈ (π/3)·10⁻ⁿ`; i.e. the digits of π right after position `n`
form a run of ≈ `n` nines. -/
theorem gap_lt_of_mem (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    (_h1 : Real.pi * (10 : ℝ) ^ n < k) (h2 : (k : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n)) :
    (k : ℝ) - Real.pi * 10 ^ n < Real.pi * 10 ^ n / (3 * 10 ^ (2 * n) - 1) := by
  set y : ℝ := (10 : ℝ) ^ n with hy
  have hy10 : (10 : ℝ) ≤ y := by
    rw [hy]; calc (10:ℝ) = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hypos : 0 < y := by linarith
  have hx0 : (0 : ℝ) ≤ 1 / y := by positivity
  have hx1 : 1 / y < 1 := by rw [div_lt_one hypos]; linarith
  obtain ⟨hlo, -⟩ := arctan_taylor_bounds (1 / y) hx0 hx1
  have hy2 : (10 : ℝ) ^ (2 * n) = y ^ 2 := by rw [hy, ← pow_mul, mul_comm]
  rw [hy2]
  have hcub : 1 / y - (1 / y) ^ 3 / 3 = (3 * y ^ 2 - 1) / (3 * y ^ 3) := by
    field_simp
  have hden : 0 < 3 * y ^ 2 - 1 := by nlinarith
  have hpos : 0 < (3 * y ^ 2 - 1) / (3 * y ^ 3) := by positivity
  rw [hcub] at hlo
  have harc : 0 < Real.arctan (1 / y) := lt_of_lt_of_le hpos hlo
  -- k < π / arctan ≤ π / ((3y²-1)/(3y³)) = 3πy³/(3y²-1)
  have h3 : (k : ℝ) < Real.pi / ((3 * y ^ 2 - 1) / (3 * y ^ 3)) :=
    lt_of_lt_of_le h2 (div_le_div_of_nonneg_left pi_pos.le hpos hlo)
  have h4 : Real.pi / ((3 * y ^ 2 - 1) / (3 * y ^ 3)) - Real.pi * y = Real.pi * y / (3 * y ^ 2 - 1) := by
    field_simp; ring
  linarith

/-- **Sufficient condition for failure.** If `⌈π·10ⁿ⌉ − π·10ⁿ < π·(1/3 − 1/500)·10⁻ⁿ` (`n ≥ 1`),
then the interval contains the integer `⌈π·10ⁿ⌉`, i.e. the conjecture fails at `n`. -/
theorem mem_of_gap_lt (n : ℕ) (hn : 1 ≤ n)
    (h : (⌈Real.pi * (10 : ℝ) ^ n⌉ : ℝ) - Real.pi * 10 ^ n < Real.pi * (1 / 3 - 1 / 500) / 10 ^ n) :
    ∃ (k : ℤ), (Real.pi * (10 : ℝ) ^ n < k) ∧
        (k < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n)) := by
  refine ⟨⌈Real.pi * (10 : ℝ) ^ n⌉, lt_of_le_of_ne (Int.le_ceil _) (pi_mul_pow_ten_ne_int n _), ?_⟩
  set K : ℝ := (⌈Real.pi * (10 : ℝ) ^ n⌉ : ℝ) with hK
  set y : ℝ := (10 : ℝ) ^ n with hy
  have hy10 : (10 : ℝ) ≤ y := by
    rw [hy]; calc (10:ℝ) = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hypos : 0 < y := by linarith
  set x : ℝ := 1 / y with hx
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have hxpos : 0 < x := by positivity
  have hx1 : x < 1 := by rw [hx, div_lt_one hypos]; linarith
  have hx10 : x ≤ 1 / 10 := by rw [hx]; exact one_div_le_one_div_of_le (by norm_num) hy10
  obtain ⟨-, hhi⟩ := arctan_taylor_bounds x hx0 hx1
  have harc : 0 < Real.arctan x := Real.arctan_pos.2 hxpos
  rw [lt_div_iff₀ harc]
  have hKge : Real.pi * y ≤ K := Int.le_ceil _
  have hxy : x * y = 1 := by rw [hx]; field_simp
  -- K · arctan x ≤ K (x − x³/3 + x⁵/5) < π
  have hK_arc : K * Real.arctan x ≤ K * (x - x ^ 3 / 3 + x ^ 5 / 5) :=
    mul_le_mul_of_nonneg_left hhi (by nlinarith [pi_pos])
  have hgap : K - Real.pi * y < Real.pi * (1 / 3 - 1 / 500) * x := by
    rw [hx, mul_one_div]; exact h
  have hx2 : x ^ 2 ≤ 1 / 100 := by nlinarith
  have hpoly : 0 < 1 - x ^ 2 / 3 + x ^ 4 / 5 := by nlinarith [pow_nonneg hx0 4]
  have hpoly1 : 1 - x ^ 2 / 3 + x ^ 4 / 5 ≤ 1 := by nlinarith [pow_nonneg hx0 4, pow_nonneg hx0 2]
  -- (π y + g) x (1 - x²/3 + x⁴/5) = π(1 - x²/3 + x⁴/5) + g x (…) 
  have key : K * (x - x ^ 3 / 3 + x ^ 5 / 5) < Real.pi := by
    have e : K * (x - x ^ 3 / 3 + x ^ 5 / 5)
        = (Real.pi * y) * x * (1 - x ^ 2 / 3 + x ^ 4 / 5) + (K - Real.pi * y) * x * (1 - x ^ 2 / 3 + x ^ 4 / 5) := by ring
    rw [e]
    have e2 : (Real.pi * y) * x * (1 - x ^ 2 / 3 + x ^ 4 / 5) = Real.pi * (1 - x ^ 2 / 3 + x ^ 4 / 5) := by
      rw [mul_assoc Real.pi y x, mul_comm y x, hxy, mul_one]
    rw [e2]
    have hg0 : 0 ≤ K - Real.pi * y := by linarith
    have h5 : (K - Real.pi * y) * x * (1 - x ^ 2 / 3 + x ^ 4 / 5) ≤ (K - Real.pi * y) * x :=
      mul_le_of_le_one_right (by positivity) hpoly1
    have h6 : (K - Real.pi * y) * x < Real.pi * (1 / 3 - 1 / 500) * x * x :=
      mul_lt_mul_of_pos_right hgap hxpos
    have h7 : Real.pi * (1 / 3 - 1 / 500) * x * x ≤ Real.pi * (x ^ 2 / 3 - x ^ 4 / 5) := by
      have : x ^ 4 ≤ x ^ 2 / 100 := by nlinarith [pow_nonneg hx0 2]
      nlinarith [pi_pos, pow_nonneg hx0 2]
    nlinarith
  exact lt_of_le_of_lt hK_arc key

/-- **Digit-run interpretation.** If the interval `(π·10ⁿ, π/arctan(10⁻ⁿ))` contains an
integer `k` (with `n ≥ 1`), then every decimal digit of π in positions `n+1, …, 2n−1`
(the `j`-th digit after the decimal point being `⌊π·10ʲ⌋ % 10`) is equal to `9`. -/
theorem digits_nine_of_mem (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    (h1 : Real.pi * (10 : ℝ) ^ n < k) (h2 : (k : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n))
    (j : ℕ) (hj1 : n < j) (hj2 : j < 2 * n) :
    ⌊Real.pi * (10 : ℝ) ^ j⌋ % 10 = 9 := by
  have hgap := gap_lt_of_mem n hn k h1 h2
  set y : ℝ := (10 : ℝ) ^ n with hy
  have hy10 : (10 : ℝ) ≤ y := by
    rw [hy]; calc (10:ℝ) = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hypos : 0 < y := by linarith
  have hy2 : (10 : ℝ) ^ (2 * n) = y ^ 2 := by rw [hy, ← pow_mul, mul_comm]
  rw [hy2] at hgap
  -- g := k - π y  satisfies 0 < g < 1.06 / y
  have hden : 0 < 3 * y ^ 2 - 1 := by nlinarith
  have hg_lt : (k : ℝ) - Real.pi * y < 1.06 / y := by
    have hpi := pi_lt_d2
    have : Real.pi * y / (3 * y ^ 2 - 1) < 1.06 / y := by
      rw [div_lt_div_iff₀ hden hypos]
      nlinarith
    linarith
  have hg_pos : 0 < (k : ℝ) - Real.pi * y := by linarith
  -- write j = n + m with 1 ≤ m ≤ n - 1
  obtain ⟨m, rfl⟩ : ∃ m, j = n + m := ⟨j - n, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hmn : m + 1 ≤ n := by omega
  have hpow : (10 : ℝ) ^ (n + m) = y * 10 ^ m := by rw [pow_add]
  have h10m : (10 : ℝ) ^ m * 10 ≤ y := by
    rw [hy, ← pow_succ]; exact pow_le_pow_right₀ (by norm_num) hmn
  have h10m_pos : (0 : ℝ) < 10 ^ m := by positivity
  -- π 10^(n+m) = k 10^m - g 10^m with 0 < g 10^m < 0.106
  have hprod : ((k : ℝ) - Real.pi * y) * 10 ^ m < 0.106 := by
    have : ((k : ℝ) - Real.pi * y) * 10 ^ m < 1.06 / y * 10 ^ m := by
      exact mul_lt_mul_of_pos_right hg_lt h10m_pos
    have : 1.06 / y * 10 ^ m ≤ 0.106 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hypos]; nlinarith
    linarith
  have hfloor : ⌊Real.pi * (10 : ℝ) ^ (n + m)⌋ = k * 10 ^ m - 1 := by
    rw [Int.floor_eq_iff]
    push_cast
    rw [hpow]
    constructor
    · nlinarith
    · nlinarith
  rw [hfloor]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ, ← mul_assoc]
  omega

/-- The conjecture at `n ≥ 1` holds as soon as some digit of π in positions `n+1, …, 2n−1`
differs from `9`. -/
theorem conjecture_of_digit_ne_nine (n : ℕ) (hn : 1 ≤ n) (j : ℕ) (hj1 : n < j) (hj2 : j < 2 * n)
    (hd : ⌊Real.pi * (10 : ℝ) ^ j⌋ % 10 ≠ 9) :
    ¬ ∃ (k : ℤ), (Real.pi * (10 : ℝ) ^ n < k) ∧
      (k < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n)) := by
  rintro ⟨k, h1, h2⟩
  exact hd (digits_nine_of_mem n hn k h1 h2 j hj1 hj2)

/-- Digit recursion: `⌊x·10^(j+1)⌋ = 10·⌊x·10^j⌋ + (⌊x·10^(j+1)⌋ % 10)`. -/
lemma floor_mul_pow_succ (x : ℝ) (j : ℕ) :
    ⌊x * (10 : ℝ) ^ (j + 1)⌋ = 10 * ⌊x * (10 : ℝ) ^ j⌋ + ⌊x * (10 : ℝ) ^ (j + 1)⌋ % 10 := by
  have h : ⌊x * (10 : ℝ) ^ j⌋ = ⌊x * (10 : ℝ) ^ (j + 1)⌋ / (10 : ℕ) := by
    rw [← Int.floor_div_natCast]
    congr 1
    rw [pow_succ]; push_cast; field_simp
  rw [h]
  have := Int.mul_ediv_add_emod ⌊x * (10 : ℝ) ^ (j + 1)⌋ 10
  push_cast
  omega

/-- If digits `n+1, …, n+t` of π are all `9`, then `⌊π·10^(n+t)⌋ = 10^t·⌊π·10^n⌋ + 10^t − 1`. -/
lemma floor_of_digits_nine (n t : ℕ)
    (h : ∀ j, n < j → j ≤ n + t → ⌊Real.pi * (10 : ℝ) ^ j⌋ % 10 = 9) :
    ⌊Real.pi * (10 : ℝ) ^ (n + t)⌋ = 10 ^ t * ⌊Real.pi * (10 : ℝ) ^ n⌋ + (10 ^ t - 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ih' := ih (fun j hj1 hj2 => h j hj1 (by omega))
    rw [← add_assoc, floor_mul_pow_succ, ih', h (n + t + 1) (by omega) (by omega)]
    ring

/-- **Sufficient digit condition.** If the digits of π in positions `n+1, …, 2n+1` are all `9`
(`n ≥ 1`), then the interval `(π·10ⁿ, π/arctan(10⁻ⁿ))` contains an integer. -/
theorem mem_of_digits_nine (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ j, n < j → j ≤ 2 * n + 1 → ⌊Real.pi * (10 : ℝ) ^ j⌋ % 10 = 9) :
    ∃ (k : ℤ), (Real.pi * (10 : ℝ) ^ n < k) ∧
        (k < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n)) := by
  apply mem_of_gap_lt n hn
  have hfl := floor_of_digits_nine n (n + 1) (fun j hj1 hj2 => h j hj1 (by omega))
  set F : ℤ := ⌊Real.pi * (10 : ℝ) ^ n⌋ with hF
  have hle : ((⌊Real.pi * (10 : ℝ) ^ (n + (n + 1))⌋ : ℤ) : ℝ) ≤ Real.pi * 10 ^ (n + (n + 1)) :=
    Int.floor_le _
  rw [hfl] at hle
  push_cast at hle
  have hceil : (⌈Real.pi * (10 : ℝ) ^ n⌉ : ℝ) ≤ (F : ℝ) + 1 := by
    have : ⌈Real.pi * (10 : ℝ) ^ n⌉ ≤ F + 1 := Int.ceil_le.2 (by push_cast; exact (Int.lt_floor_add_one _).le)
    exact_mod_cast this
  have hpow : (10 : ℝ) ^ (n + (n + 1)) = 10 ^ n * 10 ^ (n + 1) := by rw [pow_add]
  rw [hpow] at hle
  have hpos : (0 : ℝ) < 10 ^ (n + 1) := by positivity
  have hpos' : (0 : ℝ) < 10 ^ n := by positivity
  -- from hle: 10^(n+1) F + 10^(n+1) - 1 ≤ π 10^n 10^(n+1)  ⇒  F + 1 - π 10^n ≤ 1/10^(n+1)
  have hgap : (F : ℝ) + 1 - Real.pi * 10 ^ n ≤ 1 / 10 ^ (n + 1) := by
    rw [le_div_iff₀ hpos]; nlinarith
  have hsmall : (1 : ℝ) / 10 ^ (n + 1) < Real.pi * (1 / 3 - 1 / 500) / 10 ^ n := by
    rw [pow_succ, div_lt_div_iff₀ (by positivity) hpos']
    nlinarith [pi_gt_three]
  linarith

/-- The digits of π are not eventually all `9` (this is just irrationality of π, made explicit). -/
lemma not_all_digits_nine (N : ℕ) : ¬ ∀ j, N < j → ⌊Real.pi * (10 : ℝ) ^ j⌋ % 10 = 9 := by
  intro h
  set F : ℤ := ⌊Real.pi * (10 : ℝ) ^ N⌋ with hF
  have hlt : Real.pi * (10 : ℝ) ^ N < F + 1 := Int.lt_floor_add_one _
  set ε : ℝ := (F : ℝ) + 1 - Real.pi * 10 ^ N with hε
  have hεpos : 0 < ε := by linarith
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one hεpos (by norm_num : (1 / 10 : ℝ) < 1)
  have hfl := floor_of_digits_nine N t (fun j hj _ => h j hj)
  have hle : ((⌊Real.pi * (10 : ℝ) ^ (N + t)⌋ : ℤ) : ℝ) ≤ Real.pi * 10 ^ (N + t) := Int.floor_le _
  rw [hfl] at hle
  push_cast at hle
  rw [pow_add] at hle
  have hpos : (0 : ℝ) < 10 ^ t := by positivity
  -- hle : 10^t F + 10^t - 1 ≤ π 10^N 10^t  ⇒  ε ≤ 1/10^t
  have : ε * 10 ^ t ≤ 1 := by rw [hε]; nlinarith
  have h2 : (1 / 10 : ℝ) ^ t = 1 / 10 ^ t := by rw [one_div_pow]
  rw [h2, div_lt_iff₀ hpos] at ht
  linarith

/-- **The conjecture holds for infinitely many `n`** (unconditionally): for every `N` there is
`n ≥ N` such that the interval `(π·10ⁿ, π/arctan(10⁻ⁿ))` contains no integer. -/
theorem conjecture_infinitely_often (N : ℕ) :
    ∃ n, N ≤ n ∧ ¬ ∃ (k : ℤ), (Real.pi * (10 : ℝ) ^ n < k) ∧
      (k < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n)) := by
  by_contra hcon
  push_neg at hcon
  -- every `n ≥ max N 2` fails, hence every digit beyond position `max N 2 + 1` is `9`
  apply not_all_digits_nine (max N 2 + 1)
  intro j hj
  obtain ⟨k, hk1, hk2⟩ := hcon (j - 1) (by omega)
  have := digits_nine_of_mem (j - 1) (by omega) k hk1 hk2 j (by omega) (by omega)
  exact this

/-- **No infinite failure chain.** There is no strictly increasing sequence `f` with
`f (i+1) ≤ 2 f i − 1` along which the conjecture fails everywhere. (Taking `f i = N + i`
recovers `conjecture_infinitely_often`.) -/
theorem no_failure_chain (f : ℕ → ℕ) (hf : StrictMono f) (hchain : ∀ i, f (i + 1) ≤ 2 * f i - 1)
    (hfail : ∀ i, ∃ (k : ℤ), (Real.pi * (10 : ℝ) ^ (f i) < k) ∧
      (k < Real.pi / Real.arctan (1 / (10 : ℝ) ^ (f i)))) : False := by
  -- f 0 ≥ 1: failure at 0 is impossible (interval (π, 4) has no integer)
  have hf0 : 1 ≤ f 0 := by
    by_contra h0
    have h0' : f 0 = 0 := by omega
    obtain ⟨k, hk1, hk2⟩ := hfail 0
    rw [h0'] at hk1 hk2
    rw [pow_zero, mul_one] at hk1
    rw [pow_zero, one_div_one, arctan_one] at hk2
    have hpi4 : π / (π / 4) = 4 := by field_simp
    rw [hpi4] at hk2
    have h3 : (3 : ℝ) < k := pi_gt_three.trans hk1
    have i1 : (3 : ℤ) < k := by exact_mod_cast h3
    have i2 : k < (4 : ℤ) := by exact_mod_cast hk2
    omega
  have hpos : ∀ i, 1 ≤ f i := fun i => hf0.trans (hf.monotone (Nat.zero_le i))
  -- f is unbounded
  have hunb : ∀ j, ∃ i, j < 2 * f i := fun j =>
    ⟨j, by have h1 : j ≤ f j := hf.le_apply; have h2 := hpos j; omega⟩
  apply not_all_digits_nine (f 0)
  intro j hj
  -- find the last index i with f i < j; then j ≤ f (i+1) ≤ 2 f i - 1 gives j < 2 f i
  have hex : ∃ i, j < 2 * f i := hunb j
  -- take the least i with j < 2 f i
  classical
  let i₀ := Nat.find hex
  have hi₀ : j < 2 * f i₀ := Nat.find_spec hex
  have hlt : f i₀ < j := by
    rcases Nat.eq_zero_or_pos i₀ with h0 | hp
    · rw [h0]; exact hj
    · obtain ⟨m, hm⟩ : ∃ m, i₀ = m + 1 := ⟨i₀ - 1, by omega⟩
      have hmin : ¬ j < 2 * f m := Nat.find_min hex (by omega)
      have := hchain m
      rw [hm]; omega
  obtain ⟨k, hk1, hk2⟩ := hfail i₀
  exact digits_nine_of_mem (f i₀) (hpos i₀) k hk1 hk2 j hlt hi₀

/--
A property which is equivalent to the conjecture that the number of collisions
in the described physical system (with mass ratio $10^{2n}$) is $a(n)$:
the interval $(\pi \cdot 10^n, \pi / \arctan(1/10^n))$ does not contain an integer.
The mass ratio $m$ in the comment is interpreted as $\frac{M}{m}$ in the physics setup,
which is $10^{2n}$, so $\sqrt{m}=10^n$.

Note: The OEIS comment uses $m=10^n$ for the $R^2$ term where $R=10^n$ in the physics formula.
We formalize the statement $\forall n \in \mathbb{N}, \nexists k \in \mathbb{Z}$ such that
$\pi \cdot 10^n < k < \pi / \arctan(1/10^n)$.
-/
theorem oeis_a011545_conjecture_0 (n : ℕ) :
    ¬ ∃ (k : ℤ),
      (Real.pi * (10 : ℝ) ^ n.cast < k.cast) ∧
      (k.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast)) :=
  by sorry

theorem oeis_a011545_conjecture_0.disproof : ¬ (type_of% @oeis_a011545_conjecture_0) := sorry
