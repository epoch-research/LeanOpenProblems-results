import FormalConjecturesUtil

/-!
# Erdős Problem 126

*Reference:* [erdosproblems.com/126](https://www.erdosproblems.com/126)

The proof establishes the stronger bound `|A| ≤ 65 * (r + 1)^5`, where
`r` is the number of prime divisors of the off-diagonal pair-sum product.

For each prime, differences of congruence and opposite-congruence kernels
are positive semidefinite. Unwinding their signs gives a bound on the total
logarithmic gcd-distance. A small-distance anchor set consequently has
small height after gcd normalization. An exceptional-prime pigeonhole
argument propagates that height bound to the whole primitive set. Combining
the two estimates eliminates height and yields the polynomial bound.
-/

namespace Erdos126SignUnwinding

open scoped BigOperators

def quad {ι : Type*} [Fintype ι] (M : ι → ι → ℝ) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * M i j

def Positive {ι : Type*} [Fintype ι] (M : ι → ι → ℝ) : Prop :=
  ∀ c : ι → ℝ, 0 ≤ quad M c

/-- A positive quadratic form with nonpositive off-diagonal entries has
operator upper bound twice its largest diagonal entry. The elementary
proof compares the form at c and at |c|. -/
lemma quad_upper_of_nonpos_offDiag {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) (D : ℝ) (hpos : Positive M)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    (hdiag : ∀ i, M i i ≤ D) (c : ι → ℝ) :
    quad M c ≤ 2 * D * ∑ i, c i ^ 2 := by
  classical
  have hterm (i j : ι) :
      c i * c j * M i j + |c i| * |c j| * M i j ≤
        if i = j then 2 * D * c i ^ 2 else 0 := by
    by_cases h : i = j
    · subst j
      simp only [ite_true]
      have hs : |c i| * |c i| = c i ^ 2 := by nlinarith [sq_abs (c i)]
      rw [hs]
      nlinarith [mul_le_mul_of_nonneg_left (hdiag i) (sq_nonneg (c i))]
    · simp only [h, ite_false]
      have hcoef : 0 ≤ c i * c j + |c i| * |c j| := by
        rw [← abs_mul]
        have := neg_abs_le (c i * c j)
        linarith
      have hm := mul_nonpos_of_nonneg_of_nonpos hcoef (hoff i j h)
      nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hterm i j))
  have he : (∑ i, ∑ j,
      (c i * c j * M i j + |c i| * |c j| * M i j)) =
      quad M c + quad M (fun i => |c i|) := by
    simp only [quad, Finset.sum_add_distrib]
  rw [he] at hs
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hs
  rw [← Finset.mul_sum] at hs
  have hp := hpos (fun i => |c i|)
  linarith

lemma positive_sum {ι τ : Type*} [Fintype ι] [Fintype τ]
    (M : τ → ι → ι → ℝ) (hpos : ∀ p, Positive (M p)) :
    Positive (fun i j => ∑ p, M p i j) := by
  intro c
  have he : quad (fun i j => ∑ p, M p i j) c = ∑ p, quad (M p) c := by
    simp only [quad, Finset.mul_sum]
    conv_lhs =>
      enter [2, i]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [he]
  exact Finset.sum_nonneg (fun p _ => hpos p c)

lemma quad_component_le {ι τ : Type*} [Fintype ι] [Fintype τ]
    (M : τ → ι → ι → ℝ) (hpos : ∀ p, Positive (M p))
    (p : τ) (c : ι → ℝ) :
    quad (M p) c ≤ quad (fun i j => ∑ q, M q i j) c := by
  have he : quad (fun i j => ∑ q, M q i j) c = ∑ q, quad (M q) c := by
    simp only [quad, Finset.mul_sum]
    conv_lhs =>
      enter [2, i]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [he]
  exact Finset.single_le_sum (fun q _ => hpos q c) (Finset.mem_univ p)

/-- If each positive kernel is made entrywise nonnegative by changing
row and column signs, the sum of all unwound entries is at most
2 * (number of kernels) * (diagonal bound) * (number of vertices).
Neither kernel rank nor the number of features is bounded here. -/
theorem sign_unwinding_bound {ι τ : Type*} [Fintype ι] [Fintype τ]
    (M : τ → ι → ι → ℝ) (hpos : ∀ p, Positive (M p))
    (σ : τ → ι → ℝ) (hσ : ∀ p i, (σ p i) ^ 2 = 1)
    (D : ℝ)
    (hoff : ∀ i j, i ≠ j → (∑ p, M p i j) ≤ 0)
    (hdiag : ∀ i, (∑ p, M p i i) ≤ D) :
    (∑ p, ∑ i, ∑ j, σ p i * σ p j * M p i j) ≤
      2 * (Fintype.card τ : ℝ) * D * Fintype.card ι := by
  have hp (p : τ) : quad (M p) (σ p) ≤ 2 * D * Fintype.card ι := by
    have h := (quad_component_le M hpos p (σ p)).trans
      (quad_upper_of_nonpos_offDiag _ D (positive_sum M hpos) hoff hdiag (σ p))
    simpa only [hσ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using h
  have hs := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset τ)) => hp p)
  simp only [quad, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  nlinarith

end Erdos126SignUnwinding

namespace Erdos126ValuationUnwinding

open scoped BigOperators
open Erdos126SignUnwinding

lemma weighted_indicator_fibers {ι β : Type*} [Fintype ι] [Fintype β]
    [DecidableEq β] (f : ι → β) (e : β ≃ β) (c : ι → ℝ) :
    (∑ i, ∑ j, c i * c j * (if f j = e (f i) then 1 else 0)) =
      ∑ x : β, (∑ i with f i = x, c i) * (∑ j with f j = e x, c j) := by
  classical
  let C : β → ℝ := fun x => ∑ i with f i = x, c i
  change (∑ i, ∑ j, c i * c j * (if f j = e (f i) then 1 else 0)) =
    ∑ x, C x * C (e x)
  calc
    _ = ∑ i, c i * C (e (f i)) := by
      simp only [C, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_one, mul_zero]
    _ = ∑ x : β, ∑ i with f i = x, c i * C (e (f i)) :=
      (Finset.sum_fiberwise Finset.univ f (fun i => c i * C (e (f i)))).symm
    _ = ∑ x : β, C x * C (e x) := by
      apply Finset.sum_congr rfl
      intro x hx
      change _ = (∑ i with f i = x, c i) * C (e x)
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]

/-- Correlation with any permutation is at most self-correlation.
The coefficients may have either sign. -/
lemma reflection_positive {ι β : Type*} [Fintype ι] [Fintype β]
    [DecidableEq β] (f : ι → β) (e : β ≃ β) :
    Positive (fun i j => (if f j = f i then 1 else 0) -
      (if f j = e (f i) then 1 else 0)) := by
  classical
  intro c
  dsimp only [quad]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [weighted_indicator_fibers f e c]
  have heq := weighted_indicator_fibers f (Equiv.refl β) c
  simp only [Equiv.refl_apply] at heq
  rw [heq]
  let C : β → ℝ := fun x => ∑ i with f i = x, c i
  change 0 ≤ (∑ x, C x * C x) - ∑ x, C x * C (e x)
  have hterm (x : β) : 2 * (C x * C (e x)) ≤ C x ^ 2 + C (e x) ^ 2 := by
    nlinarith [sq_nonneg (C x - C (e x))]
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset β)) => hterm x)
  rw [← Finset.mul_sum, Finset.sum_add_distrib,
    e.sum_comp (fun x => C x ^ 2)] at hs
  simp only [pow_two] at hs
  linarith

lemma cast_dist_eq_zero_iff {q a b : ℕ} :
    (a : ZMod q) = b ↔ q ∣ a.dist b := by
  rw [ZMod.natCast_eq_natCast_iff]
  rcases le_total a b with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.modEq_iff_dvd' h]
  · rw [Nat.ModEq.comm, Nat.dist_comm, Nat.dist_eq_sub_of_le h, Nat.modEq_iff_dvd' h]

/-- The difference between congruence and opposite-congruence incidence
is positive semidefinite, for arbitrary natural operands. -/
lemma divisibility_difference_positive {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (q : ℕ) (hq : 0 < q) :
    Positive (fun i j => (if q ∣ (a i).dist (a j) then 1 else 0) -
      (if q ∣ a i + a j then 1 else 0)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  have h := reflection_positive (fun i => (a i : ZMod q)) (Equiv.neg (ZMod q))
  have hs (i j : ι) : ((a j : ZMod q) = -(a i : ZMod q)) ↔ q ∣ a i + a j := by
    rw [eq_neg_iff_add_eq_zero]
    have hc : (a j : ZMod q) + a i = ((a i + a j : ℕ) : ZMod q) := by push_cast; ring
    rw [hc, ZMod.natCast_eq_zero_iff]
  have hd (i j : ι) : ((a j : ZMod q) = (a i : ZMod q)) ↔ q ∣ (a i).dist (a j) := by
    rw [eq_comm]
    exact cast_dist_eq_zero_iff
  simpa only [Equiv.neg_apply, hs, hd] using h

def truncatedKernel (p K a b : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K,
    ((if p ^ (k + 1) ∣ a.dist b then 1 else 0) -
     (if p ^ (k + 1) ∣ a + b then 1 else 0))

lemma truncatedKernel_positive {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (p K : ℕ) (hp : 0 < p) :
    Positive (fun i j => truncatedKernel p K (a i) (a j)) := by
  intro c
  have he : quad (fun i j => truncatedKernel p K (a i) (a j)) c =
      ∑ k ∈ Finset.range K,
        quad (fun i j => (if p ^ (k + 1) ∣ (a i).dist (a j) then 1 else 0) -
          (if p ^ (k + 1) ∣ a i + a j then 1 else 0)) c := by
    simp only [quad, truncatedKernel, Finset.mul_sum]
    conv_lhs =>
      enter [2, i]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [he]
  exact Finset.sum_nonneg (fun k _ =>
    divisibility_difference_positive a (p ^ (k + 1)) (pow_pos hp _) c)

lemma sum_indicator_succ_le (v K : ℕ) :
    (∑ k ∈ Finset.range K, if k + 1 ≤ v then 1 else 0) = min K v := by
  have hset : (Finset.range K).filter (fun k => k + 1 ≤ v) = Finset.range (min K v) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    omega
  calc
    _ = ((Finset.range K).filter (fun k => k + 1 ≤ v)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = min K v := by rw [hset, Finset.card_range]

lemma factorization_truncation {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (K : ℕ) :
    (∑ k ∈ Finset.range K, if p ^ (k + 1) ∣ n then 1 else 0) = min K (n.factorization p) := by
  simp only [hp.pow_dvd_iff_le_factorization hn]
  exact sum_indicator_succ_le _ _

lemma truncatedKernel_eq {p K a b : ℕ} (hp : p.Prime) (hab : a ≠ b)
    (hdiff : (a.dist b).factorization p ≤ K) (hsum : (a + b).factorization p ≤ K) :
    truncatedKernel p K a b = (a.dist b).factorization p - ((a + b).factorization p : ℝ) := by
  have hdn : a.dist b ≠ 0 := by
    rcases le_total a b with h | h
    · rw [Nat.dist_eq_sub_of_le h]
      omega
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]
      omega
  have hsn : a + b ≠ 0 := by omega
  rw [truncatedKernel, Finset.sum_sub_distrib]
  have hcast (n : ℕ) :
      (∑ k ∈ Finset.range K, if p ^ (k + 1) ∣ n then (1 : ℝ) else 0) =
        ((∑ k ∈ Finset.range K, if p ^ (k + 1) ∣ n then 1 else 0 : ℕ) : ℝ) := by
    simp
  rw [hcast, hcast, factorization_truncation hp hdn,
    factorization_truncation hp hsn, min_eq_right hdiff, min_eq_right hsum]

lemma truncatedKernel_diag_bounds (p K a : ℕ) :
    0 ≤ truncatedKernel p K a a ∧ truncatedKernel p K a a ≤ K := by
  have hterm (k : ℕ) :
      0 ≤ ((if p ^ (k + 1) ∣ a.dist a then (1 : ℝ) else 0) -
        (if p ^ (k + 1) ∣ a + a then 1 else 0)) ∧
      ((if p ^ (k + 1) ∣ a.dist a then (1 : ℝ) else 0) -
        (if p ^ (k + 1) ∣ a + a then 1 else 0)) ≤ 1 := by
    simp only [Nat.dist_self, dvd_zero, ite_true]
    split_ifs <;> norm_num
  refine ⟨Finset.sum_nonneg (fun k _ => (hterm k).1), ?_⟩
  have h := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range K) => (hterm k).2)
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using h

def colorModulus (p : ℕ) : ℕ := if p = 2 then 4 else p

def residueColor (p a : ℕ) : Bool :=
  decide (2 * (a % colorModulus p) < colorModulus p)

def residueSign (p a : ℕ) : ℝ := if residueColor p a then 1 else -1

lemma residueSign_sq (p a : ℕ) : residueSign p a ^ 2 = 1 := by
  unfold residueSign
  split_ifs <;> norm_num

lemma colorModulus_eq_pow {p : ℕ} (hp : p.Prime) :
    colorModulus p = p ^ ((2 : ℕ).factorization p + 1) := by
  by_cases hp2 : p = 2
  · subst p
    norm_num [colorModulus]
  · have hzero : (2 : ℕ).factorization p = 0 := by
      rw [Nat.prime_two.factorization]
      simp [Ne.symm hp2]
    simp [colorModulus, hp2, hzero]

lemma opposite_residue_colors {p x y : ℕ} (hp : p.Prime)
    (hx : ¬p ∣ x) (hy : ¬p ∣ y) (hs : p ∣ x + y) (h4 : p = 2 → 4 ∣ x + y) :
    residueColor p x ≠ residueColor p y := by
  unfold residueColor colorModulus
  by_cases hp2 : p = 2
  · subst p
    simp only [ite_true]
    have hx' : x % 2 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hx
    have hy' : y % 2 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hy
    have hs' : (x + y) % 4 = 0 := Nat.mod_eq_zero_of_dvd (h4 rfl)
    simp only [ne_eq, decide_eq_decide]
    omega
  · simp only [hp2, ite_false]
    have hxp : 0 < x % p := Nat.pos_of_ne_zero (by simpa [Nat.dvd_iff_mod_eq_zero] using hx)
    have hyp : 0 < y % p := Nat.pos_of_ne_zero (by simpa [Nat.dvd_iff_mod_eq_zero] using hy)
    have hxlt := Nat.mod_lt x hp.pos
    have hylt := Nat.mod_lt y hp.pos
    have hxy : p ∣ x % p + y % p := by
      apply Nat.dvd_of_mod_eq_zero
      rw [← Nat.add_mod]
      exact Nat.mod_eq_zero_of_dvd hs
    obtain ⟨t, ht⟩ := hxy
    have htpos : 0 < t := by nlinarith
    have htlt : t < 2 := by nlinarith
    have ht1 : t = 1 := by omega
    rw [ht1, mul_one] at ht
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    simp only [ne_eq, decide_eq_decide]
    omega

lemma dist_ne_zero {a b : ℕ} (hab : a ≠ b) : a.dist b ≠ 0 := by
  rcases le_total a b with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    omega
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]
    omega

lemma different_color_dist_valuation_le {p a b : ℕ} (hp : p.Prime) (hab : a ≠ b)
    (hcolor : residueColor p a ≠ residueColor p b) :
    (a.dist b).factorization p ≤ (2 : ℕ).factorization p := by
  by_contra h
  have hd : colorModulus p ∣ a.dist b := by
    rw [colorModulus_eq_pow hp]
    exact (hp.pow_dvd_iff_le_factorization (dist_ne_zero hab)).mpr (by omega)
  have he : a % colorModulus p = b % colorModulus p :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mp (cast_dist_eq_zero_iff.mpr hd)
  exact hcolor (by simp only [residueColor, he])

lemma odd_dist_valuation_lower {p a b : ℕ} (hp : p.Prime) (hab : a ≠ b)
    (ha : a % 2 = 1) (hb : b % 2 = 1) :
    (2 : ℕ).factorization p ≤ (a.dist b).factorization p := by
  by_cases hp2 : p = 2
  · subst p
    rw [Nat.prime_two.factorization_self]
    apply (Nat.prime_two.dvd_iff_one_le_factorization (dist_ne_zero hab)).mp
    apply cast_dist_eq_zero_iff.mp
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
    omega
  · have hzero : (2 : ℕ).factorization p = 0 := by
      rw [Nat.prime_two.factorization]
      simp [Ne.symm hp2]
    omega

end Erdos126ValuationUnwinding

namespace Erdos126GeneralValuation

open Erdos126ValuationUnwinding

lemma min_factorization_le_add {a b p : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b) :
    min (a.factorization p) (b.factorization p) ≤ (a+b).factorization p := by
  apply (hp.pow_dvd_iff_le_factorization (by omega : a+b ≠ 0)).mp
  apply dvd_add
  · exact (hp.pow_dvd_iff_le_factorization ha.ne').mpr (min_le_left _ _)
  · exact (hp.pow_dvd_iff_le_factorization hb.ne').mpr (min_le_right _ _)

lemma factorization_add_eq_min_of_ne {a b p : ℕ} (hp : p.Prime)
    (ha : 0 < a) (hb : 0 < b) (hne : a.factorization p ≠ b.factorization p) :
    (a+b).factorization p = min (a.factorization p) (b.factorization p) := by
  have hlow := min_factorization_le_add hp ha hb
  have hn : a+b ≠ 0 := by omega
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le] at hlow ⊢
    have hupper : (a+b).factorization p ≤ a.factorization p := by
      by_contra hnle
      have hsum : p^(a.factorization p+1) ∣ a+b :=
        (hp.pow_dvd_iff_le_factorization hn).mpr (by omega)
      have hbd : p^(a.factorization p+1) ∣ b :=
        (hp.pow_dvd_iff_le_factorization hb.ne').mpr h
      have had : p^(a.factorization p+1) ∣ a := by simpa using Nat.dvd_sub hsum hbd
      have hh := (hp.pow_dvd_iff_le_factorization ha.ne').mp had
      omega
    omega
  · rw [min_eq_right h.le] at hlow ⊢
    have hupper : (a+b).factorization p ≤ b.factorization p := by
      by_contra hnle
      have hsum : p^(b.factorization p+1) ∣ a+b :=
        (hp.pow_dvd_iff_le_factorization hn).mpr (by omega)
      have had : p^(b.factorization p+1) ∣ a :=
        (hp.pow_dvd_iff_le_factorization ha.ne').mpr h
      have hbd : p^(b.factorization p+1) ∣ b := by simpa using Nat.dvd_sub hsum had
      have hh := (hp.pow_dvd_iff_le_factorization hb.ne').mp hbd
      omega
    omega

lemma factorization_dist_eq_min_of_ne {a b p : ℕ} (hp : p.Prime)
    (ha : 0 < a) (hb : 0 < b) (hne : a.factorization p ≠ b.factorization p) :
    (a.dist b).factorization p = min (a.factorization p) (b.factorization p) := by
  have hab : a ≠ b := by intro h; exact hne (congrArg (fun x : ℕ => x.factorization p) h)
  have haux (a b : ℕ) (ha : 0 < a) (hab : a < b)
      (hne : a.factorization p ≠ b.factorization p) :
      (b - a).factorization p = min (a.factorization p) (b.factorization p) := by
    have hd : 0 < b - a := by omega
    have heq : a + (b - a) = b := by omega
    by_cases hv : a.factorization p = (b - a).factorization p
    · have hlow := min_factorization_le_add hp ha hd
      rw [heq, hv, min_self] at hlow
      rw [min_eq_left (by omega)]
      exact hv.symm
    · have hs := factorization_add_eq_min_of_ne hp ha hd hv
      rw [heq] at hs
      have hlow := min_le_left (a.factorization p) ((b - a).factorization p)
      have hright := min_le_right (a.factorization p) ((b - a).factorization p)
      rw [← hs] at hlow hright
      rw [min_eq_right hlow]
      omega
  rcases lt_or_gt_of_ne hab with h | h
  · rw [Nat.dist_eq_sub_of_le h.le]
    exact haux a b ha h hne
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h.le, min_comm]
    exact haux b a hb h hne.symm

lemma same_color_unit_sum_le {p a b : ℕ} (hp : p.Prime)
    (ha : ¬p ∣ a) (hb : ¬p ∣ b)
    (hc : residueColor p a = residueColor p b) :
    (a + b).factorization p ≤ (2 : ℕ).factorization p := by
  by_contra hn
  have hs : (2 : ℕ).factorization p < (a + b).factorization p := by omega
  have hpd : p ∣ a + b := Nat.dvd_of_factorization_pos (by omega)
  have h4 (hp2 : p = 2) : 4 ∣ a + b := by
    subst p
    change 2 ^ 2 ∣ a + b
    by_cases hz : a + b = 0
    · simp [hz]
    · apply (Nat.prime_two.pow_dvd_iff_le_factorization hz).mpr
      norm_num at hs
      omega
  exact opposite_residue_colors hp ha hb hpd h4 hc

lemma unit_unwound_lower {p a b : ℕ} (hp : p.Prime) (hab : a ≠ b)
    (ha : ¬p ∣ a) (hb : ¬p ∣ b) :
    ((a + b).factorization p : ℝ) - (2 : ℕ).factorization p ≤
      residueSign p a * residueSign p b *
        (((a.dist b).factorization p : ℝ) - (a + b).factorization p) := by
  by_cases hc : residueColor p a = residueColor p b
  · have hvs : ((a + b).factorization p : ℝ) ≤ (2 : ℕ).factorization p := by
      exact_mod_cast same_color_unit_sum_le hp ha hb hc
    have hvd : ((2 : ℕ).factorization p : ℝ) ≤ (a.dist b).factorization p := by
      by_cases hp2 : p = 2
      · subst p
        exact_mod_cast odd_dist_valuation_lower Nat.prime_two hab (by omega) (by omega)
      · have hz : (2 : ℕ).factorization p = 0 := by
          rw [Nat.prime_two.factorization]
          simp [Ne.symm hp2]
        rw [hz, Nat.cast_zero]
        positivity
    have hsgn : residueSign p a * residueSign p b = 1 := by
      unfold residueSign
      rw [hc]
      split_ifs <;> norm_num
    rw [hsgn, one_mul]
    linarith
  · have hvd : ((a.dist b).factorization p : ℝ) ≤ (2 : ℕ).factorization p := by
      exact_mod_cast different_color_dist_valuation_le hp hab hc
    have hsgn : residueSign p a * residueSign p b = -1 := by
      unfold residueSign
      cases hca : residueColor p a <;> cases hcb : residueColor p b <;> simp_all
    rw [hsgn]
    linarith

def primeSign (p a : ℕ) : ℝ := residueSign p (ordCompl[p] a)

lemma primeSign_sq (p a : ℕ) : primeSign p a ^ 2 = 1 := residueSign_sq _ _

/-- Unwinding works for arbitrary positive operands. The common gcd is
exactly the baseline which must be subtracted from the recovered sum. -/
lemma general_unwound_lower {p K a b : ℕ} (hp : p.Prime)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hdiff : (a.dist b).factorization p ≤ K) (hsum : (a + b).factorization p ≤ K) :
    ((a + b).factorization p : ℝ) - (a.gcd b).factorization p - (2 : ℕ).factorization p ≤
      primeSign p a * primeSign p b * truncatedKernel p K a b := by
  rw [truncatedKernel_eq hp hab hdiff hsum]
  have hg : (a.gcd b).factorization p = min (a.factorization p) (b.factorization p) := by
    rw [Nat.factorization_gcd ha.ne' hb.ne', Finsupp.inf_apply]
  by_cases hv : a.factorization p = b.factorization p
  · let u := ordCompl[p] a
    let v := ordCompl[p] b
    have heqa : p ^ a.factorization p * u = a := Nat.ordProj_mul_ordCompl_eq_self a p
    have heqb : p ^ a.factorization p * v = b := by
      rw [hv]
      exact Nat.ordProj_mul_ordCompl_eq_self b p
    have hu : 0 < u := Nat.ordCompl_pos p ha.ne'
    have hw : 0 < v := Nat.ordCompl_pos p hb.ne'
    have huv : u ≠ v := by intro h; apply hab; rw [← heqa, ← heqb, h]
    have heqs : a + b = p ^ a.factorization p * (u + v) := by nlinarith
    have heqd : a.dist b = p ^ a.factorization p * u.dist v := by
      calc
        a.dist b = (p ^ a.factorization p * u).dist (p ^ a.factorization p * v) :=
          congrArg₂ Nat.dist heqa.symm heqb.symm
        _ = _ := Nat.dist_mul_left _ _ _
    have hsval : (a + b).factorization p = a.factorization p + (u + v).factorization p := by
      rw [heqs, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (by omega),
        Finsupp.add_apply, Nat.factorization_pow_self hp]
    have hdval : (a.dist b).factorization p = a.factorization p + (u.dist v).factorization p := by
      rw [heqd, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (dist_ne_zero huv),
        Finsupp.add_apply, Nat.factorization_pow_self hp]
    have h := unit_unwound_lower hp huv (Nat.not_dvd_ordCompl hp ha.ne')
      (Nat.not_dvd_ordCompl hp hb.ne')
    rw [hg, hv, min_self, ← hv, hsval, hdval]
    push_cast
    dsimp only [primeSign]
    change ((a.factorization p : ℝ) + (u + v).factorization p) - a.factorization p -
      (2 : ℕ).factorization p ≤ residueSign p u * residueSign p v *
        (((a.factorization p : ℝ) + (u.dist v).factorization p) -
          ((a.factorization p : ℝ) + (u + v).factorization p))
    convert h using 1 <;> ring
  · rw [factorization_add_eq_min_of_ne hp ha hb hv,
      factorization_dist_eq_min_of_ne hp ha hb hv, hg]
    simp only [sub_self, mul_zero, zero_sub]
    exact neg_nonpos.mpr (Nat.cast_nonneg _)

end Erdos126GeneralValuation

namespace Erdos126GcdEnergy

open scoped BigOperators
open Erdos126SignUnwinding Erdos126ValuationUnwinding Erdos126GeneralValuation

lemma log_eq_sum_factorization (m : ℕ) (hm : m ≠ 0) :
    Real.log m = ∑ p ∈ m.primeFactors, (m.factorization p : ℝ) * Real.log p := by
  have heq := Nat.factorization_prod_pow_eq_self hm
  change (∏ p ∈ m.factorization.support, p ^ m.factorization p) = m at heq
  rw [Nat.support_factorization] at heq
  have hreal : (∏ p ∈ m.primeFactors, (p : ℝ) ^ m.factorization p) = m := by
    exact_mod_cast heq
  rw [← hreal, Real.log_prod]
  · simp [Real.log_pow]
  · intro p hp
    apply pow_ne_zero
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero

lemma partial_factorization_log_le (S : Finset ℕ) {n : ℕ} (hn : n ≠ 0) :
    (∑ p ∈ S, (n.factorization p : ℝ) * Real.log p) ≤ Real.log n := by
  have hnonneg (p : ℕ) : 0 ≤ (n.factorization p : ℝ) * Real.log p := by
    by_cases hp : p.Prime
    · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
    · simp [Nat.factorization_eq_zero_of_not_prime n hp]
  have hzero (p : ℕ) (hp : p ∉ n.primeFactors) : (n.factorization p : ℝ) * Real.log p = 0 := by
    have hv : n.factorization p = 0 := Finsupp.notMem_support_iff.mp (by
      simpa only [Nat.support_factorization] using hp)
    simp [hv]
  have hsum : (∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log p) =
      ∑ p ∈ S ∪ n.primeFactors, (n.factorization p : ℝ) * Real.log p :=
    Finset.sum_subset Finset.subset_union_right (fun p _ hp => hzero p hp)
  rw [log_eq_sum_factorization _ hn, hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun p _ _ => hnonneg p)

lemma log_eq_sum_of_support_subset (S : Finset ℕ) {n : ℕ} (hn : n ≠ 0)
    (hsub : n.primeFactors ⊆ S) :
    Real.log n = ∑ p ∈ S, (n.factorization p : ℝ) * Real.log p := by
  rw [log_eq_sum_factorization n hn]
  apply Finset.sum_subset hsub
  intro p hp hpn
  have hv : n.factorization p = 0 := Finsupp.notMem_support_iff.mp (by
    simpa only [Nat.support_factorization] using hpn)
  simp [hv]

lemma factorization_le_log_of_le {p n U : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hnU : n ≤ U) : n.factorization p ≤ Nat.log p U := by
  have hU : U ≠ 0 := by omega
  exact (Nat.le_log_iff_pow_le hp.one_lt hU).mpr
    ((Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
      ((hp.pow_dvd_iff_le_factorization hn).mpr le_rfl)).trans hnU)

lemma nat_log_mul_real_log_le {p U : ℕ} (hp : p.Prime) (hU : U ≠ 0) :
    (Nat.log p U : ℝ) * Real.log p ≤ Real.log U := by
  have hpow : (p : ℝ) ^ Nat.log p U ≤ U := by exact_mod_cast Nat.pow_log_le_self p hU
  have h := Real.log_le_log (pow_pos (by exact_mod_cast hp.pos) _) hpow
  simpa only [Real.log_pow] using h

noncomputable def gcdDistance (a b : ℕ) : ℝ := Real.log a + Real.log b - 2 * Real.log (a.gcd b)

lemma gcdDistance_self (a : ℕ) : gcdDistance a a = 0 := by simp [gcdDistance]; ring

lemma gcdDistance_nonneg {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : 0 ≤ gcdDistance a b := by
  have hg : (0 : ℝ) < a.gcd b := by exact_mod_cast Nat.gcd_pos_of_pos_left b ha
  have hga : (a.gcd b : ℝ) ≤ a := by exact_mod_cast Nat.gcd_le_left b ha
  have hgb : (a.gcd b : ℝ) ≤ b := by exact_mod_cast Nat.gcd_le_right a hb
  have hla := Real.log_le_log hg hga
  have hlb := Real.log_le_log hg hgb
  dsimp [gcdDistance]
  linarith

lemma log_product_le_twice_log_mean {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Real.log a + Real.log b ≤ 2 * (Real.log (a + b : ℕ) - Real.log 2) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hsq : (2 : ℝ)^2 * ((a : ℝ) * b) ≤ ((a : ℝ) + b)^2 := by
    nlinarith [sq_nonneg ((a : ℝ) - b)]
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2^2 * ((a : ℝ) * b)) hsq
  rw [Real.log_mul (by positivity) (mul_pos haR hbR).ne', Real.log_pow,
    Real.log_mul haR.ne' hbR.ne', Real.log_pow] at hlog
  rw [Nat.cast_add]
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

lemma gcdDistance_le_unwound_log {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    gcdDistance a b ≤ 2 * (Real.log (a + b : ℕ) - Real.log (a.gcd b) - Real.log 2) := by
  have h := log_product_le_twice_log_mean ha hb
  dsimp [gcdDistance]
  linarith

/-- The unrestricted average gcd-distance estimate. It uses the full
actual sum-prime support but does not assume pairwise coprimality. -/
theorem gcd_distance_energy_bound (A S : Finset ℕ) (H : ℕ)
    (hH : 0 < H) (hposA : ∀ a ∈ A, 0 < a) (hhi : ∀ a ∈ A, a ≤ H)
    (hS : ∀ p ∈ S, p.Prime)
    (hsup : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (a + b).primeFactors ⊆ S) :
    (∑ a ∈ A, ∑ b ∈ A, gcdDistance a b) ≤
      4 * (S.card : ℝ)^2 * A.card * Real.log (2 * H : ℕ) := by
  classical
  let K (p : ℕ) := Nat.log p (2 * H)
  let M (p : ↥S) (a b : ↥A) := Real.log (p : ℕ) * truncatedKernel p (K p) a b
  let σ (p : ↥S) (a : ↥A) := primeSign p a
  have hlogp (p : ↥S) : 0 ≤ Real.log (p : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (hS p p.property).one_lt.le)
  have hU : 2 * H ≠ 0 := by omega
  have hK (p : ↥S) (a b : ↥A) (hab : a ≠ b) :
      (a.val.dist b.val).factorization p ≤ K p ∧
      (a.val + b.val).factorization p ≤ K p := by
    have hne : a.val ≠ b.val := Subtype.coe_ne_coe.mpr hab
    have ha := hhi a a.property
    have hb := hhi b b.property
    refine ⟨factorization_le_log_of_le (hS p p.property) (dist_ne_zero hne) ?_,
      factorization_le_log_of_le (hS p p.property) (by omega) (by omega)⟩
    rcases le_total a.val b.val with h | h
    · rw [Nat.dist_eq_sub_of_le h]
      omega
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]
      omega
  have hMeq (p : ↥S) (a b : ↥A) (hab : a ≠ b) :
      M p a b = ((a.val.dist b.val).factorization p : ℝ) * Real.log (p : ℕ) -
        ((a.val + b.val).factorization p : ℝ) * Real.log (p : ℕ) := by
    dsimp only [M]
    rw [truncatedKernel_eq (hS p p.property) (Subtype.coe_ne_coe.mpr hab)
      (hK p a b hab).1 (hK p a b hab).2]
    ring
  have hpos (p : ↥S) : Positive (M p) := by
    intro c
    have he : quad (M p) c = Real.log (p : ℕ) *
        quad (fun a b : ↥A => truncatedKernel p (K p) a b) c := by
      simp only [quad, M, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    rw [he]
    exact mul_nonneg (hlogp p)
      (truncatedKernel_positive (fun a : ↥A => a.val) p (K p) (hS p p.property).pos c)
  have hoff (a b : ↥A) (hab : a ≠ b) : (∑ p, M p a b) ≤ 0 := by
    simp_rw [hMeq _ a b hab]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_coe_sort S (fun p => ((a.val.dist b.val).factorization p : ℝ) * Real.log p),
      Finset.sum_coe_sort S (fun p => ((a.val + b.val).factorization p : ℝ) * Real.log p),
      ← log_eq_sum_of_support_subset S (by have := Subtype.coe_ne_coe.mpr hab; omega)
        (hsup a a.property b b.property (Subtype.coe_ne_coe.mpr hab))]
    have hpart := partial_factorization_log_le S (dist_ne_zero (Subtype.coe_ne_coe.mpr hab))
    have hdist : a.val.dist b.val ≤ a.val + b.val := by
      rcases le_total a.val b.val with h | h
      · rw [Nat.dist_eq_sub_of_le h]; omega
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]; omega
    have hlogs : Real.log (a.val.dist b.val) ≤ Real.log (a.val + b.val : ℕ) := Real.log_le_log
      (by exact_mod_cast (Nat.pos_of_ne_zero (dist_ne_zero (Subtype.coe_ne_coe.mpr hab))))
      (by exact_mod_cast hdist)
    linarith
  have hdiag (a : ↥A) : (∑ p, M p a a) ≤ (S.card : ℝ) * Real.log (2 * H : ℕ) := by
    have hp (p : ↥S) : M p a a ≤ Real.log (2 * H : ℕ) := by
      have h := mul_le_mul_of_nonneg_left (truncatedKernel_diag_bounds p (K p) a).2 (hlogp p)
      apply h.trans
      simpa [K, mul_comm] using nat_log_mul_real_log_le (hS p p.property) hU
    have h := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset ↥S)) => hp p)
    simpa using h
  have hdiagpos (a : ↥A) : 0 ≤ ∑ p, σ p a * σ p a * M p a a := by
    apply Finset.sum_nonneg
    intro p hp
    have hsq : σ p a * σ p a = 1 := by simpa [σ, pow_two] using primeSign_sq p a
    rw [hsq, one_mul]
    exact mul_nonneg (hlogp p) (truncatedKernel_diag_bounds p (K p) a).1
  have hlower (a b : ↥A) : gcdDistance a b ≤ 2 * ∑ p, σ p a * σ p b * M p a b := by
    by_cases hab : a = b
    · subst b
      rw [gcdDistance_self]
      exact mul_nonneg (by norm_num) (hdiagpos a)
    have hlocal (p : ↥S) :
        (((a.val + b.val).factorization p : ℝ) - (a.val.gcd b.val).factorization p -
          (2 : ℕ).factorization p) * Real.log (p : ℕ) ≤ σ p a * σ p b * M p a b := by
      have h := mul_le_mul_of_nonneg_right
        (general_unwound_lower (hS p p.property) (hposA a a.property) (hposA b b.property)
          (Subtype.coe_ne_coe.mpr hab) (hK p a b hab).1 (hK p a b hab).2) (hlogp p)
      simpa only [σ, M, mul_assoc, mul_left_comm, mul_comm] using h
    have hs := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset ↥S)) => hlocal p)
    simp only [sub_mul, Finset.sum_sub_distrib] at hs
    rw [Finset.sum_coe_sort S (fun p => ((a.val + b.val).factorization p : ℝ) * Real.log p),
      Finset.sum_coe_sort S (fun p => ((a.val.gcd b.val).factorization p : ℝ) * Real.log p),
      Finset.sum_coe_sort S (fun p => ((2 : ℕ).factorization p : ℝ) * Real.log p),
      ← log_eq_sum_of_support_subset S (by have := Subtype.coe_ne_coe.mpr hab; omega)
        (hsup a a.property b b.property (Subtype.coe_ne_coe.mpr hab))] at hs
    have ht := partial_factorization_log_le S (by decide : (2 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at ht
    have hg := partial_factorization_log_le S
      (Nat.gcd_pos_of_pos_left b.val (hposA a a.property)).ne'
    have hdist := gcdDistance_le_unwound_log (hposA a a.property) (hposA b b.property)
    linarith
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset ↥A)) =>
    Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset ↥A)) => hlower a b))
  simp only [← Finset.mul_sum] at hsum
  have hswap : (∑ a : ↥A, ∑ b : ↥A, ∑ p : ↥S, σ p a * σ p b * M p a b) =
      ∑ p : ↥S, ∑ a : ↥A, ∑ b : ↥A, σ p a * σ p b * M p a b := by
    conv_lhs =>
      enter [2, a]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [hswap] at hsum
  have hupper := sign_unwinding_bound M hpos σ (fun p a => primeSign_sq p a)
    ((S.card : ℝ) * Real.log (2 * H : ℕ)) hoff hdiag
  have htot := hsum.trans (mul_le_mul_of_nonneg_left hupper (by norm_num : (0 : ℝ) ≤ 2))
  have hlhs : (∑ a : ↥A, ∑ b : ↥A, gcdDistance a b) = ∑ a ∈ A, ∑ b ∈ A, gcdDistance a b := by
    conv_lhs =>
      enter [2, a]
      rw [Finset.sum_coe_sort A (fun b => gcdDistance a b)]
    exact Finset.sum_coe_sort A (fun a => ∑ b ∈ A, gcdDistance a b)
  rw [hlhs] at htot
  simp only [Fintype.card_coe] at htot
  convert htot using 1
  ring

end Erdos126GcdEnergy

namespace Erdos126Normalization

open Finset

def sumProduct (A : Finset ℕ) : ℕ :=
  ∏ ab ∈ A.offDiag, (ab.1 + ab.2)

def primitivePart (A : Finset ℕ) : Finset ℕ :=
  A.image (fun a => a / A.gcd id)

def primitiveHeight (A : Finset ℕ) : ℕ :=
  (primitivePart A).sup id

lemma sumProduct_ne_zero (A : Finset ℕ) : sumProduct A ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro ab hab
  have := (Finset.mem_offDiag.mp hab).2.2
  omega

lemma sumProduct_image (A : Finset ℕ) (F : ℕ → ℕ) (hF : Set.InjOn F A) :
    (∏ ab ∈ A.offDiag, (F ab.1 + F ab.2)) = sumProduct (A.image F) := by
  apply Finset.prod_bij (fun ab _ => (F ab.1, F ab.2))
  · intro ab hab
    obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
    exact Finset.mem_offDiag.mpr ⟨Finset.mem_image_of_mem F ha,
      Finset.mem_image_of_mem F hb, fun h => hne (hF ha hb h)⟩
  · intro ab hab cd hcd heq
    have hf := congrArg Prod.fst heq
    have hs := congrArg Prod.snd heq
    exact Prod.ext (hF (Finset.mem_offDiag.mp hab).1 (Finset.mem_offDiag.mp hcd).1 hf)
      (hF (Finset.mem_offDiag.mp hab).2.1 (Finset.mem_offDiag.mp hcd).2.1 hs)
  · intro ab hab
    obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
    obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp ha
    obtain ⟨b, hb, heb⟩ := Finset.mem_image.mp hb
    have hn : a ≠ b := by rintro rfl; exact hne (hea.symm.trans heb)
    refine ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hn⟩, ?_⟩
    exact Prod.ext hea heb
  · intro ab hab
    rfl

lemma divide_gcd_injOn (A : Finset ℕ) :
    Set.InjOn (fun a => a / A.gcd id) A := by
  intro a ha b hb heq
  have ha' := Nat.div_mul_cancel (Finset.gcd_dvd (f := id) ha)
  have hb' := Nat.div_mul_cancel (Finset.gcd_dvd (f := id) hb)
  change a / A.gcd id * A.gcd id = a at ha'
  change b / A.gcd id * A.gcd id = b at hb'
  dsimp only at heq
  rw [heq] at ha'
  omega

lemma primitivePart_card (A : Finset ℕ) : (primitivePart A).card = A.card :=
  Finset.card_image_iff.mpr (divide_gcd_injOn A)

lemma sumProduct_primitive_factorization (A : Finset ℕ) :
    sumProduct A = (A.gcd id) ^ A.offDiag.card * sumProduct (primitivePart A) := by
  have heq := sumProduct_image A (fun a => a / A.gcd id) (divide_gcd_injOn A)
  change (∏ ab ∈ A.offDiag, (ab.1 / A.gcd id + ab.2 / A.gcd id)) =
    sumProduct (primitivePart A) at heq
  rw [← heq, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro ab hab
  obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
  rw [mul_add]
  have hga : A.gcd id ∣ ab.1 := Finset.gcd_dvd ha
  have hgb : A.gcd id ∣ ab.2 := Finset.gcd_dvd hb
  rw [Nat.mul_div_cancel' hga, Nat.mul_div_cancel' hgb]

lemma primitive_sumProduct_dvd (A : Finset ℕ) :
    sumProduct (primitivePart A) ∣ sumProduct A := by
  rw [sumProduct_primitive_factorization A]
  exact dvd_mul_left _ _

lemma primitive_support_subset (A : Finset ℕ) :
    (sumProduct (primitivePart A)).primeFactors ⊆ (sumProduct A).primeFactors :=
  Nat.primeFactors_mono (primitive_sumProduct_dvd A) (sumProduct_ne_zero A)

lemma exists_nonzero_of_two_le_card (A : Finset ℕ) (hcard : 2 ≤ A.card) :
    ∃ a ∈ A, a ≠ 0 := by
  by_contra h
  push_neg at h
  have hsub : A ⊆ {0} := by intro a ha; simp [h a ha]
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hc
  omega

lemma primitivePart_gcd_eq_one (A : Finset ℕ) (hcard : 2 ≤ A.card) :
    (primitivePart A).gcd id = 1 := by
  obtain ⟨a, ha, ha0⟩ := exists_nonzero_of_two_le_card A hcard
  rw [primitivePart, Finset.gcd_image]
  exact Finset.gcd_div_id_eq_one ha ha0

lemma gcd_pos_of_two_le_card (A : Finset ℕ) (hcard : 2 ≤ A.card) :
    0 < A.gcd id := by
  apply Nat.pos_of_ne_zero
  apply Finset.gcd_ne_zero_iff.mpr
  exact exists_nonzero_of_two_le_card A hcard

lemma primitiveHeight_pos (A : Finset ℕ) (hcard : 2 ≤ A.card) :
    0 < primitiveHeight A := by
  obtain ⟨a, ha, ha0⟩ := exists_nonzero_of_two_le_card (primitivePart A)
    (by simpa [primitivePart_card] using hcard)
  have hl : a ≤ primitiveHeight A := Finset.le_sup (f := id) ha
  omega

lemma primitivePart_le_height (A : Finset ℕ) :
    ∀ a ∈ primitivePart A, a ≤ primitiveHeight A :=
  fun _ ha => Finset.le_sup (f := id) ha

end Erdos126Normalization

namespace Erdos126GcdAnchors

open Erdos126GcdEnergy Erdos126Normalization

lemma base_gcd_quotient_dvd_product (a : ℕ) (ha : 0 < a) (B : Finset ℕ) :
    a / a.gcd (B.gcd id) ∣ ∏ b ∈ B, a / a.gcd b := by
  classical
  induction B using Finset.induction_on with
  | empty => simp [Nat.div_self ha]
  | @insert b B hb ih =>
      rw [Finset.gcd_insert, Finset.prod_insert hb]
      change a / a.gcd (b.gcd (B.gcd id)) ∣ (a / a.gcd b) * ∏ x ∈ B, a / a.gcd x
      have he : a.gcd (b.gcd (B.gcd id)) = (a.gcd b).gcd (a.gcd (B.gcd id)) := by
        symm
        calc
          (a.gcd b).gcd (a.gcd (B.gcd id)) = ((a.gcd b).gcd a).gcd (B.gcd id) :=
            (Nat.gcd_assoc _ _ _).symm
          _ = (a.gcd b).gcd (B.gcd id) := by rw [Nat.gcd_eq_left (Nat.gcd_dvd_left a b)]
          _ = a.gcd (b.gcd (B.gcd id)) := Nat.gcd_assoc _ _ _
      rw [he, ← Nat.div_lcm_eq_div_gcd (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_left a (B.gcd id))]
      exact (Nat.lcm_dvd_mul _ _).trans (Nat.mul_dvd_mul_left _ ih)

lemma log_nat_div {a g : ℕ} (ha : 0 < a) (hg : 0 < g) (hd : g ∣ a) :
    Real.log (a / g : ℕ) = Real.log a - Real.log g := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  rw [Nat.cast_div hd hgR, Real.log_div haR hgR]

lemma log_base_quotient_le_sum_distance (B : Finset ℕ) (a : ℕ) (haB : a ∈ B)
    (hpos : ∀ b ∈ B, 0 < b) :
    Real.log (a / B.gcd id : ℕ) ≤ ∑ b ∈ B, gcdDistance a b := by
  have ha := hpos a haB
  have hg : 0 < B.gcd id := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hd : B.gcd id ∣ a := Finset.gcd_dvd haB
    rw [hz, zero_dvd_iff] at hd
    omega
  have hdiv := base_gcd_quotient_dvd_product a ha B
  rw [Nat.gcd_eq_right (show B.gcd id ∣ a from Finset.gcd_dvd (f := id) haB)] at hdiv
  have hqpos (b : ℕ) : 0 < a / a.gcd b :=
    Nat.div_pos (Nat.gcd_le_left b ha) (Nat.gcd_pos_of_pos_left b ha)
  have hprodpos : 0 < ∏ b ∈ B, a / a.gcd b := Finset.prod_pos (fun b _ => hqpos b)
  have hbasepos : 0 < a / B.gcd id :=
    Nat.div_pos (Nat.le_of_dvd ha (Finset.gcd_dvd haB)) hg
  have hle : ((a / B.gcd id : ℕ) : ℝ) ≤ ((∏ b ∈ B, a / a.gcd b : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hprodpos hdiv
  have hlog : Real.log (a / B.gcd id : ℕ) ≤ Real.log ((∏ b ∈ B, a / a.gcd b : ℕ) : ℝ) := by
    exact Real.log_le_log (by exact_mod_cast hbasepos) hle
  rw [Nat.cast_prod, Real.log_prod (fun b _ => by exact_mod_cast (hqpos b).ne')] at hlog
  apply hlog.trans
  apply Finset.sum_le_sum
  intro b hb
  rw [log_nat_div ha (Nat.gcd_pos_of_pos_left b ha) (Nat.gcd_dvd_left a b)]
  have hgb := Real.log_le_log
    (show (0 : ℝ) < a.gcd b by exact_mod_cast Nat.gcd_pos_of_pos_left b ha)
    (show (a.gcd b : ℝ) ≤ b by exact_mod_cast Nat.gcd_le_right a (hpos b hb))
  dsimp [gcdDistance]
  linarith

/-- The common-gcd-normalized height of a finite anchor set is controlled
by its total gcd-distance from any one of its members. -/
theorem log_primitiveHeight_le_sum_distance (B : Finset ℕ) (a : ℕ) (haB : a ∈ B)
    (hpos : ∀ b ∈ B, 0 < b) :
    Real.log (primitiveHeight B) ≤ 2 * ∑ b ∈ B, gcdDistance a b := by
  have ha := hpos a haB
  have hBnon : B.Nonempty := ⟨a, haB⟩
  have hg : 0 < B.gcd id := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hd : B.gcd id ∣ a := Finset.gcd_dvd haB
    rw [hz, zero_dvd_iff] at hd
    omega
  have hbase := log_base_quotient_le_sum_distance B a haB hpos
  rw [log_nat_div ha hg (Finset.gcd_dvd haB)] at hbase
  have hpoint (b : ℕ) (hb : b ∈ B) :
      Real.log (b / B.gcd id : ℕ) ≤ 2 * ∑ c ∈ B, gcdDistance a c := by
    rw [log_nat_div (hpos b hb) hg (Finset.gcd_dvd hb)]
    have hga := Real.log_le_log
      (show (0 : ℝ) < a.gcd b by exact_mod_cast Nat.gcd_pos_of_pos_left b ha)
      (show (a.gcd b : ℝ) ≤ a by exact_mod_cast Nat.gcd_le_left b ha)
    have hd : Real.log b - Real.log a ≤ gcdDistance a b := by
      dsimp [gcdDistance]
      linarith
    have hsingle : gcdDistance a b ≤ ∑ c ∈ B, gcdDistance a c :=
      Finset.single_le_sum (fun c hc => gcdDistance_nonneg ha (hpos c hc)) hb
    linarith
  obtain ⟨b, hb, hsup⟩ := Finset.exists_mem_eq_sup (primitivePart B)
    (hBnon.image (fun b => b / B.gcd id)) id
  obtain ⟨c, hc, hcb⟩ := Finset.mem_image.mp hb
  change (primitivePart B).sup id = b at hsup
  change Real.log (((primitivePart B).sup id : ℕ) : ℝ) ≤ _
  rw [hsup, ← hcb]
  exact hpoint c hc

/-- Selecting a fixed number of low-weight points costs at most twice
the corresponding fraction of total weight. Stated without division. -/
lemma exists_small_weight_subset {α : Type*} [DecidableEq α]
    (A : Finset α) (f : α → ℝ) (hf : ∀ a ∈ A, 0 ≤ f a)
    (m : ℕ) (_hm : 0 < m) (hn : 2 * m ≤ A.card) :
    ∃ B ⊆ A, B.card = m ∧
      (A.card : ℝ) * (∑ b ∈ B, f b) ≤ 2 * m * (∑ a ∈ A, f a) := by
  classical
  let T := ∑ a ∈ A, f a
  have hT : 0 ≤ T := Finset.sum_nonneg hf
  let C := A.filter (fun a => (A.card : ℝ) * f a ≤ 2 * T)
  let D := A.filter (fun a => ¬ (A.card : ℝ) * f a ≤ 2 * T)
  have hDC : D.card + C.card = A.card := by
    simpa only [C, D, Nat.add_comm] using
      (Finset.card_filter_add_card_filter_not (s := A) (fun a => (A.card : ℝ) * f a ≤ 2 * T))
  have hCcard : m ≤ C.card := by
    by_contra h
    have hDpos : 0 < D.card := by omega
    have hDnon := Finset.card_pos.mp hDpos
    have hstrict : (D.card : ℝ) * (2 * T) < (A.card : ℝ) * (∑ a ∈ D, f a) := by
      have hh := Finset.sum_lt_sum_of_nonempty hDnon
        (fun a ha => lt_of_not_ge (Finset.mem_filter.mp ha).2)
      simpa only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] using hh
    have hsubset : D ⊆ A := Finset.filter_subset _ _
    have hsum : (∑ a ∈ D, f a) ≤ T :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun a ha _ => hf a ha)
    have hbound := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg A.card : (0 : ℝ) ≤ _)
    have hcards : (A.card : ℝ) ≤ 2 * D.card := by exact_mod_cast (show A.card ≤ 2 * D.card by omega)
    have hmul := mul_le_mul_of_nonneg_right hcards hT
    nlinarith
  obtain ⟨B, hBC, hBm⟩ := Finset.exists_subset_card_eq hCcard
  refine ⟨B, hBC.trans (Finset.filter_subset _ _), hBm, ?_⟩
  have hh := Finset.sum_le_sum (fun b hb => (Finset.mem_filter.mp (hBC hb)).2)
  rw [← Finset.mul_sum, Finset.sum_const, hBm, nsmul_eq_mul] at hh
  nlinarith

end Erdos126GcdAnchors

namespace Erdos126Anchors

open Finset

lemma exists_excess_prime (S : Finset ℕ) {m M : ℕ}
    (hm : m ≠ 0) (hM : M ≠ 0) (hsup : m.primeFactors ⊆ S)
    (hndiv : ¬m ∣ M) :
    ∃ p ∈ S, M.factorization p < m.factorization p := by
  have hnot : ¬m.factorization ≤ M.factorization := by
    intro h
    exact hndiv ((Nat.factorization_le_iff_dvd hm hM).mp h)
  have hex : ∃ p, ¬m.factorization p ≤ M.factorization p := by
    by_contra h
    push_neg at h
    exact hnot h
  obtain ⟨p, hp⟩ := hex
  refine ⟨p, hsup ?_, by omega⟩
  rw [← Nat.support_factorization, Finsupp.mem_support_iff]
  omega

lemma no_shared_excess_prime {a b M p : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hM : M ≠ 0)
    (hp : p.Prime) (hgcd : a.gcd b ∣ M)
    (hpa : M.factorization p < a.factorization p)
    (hpb : M.factorization p < b.factorization p) : False := by
  have hd1 : p ^ (M.factorization p + 1) ∣ a :=
    (hp.pow_dvd_iff_le_factorization ha).mpr (by omega)
  have hd2 : p ^ (M.factorization p + 1) ∣ b :=
    (hp.pow_dvd_iff_le_factorization hb).mpr (by omega)
  have hd := (Nat.dvd_gcd hd1 hd2).trans hgcd
  have hv := (hp.pow_dvd_iff_le_factorization hM).mp hd
  omega

/-- If more than |S| nonzero S-smooth values have pairwise gcds dividing M,
one of the values divides M. Values are indexed by an arbitrary finite set. -/
theorem exists_dvd_of_few_primes {α : Type*} [DecidableEq α]
    (B : Finset α) (F : α → ℕ) (S : Finset ℕ) {M : ℕ}
    (hM : M ≠ 0) (hS : ∀ p ∈ S, p.Prime)
    (hpos : ∀ b ∈ B, F b ≠ 0)
    (hsup : ∀ b ∈ B, (F b).primeFactors ⊆ S)
    (hpair : ∀ b ∈ B, ∀ c ∈ B, b ≠ c → (F b).gcd (F c) ∣ M)
    (hcard : S.card < B.card) :
    ∃ b ∈ B, F b ∣ M := by
  classical
  by_contra h
  push_neg at h
  have hex : ∀ b ∈ B, ∃ p ∈ S, M.factorization p < (F b).factorization p :=
    fun b hb => exists_excess_prime S (hpos b hb) hM (hsup b hb) (h b hb)
  choose! p hpS hpval using hex
  have hbound : B.card ≤ S.card := by
    apply Finset.card_le_card_of_injOn p
    · intro b hb
      exact hpS b hb
    · intro b hb c hc heq
      by_contra hne
      have hpb := hpval b hb
      have hpc := hpval c hc
      rw [← heq] at hpc
      exact no_shared_excess_prime (hpos b hb) (hpos c hc) hM
        (hS _ (hpS b hb)) (hpair b hb c hc hne) hpb hpc
  omega

def primeBox (S : Finset ℕ) (D : ℕ) : ℕ :=
  ∏ p ∈ S, p ^ Nat.log p D

lemma primeBox_ne_zero {S : Finset ℕ} {D : ℕ}
    (hS : ∀ p ∈ S, p.Prime) : primeBox S D ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hS p hp).ne_zero)

lemma primeBox_le (S : Finset ℕ) {D : ℕ} (hD : D ≠ 0) :
    primeBox S D ≤ D ^ S.card := by
  have h := Finset.prod_le_prod (fun p (_ : p ∈ S) => Nat.zero_le (p ^ Nat.log p D))
    (fun p (_ : p ∈ S) => Nat.pow_log_le_self p hD)
  simpa [primeBox] using h

lemma dvd_primeBox {S : Finset ℕ} {D m : ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hm : m ≠ 0) (hmD : m ≤ D)
    (hsup : m.primeFactors ⊆ S) : m ∣ primeBox S D := by
  have hD : D ≠ 0 := by omega
  apply (Nat.factorization_le_iff_dvd hm (primeBox_ne_zero hS)).mp
  intro p
  by_cases hv : m.factorization p = 0
  · simp [hv]
  · have hp : p ∈ m.primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      exact hv
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hd : p ^ m.factorization p ∣ m :=
      (hprime.pow_dvd_iff_le_factorization hm).mpr le_rfl
    have he : m.factorization p ≤ Nat.log p D :=
      (Nat.le_log_iff_pow_le hprime.one_lt hD).mpr
        ((Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hd).trans hmD)
    have hbox : p ^ Nat.log p D ∣ primeBox S D :=
      Finset.dvd_prod_of_mem (fun q => q ^ Nat.log q D) (hsup hp)
    exact he.trans ((hprime.pow_dvd_iff_le_factorization (primeBox_ne_zero hS)).mp hbox)

lemma gcd_add_dvd_dist (x b c : ℕ) : (x + b).gcd (x + c) ∣ b.dist c := by
  have h1 := Nat.gcd_dvd_left (x + b) (x + c)
  have h2 := Nat.gcd_dvd_right (x + b) (x + c)
  rcases le_total b c with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    have hd := Nat.dvd_sub h2 h1
    simpa only [Nat.add_sub_add_left] using hd
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]
    have hd := Nat.dvd_sub h1 h2
    simpa only [Nat.add_sub_add_left] using hd

lemma dist_ne_zero {b c : ℕ} (hbc : b ≠ c) : b.dist c ≠ 0 := by
  rcases le_total b c with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    omega
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]
    omega

def sumProduct (A : Finset ℕ) : ℕ :=
  ∏ ab ∈ A.offDiag, (ab.1 + ab.2)

lemma sumProduct_ne_zero (A : Finset ℕ) : sumProduct A ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro ab hab
  have := (Finset.mem_offDiag.mp hab).2.2
  omega

lemma sum_support_subset {A : Finset ℕ} {a b : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    (a + b).primeFactors ⊆ (sumProduct A).primeFactors := by
  apply Nat.primeFactors_mono _ (sumProduct_ne_zero A)
  have hmem : (a, b) ∈ A.offDiag := Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩
  exact Finset.dvd_prod_of_mem (fun ab : ℕ × ℕ => ab.1 + ab.2) hmem

end Erdos126Anchors

namespace Erdos126AffineAnchors

open Finset Erdos126Anchors

lemma gcd_affine_dvd_dist (t u b c : ℕ) (hcop : t.Coprime u) :
    (t + u * b).gcd (t + u * c) ∣ b.dist c := by
  have h := Erdos126Anchors.gcd_add_dvd_dist t (u * b) (u * c)
  rw [Nat.dist_mul_left] at h
  have htu : (t + u * b).Coprime u :=
    (Nat.coprime_add_mul_left_left t u b).mpr hcop
  have hgu : ((t + u * b).gcd (t + u * c)).Coprime u :=
    htu.of_dvd_left (Nat.gcd_dvd_left _ _)
  exact hgu.dvd_of_dvd_mul_left h

/-- Coprime affine coefficients disappear from pairwise gcd bounds.
More anchors than primes therefore bound the coefficients themselves. -/
theorem affine_star_parameter_bound (B S : Finset ℕ) (t u H : ℕ)
    (hu : 0 < u) (hcop : t.Coprime u) (hH : 0 < H)
    (hB : ∀ b ∈ B, 0 < b ∧ b ≤ H) (hS : ∀ p ∈ S, p.Prime)
    (hsup : ∀ b ∈ B, (t + u * b).primeFactors ⊆ S)
    (hcard : S.card < B.card) : t + u ≤ H ^ S.card := by
  have hpos (b : ℕ) (hb : b ∈ B) : t + u * b ≠ 0 := by
    have h := Nat.mul_pos hu (hB b hb).1
    omega
  have hM : primeBox S H ≠ 0 := primeBox_ne_zero hS
  have hpair : ∀ b ∈ B, ∀ c ∈ B, b ≠ c →
      (t + u * b).gcd (t + u * c) ∣ primeBox S H := by
    intro b hb c hc hbc
    have hg : (t + u * b).gcd (t + u * c) ≠ 0 := by
      intro heq
      have hh := Nat.gcd_dvd_left (t + u * b) (t + u * c)
      rw [heq, zero_dvd_iff] at hh
      exact hpos b hb hh
    apply dvd_primeBox hS hg
    · have hdist := Nat.le_of_dvd
        (Nat.pos_of_ne_zero (Erdos126Anchors.dist_ne_zero hbc))
        (gcd_affine_dvd_dist t u b c hcop)
      have hbH := (hB b hb).2
      have hcH := (hB c hc).2
      rcases le_total b c with h | h
      · rw [Nat.dist_eq_sub_of_le h] at hdist; omega
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h] at hdist; omega
    · exact (Nat.primeFactors_mono (Nat.gcd_dvd_left _ _) (hpos b hb)).trans (hsup b hb)
  obtain ⟨b, hb, hdiv⟩ := Erdos126Anchors.exists_dvd_of_few_primes B
    (fun b => t + u * b) S hM hS hpos hsup hpair hcard
  have hle := (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hdiv).trans
    (primeBox_le S hH.ne')
  have hbpos := (hB b hb).1
  have hlow : t + u ≤ t + u * b := by
    have hh := Nat.mul_le_mul_left u (show 1 ≤ b by omega)
    simpa using Nat.add_le_add_left hh t
  exact hlow.trans hle

lemma card_le_erase_add_one (B : Finset ℕ) (b : ℕ) :
    B.card ≤ (B.erase b).card + 1 := by
  by_cases hb : b ∈ B
  · rw [Finset.card_erase_add_one hb]
  · rw [Finset.erase_eq_of_notMem hb]
    omega

/-- An arbitrary scale on an anchor set is bounded modulo its gcd with
each operand of the ambient clique. -/
theorem scaled_anchor_quotient_bound (A B : Finset ℕ) (g H : ℕ)
    (hg : 0 < g) (hH : 0 < H) (hB : ∀ b ∈ B, 0 < b ∧ b ≤ H)
    (hBA : B.image (fun b => g * b) ⊆ A)
    (hcard : (sumProduct A).primeFactors.card + 2 ≤ B.card) :
    ∀ x ∈ A, x / x.gcd g + g / x.gcd g ≤ H ^ (sumProduct A).primeFactors.card := by
  intro x hx
  let S := (sumProduct A).primeFactors
  let C := B.erase (x / g)
  let h := x.gcd g
  have hh : 0 < h := Nat.gcd_pos_of_pos_right x hg
  have hgh : h ≤ g := Nat.le_of_dvd hg (Nat.gcd_dvd_right x g)
  have hu : 0 < g / h := Nat.div_pos hgh hh
  have hcop : (x / h).Coprime (g / h) := Nat.coprime_div_gcd_div_gcd hh
  have hS : ∀ p ∈ S, p.Prime := fun _ hp => Nat.prime_of_mem_primeFactors hp
  have hCB : C ⊆ B := Finset.erase_subset _ _
  have hCcard : S.card < C.card := by
    have hc := card_le_erase_add_one B (x / g)
    dsimp [S, C]
    omega
  apply affine_star_parameter_bound C S (x / h) (g / h) H hu hcop hH
    (fun b hb => hB b (hCB hb)) hS _ hCcard
  intro b hb
  have hbB := hCB hb
  have hbA : g * b ∈ A := hBA (Finset.mem_image_of_mem _ hbB)
  have hne : x ≠ g * b := by
    intro heq
    have hhne := (Finset.mem_erase.mp hb).1
    apply hhne
    rw [heq, Nat.mul_div_cancel_left b hg]
  have hsup : (x + g * b).primeFactors ⊆ S :=
    Erdos126Anchors.sum_support_subset hx hbA hne
  apply (Nat.primeFactors_mono _ (by
    have hpos := Nat.mul_pos hg (hB b hbB).1
    omega : x + g * b ≠ 0)).trans hsup
  refine ⟨h, ?_⟩
  have hhx : h * (x / h) = x := Nat.mul_div_cancel' (Nat.gcd_dvd_left x g)
  have hhg : h * (g / h) = g := Nat.mul_div_cancel' (Nat.gcd_dvd_right x g)
  calc
    x + g * b = h * (x / h) + (h * (g / h)) * b := by rw [hhx, hhg]
    _ = _ := by ring

lemma exists_not_dvd_of_gcd_one (A : Finset ℕ) (hA : A.gcd id = 1)
    {p : ℕ} (hp : p.Prime) : ∃ x ∈ A, ¬p ∣ x := by
  by_contra h
  push_neg at h
  have hd : p ∣ A.gcd id := Finset.dvd_gcd_iff.mpr h
  rw [hA] at hd
  exact hp.not_dvd_one hd

lemma scale_le_of_primitive (A S : Finset ℕ) (g L : ℕ)
    (hg : 0 < g) (hL : 0 < L) (hA : A.gcd id = 1)
    (hsup : g.primeFactors ⊆ S)
    (hbound : ∀ x ∈ A, g / x.gcd g ≤ L) : g ≤ L ^ S.card := by
  have hpower : ∀ p ∈ g.primeFactors, p ^ g.factorization p ≤ L := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    obtain ⟨x, hx, hpx⟩ := exists_not_dvd_of_gcd_one A hA hprime
    have hph : ¬p ∣ x.gcd g := fun hd => hpx (hd.trans (Nat.gcd_dvd_left x g))
    have hcop : (p ^ g.factorization p).Coprime (x.gcd g) :=
      (hprime.coprime_iff_not_dvd.mpr hph).pow_left _
    have hdiv : p ^ g.factorization p ∣ g :=
      (hprime.pow_dvd_iff_le_factorization hg.ne').mpr le_rfl
    have hdivq : p ^ g.factorization p ∣ g / x.gcd g := by
      apply hcop.dvd_of_dvd_mul_left
      rwa [Nat.mul_div_cancel' (Nat.gcd_dvd_right x g)]
    have hqpos : 0 < g / x.gcd g := Nat.div_pos
      (Nat.le_of_dvd hg (Nat.gcd_dvd_right x g)) (Nat.gcd_pos_of_pos_right x hg)
    exact (Nat.le_of_dvd hqpos hdivq).trans (hbound x hx)
  calc
    g = ∏ p ∈ g.primeFactors, p ^ g.factorization p := by
      simpa only [Nat.prod_factorization_eq_prod_primeFactors] using
        (Nat.factorization_prod_pow_eq_self hg.ne').symm
    _ ≤ ∏ p ∈ g.primeFactors, L :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hpower
    _ = L ^ g.primeFactors.card := by simp
    _ ≤ L ^ S.card := Nat.pow_le_pow_right hL (Finset.card_le_card hsup)

/-- In a primitive ambient clique, a short normalized anchor set controls
the common scale and hence the height of every ambient operand. -/
theorem primitive_height_from_scaled_anchors (A B : Finset ℕ) (g H : ℕ)
    (hg : 0 < g) (hH : 0 < H) (hA : A.gcd id = 1)
    (hB : ∀ b ∈ B, 0 < b ∧ b ≤ H)
    (hBA : B.image (fun b => g * b) ⊆ A)
    (hcard : (sumProduct A).primeFactors.card + 2 ≤ B.card) :
    ∀ x ∈ A, x ≤ H ^ ((sumProduct A).primeFactors.card *
      ((sumProduct A).primeFactors.card + 1)) := by
  let S := (sumProduct A).primeFactors
  let r := S.card
  have hquot := scaled_anchor_quotient_bound A B g H hg hH hB hBA hcard
  have hsupport : g.primeFactors ⊆ S := by
    obtain ⟨b, hb, c, hc, hbc⟩ := Finset.one_lt_card.mp (show 1 < B.card by omega)
    have hbA := hBA (Finset.mem_image_of_mem _ hb)
    have hcA := hBA (Finset.mem_image_of_mem _ hc)
    have hne : g * b ≠ g * c := fun h => hbc (Nat.mul_left_cancel hg h)
    have hsup : (g * b + g * c).primeFactors ⊆ S :=
      Erdos126Anchors.sum_support_subset hbA hcA hne
    apply (Nat.primeFactors_mono _ (by
      have hpos := Nat.mul_pos hg (hB b hb).1
      omega : g * b + g * c ≠ 0)).trans hsup
    exact dvd_add (dvd_mul_right g b) (dvd_mul_right g c)
  have hgBound : g ≤ (H ^ r) ^ r := scale_le_of_primitive A S g (H ^ r)
    hg (pow_pos hH _) hA hsupport (fun x hx => (Nat.le_add_left _ _).trans (hquot x hx))
  intro x hx
  have hsmall : x / x.gcd g ≤ H ^ r := (Nat.le_add_right _ _).trans (hquot x hx)
  have hhg : x.gcd g ≤ g := Nat.le_of_dvd hg (Nat.gcd_dvd_right x g)
  calc
    x = x.gcd g * (x / x.gcd g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left x g)).symm
    _ ≤ g * H ^ r := Nat.mul_le_mul hhg hsmall
    _ ≤ (H ^ r) ^ r * H ^ r := Nat.mul_le_mul_right _ hgBound
    _ = H ^ (r * (r + 1)) := by rw [← pow_succ, ← pow_mul]

end Erdos126AffineAnchors

namespace Erdos126GlobalPolynomial

open Erdos126GcdEnergy Erdos126GcdAnchors Erdos126Normalization

lemma primitivePart_pos (B : Finset ℕ) (hpos : ∀ b ∈ B, 0 < b) :
    ∀ b ∈ primitivePart B, 0 < b := by
  intro b hb
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
  have hg : 0 < B.gcd id := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hd : B.gcd id ∣ c := Finset.gcd_dvd hc
    rw [hz, zero_dvd_iff] at hd
    have := hpos c hc
    omega
  exact Nat.div_pos (Nat.le_of_dvd (hpos c hc) (Finset.gcd_dvd hc)) hg

/-- An arbitrary sufficiently large subset, after its own gcd
normalization, controls the height of a primitive ambient clique. -/
lemma height_from_primitive_subset (A B : Finset ℕ)
    (hA : A.gcd id = 1) (hBA : B ⊆ A) (hpos : ∀ b ∈ B, 0 < b)
    (hcard : (sumProduct A).primeFactors.card + 2 ≤ B.card) :
    ∀ x ∈ A, x ≤ primitiveHeight B ^ ((sumProduct A).primeFactors.card *
      ((sumProduct A).primeFactors.card + 1)) := by
  let g := B.gcd id
  have hB2 : 2 ≤ B.card := by omega
  have hg : 0 < g := gcd_pos_of_two_le_card B hB2
  have hH : 0 < primitiveHeight B := primitiveHeight_pos B hB2
  have hscaled : (primitivePart B).image (fun b => g * b) ⊆ A := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
    have heq : g * (c / g) = c := Nat.mul_div_cancel' (Finset.gcd_dvd hc)
    rw [heq]
    exact hBA hc
  exact Erdos126AffineAnchors.primitive_height_from_scaled_anchors A (primitivePart B) g
    (primitiveHeight B) hg hH hA
    (fun b hb => ⟨primitivePart_pos B hpos b hb, primitivePart_le_height B b hb⟩)
    hscaled (by simpa only [primitivePart_card] using hcard)

/-- A sparse set of prime divisors forces a small total gcd-distance from
at least one operand. This is a row average of the matrix estimate. -/
lemma exists_small_distance_row (A : Finset ℕ) (H : ℕ) (hne : A.Nonempty)
    (hH : 0 < H) (hpos : ∀ a ∈ A, 0 < a) (hhi : ∀ a ∈ A, a ≤ H) :
    ∃ a ∈ A, (∑ b ∈ A, gcdDistance a b) ≤
      4 * ((sumProduct A).primeFactors.card : ℝ)^2 * Real.log (2 * H : ℕ) := by
  let S := (sumProduct A).primeFactors
  have hbound := gcd_distance_energy_bound A S H hH hpos hhi
    (fun _ hp => Nat.prime_of_mem_primeFactors hp)
    (fun _ ha _ hb hab => Erdos126Anchors.sum_support_subset ha hb hab)
  apply Finset.exists_le_of_sum_le hne
  have he : (∑ _a ∈ A, 4 * (S.card : ℝ)^2 * Real.log (2 * H : ℕ)) =
      4 * (S.card : ℝ)^2 * A.card * Real.log (2 * H : ℕ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [he]
  exact hbound

/-- Height-free polynomial bound for positive primitive sets. -/
theorem primitive_card_polynomial (A : Finset ℕ)
    (hpos : ∀ a ∈ A, 0 < a) (hprim : A.gcd id = 1) :
    A.card ≤ 64 * ((sumProduct A).primeFactors.card + 1)^5 := by
  classical
  let r := (sumProduct A).primeFactors.card
  let m := r + 2
  by_cases hsmall : A.card < 2 * m
  · change A.card ≤ 64 * (r + 1)^5
    have hp : r + 1 ≤ (r + 1)^5 := Nat.le_self_pow (by omega) _
    dsimp [m] at hsmall
    nlinarith
  have hn : 2 * m ≤ A.card := by omega
  have hn4 : 4 ≤ A.card := by dsimp [m] at hn; omega
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  let H := A.sup id
  have hhi : ∀ a ∈ A, a ≤ H := fun a ha => Finset.le_sup (f := id) ha
  have hH2 : 2 ≤ H := by
    by_contra h
    have hsub : A ⊆ {1} := by
      intro a ha
      have := hhi a ha
      have := hpos a ha
      simp only [Finset.mem_singleton]
      omega
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  have hH : 0 < H := by omega
  have hlogH : 0 < Real.log H := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
  have hlog2H : Real.log (2 * H : ℕ) ≤ 2 * Real.log H := by
    rw [Nat.cast_mul, Real.log_mul (by norm_num) (by exact_mod_cast hH.ne')]
    have hlog2 : Real.log 2 ≤ Real.log H := Real.log_le_log (by norm_num) (by exact_mod_cast hH2)
    norm_num only [Nat.cast_ofNat]
    linarith
  obtain ⟨a, ha, hrow⟩ := exists_small_distance_row A H hne hH hpos hhi
  obtain ⟨B, hBA, hBm, hBsum⟩ := exists_small_weight_subset A (gcdDistance a)
    (fun b hb => gcdDistance_nonneg (hpos a ha) (hpos b hb)) m (by dsimp [m]; omega) hn
  let C := insert a B
  have hCA : C ⊆ A := Finset.insert_subset ha hBA
  have haC : a ∈ C := Finset.mem_insert_self _ _
  have hCcard : r + 2 ≤ C.card := by
    have h := Finset.card_le_card (Finset.subset_insert a B)
    dsimp [C, m] at *
    omega
  have hCpos : ∀ c ∈ C, 0 < c := fun c hc => hpos c (hCA hc)
  have hsumC : (∑ c ∈ C, gcdDistance a c) = ∑ b ∈ B, gcdDistance a b := by
    by_cases haB : a ∈ B
    · simp [C, Finset.insert_eq_of_mem haB]
    · rw [show C = insert a B from rfl, Finset.sum_insert haB, gcdDistance_self, zero_add]
  have hlogC := log_primitiveHeight_le_sum_distance C a haC hCpos
  rw [hsumC] at hlogC
  have hClarge : 2 ≤ C.card := by omega
  have hHCpos : 0 < primitiveHeight C := primitiveHeight_pos C hClarge
  have hheight : H ≤ primitiveHeight C ^ (r * (r + 1)) := by
    apply Finset.sup_le
    exact height_from_primitive_subset A C hprim hCA hCpos hCcard
  have hheightlog : Real.log H ≤ (r * (r + 1) : ℕ) * Real.log (primitiveHeight C) := by
    have hh : (H : ℝ) ≤ (primitiveHeight C : ℝ) ^ (r * (r + 1)) := by exact_mod_cast hheight
    have h := Real.log_le_log (by exact_mod_cast hH) hh
    simpa only [Real.log_pow] using h
  have hnR : (0 : ℝ) < A.card := by exact_mod_cast (show 0 < A.card by omega)
  have hCsumR : (A.card : ℝ) * Real.log (primitiveHeight C) ≤
      4 * m * (∑ b ∈ A, gcdDistance a b) := by
    have hh := mul_le_mul_of_nonneg_left hlogC hnR.le
    nlinarith
  have hCsumR' : (A.card : ℝ) * Real.log (primitiveHeight C) ≤
      16 * m * (r : ℝ)^2 * Real.log (2 * H : ℕ) := by
    have hr : (∑ b ∈ A, gcdDistance a b) ≤ 4 * (r : ℝ)^2 * Real.log (2 * H : ℕ) := hrow
    have hh := mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ 4 * m)
    nlinarith
  have hcombine : (A.card : ℝ) * Real.log H ≤
      16 * m * (r : ℝ)^3 * (r + 1) * Real.log (2 * H : ℕ) := by
    have hh := mul_le_mul_of_nonneg_left hheightlog hnR.le
    have hh' := mul_le_mul_of_nonneg_left hCsumR'
      (by positivity : (0 : ℝ) ≤ (r : ℝ) * (r + 1))
    push_cast at hh
    nlinarith
  have hfinal : (A.card : ℝ) ≤ 32 * m * (r : ℝ)^3 * (r + 1) := by
    have hh := mul_le_mul_of_nonneg_left hlog2H
      (by positivity : (0 : ℝ) ≤ 16 * m * (r : ℝ)^3 * (r + 1))
    nlinarith
  have hnNat : A.card ≤ 32 * m * r^3 * (r + 1) := by exact_mod_cast hfinal
  change A.card ≤ 64 * (r + 1)^5
  apply hnNat.trans
  dsimp [m]
  have hpow : r^3 ≤ (r + 1)^3 := Nat.pow_le_pow_left (by omega) 3
  calc
    32 * (r + 2) * r^3 * (r + 1) ≤ 32 * (2 * (r + 1)) * (r + 1)^3 * (r + 1) := by gcongr; omega
    _ = 64 * (r + 1)^5 := by ring

end Erdos126GlobalPolynomial

namespace Erdos126GlobalPolynomial

open Erdos126Normalization Filter

lemma sum_support_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    (sumProduct A).primeFactors ⊆ (sumProduct B).primeFactors := by
  apply Nat.primeFactors_mono _ (sumProduct_ne_zero B)
  exact Finset.prod_dvd_prod_of_subset A.offDiag B.offDiag _ (Finset.offDiag_mono hAB)

/-- An unrestricted polynomial bound in the complete prime support of
all ordered off-diagonal sums. -/
theorem card_polynomial (A : Finset ℕ) :
    A.card ≤ 65 * ((sumProduct A).primeFactors.card + 1)^5 := by
  classical
  let B := A.erase 0
  have hABcard : A.card ≤ B.card + 1 := Erdos126AffineAnchors.card_le_erase_add_one A 0
  have hBpos : ∀ b ∈ B, 0 < b := by
    intro b hb
    have hne := (Finset.mem_erase.mp hb).1
    omega
  have hpone : 1 ≤ ((sumProduct A).primeFactors.card + 1)^5 := by
    exact Nat.one_le_pow _ _ (by omega)
  by_cases hsmall : B.card < 2
  · omega
  have hB2 : 2 ≤ B.card := by omega
  let C := primitivePart B
  have hCpos : ∀ c ∈ C, 0 < c := primitivePart_pos B hBpos
  have hCprim : C.gcd id = 1 := primitivePart_gcd_eq_one B hB2
  have hcount : (sumProduct C).primeFactors.card ≤ (sumProduct A).primeFactors.card :=
    (Finset.card_le_card (primitive_support_subset B)).trans
      (Finset.card_le_card (sum_support_mono (Finset.erase_subset 0 A)))
  have hb := primitive_card_polynomial C hCpos hCprim
  have hcard : C.card = B.card := primitivePart_card B
  have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right hcount 1) 5
  have hmul := Nat.mul_le_mul_left 64 hpow
  nlinarith

/-- Uniform superlogarithmic growth, now with no auxiliary hypotheses. -/
theorem uniform_superlog (K : ℝ) :
    ∃ N : ℕ, ∀ A : Finset ℕ, N ≤ A.card →
      K * Real.log A.card < ((sumProduct A).primeFactors.card : ℝ) := by
  let D : ℝ := 65 * (K + 1)^5
  have hlim : Tendsto (fun n : ℕ => D * Real.log (n : ℝ)^5 / n) atTop (nhds 0) := by
    have hbase : Tendsto (fun n : ℕ => Real.log (n : ℝ)^5 / n) atTop (nhds 0) := by
      simpa [Function.comp_def] using
        (Real.tendsto_pow_log_div_mul_add_atTop 1 0 5 (by norm_num)).comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [mul_div_assoc] using hbase.const_mul D
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop 1)
  have hevent : ∀ᶠ n : ℕ in atTop,
      0 < n ∧ 1 ≤ Real.log (n : ℝ) ∧ D * Real.log (n : ℝ)^5 < n := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), hlog,
      hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with n hn hl hs
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact ⟨by omega, hl, by simpa using (div_lt_iff₀ hnpos).mp hs⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨N, ?_⟩
  intro A hlarge
  obtain ⟨hnpos, hlog, hstrict⟩ := hN A.card hlarge
  have hbound : (A.card : ℝ) ≤ 65 * (((sumProduct A).primeFactors.card : ℝ) + 1)^5 := by
    exact_mod_cast card_polynomial A
  by_contra h
  have hr : ((sumProduct A).primeFactors.card : ℝ) ≤ K * Real.log A.card := le_of_not_gt h
  have hr1 : ((sumProduct A).primeFactors.card : ℝ) + 1 ≤ (K + 1) * Real.log A.card := by
    nlinarith
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
    ((sumProduct A).primeFactors.card : ℝ) + 1) hr1 5
  have heq : 65 * ((K + 1) * Real.log A.card)^5 = D * Real.log A.card^5 := by
    dsimp [D]
    ring
  have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 65)
  rw [heq] at hm
  linarith

end Erdos126GlobalPolynomial

open Filter
namespace Erdos126

def IsMaximalAddFactorsCard (f : ℕ → ℕ) : Prop := ∀ n,
    IsGreatest
      { m | ∀ (A : Finset ℕ), A.card = n →
        m ≤ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card}
      (f n)

/--
Let $f(n)$ be maximal such that if $A\subseteq\mathbb{N}$ has $|A| = n$ then
$\prod_{a\neq b\in A}(a + b)$ has at least $f(n)$ distinct prime factors.
Is it true that $\frac{f(n)}{\log n} \to\infty$?
-/
theorem erdos_126 : ∀ (f : ℕ → ℕ), IsMaximalAddFactorsCard f →
    Tendsto (fun n => f n / Real.log n) atTop atTop := by
  intro f hf
  apply tendsto_atTop.mpr
  intro K
  obtain ⟨N, hN⟩ := Erdos126GlobalPolynomial.uniform_superlog K
  filter_upwards [eventually_ge_atTop (max N 2)] with n hn
  have hnN : N ≤ n := (le_max_left N 2).trans hn
  have hn2 : 2 ≤ n := (le_max_right N 2).trans hn
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hmem : (⌈K * Real.log n⌉₊ : ℕ) ∈
      { m | ∀ (A : Finset ℕ), A.card = n →
        m ≤ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card} := by
    intro A hcard
    apply Nat.ceil_le.mpr
    have hh := hN A (by omega)
    simpa only [hcard] using hh.le
  have hle : (⌈K * Real.log n⌉₊ : ℕ) ≤ f n := (hf n).2 hmem
  have hceil : K * Real.log n ≤ (f n : ℝ) :=
    (Nat.le_ceil (K * Real.log n)).trans (by exact_mod_cast hle)
  exact (le_div_iff₀ hlog).mpr hceil

end Erdos126
