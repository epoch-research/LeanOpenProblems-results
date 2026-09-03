import FormalConjecturesUtil

/-!
# Erdős Problem 975

*References:*
 - [erdosproblems.com/975](https://www.erdosproblems.com/975)
 - [Va39] van der Corput, J. G., Une in\'egalit\'e{} relative au nombre des diviseurs. Nederl. Akad. Wetensch., Proc. (1939), 547--553.
 - [Er52b] Erd\"os, P., On the sum {$\sum^x_{k=1} d(f(k))$}. J. London Math. Soc. (1952), 7--15.
 - [Ho63] Hooley, Christopher, On the number of divisors of a quadratic polynomial. Acta Math. (1963), 97--114.
 - [Mc95] McKee, James, On the average number of divisors of quadratic polynomials. Math. Proc. Cambridge Philos. Soc. (1995), 389--392.
 - [Mc97] McKee, James, A note on the number of divisors of quadratic polynomials. (1997), 275--281.
 - [Mc99] McKee, James, The average number of divisors of an irreducible quadratic polynomial. Math. Proc. Cambridge Philos. Soc. (1999), 17--22.
 - [T] T. Tao, Erdos' divisor bound, https://terrytao.wordpress.com/2011/07/23/erdos-divisor-bound/
-/

open Filter Real Polynomial
open scoped ArithmeticFunction.sigma Topology

namespace Erdos975

/-- Sum of $\tau(f(n))$ from `0` to `⌊x⌋` for a polynomial $f \in \mathbb{Z}[X]$.

Here $\tau$ is the divisor counting function, which is `σ 0` in mathlib.
Also, for simplicity, we use `Nat.floor` to convert rational values to natural numbers, instead of
dealing with negative values. -/
noncomputable def Erdos975Sum (f : ℤ[X]) (x : ℝ) : ℝ :=
  ∑ n ≤ ⌊x⌋₊, σ 0 ⌊f.eval ↑n⌋₊

private lemma sum_sigma_Iic (N : ℕ) :
    ∑ n ∈ Finset.Iic N, σ 0 n = ∑ n ∈ Finset.Ioc 0 N, σ 0 n := by
  have h := Finset.sum_Ioc_add_eq_sum_Icc (f := fun n : ℕ => σ 0 n) (Nat.zero_le N)
  simpa using h.symm

lemma Erdos975Sum_X_eq (x : ℝ) :
    Erdos975Sum X x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (⌊x / n⌋₊ : ℝ) := by
  simp only [Erdos975Sum, eval_X, Nat.floor_natCast]
  rw [← Nat.cast_sum, sum_sigma_Iic, ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div,
    Nat.cast_sum]
  simp only [Nat.floor_div_natCast]

private lemma harmonic_sum (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, (n : ℝ)⁻¹ = (harmonic N : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [← Finset.Icc_add_one_left_eq_Ioc]
  rfl

lemma Erdos975Sum_X_bounds {x : ℝ} (hx : 1 ≤ x) :
    x * log x - x ≤ Erdos975Sum X x ∧ Erdos975Sum X x ≤ x * log x + x := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hupper : Erdos975Sum X x ≤ x * (harmonic ⌊x⌋₊ : ℝ) := by
    rw [Erdos975Sum_X_eq, ← harmonic_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    simpa only [div_eq_mul_inv] using Nat.floor_le (div_nonneg hx0 (Nat.cast_nonneg n))
  have hlower : x * (harmonic ⌊x⌋₊ : ℝ) - ⌊x⌋₊ ≤ Erdos975Sum X x := by
    rw [Erdos975Sum_X_eq, ← harmonic_sum, Finset.mul_sum]
    have h := Finset.sum_le_sum (s := Finset.Ioc 0 ⌊x⌋₊)
      (f := fun n : ℕ => x / n - 1) (g := fun n : ℕ => (⌊x / n⌋₊ : ℝ))
      (fun n _ => (Nat.sub_one_lt_floor (x / n)).le)
    simpa [Finset.sum_sub_distrib, div_eq_mul_inv] using h
  have hlog := log_le_harmonic_floor x hx0
  have hlog' := harmonic_floor_le_one_add_log x hx
  have hfloor := Nat.floor_le hx0
  constructor
  · nlinarith
  · nlinarith

lemma Erdos975Sum_X_tendsto :
    Tendsto (fun x : ℝ => Erdos975Sum X x / (x * log x)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun x : ℝ => (log x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hlow : Tendsto (fun x : ℝ => 1 - (log x)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hinv
  have hupp : Tendsto (fun x : ℝ => 1 + (log x)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hl0 : 0 < log x := Real.log_pos hx
    rw [le_div_iff₀ (mul_pos hx0 hl0)]
    convert (Erdos975Sum_X_bounds hx.le).1 using 1
    field_simp
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hl0 : 0 < log x := Real.log_pos hx
    rw [div_le_iff₀ (mul_pos hx0 hl0)]
    convert (Erdos975Sum_X_bounds hx.le).2 using 1
    field_simp

lemma real_limit_iff_nat_limit (f : ℤ[X]) (c : ℝ) :
    Tendsto (fun x : ℝ => Erdos975Sum f x / (x * log x)) atTop (𝓝 c) ↔
    Tendsto (fun n : ℕ => Erdos975Sum f n / ((n : ℝ) * log n)) atTop (𝓝 c) := by
  constructor
  · intro h
    exact h.comp tendsto_natCast_atTop_atTop
  · intro h
    have hf : Asymptotics.IsEquivalent atTop (fun x : ℝ => (⌊x⌋₊ : ℝ)) id :=
      Asymptotics.isEquivalent_nat_floor
    have hg := hf.mul (hf.log tendsto_id)
    have hs : Asymptotics.IsEquivalent atTop
        (fun x : ℝ => Erdos975Sum f x / ((⌊x⌋₊ : ℝ) * log (⌊x⌋₊ : ℝ)))
        (fun x : ℝ => Erdos975Sum f x / (x * log x)) :=
      Asymptotics.IsEquivalent.refl.div hg
    apply hs.tendsto_nhds_iff.mp
    simpa [Function.comp_def, Erdos975Sum] using h.comp (tendsto_nat_floor_atTop (α := ℝ))

private noncomputable def partialSum (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), a i

private lemma partialSum_shift (a : ℕ → ℝ) (n k : ℕ) :
    partialSum a (n + k) = partialSum (fun i => a (i + k)) n +
      ∑ i ∈ Finset.range k, a i := by
  simp only [partialSum]
  rw [show n + k + 1 = k + (n + 1) by omega, Finset.sum_range_add]
  simp [add_comm]

private lemma partialSum_shift_limit_iff (a : ℕ → ℝ) (k : ℕ) (c : ℝ) :
    Tendsto (fun n : ℕ => partialSum (fun i => a (i + k)) n / ((n : ℝ) * log n))
      atTop (𝓝 c) ↔
    Tendsto (fun n : ℕ => partialSum a n / ((n : ℝ) * log n)) atTop (𝓝 c) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have he : Asymptotics.IsEquivalent atTop (fun n : ℕ => ((n + k : ℕ) : ℝ))
      (fun n : ℕ => (n : ℝ)) := by
    simpa only [Nat.cast_add] using
      (Asymptotics.IsEquivalent.refl.add_isLittleO
        ((Asymptotics.isLittleO_const_id_atTop (k : ℝ)).comp_tendsto ht))
  have hd := he.mul (he.log ht)
  have hq : Asymptotics.IsEquivalent atTop
      (fun n : ℕ => partialSum a (n + k) / ((n + k : ℕ) * log (n + k : ℕ)))
      (fun n : ℕ => partialSum a (n + k) / ((n : ℝ) * log n)) :=
    Asymptotics.IsEquivalent.refl.div hd
  have hden : Tendsto (fun n : ℕ => (n : ℝ) * log n) atTop atTop :=
    ht.atTop_mul_atTop₀ (Real.tendsto_log_atTop.comp ht)
  have hc : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range k, a i) / ((n : ℝ) * log n))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hden
  constructor
  · intro h
    apply (tendsto_add_atTop_iff_nat k).mp
    apply hq.tendsto_nhds_iff.mpr
    simpa only [partialSum_shift, add_div, add_zero] using h.add hc
  · intro h
    have hh := hq.tendsto_nhds_iff.mp ((tendsto_add_atTop_iff_nat k).mpr h)
    have hsub := hh.sub hc
    simpa only [partialSum_shift, add_div, add_sub_cancel_right, sub_zero] using hsub

lemma nat_shift_limit_iff (f : ℤ[X]) (k : ℕ) (c : ℝ) :
    Tendsto (fun x : ℝ => Erdos975Sum (f.comp (X + C (k : ℤ))) x / (x * log x))
      atTop (𝓝 c) ↔
    Tendsto (fun x : ℝ => Erdos975Sum f x / (x * log x)) atTop (𝓝 c) := by
  rw [real_limit_iff_nat_limit, real_limit_iff_nat_limit]
  simpa [partialSum, Erdos975Sum, Nat.range_succ_eq_Iic, eval_comp, Nat.cast_add]
    using partialSum_shift_limit_iff (fun i : ℕ => (σ 0 ⌊f.eval (i : ℤ)⌋₊ : ℝ)) k c

lemma Erdos975Sum_X_add_C_nat_tendsto (k : ℕ) :
    Tendsto (fun x : ℝ => Erdos975Sum (X + C (k : ℤ)) x / (x * log x)) atTop (𝓝 1) := by
  simpa using (nat_shift_limit_iff X k 1).mpr Erdos975Sum_X_tendsto

lemma Erdos975Sum_X_sub_C_nat_tendsto (k : ℕ) :
    Tendsto (fun x : ℝ => Erdos975Sum (X - C (k : ℤ)) x / (x * log x)) atTop (𝓝 1) := by
  apply (nat_shift_limit_iff (X - C (k : ℤ)) k 1).mp
  simpa using Erdos975Sum_X_tendsto

lemma Erdos975Sum_X_add_C_tendsto (b : ℤ) :
    Tendsto (fun x : ℝ => Erdos975Sum (X + C b) x / (x * log x)) atTop (𝓝 1) := by
  cases b with
  | ofNat k => exact Erdos975Sum_X_add_C_nat_tendsto k
  | negSucc k =>
    simpa [Int.negSucc_eq, sub_eq_add_neg] using Erdos975Sum_X_sub_C_nat_tendsto (k + 1)

lemma Erdos975Sum_monic_linear_tendsto (f : ℤ[X]) (hm : f.Monic)
    (hd : f.natDegree = 1) :
    Tendsto (fun x : ℝ => Erdos975Sum f x / (x * log x)) atTop (𝓝 1) := by
  rw [hm.eq_X_add_C hd]
  exact Erdos975Sum_X_add_C_tendsto _


namespace Aux

/- Elementary finite hyperbola bounds. -/
open Finset

lemma hyperbola_card_bounds (T : Finset (ℕ × ℕ)) (Y : ℕ)
    (hpos : ∀ p ∈ T, 0 < p.1 ∧ 0 < p.2)
    (hsize : ∀ p ∈ T, p.1 * p.2 ≤ Y ^ 2)
    (hswap : ∀ p, p.swap ∈ T ↔ p ∈ T) :
    T.card ≤ 2 * (T.filter (fun p => p.1 ≤ Y)).card ∧
    2 * (T.filter (fun p => p.1 ≤ Y)).card ≤ T.card + Y ^ 2 := by
  let A := T.filter (fun p => p.1 ≤ Y)
  let B := T.filter (fun p => p.2 ≤ Y)
  have hunion : A ∪ B = T := by
    ext p
    simp only [A, B, mem_union, mem_filter]
    constructor
    · tauto
    · intro hp
      have hm := hsize p hp
      have hh : p.1 ≤ Y ∨ p.2 ≤ Y := by
        by_contra! hn
        have hh : (Y + 1) * (Y + 1) ≤ p.1 * p.2 := Nat.mul_le_mul hn.1 hn.2
        nlinarith
      tauto
  have hcard : A.card = B.card := by
    apply card_nbij' Prod.swap Prod.swap
    · intro p hp
      simp only [A] at hp
      simpa [B, hswap] using hp
    · intro p hp
      simp only [B] at hp
      simpa [A, hswap] using hp
    · intro p hp
      simp
    · intro p hp
      simp
  have hinter : A ∩ B ⊆ (Icc 1 Y) ×ˢ (Icc 1 Y) := by
    intro p hp
    simp only [A, B, mem_inter, mem_filter] at hp
    have hp0 := hpos p hp.1.1
    simp only [mem_product, mem_Icc]
    omega
  have hi : (A ∩ B).card ≤ Y ^ 2 := by
    have hh := card_le_card hinter
    simpa [card_product, Nat.card_Icc, pow_two] using hh
  have h := card_union_add_card_inter A B
  rw [hunion, ← hcard] at h
  constructor <;> dsimp [A] at * <;> omega


/- Harmonic averages of periodic sequences. -/
open Finset Filter Real
open scoped Topology
namespace PeriodicHarmonic

lemma periodic_zero_sum_bounded {g : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (hg : Function.Periodic g q) (hz : ∑ i ∈ range q, g i = 0) :
    ∀ n, ‖∑ i ∈ range n, g i‖ ≤ ∑ i ∈ range q, ‖g i‖ := by
  have hshift (k r : ℕ) : ∑ i ∈ range r, g (q * k + i) = ∑ i ∈ range r, g i := by
    apply sum_congr rfl
    intro i hi
    simpa [mul_comm, add_comm] using hg.nat_mul k i
  have hblock (k : ℕ) : ∑ i ∈ range (q * k), g i = 0 := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, sum_range_add, ih, hshift, hz, add_zero]
  intro n
  have heq : ∑ i ∈ range n, g i = ∑ i ∈ range (n % q), g i := by
    conv_lhs => rw [← Nat.div_add_mod n q]
    rw [sum_range_add, hblock, hshift, zero_add]
  rw [heq]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum_of_subset_of_nonneg (range_mono (Nat.mod_lt n hq).le)
  intro i hi hnot
  exact norm_nonneg _

lemma periodic_harmonic_remainder_converges (a : ℕ → ℝ) {q : ℕ}
    (hq : 0 < q) (ha : Function.Periodic a q) :
    ∃ c : ℝ, Tendsto (fun n : ℕ =>
      (∑ i ∈ range n, a (i + 1) / (i + 1)) -
        ((∑ i ∈ range q, a (i + 1)) / q) * (harmonic n : ℝ)) atTop (𝓝 c) := by
  let A : ℝ := (∑ i ∈ range q, a (i + 1)) / q
  let g : ℕ → ℝ := fun i => a (i + 1) - A
  have hg : Function.Periodic g q := by
    intro n
    dsimp [g]
    congr 1
    simpa [add_assoc, add_comm, add_left_comm] using ha (n + 1)
  have hz : ∑ i ∈ range q, g i = 0 := by
    simp [g, A, sum_sub_distrib, mul_div_cancel₀, hq.ne']
  have hb := periodic_zero_sum_bounded hq hg hz
  have hw : Antitone (fun i : ℕ => ((i : ℝ) + 1)⁻¹) := by
    intro m n hmn
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hw0 : Tendsto (fun i : ℕ => ((i : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete
    (hw.cauchySeq_series_mul_of_tendsto_zero_of_bounded hw0 hb)
  refine ⟨c, ?_⟩
  convert hc using 1
  ext n
  simp only [smul_eq_mul, g, mul_sub, sum_sub_distrib, mul_comm, ← sum_mul,
    harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_one, Rat.cast_natCast, Nat.cast_add, Nat.cast_one,
    div_eq_mul_inv, A]

lemma periodic_harmonic_limit (a : ℕ → ℝ) {q : ℕ}
    (hq : 0 < q) (ha : Function.Periodic a q) :
    Tendsto (fun n : ℕ => (∑ i ∈ range n, a (i + 1) / (i + 1)) / log n)
      atTop (𝓝 ((∑ i ∈ range q, a (i + 1)) / q)) := by
  let A : ℝ := (∑ i ∈ range q, a (i + 1)) / q
  obtain ⟨c, hc⟩ := periodic_harmonic_remainder_converges a hq ha
  have hres : Tendsto (fun n : ℕ =>
      (∑ i ∈ range n, a (i + 1) / (i + 1)) - A * log n)
      atTop (𝓝 (c + A * Real.eulerMascheroniConstant)) := by
    convert hc.add (Real.tendsto_harmonic_sub_log.const_mul A) using 1
    ext n
    dsimp [A]
    ring
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim := (hres.div_atTop hlog).add_const A
  simp only [zero_add] at hlim
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hln : log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  field_simp
  ring

lemma coprime_harmonic_limit {q : ℕ} (hq : 0 < q) :
    Tendsto (fun n : ℕ =>
      (∑ i ∈ Ioc 0 n, if i.Coprime q then (i : ℝ)⁻¹ else 0) / log n)
      atTop (𝓝 ((q.totient : ℝ) / q)) := by
  have ha : Function.Periodic (fun i : ℕ => if i.Coprime q then (1 : ℝ) else 0) q := by
    intro n
    simp only [Nat.coprime_add_self_left]
  have hmean : (∑ i ∈ range q, if (i + 1).Coprime q then (1 : ℝ) else 0) = q.totient := by
    calc
      _ = ∑ i ∈ Ico 1 (q + 1), if q.Coprime i then (1 : ℝ) else 0 := by
        rw [sum_Ico_eq_sum_range]
        simp [Nat.coprime_comm, add_comm]
      _ = _ := by
        rw [sum_boole]
        norm_cast
        simpa [add_comm] using Nat.filter_coprime_Ico_eq_totient q 1
  have hh := periodic_harmonic_limit _ hq ha
  rw [hmean] at hh
  convert hh using 1
  ext n
  have hset : Ioc 0 n = Ico 1 (n + 1) := by
    ext i
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hset, sum_Ico_eq_sum_range]
  simp [add_comm, ite_div, one_div]

end PeriodicHarmonic

/- Counting divisors in arithmetic progressions. -/
open Finset Filter Real
open scoped ArithmeticFunction.sigma Topology
namespace LinearCount

lemma sigma0_eq_card_antidiagonal (n : ℕ) : σ 0 n = n.divisorsAntidiagonal.card := by
  simpa [ArithmeticFunction.sigma_zero_apply] using
    (Nat.sum_divisorsAntidiagonal (fun _ _ => (1 : ℕ)) (n := n)).symm

lemma sum_weight_sigma0 (w : ℕ → ℕ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, w n * σ 0 n =
      ∑ p ∈ (Ioc 0 N ×ˢ Ioc 0 N).filter (fun p => p.1 * p.2 ≤ N), w (p.1 * p.2) := by
  simp only [sigma0_eq_card_antidiagonal]
  trans ∑ n ∈ Ioc 0 N, ∑ p ∈ (Ioc 0 N ×ˢ Ioc 0 N).filter
    (fun p => p.1 * p.2 = n), w n
  · apply sum_congr rfl
    intro n hn
    have hn' := mem_Ioc.mp hn
    rw [← Nat.divisorsAntidiagonal_eq_prod_filter_of_le hn'.1.ne' hn'.2]
    simp [mul_comm]
  · simp_rw [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    simp only [mem_product, mem_Ioc] at hp
    have hpos : 0 < p.1 * p.2 := Nat.mul_pos hp.1.1 hp.2.1
    by_cases hle : p.1 * p.2 ≤ N
    · rw [if_pos hle]
      simp [hpos, hle]
    · rw [if_neg hle]
      apply sum_eq_zero
      intro n hn
      have hn' := mem_Ioc.mp hn
      rw [if_neg (by omega)]

lemma sum_AP_sigma0_eq_card (q b N : ℕ) :
    ∑ n ∈ Ioc 0 N, (if n % q = b % q then σ 0 n else 0) =
      ((Ioc 0 N ×ˢ Ioc 0 N).filter
        (fun p => p.1 * p.2 ≤ N ∧ (p.1 * p.2) % q = b % q)).card := by
  have hh := sum_weight_sigma0 (fun n => if n % q = b % q then 1 else 0) N
  simpa [ite_mul, sum_boole, filter_filter] using hh

lemma mul_mod_eq_iff {q b : ℕ} (hq : 0 < q) (hb : b.Coprime q) (d e : ℕ) :
    (d * e) % q = b % q ↔ d.Coprime q ∧
      e ≡ (((d : ZMod q)⁻¹ * (b : ZMod q)).val) [MOD q] := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_mul,
    ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  constructor
  · intro h
    have hu : IsUnit (d : ZMod q) :=
      isUnit_of_mul_isUnit_left (h.symm ▸ (ZMod.isUnit_iff_coprime b q).mpr hb)
    refine ⟨(ZMod.isUnit_iff_coprime d q).mp hu, ?_⟩
    calc
      (e : ZMod q) = (d : ZMod q)⁻¹ * ((d : ZMod q) * e) := by
        rw [← mul_assoc, ZMod.inv_mul_of_unit _ hu, one_mul]
      _ = _ := congrArg ((d : ZMod q)⁻¹ * ·) h
  · rintro ⟨hd, he⟩
    rw [he, ← mul_assoc, ZMod.coe_mul_inv_eq_one d hd, one_mul]

lemma residue_count_bounds {q : ℕ} (hq : 0 < q) (K r : ℕ) :
    (K : ℝ) / q - 2 ≤ ({e ∈ Ioc 0 K | e ≡ r [MOD q]}.card : ℝ) ∧
    ({e ∈ Ioc 0 K | e ≡ r [MOD q]}.card : ℝ) ≤ (K : ℝ) / q + 2 := by
  let C := {e ∈ Ioc 0 K | e ≡ r [MOD q]}.card
  have hc : C + (if 0 ≡ r [MOD q] then 1 else 0) =
      (K + 1) / q + (if r % q < (K + 1) % q then 1 else 0) := by
    rw [← Nat.count_modEq_card (K + 1) hq r]
    simpa [C, sum_boole, Nat.count_eq_card_filter_range, Nat.range_succ_eq_Iic]
      using sum_Ioc_add_eq_sum_Icc (f := fun e : ℕ => if e ≡ r [MOD q] then (1 : ℕ) else 0)
        (Nat.zero_le K)
  have hcu : C ≤ (K + 1) / q + 1 := by split_ifs at hc <;> omega
  have hcl : (K + 1) / q ≤ C + 1 := by split_ifs at hc <;> omega
  have hcuR : (C : ℝ) ≤ ((K + 1) / q : ℕ) + 1 := by exact_mod_cast hcu
  have hclR : (((K + 1) / q : ℕ) : ℝ) ≤ C + 1 := by exact_mod_cast hcl
  have hfu := Nat.cast_div_le (α := ℝ) (m := K + 1) (n := q)
  have hfl := Nat.sub_one_lt_floor (((K + 1 : ℕ) : ℝ) / q)
  rw [Nat.floor_div_natCast, Nat.floor_natCast] at hfl
  simp only [Nat.cast_add, Nat.cast_one, add_div] at hfu hfl
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hi : (1 : ℝ) / q ≤ 1 := (div_le_one (by positivity)).mpr hqR
  have hi0 : (0 : ℝ) ≤ 1 / q := by positivity
  change (K : ℝ) / q - 2 ≤ (C : ℝ) ∧ (C : ℝ) ≤ (K : ℝ) / q + 2
  constructor <;> linarith

lemma mul_residue_count_error {q b : ℕ} (hq : 0 < q) (hb : b.Coprime q)
    (N d : ℕ) :
    |({e ∈ Ioc 0 (N / d) | (d * e) % q = b % q}.card : ℝ) -
      (if d.Coprime q then (N : ℝ) / (q * d) else 0)| ≤ 3 := by
  by_cases hd : d.Coprime q
  · have hset : {e ∈ Ioc 0 (N / d) | (d * e) % q = b % q} =
        {e ∈ Ioc 0 (N / d) | e ≡ (((d : ZMod q)⁻¹ * b).val) [MOD q]} := by
      ext e
      simp only [mem_filter]
      rw [mul_mod_eq_iff hq hb]
      constructor
      · rintro ⟨he, hc, hm⟩
        exact ⟨he, hm⟩
      · rintro ⟨he, hm⟩
        exact ⟨he, hd, hm⟩
    rw [hset, if_pos hd, abs_le]
    have hc := residue_count_bounds hq (N / d) (((d : ZMod q)⁻¹ * b).val)
    have hku := Nat.cast_div_le (α := ℝ) (m := N) (n := d)
    have hkl := Nat.sub_one_lt_floor ((N : ℝ) / d)
    rw [Nat.floor_div_natCast, Nat.floor_natCast] at hkl
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hku' := div_le_div_of_nonneg_right hku hqR.le
    have hkl' := div_lt_div_of_pos_right hkl hqR
    simp only [sub_div, div_div] at hku' hkl'
    have hi : (1 : ℝ) / q ≤ 1 := (div_le_one hqR).mpr (by exact_mod_cast hq)
    rw [mul_comm (d : ℝ) (q : ℝ)] at hku' hkl'
    constructor <;> linarith [hc.1, hc.2]
  · simp [mul_mod_eq_iff hq hb, hd]

lemma AP_strip_card (q b N Y : ℕ) (hY : Y ≤ N) :
    (((Ioc 0 N ×ˢ Ioc 0 N).filter
      (fun p => p.1 * p.2 ≤ N ∧ (p.1 * p.2) % q = b % q)).filter
      (fun p => p.1 ≤ Y)).card =
      ∑ d ∈ Ioc 0 Y, {e ∈ Ioc 0 (N / d) | (d * e) % q = b % q}.card := by
  rw [filter_filter, card_filter, sum_product]
  trans ∑ d ∈ Ioc 0 N, if d ≤ Y then
    {e ∈ Ioc 0 (N / d) | (d * e) % q = b % q}.card else 0
  · apply sum_congr rfl
    intro d hd
    have hd0 : 0 < d := (mem_Ioc.mp hd).1
    by_cases hdY : d ≤ Y
    · simp only [hdY, and_true, if_pos]
      rw [← card_filter]
      congr 1
      ext e
      simp only [mem_filter, mem_Ioc]
      have hdiv := Nat.div_le_self N d
      have hh : d * e ≤ N ↔ e ≤ N / d := by
        rw [Nat.le_div_iff_mul_le hd0, mul_comm]
      rw [hh]
      omega
    · simp [hdY]
  · rw [← sum_filter]
    congr 1
    ext d
    simp only [mem_filter, mem_Ioc]
    omega

lemma AP_strip_error {q b : ℕ} (hq : 0 < q) (hb : b.Coprime q)
    (N Y : ℕ) (hY : Y ≤ N) :
    |((((Ioc 0 N ×ˢ Ioc 0 N).filter
      (fun p => p.1 * p.2 ≤ N ∧ (p.1 * p.2) % q = b % q)).filter
      (fun p => p.1 ≤ Y)).card : ℝ) -
      ((N : ℝ) / q) * ∑ d ∈ Ioc 0 Y, if d.Coprime q then (d : ℝ)⁻¹ else 0| ≤ 3 * Y := by
  rw [AP_strip_card q b N Y hY, Nat.cast_sum]
  have hh : |∑ d ∈ Ioc 0 Y,
      (({e ∈ Ioc 0 (N / d) | (d * e) % q = b % q}.card : ℝ) -
        (if d.Coprime q then (N : ℝ) / (q * d) else 0))| ≤ 3 * Y := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _d ∈ Ioc 0 Y, (3 : ℝ) := sum_le_sum (fun d _ => mul_residue_count_error hq hb N d)
      _ = _ := by simp [mul_comm]
  convert hh using 1
  rw [sum_sub_distrib, mul_sum]
  congr 2
  apply sum_congr rfl
  intro d hd
  simp only [mul_ite, mul_zero, div_eq_mul_inv, mul_inv_rev]
  split_ifs <;> ring

end LinearCount

namespace LinearCount

noncomputable def APSum (q b N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, if n % q = b % q then (σ 0 n : ℝ) else 0

lemma AP_main_error {q b : ℕ} (hq : 0 < q) (hb : b.Coprime q)
    {N : ℕ} (hN : 2 ≤ N) :
    |APSum q b N - 2 * ((N : ℝ) / q) *
      ∑ d ∈ Ioc 0 (N.sqrt + 1), if d.Coprime q then (d : ℝ)⁻¹ else 0| ≤ 10 * N := by
  let Y := N.sqrt + 1
  let T := (Ioc 0 N ×ˢ Ioc 0 N).filter
    (fun p => p.1 * p.2 ≤ N ∧ (p.1 * p.2) % q = b % q)
  have hY : Y ≤ N := Nat.sqrt_lt_self (by omega)
  have hNY : N ≤ Y ^ 2 := (Nat.lt_succ_sqrt' N).le
  have hY2 : Y ^ 2 ≤ 4 * N := by
    have hs := Nat.sqrt_le' N
    have hs0 : 1 ≤ N.sqrt := Nat.sqrt_pos.mpr (by omega)
    dsimp [Y]
    nlinarith [sq_nonneg (N.sqrt - 1 : ℤ)]
  have hcount : (T.card : ℝ) = APSum q b N := by
    rw [APSum, ← sum_AP_sigma0_eq_card q b N]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  have hh := hyperbola_card_bounds T Y
    (by intro p hp; simp only [T, mem_filter, mem_product, mem_Ioc] at hp; omega)
    (by intro p hp; exact (mem_filter.mp hp).2.1.trans hNY)
    (by intro p; simp [T, mul_comm, and_left_comm, and_comm])
  have hstrip := AP_strip_error hq hb N Y hY
  change |((T.filter (fun p => p.1 ≤ Y)).card : ℝ) - _| ≤ _ at hstrip
  have hh1 : (T.card : ℝ) ≤ 2 * (T.filter (fun p => p.1 ≤ Y)).card := by
    exact_mod_cast hh.1
  have hh2 : 2 * ((T.filter (fun p => p.1 ≤ Y)).card : ℝ) ≤ T.card + (Y : ℝ) ^ 2 := by
    exact_mod_cast hh.2
  have hY2R : (Y : ℝ) ^ 2 ≤ 4 * N := by exact_mod_cast hY2
  have hYR : (Y : ℝ) ≤ N := by exact_mod_cast hY
  rw [abs_le] at hstrip ⊢
  rw [← hcount]
  change -(10 * (N : ℝ)) ≤ (T.card : ℝ) - 2 * ((N : ℝ) / q) *
      (∑ d ∈ Ioc 0 Y, if d.Coprime q then (d : ℝ)⁻¹ else 0) ∧ _
  constructor <;> nlinarith [hstrip.1, hstrip.2]

lemma sqrt_cutoff_tendsto : Tendsto (fun n : ℕ => n.sqrt + 1) atTop atTop := by
  have hs : Tendsto Nat.sqrt atTop atTop :=
    (show Monotone Nat.sqrt from fun _ _ h => Nat.sqrt_le_sqrt h).tendsto_atTop_atTop
      (fun n => ⟨n * n, by simp⟩)
  exact (tendsto_add_atTop_nat 1).comp hs

lemma sqrt_cutoff_log_limit :
    Tendsto (fun n : ℕ => log (n.sqrt + 1 : ℕ) / log n) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun n : ℕ => (log 4 / 2) / log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hu : Tendsto (fun n : ℕ => (1 / 2 : ℝ) + (log 4 / 2) / log n)
      atTop (𝓝 (1 / 2 : ℝ)) := by simpa using tendsto_const_nhds.add hz
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hln : 0 < log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hb : (n : ℝ) ≤ ((n.sqrt + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast (Nat.lt_succ_sqrt' n).le
    have hh := Real.log_le_log hn0 hb
    rw [Real.log_pow] at hh
    rw [le_div_iff₀ hln]
    norm_num at hh ⊢
    linarith
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hln : 0 < log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hb : (n.sqrt + 1) ^ 2 ≤ 4 * n := by
      have hs := Nat.sqrt_le' n
      have hs0 : 1 ≤ n.sqrt := Nat.sqrt_pos.mpr (by omega)
      nlinarith [sq_nonneg (n.sqrt - 1 : ℤ)]
    have hbR : (((n.sqrt + 1 : ℕ) : ℝ) ^ 2) ≤ 4 * n := by exact_mod_cast hb
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < ((n.sqrt + 1 : ℕ) : ℝ) ^ 2) hbR
    rw [Real.log_pow, Real.log_mul (by norm_num) hn0.ne'] at hh
    rw [div_le_iff₀ hln]
    have heq : ((1 / 2 : ℝ) + (log 4 / 2) / log n) * log n = (log n + log 4) / 2 := by
      field_simp
    rw [heq]
    norm_num at hh ⊢
    linarith

lemma coprime_harmonic_sqrt_limit {q : ℕ} (hq : 0 < q) :
    Tendsto (fun n : ℕ =>
      (∑ d ∈ Ioc 0 (n.sqrt + 1), if d.Coprime q then (d : ℝ)⁻¹ else 0) / log n)
      atTop (𝓝 ((q.totient : ℝ) / (2 * q))) := by
  have hh := ((PeriodicHarmonic.coprime_harmonic_limit hq).comp sqrt_cutoff_tendsto).mul
    sqrt_cutoff_log_limit
  have heq : (q.totient : ℝ) / q * (1 / 2) = (q.totient : ℝ) / (2 * q) := by ring
  rw [heq] at hh
  apply Filter.Tendsto.congr' _ hh
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hs : 1 < n.sqrt + 1 := by have := Nat.sqrt_pos.mpr (show 0 < n by omega); omega
  have hls : log (n.sqrt + 1 : ℕ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hs))
  dsimp only [Function.comp_def]
  field_simp

lemma APSum_limit {q b : ℕ} (hq : 0 < q) (hb : b.Coprime q) :
    Tendsto (fun n : ℕ => APSum q b n / ((n : ℝ) * log n)) atTop
      (𝓝 ((q.totient : ℝ) / q ^ 2)) := by
  let H : ℕ → ℝ := fun n => ∑ d ∈ Ioc 0 (n.sqrt + 1), if d.Coprime q then (d : ℝ)⁻¹ else 0
  let main : ℕ → ℝ := fun n => 2 * ((n : ℝ) / q) * H n
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hm : Tendsto (fun n : ℕ => main n / ((n : ℝ) * log n)) atTop
      (𝓝 ((q.totient : ℝ) / q ^ 2)) := by
    have hh := (coprime_harmonic_sqrt_limit hq).const_mul (2 / (q : ℝ))
    have heq : (2 / (q : ℝ)) * ((q.totient : ℝ) / (2 * q)) = (q.totient : ℝ) / q ^ 2 := by
      field_simp
    rw [heq] at hh
    apply Filter.Tendsto.congr' _ hh
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    dsimp [main, H]
    field_simp
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun n : ℕ => (APSum q b n - main n) / ((n : ℝ) * log n))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (show Tendsto (fun n : ℕ => 10 / log n) atTop (𝓝 0)
      from tendsto_const_nhds.div_atTop hlog)
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hln : 0 < log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have heq : (10 : ℝ) / log n = 10 * n / ((n : ℝ) * log n) := by field_simp
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hn0 hln), heq]
    exact div_le_div_of_nonneg_right (AP_main_error hq hb hn) (mul_pos hn0 hln).le
  have hh := herr.add hm
  simpa only [sub_div, sub_add_cancel, zero_add] using hh

lemma APSum_eq_sum_Iic (q b N : ℕ) :
    APSum q b N = ∑ n ∈ Iic N, if n % q = b % q then (σ 0 n : ℝ) else 0 := by
  simpa [APSum] using sum_Ioc_add_eq_sum_Icc
    (f := fun n : ℕ => if n % q = b % q then (σ 0 n : ℝ) else 0) (Nat.zero_le N)

lemma linear_sum_eq_APSum {q r : ℕ} (hq : 0 < q) (hr : r < q) (N : ℕ) :
    (∑ n ∈ Iic N, (σ 0 (q * n + r) : ℝ)) = APSum q r (q * N + r) := by
  rw [APSum_eq_sum_Iic, ← sum_filter]
  apply sum_nbij' (fun n => q * n + r) (fun m => m / q)
  · intro n hn
    simp only [mem_filter, mem_Iic] at hn ⊢
    constructor
    · exact Nat.add_le_add_right (Nat.mul_le_mul_left q hn) r
    · simp [Nat.add_mod]
  · intro m hm
    simp only [mem_filter, mem_Iic] at hm ⊢
    have hh := Nat.div_le_div_right hm.1 (c := q)
    simpa [Nat.mul_add_div hq, Nat.div_eq_of_lt hr] using hh
  · intro n hn
    simp [Nat.mul_add_div hq, Nat.div_eq_of_lt hr]
  · intro m hm
    have hmod : m % q = r := (mem_filter.mp hm).2.trans (Nat.mod_eq_of_lt hr)
    simpa [hmod, add_comm] using Nat.mod_add_div m q
  · intro n hn
    rfl

lemma linear_reparam_limit (F : ℕ → ℝ) {q : ℕ} (hq : 0 < q) (r : ℕ)
    {c : ℝ} (h : Tendsto (fun n : ℕ => F n / ((n : ℝ) * log n)) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => F (q * n + r) / ((n : ℝ) * log n)) atTop (𝓝 ((q : ℝ) * c)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun n : ℕ => (q : ℝ) * n) atTop atTop := ht.const_mul_atTop hqR
  have hu : Tendsto (fun n : ℕ => q * n + r) atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) tendsto_id
    have hh := Nat.mul_le_mul_right n (show 1 ≤ q by omega)
    change n ≤ q * n + r
    omega
  have he : Asymptotics.IsEquivalent atTop (fun n : ℕ => ((q * n + r : ℕ) : ℝ))
      (fun n : ℕ => (q : ℝ) * n) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using
      (Asymptotics.IsEquivalent.refl.add_const_of_norm_tendsto_atTop (c := (r : ℝ))
        (tendsto_norm_atTop_atTop.comp hb))
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp ht
  have hlb : Asymptotics.IsEquivalent atTop (fun n : ℕ => log ((q : ℝ) * n))
      (fun n : ℕ => log (n : ℝ)) := by
    have hh := Asymptotics.IsEquivalent.refl.const_add_of_norm_tendsto_atTop
      (c := log (q : ℝ)) (tendsto_norm_atTop_atTop.comp hlog)
    apply hh.congr_left
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [Real.log_mul hqR.ne' (by exact_mod_cast hn.ne')]
  have hd : Asymptotics.IsEquivalent atTop
      (fun n : ℕ => ((q * n + r : ℕ) : ℝ) * log (q * n + r : ℕ))
      (fun n : ℕ => (q : ℝ) * ((n : ℝ) * log n)) := by
    apply (he.mul ((he.log hb).trans hlb)).congr_right
    filter_upwards with n
    exact mul_assoc _ _ _
  have hquot : Asymptotics.IsEquivalent atTop
      (fun n : ℕ => F (q * n + r) / (((q * n + r : ℕ) : ℝ) * log (q * n + r : ℕ)))
      (fun n : ℕ => F (q * n + r) / ((q : ℝ) * ((n : ℝ) * log n))) :=
    Asymptotics.IsEquivalent.refl.div hd
  have hh := (hquot.tendsto_nhds_iff.mp (h.comp hu)).const_mul (q : ℝ)
  apply Filter.Tendsto.congr' _ hh
  filter_upwards with n
  field_simp

lemma linear_sum_limit {q r : ℕ} (hq : 0 < q) (hr : r < q) (hcop : r.Coprime q) :
    Tendsto (fun N : ℕ => (∑ n ∈ Iic N, (σ 0 (q * n + r) : ℝ)) / ((N : ℝ) * log N))
      atTop (𝓝 ((q.totient : ℝ) / q)) := by
  have hh := linear_reparam_limit (APSum q r) hq r (APSum_limit hq hcop)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have heq : (q : ℝ) * ((q.totient : ℝ) / q ^ 2) = (q.totient : ℝ) / q := by field_simp
  rw [heq] at hh
  simpa only [← linear_sum_eq_APSum hq hr] using hh

end LinearCount

end Aux

lemma neg_nat_shift_limit_iff (f : ℤ[X]) (k : ℕ) (c : ℝ) :
    Tendsto (fun x : ℝ => Erdos975Sum (f.comp (X - C (k : ℤ))) x / (x * log x))
      atTop (𝓝 c) ↔
    Tendsto (fun x : ℝ => Erdos975Sum f x / (x * log x)) atTop (𝓝 c) := by
  have heq : (X - C (k : ℤ)).comp (X + C (k : ℤ)) = X := by
    rw [sub_comp, X_comp, C_comp, add_sub_cancel_right]
  have hh := (nat_shift_limit_iff (f.comp (X - C (k : ℤ))) k c).symm
  rw [Polynomial.comp_assoc, heq, Polynomial.comp_X] at hh
  exact hh

lemma int_shift_limit_iff (f : ℤ[X]) (k : ℤ) (c : ℝ) :
    Tendsto (fun x : ℝ => Erdos975Sum (f.comp (X + C k)) x / (x * log x))
      atTop (𝓝 c) ↔
    Tendsto (fun x : ℝ => Erdos975Sum f x / (x * log x)) atTop (𝓝 c) := by
  cases k with
  | ofNat k => exact nat_shift_limit_iff f k c
  | negSucc k =>
    simpa [Int.negSucc_eq, sub_eq_add_neg] using neg_nat_shift_limit_iff f (k + 1) c

lemma Erdos975Sum_linear_nat_tendsto {q r : ℕ} (hq : 0 < q) (hr : r < q)
    (hcop : r.Coprime q) :
    Tendsto (fun x : ℝ => Erdos975Sum (C (q : ℤ) * X + C (r : ℤ)) x / (x * log x))
      atTop (𝓝 ((q.totient : ℝ) / q)) := by
  apply (real_limit_iff_nat_limit _ _).mpr
  have hv (n : ℕ) : ⌊(q : ℤ) * (n : ℤ) + r⌋₊ = q * n + r := by
    rw [← Nat.cast_mul, ← Nat.cast_add, Nat.floor_natCast]
  simpa only [Erdos975Sum, eval_add, eval_mul, eval_C, eval_X, Nat.floor_natCast, hv] using
    Aux.LinearCount.linear_sum_limit hq hr hcop

lemma Erdos975Sum_linear_int_tendsto {a b : ℤ} (ha : 0 < a) (hcop : IsCoprime a b) :
    Tendsto (fun x : ℝ => Erdos975Sum (C a * X + C b) x / (x * log x))
      atTop (𝓝 ((a.toNat.totient : ℝ) / a.toNat)) := by
  let q := a.toNat
  let r := (b % a).toNat
  have hqcast : (q : ℤ) = a := Int.toNat_of_nonneg ha.le
  have hr0 : 0 ≤ b % a := Int.emod_nonneg b ha.ne'
  have hrcast : (r : ℤ) = b % a := Int.toNat_of_nonneg hr0
  have hq : 0 < q := by exact_mod_cast (show (0 : ℤ) < q by rw [hqcast]; exact ha)
  have hr : r < q := by
    exact_mod_cast (show (r : ℤ) < q by rw [hrcast, hqcast]; exact Int.emod_lt_of_pos b ha)
  have hcg : IsCoprime (b % a) a := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_emod]
    exact Int.isCoprime_iff_gcd_eq_one.mp hcop.symm
  rw [← hrcast, ← hqcast] at hcg
  have hcr : r.Coprime q := by simpa using Int.isCoprime_iff_nat_coprime.mp hcg
  have heq : (C (q : ℤ) * X + C (r : ℤ)).comp (X + C (b / a)) = C a * X + C b := by
    rw [add_comp, mul_comp, C_comp, X_comp, C_comp, hqcast, hrcast]
    rw [mul_add, ← C_mul, add_assoc, ← C_add]
    congr 2
    simpa [add_comm] using Int.emod_add_mul_ediv b a
  have hh := (int_shift_limit_iff (C (q : ℤ) * X + C (r : ℤ)) (b / a)
    ((q.totient : ℝ) / q)).mpr (Erdos975Sum_linear_nat_tendsto hq hr hcr)
  rw [heq] at hh
  exact hh

lemma linear_coeffs_coprime {a b : ℤ} (hp : (C a * X + C b : ℤ[X]).IsPrimitive) :
    IsCoprime a b := by
  have hu := hp (a.gcd b : ℤ)
    (dvd_add ((map_dvd C (Int.gcd_dvd_left a b)).mul_right X)
      (map_dvd C (Int.gcd_dvd_right a b)))
  rw [Int.isCoprime_iff_gcd_eq_one]
  simpa [Int.isUnit_iff_natAbs_eq] using hu

lemma erdos_975_degree_one (f : ℤ[X]) (hd : f.natDegree = 1)
    (hirr : Irreducible f) (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    ∃ c > (0 : ℝ), Tendsto (fun x => Erdos975Sum f x / (x * log x)) atTop (𝓝 c) := by
  let a := f.coeff 1
  let b := f.coeff 0
  have hf : f = C a * X + C b := Polynomial.eq_X_add_C_of_natDegree_le_one hd.le
  have ha0 : a ≠ 0 := by
    have hh := Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero
    simpa [Polynomial.leadingCoeff, hd, a] using hh
  have ha : 0 < a := by
    by_contra hna
    have han : a ≤ -1 := by omega
    obtain ⟨N, hN⟩ := eventually_atTop.mp hpos
    let n := max N (max 1 (b + 1))
    have hnN : N ≤ n := le_max_left _ _
    have hn1 : 1 ≤ n := (le_max_left 1 (b + 1)).trans (le_max_right _ _)
    have hnb : b + 1 ≤ n := (le_max_right 1 (b + 1)).trans (le_max_right _ _)
    have he := hN n hnN
    rw [hf] at he
    simp only [eval_add, eval_mul, eval_C, eval_X] at he
    have ham := mul_le_mul_of_nonneg_right han (show 0 ≤ n by omega)
    nlinarith
  have hprim : (C a * X + C b : ℤ[X]).IsPrimitive := by
    rw [← hf]
    exact hirr.isPrimitive (by rw [hd]; norm_num)
  have hcop := linear_coeffs_coprime hprim
  have hnat : 0 < a.toNat := by omega
  refine ⟨(a.toNat.totient : ℝ) / a.toNat, ?_, ?_⟩
  · apply div_pos
    · exact_mod_cast Nat.totient_pos.mpr hnat
    · exact_mod_cast hnat
  · rw [hf]
    exact Erdos975Sum_linear_int_tendsto ha hcop

/- Roots of the congruence x² + 1 = 0. -/
open Finset Polynomial
namespace QuadraticRoots

lemma cyclic_sq_eq_iff_order_four {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    {a : G} (ha : orderOf a = 2) (u : G) : u ^ 2 = a ↔ orderOf u = 4 := by
  classical
  have ha1 : a ≠ 1 := by intro h; simp [h] at ha
  constructor
  · intro h
    have hnot : u ^ (2 ^ 1) ≠ 1 := by simpa [h] using ha1
    have hfin : u ^ (2 ^ (1 + 1)) = 1 := by
      calc
        _ = (u ^ 2) ^ 2 := by rw [← pow_mul]; norm_num
        _ = a ^ 2 := by rw [h]
        _ = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
    simpa using orderOf_eq_prime_pow (p := 2) (n := 1) hnot hfin
  · intro hu
    have hu2 : orderOf (u ^ 2) = 2 := by rw [orderOf_pow, hu]; norm_num
    have hcard : ({v : G | orderOf v = 2} : Finset G).card ≤ 1 := by
      rw [IsCyclic.card_orderOf_eq_totient (show 2 ∣ Fintype.card G by rw [← ha]; exact orderOf_dvd_card)]
      norm_num
    exact card_le_one.mp hcard _ (by simp [hu2]) _ (by simp [ha])

lemma cyclic_card_sq_eq_order_two {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    {a : G} (ha : orderOf a = 2) :
    Nat.card {u : G // u ^ 2 = a} = if 4 ∣ Fintype.card G then 2 else 0 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp_rw [cyclic_sq_eq_iff_order_four ha]
  by_cases h4 : 4 ∣ Fintype.card G
  · rw [if_pos h4, IsCyclic.card_orderOf_eq_totient h4]
    decide
  · rw [if_neg h4]
    apply card_eq_zero.mpr
    apply filter_eq_empty_iff.mpr
    intro u hu horder
    exact h4 (horder ▸ orderOf_dvd_card (x := u))

noncomputable def rootsEquiv {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) :
    {x : R // x ^ 2 = -1} ≃ {x : S // x ^ 2 = -1} :=
  e.toEquiv.subtypeEquiv fun x => by
    constructor
    · intro h
      simpa using congrArg e h
    · intro h
      apply e.injective
      simpa using h

noncomputable def rootsProdEquiv (R S : Type*) [Ring R] [Ring S] :
    {x : R × S // x ^ 2 = -1} ≃ ({x : R // x ^ 2 = -1} × {x : S // x ^ 2 = -1}) where
  toFun x := (⟨x.1.1, congrArg Prod.fst x.2⟩, ⟨x.1.2, congrArg Prod.snd x.2⟩)
  invFun x := ⟨(x.1.1, x.2.1), Prod.ext x.1.2 x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def rootsUnitsEquiv (R : Type*) [CommRing R] :
    {x : R // x ^ 2 = -1} ≃ {u : Rˣ // u ^ 2 = -1} where
  toFun x := ⟨⟨x.1, -x.1, by rw [mul_neg, ← sq, x.2, neg_neg],
      by rw [neg_mul, ← sq, x.2, neg_neg]⟩, by apply Units.ext; exact x.2⟩
  invFun u := ⟨u.1.val, by have h := congrArg Units.val u.2; exact h⟩
  left_inv x := rfl
  right_inv u := by apply Subtype.ext; apply Units.ext; rfl

noncomputable def rho (n : ℕ) : ℕ := Nat.card {x : ZMod n // x ^ 2 = -1}

lemma rho_mul {m n : ℕ} (hc : m.Coprime n) : rho (m * n) = rho m * rho n := by
  unfold rho
  rw [Nat.card_congr ((rootsEquiv (ZMod.chineseRemainder hc)).trans
    (rootsProdEquiv (ZMod m) (ZMod n))), Nat.card_prod]

lemma rho_zero : rho 0 = 0 := by
  have h : IsEmpty {x : ZMod 0 // x ^ 2 = -1} := by
    change IsEmpty {x : ℤ // x ^ 2 = -1}
    apply IsEmpty.mk
    rintro ⟨x, hx⟩
    change (x : ℤ) ^ 2 = -1 at hx
    nlinarith [sq_nonneg (x : ℤ)]
  exact @Nat.card_of_isEmpty _ h

lemma rho_one : rho 1 = 1 := by
  unfold rho
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

lemma rho_two : rho 2 = 1 := by
  unfold rho
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

lemma rho_four : rho 4 = 0 := by
  unfold rho
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

lemma rho_prime_pow_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ} (hk : 0 < k) :
    rho (p ^ k) = if 4 ∣ (p ^ k).totient then 2 else 0 := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  letI : IsCyclic (ZMod (p ^ k))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 k
  have hneg : (-1 : (ZMod (p ^ k))ˣ) ≠ 1 := by
    intro h
    have he : (-1 : ZMod (p ^ k)) = 1 := congrArg Units.val h
    have ht : (2 : ZMod (p ^ k)) = 0 := by linear_combination -he
    have hdiv : p ^ k ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (p ^ k)).mp (by simpa using ht)
    have hpd : p ∣ 2 := dvd_trans (dvd_pow_self p hk.ne') hdiv
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hpd |>.resolve_left hp.ne_one)
  have horder : orderOf (-1 : (ZMod (p ^ k))ˣ) = 2 := orderOf_eq_prime (by simp) hneg
  unfold rho
  rw [Nat.card_congr (rootsUnitsEquiv (ZMod (p ^ k))), cyclic_card_sq_eq_order_two horder,
    ZMod.card_units_eq_totient]

lemma rho_two_pow_of_two_le {k : ℕ} (hk : 2 ≤ k) : rho (2 ^ k) = 0 := by
  have hnone : ∀ x : ZMod 4, x ^ 2 ≠ -1 := by decide
  have hd : 4 ∣ 2 ^ k := by simpa using (pow_dvd_pow (2 : ℕ) hk)
  let e : ZMod (2 ^ k) →+* ZMod 4 := ZMod.castHom hd (ZMod 4)
  have h : IsEmpty {x : ZMod (2 ^ k) // x ^ 2 = -1} := by
    apply IsEmpty.mk
    intro x
    have he : (e x.1) ^ 2 = -1 := by simpa using congrArg e x.2
    exact hnone _ he
  exact @Nat.card_of_isEmpty _ h

lemma rho_prime_pow_odd_mod_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ} (hk : 0 < k) :
    rho (p ^ k) = if p % 4 = 1 then 2 else 0 := by
  have hc : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr (fun h =>
    hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one))
  have hc4 : (4 : ℕ).Coprime (p ^ (k - 1)) := by
    simpa using (hc.symm.pow_left 2).pow_right (k - 1)
  have heq : 4 ∣ p - 1 ↔ p % 4 = 1 := by have := hp.two_le; omega
  have hiff : 4 ∣ (p ^ k).totient ↔ p % 4 = 1 := by
    rw [Nat.totient_prime_pow hp hk]
    exact hc4.dvd_mul_left.trans heq
  rw [rho_prime_pow_odd hp hp2 hk]
  simp only [hiff]

noncomputable def rhoZ : ArithmeticFunction ℤ where
  toFun n := rho n
  map_zero' := by simp [rho_zero]

lemma rhoZ_apply (n : ℕ) : rhoZ n = (rho n : ℤ) := rfl

lemma rhoZ_multiplicative : rhoZ.IsMultiplicative := by
  constructor
  · simp only [rhoZ_apply, rho_one, Nat.cast_one]
  · intro m n hmn
    simp only [rhoZ_apply, rho_mul hmn, Nat.cast_mul]

def chi4 : ArithmeticFunction ℤ where
  toFun n := if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0
  map_zero' := rfl

lemma chi4_apply (n : ℕ) : chi4 n = if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0 := rfl

lemma chi4_mul (m n : ℕ) : chi4 (m * n) = chi4 m * chi4 n := by
  simp only [chi4_apply]
  rw [Nat.mul_mod m n 4]
  have hm : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  have hn : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases m % 4 <;> interval_cases n % 4 <;> norm_num

lemma chi4_multiplicative : chi4.IsMultiplicative := ⟨rfl, fun {m n} _ => chi4_mul m n⟩

lemma chi4_pow (p k : ℕ) : chi4 (p ^ k) = chi4 p ^ k := by
  induction k with
  | zero => simp [chi4_apply]
  | succ k ih => rw [pow_succ, chi4_mul, ih, pow_succ]

noncomputable def sqfree : ArithmeticFunction ℤ :=
  ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius

lemma sqfree_apply (n : ℕ) : sqfree n = ArithmeticFunction.moebius n ^ 2 := by
  simp [sqfree, ArithmeticFunction.pmul_apply, pow_two]

lemma sqfree_multiplicative : sqfree.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.pmul ArithmeticFunction.isMultiplicative_moebius

lemma convolution_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (sqfree * chi4) (p ^ (k + 1)) = chi4 p ^ (k + 1) + chi4 p ^ k := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun i j => sqfree i * chi4 j),
    Nat.sum_divisors_prime_pow hp]
  have hsub : ({0, 1} : Finset ℕ) ⊆ range (k + 1 + 1) := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp
  rw [← sum_subset hsub (fun i hi hin => ?_)]
  · simp [sqfree_apply, ArithmeticFunction.moebius_apply_prime hp, pow_succ, Nat.mul_div_cancel _ hp.pos, chi4_mul, chi4_pow]
  · have hi0 : i ≠ 0 := by intro h; simp [h] at hin
    have hi1 : i ≠ 1 := by intro h; simp [h] at hin
    simp [sqfree_apply, ArithmeticFunction.moebius_apply_prime_pow hp hi0, hi1]

lemma rhoZ_eq_convolution : rhoZ = sqfree * chi4 := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers rhoZ rhoZ_multiplicative
    (sqfree * chi4) (sqfree_multiplicative.mul chi4_multiplicative)).mpr
  intro p k hp
  cases k with
  | zero =>
    simp only [pow_zero]
    exact rhoZ_multiplicative.map_one.trans (sqfree_multiplicative.mul chi4_multiplicative).map_one.symm
  | succ k =>
    rw [convolution_prime_pow hp]
    by_cases hp2 : p = 2
    · subst p
      cases k with
      | zero => simp [rhoZ_apply, rho_two, chi4_apply]
      | succ k => simp [rhoZ_apply, rho_two_pow_of_two_le (show 2 ≤ k + 1 + 1 by omega), chi4_apply]
    · rw [rhoZ_apply, rho_prime_pow_odd_mod_four hp hp2 (show 0 < k + 1 by omega)]
      have hpodd := hp.eq_two_or_odd.resolve_left hp2
      have hpmod : p % 4 = 1 ∨ p % 4 = 3 := by omega
      rcases hpmod with hp1 | hp3
      · simp [chi4_apply, hp1]
      · simp [chi4_apply, hp3, pow_succ]

end QuadraticRoots

namespace QuadraticRoots
open Filter Real
open scoped Topology

lemma chi4_real_periodic : Function.Periodic (fun n : ℕ => (chi4 n : ℝ)) 4 := by
  intro n
  simp [chi4_apply]

lemma chi4_partial_bound (N : ℕ) : |∑ i ∈ Finset.Ioc 0 N, chi4 i| ≤ 2 := by
  have hp : Function.Periodic (fun n : ℕ => (chi4 (n + 1) : ℝ)) 4 := by
    intro n
    simpa [add_assoc, add_comm, add_left_comm] using chi4_real_periodic (n + 1)
  have hz : ∑ i ∈ range 4, (chi4 (i + 1) : ℝ) = 0 := by
    norm_num [chi4_apply, sum_range_succ]
  have hh := Aux.PeriodicHarmonic.periodic_zero_sum_bounded (by norm_num : 0 < 4) hp hz N
  norm_num [chi4_apply, sum_range_succ] at hh
  have hset : Ioc 0 N = Ico 1 (N + 1) := by ext i; simp only [mem_Ioc, mem_Ico]; omega
  have heq : ∑ i ∈ Ioc 0 N, (chi4 i : ℝ) = ∑ i ∈ range N, (chi4 (i + 1) : ℝ) := by
    rw [hset, sum_Ico_eq_sum_range]
    simp [add_comm]
  have hh' : |∑ i ∈ Ioc 0 N, (chi4 i : ℝ)| ≤ 2 := by
    rw [heq]
    simpa [Real.norm_eq_abs, chi4_apply] using hh
  exact_mod_cast hh'

lemma rho_sum_bound (N : ℕ) : ∑ i ∈ Ioc 0 N, rho i ≤ 2 * N := by
  suffices h : (∑ i ∈ Ioc 0 N, (rho i : ℤ)) ≤ 2 * N by exact_mod_cast h
  simp_rw [← rhoZ_apply, rhoZ_eq_convolution]
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  calc
    _ ≤ ∑ _i ∈ Ioc 0 N, (2 : ℤ) := by
      apply sum_le_sum
      intro i hi
      have hchi : ∑ j ∈ Ioc 0 (N / i), chi4 j ≤ 2 :=
        (le_abs_self _).trans (chi4_partial_bound _)
      have hsq0 : (0 : ℤ) ≤ sqfree i := by rw [sqfree_apply]; positivity
      have hsq1 : sqfree i ≤ 1 := by rw [sqfree_apply, ArithmeticFunction.moebius_sq]; split_ifs <;> norm_num
      exact (mul_le_mul_of_nonneg_left hchi hsq0).trans (by nlinarith)
    _ = _ := by simp [mul_comm]

lemma chi4_harmonic_limit_positive :
    ∃ L > (0 : ℝ), Tendsto (fun N : ℕ => ∑ i ∈ range N,
      (chi4 (i + 1) : ℝ) / (i + 1)) atTop (𝓝 L) := by
  have hh := Aux.PeriodicHarmonic.periodic_harmonic_remainder_converges
    (fun n : ℕ => (chi4 n : ℝ)) (by norm_num : 0 < 4) chi4_real_periodic
  have hz : ∑ i ∈ range 4, (chi4 (i + 1) : ℝ) = 0 := by norm_num [chi4_apply, sum_range_succ]
  simp only [hz, zero_div, zero_mul, sub_zero] at hh
  obtain ⟨L, hL⟩ := hh
  let P : ℕ → ℝ := fun N => ∑ i ∈ range N, (chi4 (i + 1) : ℝ) / (i + 1)
  have hrec (m : ℕ) : P (4 * (m + 1)) = P (4 * m) +
      ((4 * (m : ℝ) + 1)⁻¹ - (4 * (m : ℝ) + 3)⁻¹) := by
    dsimp only [P]
    rw [Nat.mul_succ, sum_range_add]
    norm_num [sum_range_succ, chi4_apply, Nat.add_mod, Nat.cast_add, Nat.cast_mul]
    ring
  have hstep (m : ℕ) : P (4 * m) ≤ P (4 * (m + 1)) := by
    rw [hrec]
    have hh : (4 * (m : ℝ) + 3)⁻¹ ≤ (4 * (m : ℝ) + 1)⁻¹ :=
      inv_anti₀ (by positivity) (by linarith)
    linarith
  have hb (n : ℕ) : (2 / 3 : ℝ) ≤ P (4 * (n + 1)) := by
    induction n with
    | zero => norm_num [P, sum_range_succ, chi4_apply]
    | succ n ih => exact ih.trans (hstep (n + 1))
  have ht : Tendsto (fun n : ℕ => 4 * (n + 1)) atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) tendsto_id
    change n ≤ 4 * (n + 1)
    omega
  have hLb : (2 / 3 : ℝ) ≤ L := ge_of_tendsto' (hL.comp ht) hb
  exact ⟨L, by linarith, hL⟩

end QuadraticRoots

namespace QuadraticRoots

lemma sq_dvd_sq_mul_squarefree_iff {a b d : ℕ} (ha : Squarefree a) (hb : b ≠ 0) :
    d ^ 2 ∣ b ^ 2 * a ↔ d ∣ b := by
  by_cases hd : d = 0
  · simp [hd, hb, ha.ne_zero]
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ hd) (mul_ne_zero (pow_ne_zero _ hb) ha.ne_zero),
    ← Nat.factorization_le_iff_dvd hd hb]
  simp only [Nat.factorization_mul (pow_ne_zero _ hb) ha.ne_zero, Nat.factorization_pow,
    Finsupp.le_def, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  constructor
  · intro h p
    have hle := ha.natFactorization_le_one p
    have hh := h p
    omega
  · intro h p
    have hh := h p
    omega

lemma sum_square_divisors_moebius {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors with d ^ 2 ∣ n, ArithmeticFunction.moebius d = sqfree n := by
  obtain ⟨a, b, ha, hb, heq, hsf⟩ := Nat.sq_mul_squarefree_of_pos hn
  subst n
  have hset : {d ∈ (b ^ 2 * a).divisors | d ^ 2 ∣ b ^ 2 * a} = b.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors,
      sq_dvd_sq_mul_squarefree_iff hsf hb.ne']
    constructor
    · intro h
      exact ⟨h.2, hb.ne'⟩
    · intro h
      exact ⟨⟨h.1.trans ((dvd_pow_self b (by decide : 2 ≠ 0)).trans
        (dvd_mul_right _ _)), mul_ne_zero (pow_ne_zero 2 hb.ne') ha.ne'⟩, h.1⟩
  rw [hset, ← ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.coe_zeta_mul_moebius]
  have hs : Squarefree (b ^ 2 * a) ↔ b = 1 := by
    constructor
    · intro h
      exact Nat.isUnit_iff.mp (h b (by simpa [pow_two] using (dvd_mul_right (b ^ 2) a)))
    · rintro rfl
      simpa using hsf
  simp [sqfree_apply, ArithmeticFunction.moebius_sq, hs, ArithmeticFunction.one_apply]

lemma sum_sqfree_weight (N : ℕ) (w : ℕ → ℝ) :
    ∑ n ∈ Ioc 0 N, (sqfree n : ℝ) * w n =
      ∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) *
        ∑ m ∈ Ioc 0 (N / d ^ 2), w (d ^ 2 * m) := by
  have hset (n : ℕ) (hn : n ∈ Ioc 0 N) :
      {d ∈ n.divisors | d ^ 2 ∣ n} = {d ∈ Ioc 0 N | d ^ 2 ∣ n} := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, mem_Ioc] at *
    constructor
    · rintro ⟨⟨hd, hn0⟩, hsq⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn.1, (Nat.le_of_dvd hn.1 hd).trans hn.2⟩, hsq⟩
    · rintro ⟨hd, hsq⟩
      exact ⟨⟨(dvd_pow_self d (by decide : 2 ≠ 0)).trans hsq, hn.1.ne'⟩, hsq⟩
  calc
    _ = ∑ n ∈ Ioc 0 N, ∑ d ∈ Ioc 0 N,
        if d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℝ) * w n else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [← sum_square_divisors_moebius (mem_Ioc.mp hn).1, Int.cast_sum, sum_mul, hset n hn,
        sum_filter]
    _ = ∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) *
        ∑ n ∈ Ioc 0 N with d ^ 2 ∣ n, w n := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d hd
      rw [mul_sum, sum_filter]
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      congr 1
      have hdpos : 0 < d ^ 2 := pow_pos (mem_Ioc.mp hd).1 _
      symm
      apply sum_bij (fun m _ => d ^ 2 * m)
      · intro m hm
        simp only [mem_Ioc] at hm
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.mul_pos hdpos hm.1,
          by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hdpos).mp hm.2⟩,
          dvd_mul_right _ _⟩
      · intro a ha b hb hab
        exact Nat.eq_of_mul_eq_mul_left hdpos hab
      · intro n hn
        obtain ⟨hnmem, hdn⟩ := mem_filter.mp hn
        obtain ⟨hnpos, hnle⟩ := mem_Ioc.mp hnmem
        refine ⟨n / d ^ 2, mem_Ioc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hnpos hdn) hdpos,
          Nat.div_le_div_right hnle⟩, Nat.mul_div_cancel' hdn⟩
      · intro m hm
        rfl

lemma sum_sqfree (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (sqfree n : ℝ) =
      ∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) * (N / d ^ 2 : ℕ) := by
  simpa using sum_sqfree_weight N (fun _ => 1)

noncomputable def sqfreeDensity : ℝ :=
  ∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2

lemma moebius_real_abs_le_one (d : ℕ) : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))

lemma summable_moebius_div_sq :
    Summable (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) := by
  apply (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).of_norm_bounded
  intro d
  simp only [Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (moebius_real_abs_le_one d) (sq_nonneg _)

lemma nat_div_ratio_limit (q : ℕ) :
    Tendsto (fun N : ℕ => (N / q : ℕ) / (N : ℝ)) atTop (𝓝 (1 / (q : ℝ))) := by
  by_cases hq : q = 0
  · subst q
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hq)
  have ht : Tendsto (fun N : ℕ => (N : ℝ) / q) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hqr
  have hh := (tendsto_nat_floor_div_atTop.comp ht).div_const (q : ℝ)
  convert hh using 1
  ext N
  simp only [Function.comp_def, Nat.floor_div_natCast, Nat.floor_natCast, div_div,
    div_mul_cancel₀ _ hqr.ne']

lemma sqfree_density_limit :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, (sqfree n : ℝ)) / (N : ℝ))
      atTop (𝓝 sqfreeDensity) := by
  have hh := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    (f := fun N d : ℕ => (ArithmeticFunction.moebius d : ℝ) * (N / d ^ 2 : ℕ) / (N : ℝ))
    (g := fun d : ℕ => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2)
    (fun d => by
      have ht := (nat_div_ratio_limit (d ^ 2)).const_mul (ArithmeticFunction.moebius d : ℝ)
      simpa [mul_div_assoc] using ht) ?_
  · apply hh.congr'
    filter_upwards [] with N
    rw [sum_sqfree, sum_div]
    exact tsum_eq_sum (fun d hd => by
      by_cases hd0 : d = 0
      · simp [hd0]
      · have hNd : N < d := by simpa [mem_Ioc, Nat.pos_of_ne_zero hd0] using hd
        have hsq : N < d ^ 2 := by nlinarith
        simp [Nat.div_eq_of_lt hsq])
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN d
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    calc
      ‖(ArithmeticFunction.moebius d : ℝ) * (N / d ^ 2 : ℕ) / (N : ℝ)‖ =
          |(ArithmeticFunction.moebius d : ℝ)| * ((N / d ^ 2 : ℕ) / (N : ℝ)) := by
        simp [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hNr, mul_div_assoc]
      _ ≤ 1 * ((N / d ^ 2 : ℕ) / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right (moebius_real_abs_le_one d) (by positivity)
      _ ≤ ((N : ℝ) / (d : ℝ) ^ 2) / N := by
        have hc : ((N / d ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) ^ 2 := by
          exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := N) (n := d ^ 2))
        simpa only [one_mul] using div_le_div_of_nonneg_right hc hNr.le
      _ = 1 / (d : ℝ) ^ 2 := by rw [div_right_comm, div_self hNr.ne']

lemma sqfreeDensity_pos : 0 < sqfreeDensity := by
  have hl := (hasSum_ite_eq (1 : ℕ) (2 : ℝ)).sub hasSum_zeta_two
  have hle : 2 - π ^ 2 / 6 ≤ sqfreeDensity := by
    rw [← hl.tsum_eq]
    apply Summable.tsum_le_tsum _ hl.summable summable_moebius_div_sq
    intro d
    by_cases hd : d = 1
    · norm_num [hd]
    · simp only [if_neg hd, zero_sub]
      have hm : -(1 : ℝ) ≤ (ArithmeticFunction.moebius d : ℝ) :=
        (abs_le.mp (moebius_real_abs_le_one d)).1
      simpa only [neg_div] using div_le_div_of_nonneg_right hm (sq_nonneg (d : ℝ))
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  nlinarith

lemma sum_sqfree_div (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (sqfree n : ℝ) / n =
      ∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 *
        (harmonic (N / d ^ 2) : ℝ) := by
  have hh := sum_sqfree_weight N (fun n => (n : ℝ)⁻¹)
  simp only [Nat.cast_mul, Nat.cast_pow, mul_inv, ← mul_sum, harmonic_sum] at hh
  simpa only [div_eq_mul_inv, mul_assoc] using hh

lemma nat_div_harmonic_log_limit {q : ℕ} (hq : 0 < q) :
    Tendsto (fun N : ℕ => (harmonic (N / q) : ℝ) / log N) atTop (𝓝 1) := by
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have htlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp htlog
  have hl : Tendsto (fun N : ℕ => 1 - log (q : ℝ) / log N) atTop (𝓝 1) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.sub (hinv.const_mul (log (q : ℝ)))
  have hu : Tendsto (fun N : ℕ => 1 + (1 - log (q : ℝ)) / log N) atTop (𝓝 1) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.add (hinv.const_mul (1 - log (q : ℝ)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  all_goals
    filter_upwards [eventually_ge_atTop q, eventually_gt_atTop (1 : ℕ)] with N hN hN1
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hlog : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
    have hx : (1 : ℝ) ≤ N / q := (le_div_iff₀ hqr).mpr (by simpa only [one_mul] using (Nat.cast_le (α := ℝ)).mpr hN)
  · have hh := log_le_harmonic_floor ((N : ℝ) / q) (zero_le_one.trans hx)
    simp only [Nat.floor_div_natCast, Nat.floor_natCast, Real.log_div hNr.ne' hqr.ne'] at hh
    rw [le_div_iff₀ hlog]
    convert hh using 1 <;> field_simp
  · have hh := harmonic_floor_le_one_add_log ((N : ℝ) / q) hx
    simp only [Nat.floor_div_natCast, Nat.floor_natCast, Real.log_div hNr.ne' hqr.ne'] at hh
    rw [div_le_iff₀ hlog]
    convert hh using 1 <;> field_simp <;> ring

lemma sqfree_harmonic_limit :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, (sqfree n : ℝ) / n) / log N)
      atTop (𝓝 sqfreeDensity) := by
  have htlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left 2)
    (f := fun N d : ℕ => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 *
      (harmonic (N / d ^ 2) : ℝ) / log N)
    (g := fun d : ℕ => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2)
    (fun d => by
      by_cases hd : d = 0
      · subst d
        simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), div_zero, zero_mul, zero_div]
        exact tendsto_const_nhds
      · have ht := (nat_div_harmonic_log_limit (pow_pos (Nat.pos_of_ne_zero hd) 2)).const_mul
          ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2)
        simpa only [mul_one, mul_div_assoc] using ht) ?_
  · apply hh.congr'
    filter_upwards [] with N
    rw [sum_sqfree_div, sum_div]
    exact tsum_eq_sum (fun d hd => by
      by_cases hd0 : d = 0
      · simp [hd0]
      · have hNd : N < d := by simpa [mem_Ioc, Nat.pos_of_ne_zero hd0] using hd
        have hsq : N < d ^ 2 := by nlinarith
        simp [Nat.div_eq_of_lt hsq])
  · filter_upwards [htlog.eventually_ge_atTop 1] with N hN d
    have hlog : 0 < log (N : ℝ) := by linarith
    have hh0 : (0 : ℝ) ≤ (harmonic (N / d ^ 2) : ℝ) := by
      rw [← harmonic_sum]
      exact sum_nonneg (fun _ _ => by positivity)
    have hle : (harmonic (N / d ^ 2) : ℝ) ≤ (harmonic N : ℝ) := by
      rw [← harmonic_sum, ← harmonic_sum]
      exact sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right (Nat.div_le_self _ _))
        (fun _ _ _ => by positivity)
    have hb : (harmonic (N / d ^ 2) : ℝ) / log N ≤ 2 := by
      apply (div_le_iff₀ hlog).mpr
      have hh := hle.trans (harmonic_le_one_add_log N)
      linarith
    calc
      ‖(ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 *
          (harmonic (N / d ^ 2) : ℝ) / log N‖ =
        (|(ArithmeticFunction.moebius d : ℝ)| / (d : ℝ) ^ 2) *
          ((harmonic (N / d ^ 2) : ℝ) / log N) := by
            simp only [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, Nat.abs_cast,
              abs_of_nonneg hh0, abs_of_pos hlog, mul_div_assoc]
      _ ≤ (1 / (d : ℝ) ^ 2) * 2 := mul_le_mul
        (div_le_div_of_nonneg_right (moebius_real_abs_le_one d) (sq_nonneg _)) hb
        (div_nonneg hh0 hlog.le) (by positivity)
      _ = _ := mul_comm _ _

lemma abs_weighted_sum_le {a w : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ n, |∑ i ∈ range n, a i| ≤ B) (hw : Antitone w) (hw0 : ∀ i, 0 ≤ w i)
    (n : ℕ) : |∑ i ∈ range n, w i * a i| ≤ B * w 0 := by
  by_cases hn : n = 0
  · subst n
    simpa using mul_nonneg hB (hw0 0)
  have heq := sum_range_by_parts w a n
  simp only [smul_eq_mul] at heq
  rw [heq]
  calc
    _ ≤ |w (n - 1) * ∑ i ∈ range n, a i| +
        |∑ i ∈ range (n - 1), (w (i + 1) - w i) * ∑ j ∈ range (i + 1), a j| := abs_sub _ _
    _ ≤ w (n - 1) * B + ∑ i ∈ range (n - 1), (w i - w (i + 1)) * B := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg (hw0 _)]
        exact mul_le_mul_of_nonneg_left (ha n) (hw0 _)
      · apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro i hi
        rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hw (Nat.le_succ i))), neg_sub]
        exact mul_le_mul_of_nonneg_left (ha (i + 1)) (sub_nonneg.mpr (hw (Nat.le_succ i)))
    _ = B * w 0 := by rw [← sum_mul, sum_range_sub']; ring

set_option maxHeartbeats 800000 in
lemma chi4_sum_range_bound (N : ℕ) : |∑ i ∈ range N, (chi4 (i + 1) : ℝ)| ≤ 2 := by
  have hh : |∑ i ∈ Ioc 0 N, (chi4 i : ℝ)| ≤ 2 := by exact_mod_cast chi4_partial_bound N
  have hset : Ioc 0 N = Ico 1 (N + 1) := by ext i; simp only [mem_Ioc, mem_Ico]; omega
  rw [hset, sum_Ico_eq_sum_range] at hh
  simpa [add_comm] using hh

set_option maxHeartbeats 800000 in
lemma chi4_harmonic_tail_bound {L : ℝ}
    (hL : Tendsto (fun N : ℕ => ∑ i ∈ range N, (chi4 (i + 1) : ℝ) / (i + 1)) atTop (𝓝 L))
    (N : ℕ) : |L - ∑ i ∈ range N, (chi4 (i + 1) : ℝ) / (i + 1)| ≤ 4 / (N + 1) := by
  let a : ℕ → ℝ := fun i => (chi4 (i + 1) : ℝ)
  have ha (M : ℕ) : |∑ i ∈ range M, a (N + i)| ≤ 4 := by
    have heq : ∑ i ∈ range M, a (N + i) =
        (∑ i ∈ range (N + M), a i) - ∑ i ∈ range N, a i := by rw [sum_range_add]; ring
    rw [heq]
    exact (abs_sub _ _).trans ((add_le_add (chi4_sum_range_bound _) (chi4_sum_range_bound _)).trans (by norm_num))
  have hw : Antitone (fun i : ℕ => ((N + i + 1 : ℕ) : ℝ)⁻¹) := by
    intro i j hij
    apply inv_anti₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_left hij N) 1
  have hb (M : ℕ) : |(∑ i ∈ range (N + M), a i / (i + 1)) -
      ∑ i ∈ range N, a i / (i + 1)| ≤ 4 / (N + 1) := by
    rw [sum_range_add, add_sub_cancel_left]
    simpa [div_eq_mul_inv, mul_comm, Nat.cast_add, Nat.cast_one] using
      abs_weighted_sum_le (by norm_num : (0 : ℝ) ≤ 4) ha hw (fun i => by positivity) M
  have ht : Tendsto (fun M : ℕ => N + M) atTop atTop :=
    tendsto_atTop_mono (fun M => Nat.le_add_left M N) tendsto_id
  have hh := ((hL.comp ht).sub_const (∑ i ∈ range N, a i / (i + 1))).abs
  exact le_of_tendsto' hh hb

noncomputable def arithDiv (f : ArithmeticFunction ℤ) : ArithmeticFunction ℝ where
  toFun n := (f n : ℝ) / n
  map_zero' := by simp

lemma arithDiv_apply (f : ArithmeticFunction ℤ) (n : ℕ) : arithDiv f n = (f n : ℝ) / n := rfl

lemma arithDiv_mul (f g : ArithmeticFunction ℤ) : arithDiv (f * g) = arithDiv f * arithDiv g := by
  ext n
  simp only [arithDiv_apply, ArithmeticFunction.mul_apply, Int.cast_sum, Int.cast_mul, sum_div]
  apply sum_congr rfl
  intro p hp
  have heq : p.1 * p.2 = n := (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [← heq, Nat.cast_mul]
  ring

lemma sum_rho_div (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (rho n : ℝ) / n =
      ∑ d ∈ Ioc 0 N, (sqfree d : ℝ) / d *
        ∑ m ∈ Ioc 0 (N / d), (chi4 m : ℝ) / m := by
  have hh := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum (arithDiv sqfree) (arithDiv chi4) N
  rw [← arithDiv_mul, ← rhoZ_eq_convolution] at hh
  simpa only [arithDiv_apply, rhoZ_apply, Int.cast_natCast] using hh

lemma chi4_harmonic_Ioc_tail_bound {L : ℝ}
    (hL : Tendsto (fun N : ℕ => ∑ i ∈ range N, (chi4 (i + 1) : ℝ) / (i + 1)) atTop (𝓝 L))
    (N : ℕ) : |L - ∑ i ∈ Ioc 0 N, (chi4 i : ℝ) / i| ≤ 4 / (N + 1) := by
  have hset : Ioc 0 N = Ico 1 (N + 1) := by ext i; simp only [mem_Ioc, mem_Ico]; omega
  rw [hset, sum_Ico_eq_sum_range]
  simpa [add_comm] using chi4_harmonic_tail_bound hL N

lemma rho_harmonic_error_bound {L : ℝ}
    (hL : Tendsto (fun N : ℕ => ∑ i ∈ range N, (chi4 (i + 1) : ℝ) / (i + 1)) atTop (𝓝 L))
    {N : ℕ} (hN : 0 < N) :
    |(∑ n ∈ Ioc 0 N, (rho n : ℝ) / n) - L * ∑ n ∈ Ioc 0 N, (sqfree n : ℝ) / n| ≤ 4 := by
  rw [sum_rho_div, mul_sum, ← sum_sub_distrib]
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  calc
    _ ≤ ∑ d ∈ Ioc 0 N, (4 : ℝ) / N := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro d hd
      have hdr : (0 : ℝ) < d := Nat.cast_pos.mpr (mem_Ioc.mp hd).1
      have hs0 : (0 : ℝ) ≤ (sqfree d : ℝ) := by rw [sqfree_apply, Int.cast_pow]; positivity
      have hs1 : (sqfree d : ℝ) ≤ 1 := by
        rw [sqfree_apply, ArithmeticFunction.moebius_sq]
        split_ifs <;> norm_num
      have htail := chi4_harmonic_Ioc_tail_bound hL (N / d)
      have hmpos : (0 : ℝ) < (N / d : ℕ) + 1 := by positivity
      have hm : (N : ℝ) ≤ d * ((N / d : ℕ) + 1) := by
        exact_mod_cast (Nat.lt_mul_div_succ N (mem_Ioc.mp hd).1).le
      calc
        _ = ((sqfree d : ℝ) / d) * |L - ∑ m ∈ Ioc 0 (N / d), (chi4 m : ℝ) / m| := by
          rw [mul_comm L, ← mul_sub, abs_mul, abs_of_nonneg (div_nonneg hs0 hdr.le), abs_sub_comm]
        _ ≤ (1 / (d : ℝ)) * (4 / ((N / d : ℕ) + 1)) := mul_le_mul
          (div_le_div_of_nonneg_right hs1 hdr.le) htail (abs_nonneg _) (by positivity)
        _ = 4 / ((d : ℝ) * ((N / d : ℕ) + 1)) := by rw [div_mul_div_comm, one_mul]
        _ ≤ 4 / (N : ℝ) := div_le_div_of_nonneg_left (by norm_num) hNr hm
    _ = 4 := by simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]; field_simp

lemma rho_harmonic_limit_positive :
    ∃ C > (0 : ℝ), Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, (rho n : ℝ) / n) / log N)
      atTop (𝓝 C) := by
  obtain ⟨L, hLpos, hL⟩ := chi4_harmonic_limit_positive
  refine ⟨L * sqfreeDensity, mul_pos hLpos sqfreeDensity_pos, ?_⟩
  have htlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun N : ℕ => ((∑ n ∈ Ioc 0 N, (rho n : ℝ) / n) -
      L * ∑ n ∈ Ioc 0 N, (sqfree n : ℝ) / n) / log N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ => 4 / log (N : ℝ))
    · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
      have hlog : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hlog]
      exact div_le_div_of_nonneg_right (rho_harmonic_error_bound hL (by omega)) hlog.le
    · exact tendsto_const_nhds.div_atTop htlog
  have hh := (sqfree_harmonic_limit.const_mul L).add he
  simpa only [add_zero, ← mul_div_assoc, ← add_div, add_sub_cancel] using hh

lemma sigma0_sq_add_one {n : ℕ} (hn : 0 < n) :
    σ 0 (n ^ 2 + 1) = 2 * {d ∈ Ioc 0 n | d ∣ n ^ 2 + 1}.card := by
  let T := (n ^ 2 + 1).divisorsAntidiagonal
  let A := T.filter (fun p => p.1 ≤ n)
  let B := T.filter (fun p => p.2 ≤ n)
  have hunion : A ∪ B = T := by
    ext p
    simp only [A, B, mem_union, mem_filter]
    constructor
    · tauto
    · intro hp
      have heq : p.1 * p.2 = n ^ 2 + 1 := (Nat.mem_divisorsAntidiagonal.mp hp).1
      have hle : p.1 ≤ n ∨ p.2 ≤ n := by
        by_contra! h
        have hh := Nat.mul_le_mul h.1 h.2
        nlinarith
      tauto
  have hdisj : Disjoint A B := by
    apply disjoint_filter.mpr
    intro p hp h1 h2
    have heq : p.1 * p.2 = n ^ 2 + 1 := (Nat.mem_divisorsAntidiagonal.mp hp).1
    have hh := Nat.mul_le_mul h1 h2
    nlinarith
  have hcard : A.card = B.card := by
    apply card_nbij' Prod.swap Prod.swap
    · intro p hp
      simpa [A, B, T, Nat.swap_mem_divisorsAntidiagonal, mul_comm] using hp
    · intro p hp
      simpa [A, B, T, Nat.swap_mem_divisorsAntidiagonal, mul_comm] using hp
    · intro p hp
      simp
    · intro p hp
      simp
  have hA : A.card = {d ∈ Ioc 0 n | d ∣ n ^ 2 + 1}.card := by
    dsimp [A, T]
    rw [card_filter, Nat.sum_divisorsAntidiagonal (fun d _ => if d ≤ n then (1 : ℕ) else 0), ← card_filter]
    congr 1
    ext d
    simp only [mem_filter, Nat.mem_divisors, mem_Ioc]
    constructor
    · rintro ⟨⟨hd, _⟩, hle⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by positivity), hle⟩, hd⟩
    · rintro ⟨⟨_, hle⟩, hd⟩
      exact ⟨⟨hd, by positivity⟩, hle⟩
  rw [Aux.LinearCount.sigma0_eq_card_antidiagonal]
  change T.card = _
  rw [← hunion, card_union_of_disjoint hdisj, ← hcard, hA, two_mul]

lemma dvd_sq_add_one_iff_zmod (q n : ℕ) : q ∣ n ^ 2 + 1 ↔ (n : ZMod q) ^ 2 = -1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, add_eq_zero_iff_eq_neg]

lemma root_count_error {q : ℕ} (hq : 0 < q) (K : ℕ) :
    |({n ∈ Ioc 0 K | q ∣ n ^ 2 + 1}.card : ℝ) - (K : ℝ) / q * rho q| ≤ 2 * rho q := by
  letI : NeZero q := ⟨hq.ne'⟩
  let R : Finset (ZMod q) := univ.filter (fun r => r ^ 2 = -1)
  have hcard : R.card = rho q := by simp only [rho, Nat.card_eq_fintype_card, Fintype.card_subtype, R]
  have heq : {n ∈ Ioc 0 K | q ∣ n ^ 2 + 1}.card =
      ∑ r ∈ R, {n ∈ Ioc 0 K | n ≡ r.val [MOD q]}.card := by
    have hh := sum_card_fiberwise_eq_card_filter (Ioc 0 K) R (fun n : ℕ => (n : ZMod q))
    have hf (r : ZMod q) : {n ∈ Ioc (0 : ℕ) K | ((n : ℕ) : ZMod q) = r} =
        {n ∈ Ioc 0 K | n ≡ r.val [MOD q]} := by
      ext n
      simp only [mem_filter, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
    simp only [hf, R, mem_filter, mem_univ, true_and, ← dvd_sq_add_one_iff_zmod] at hh
    exact hh.symm
  have hmain : (K : ℝ) / q * R.card = ∑ _r ∈ R, (K : ℝ) / q := by simp [mul_comm]
  rw [heq, Nat.cast_sum, ← hcard, hmain, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _r ∈ R, (2 : ℝ) := by
      apply sum_le_sum
      intro r hr
      obtain ⟨hl, hu⟩ := Aux.LinearCount.residue_count_bounds hq K r.val
      rw [abs_le]
      constructor <;> linarith
    _ = _ := by simp [mul_comm]

def rootCount (q K : ℕ) : ℕ := {n ∈ Ioc 0 K | q ∣ n ^ 2 + 1}.card

def shortDivSum (N : ℕ) : ℕ := ∑ n ∈ Ioc 0 N, {d ∈ Ioc 0 n | d ∣ n ^ 2 + 1}.card

lemma triangular_decomposition (N : ℕ) :
    shortDivSum N + ∑ d ∈ Ioc 0 N, rootCount d (d - 1) = ∑ d ∈ Ioc 0 N, rootCount d N := by
  have heq : shortDivSum N = ∑ d ∈ Ioc 0 N,
      {n ∈ Ioc 0 N | d ≤ n ∧ d ∣ n ^ 2 + 1}.card := by
    unfold shortDivSum
    trans ∑ n ∈ Ioc 0 N, {d ∈ Ioc 0 N | d ≤ n ∧ d ∣ n ^ 2 + 1}.card
    · apply sum_congr rfl
      intro n hn
      congr 1
      ext d
      simp only [mem_filter, mem_Ioc] at *
      omega
    · simp only [card_filter]
      rw [sum_comm]
  rw [heq, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  have hlow : rootCount d (d - 1) = {n ∈ Ioc 0 N | n < d ∧ d ∣ n ^ 2 + 1}.card := by
    unfold rootCount
    congr 1
    ext n
    simp only [mem_filter, mem_Ioc] at *
    omega
  rw [hlow, rootCount, card_filter, card_filter, card_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  by_cases hp : d ∣ n ^ 2 + 1 <;> by_cases hdn : d ≤ n <;> simp [hp, hdn, show n < d ↔ ¬d ≤ n by omega]

lemma shortDivSum_error (N : ℕ) :
    |(shortDivSum N : ℝ) - (N : ℝ) * ∑ d ∈ Ioc 0 N, (rho d : ℝ) / d| ≤ 10 * N := by
  have hrho : ∑ d ∈ Ioc 0 N, (rho d : ℝ) ≤ 2 * N := by exact_mod_cast rho_sum_bound N
  have hb : |(∑ d ∈ Ioc 0 N, (rootCount d N : ℝ)) -
      (N : ℝ) * ∑ d ∈ Ioc 0 N, (rho d : ℝ) / d| ≤ 4 * N := by
    rw [mul_sum, ← sum_sub_distrib]
    calc
      _ ≤ ∑ d ∈ Ioc 0 N, (2 : ℝ) * rho d := by
        apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro d hd
        simpa only [rootCount, mul_div_assoc, div_mul_eq_mul_div, mul_comm (N : ℝ)] using
          root_count_error (mem_Ioc.mp hd).1 N
      _ ≤ 4 * N := by rw [← mul_sum]; linarith
  have he0 : (0 : ℝ) ≤ ∑ d ∈ Ioc 0 N, (rootCount d (d - 1) : ℝ) := by positivity
  have he : ∑ d ∈ Ioc 0 N, (rootCount d (d - 1) : ℝ) ≤ 6 * N := by
    calc
      _ ≤ ∑ d ∈ Ioc 0 N, (3 : ℝ) * rho d := by
        apply sum_le_sum
        intro d hd
        have hh := (abs_le.mp (root_count_error (mem_Ioc.mp hd).1 (d - 1))).2
        have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr (mem_Ioc.mp hd).1
        have hle : ((d - 1 : ℕ) : ℝ) / d ≤ 1 := by
          apply (div_le_one hdR).mpr
          exact_mod_cast Nat.sub_le d 1
        have hh' := mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg (rho d) (α := ℝ))
        change (rootCount d (d - 1) : ℝ) - _ ≤ _ at hh
        linarith
      _ ≤ 6 * N := by rw [← mul_sum]; linarith
  have ht : (shortDivSum N : ℝ) + (∑ d ∈ Ioc 0 N, (rootCount d (d - 1) : ℝ)) =
      ∑ d ∈ Ioc 0 N, (rootCount d N : ℝ) := by exact_mod_cast triangular_decomposition N
  have hh := abs_sub (∑ d ∈ Ioc 0 N, (rootCount d N : ℝ) -
    (N : ℝ) * ∑ d ∈ Ioc 0 N, (rho d : ℝ) / d) (∑ d ∈ Ioc 0 N, (rootCount d (d - 1) : ℝ))
  rw [abs_of_nonneg he0] at hh
  have heq : (∑ d ∈ Ioc 0 N, (rootCount d N : ℝ) -
      (N : ℝ) * ∑ d ∈ Ioc 0 N, (rho d : ℝ) / d) -
      (∑ d ∈ Ioc 0 N, (rootCount d (d - 1) : ℝ)) =
      (shortDivSum N : ℝ) - (N : ℝ) * ∑ d ∈ Ioc 0 N, (rho d : ℝ) / d := by linarith
  rw [heq] at hh
  linarith

lemma sum_sigma0_sq_add_one (N : ℕ) :
    ∑ n ∈ Ioc 0 N, σ 0 (n ^ 2 + 1) = 2 * shortDivSum N := by
  unfold shortDivSum
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  exact sigma0_sq_add_one (mem_Ioc.mp hn).1

lemma shortDivSum_limit_positive :
    ∃ C > (0 : ℝ), Tendsto (fun N : ℕ => (shortDivSum N : ℝ) / (N * log N)) atTop (𝓝 C) := by
  obtain ⟨C, hC, hlim⟩ := rho_harmonic_limit_positive
  refine ⟨C, hC, ?_⟩
  have htlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun N : ℕ => ((shortDivSum N : ℝ) -
      (N : ℝ) * ∑ d ∈ Ioc 0 N, (rho d : ℝ) / d) / (N * log N)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ => 10 / log (N : ℝ))
    · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
      have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
      have hlog : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hNr hlog)]
      calc
        _ ≤ (10 * N) / (N * log (N : ℝ)) :=
          div_le_div_of_nonneg_right (shortDivSum_error N) (mul_pos hNr hlog).le
        _ = 10 / log (N : ℝ) := by field_simp
    · exact tendsto_const_nhds.div_atTop htlog
  have hh := hlim.add he
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlog : log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  field_simp
  ring

lemma Erdos975Sum_sq_add_one_nat (N : ℕ) :
    Erdos975Sum (X ^ 2 + 1) N = 1 + 2 * (shortDivSum N : ℝ) := by
  have he (n : ℕ) : ⌊(X ^ 2 + 1 : ℤ[X]).eval (n : ℤ)⌋₊ = n ^ 2 + 1 := by
    simp only [eval_add, eval_pow, eval_X, eval_one]
    exact_mod_cast (Nat.floor_natCast (R := ℤ) (n ^ 2 + 1))
  simp only [Erdos975Sum, Nat.floor_natCast, he]
  rw [← Nat.cast_sum]
  have hh := sum_Ioc_add_eq_sum_Icc (f := fun n : ℕ => σ 0 (n ^ 2 + 1)) (Nat.zero_le N)
  have heq : ∑ n ∈ Iic N, σ 0 (n ^ 2 + 1) = 1 + 2 * shortDivSum N := by
    rw [sum_sigma0_sq_add_one] at hh
    simpa [add_comm] using hh.symm
  exact_mod_cast heq

end QuadraticRoots

lemma Erdos975Sum_X_sq_add_one_tendsto :
    ∃ C > (0 : ℝ), Tendsto (fun x : ℝ => Erdos975Sum (X ^ 2 + 1) x / (x * log x)) atTop (𝓝 C) := by
  obtain ⟨C, hC, hlim⟩ := QuadraticRoots.shortDivSum_limit_positive
  refine ⟨2 * C, mul_pos (by norm_num) hC, (real_limit_iff_nat_limit _ _).mpr ?_⟩
  have htlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htden : Tendsto (fun N : ℕ => (N : ℝ) * log N) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ htlog
  have hzero : Tendsto (fun N : ℕ => 1 / ((N : ℝ) * log N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop htden
  have hh := hzero.add (hlim.const_mul 2)
  simpa only [zero_add, QuadraticRoots.Erdos975Sum_sq_add_one_nat, add_div, mul_div_assoc] using hh

namespace GeneralDivisors

open Finset

def halfDivisorCount (m : ℕ) : ℕ := {d ∈ m.divisors | d * d ≤ m}.card

lemma sigma0_halfDivisorCount (m : ℕ) :
    σ 0 m ≤ 2 * halfDivisorCount m ∧ 2 * halfDivisorCount m ≤ σ 0 m + 1 := by
  let T := m.divisorsAntidiagonal
  let A := T.filter (fun p => p.1 ≤ p.2)
  let B := T.filter (fun p => p.2 ≤ p.1)
  have hunion : A ∪ B = T := by
    ext p
    simp only [A, B, mem_union, mem_filter]
    have h := le_total p.1 p.2
    tauto
  have hcard : A.card = B.card := by
    apply card_nbij' Prod.swap Prod.swap
    · intro p hp
      simpa [A, B, T, Nat.swap_mem_divisorsAntidiagonal, mul_comm] using hp
    · intro p hp
      simpa [A, B, T, Nat.swap_mem_divisorsAntidiagonal, mul_comm] using hp
    · intro p hp
      simp
    · intro p hp
      simp
  have hinter : (A ∩ B).card ≤ 1 := by
    apply card_le_one.mpr
    intro p hp q hq
    simp only [A, B, mem_inter, mem_filter] at hp hq
    have hpdiag : p.1 = p.2 := le_antisymm hp.1.2 hp.2.2
    have hqdiag : q.1 = q.2 := le_antisymm hq.1.2 hq.2.2
    have hpeq := (Nat.mem_divisorsAntidiagonal.mp hp.1.1).1
    have hqeq := (Nat.mem_divisorsAntidiagonal.mp hq.1.1).1
    have heq : p.1 * p.1 = q.1 * q.1 := by nlinarith [hpeq, hqeq]
    have hf : p.1 = q.1 := by nlinarith
    exact Prod.ext hf (by omega)
  have hA : A.card = halfDivisorCount m := by
    dsimp [A, T, halfDivisorCount]
    rw [card_filter, Nat.sum_divisorsAntidiagonal (fun d e => if d ≤ e then (1 : ℕ) else 0), card_filter]
    apply sum_congr rfl
    intro d hd
    simp only [Nat.le_div_iff_mul_le (Nat.pos_of_mem_divisors hd)]
  have hh := card_union_add_card_inter A B
  rw [hunion, ← hcard, hA] at hh
  rw [Aux.LinearCount.sigma0_eq_card_antidiagonal]
  change T.card ≤ _ ∧ _ ≤ T.card + 1
  omega

lemma sigma0_halfDivisorCount_error (m : ℕ) :
    |(σ 0 m : ℝ) - 2 * halfDivisorCount m| ≤ 1 := by
  obtain ⟨h1, h2⟩ := sigma0_halfDivisorCount m
  have h1r : (σ 0 m : ℝ) ≤ 2 * halfDivisorCount m := by exact_mod_cast h1
  have h2r : (2 : ℝ) * halfDivisorCount m ≤ σ 0 m + 1 := by exact_mod_cast h2
  rw [abs_le]
  constructor <;> linarith

noncomputable def halfSum (f : ℤ[X]) (N : ℕ) : ℝ :=
  ∑ n ∈ Iic N, (halfDivisorCount ⌊f.eval (n : ℤ)⌋₊ : ℝ)

lemma halfSum_error (f : ℤ[X]) (N : ℕ) :
    |Erdos975Sum f N - 2 * halfSum f N| ≤ N + 1 := by
  simp only [Erdos975Sum, Nat.floor_natCast, halfSum, mul_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ _n ∈ Iic N, (1 : ℝ) :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun n _ => sigma0_halfDivisorCount_error _))
    _ = _ := by simp

lemma halfSum_error_tendsto (f : ℤ[X]) :
    Tendsto (fun N : ℕ => (Erdos975Sum f N - 2 * halfSum f N) / ((N : ℝ) * log N))
      atTop (𝓝 0) := by
  have htlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero_norm' (a := fun N : ℕ => 2 / log (N : ℝ))
  · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
    have hlog : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hNr hlog)]
    calc
      _ ≤ (2 * N) / ((N : ℝ) * log N) := div_le_div_of_nonneg_right
        ((halfSum_error f N).trans (by linarith)) (mul_pos hNr hlog).le
      _ = 2 / log (N : ℝ) := by field_simp
  · exact tendsto_const_nhds.div_atTop htlog

lemma halfSum_limit_iff (f : ℤ[X]) (c : ℝ) :
    Tendsto (fun N : ℕ => halfSum f N / ((N : ℝ) * log N)) atTop (𝓝 c) ↔
      Tendsto (fun x : ℝ => Erdos975Sum f x / (x * log x)) atTop (𝓝 (2 * c)) := by
  rw [real_limit_iff_nat_limit]
  constructor
  · intro h
    have hh := (h.const_mul 2).add (halfSum_error_tendsto f)
    simpa only [add_zero, ← mul_div_assoc, ← add_div, add_sub_cancel] using hh
  · intro h
    have hh := (h.sub (halfSum_error_tendsto f)).div_const 2
    simp only [sub_zero, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at hh
    convert hh using 1
    ext N
    ring

lemma positive_limit_iff_halfSum (f : ℤ[X]) :
    (∃ c > (0 : ℝ), Tendsto (fun x : ℝ => Erdos975Sum f x / (x * log x)) atTop (𝓝 c)) ↔
      ∃ c > (0 : ℝ), Tendsto (fun N : ℕ => halfSum f N / ((N : ℝ) * log N)) atTop (𝓝 c) := by
  constructor
  · rintro ⟨c, hc, hlim⟩
    refine ⟨c / 2, div_pos hc (by norm_num), (halfSum_limit_iff f (c / 2)).mpr ?_⟩
    convert hlim using 1
    congr 1
    ring
  · rintro ⟨c, hc, hlim⟩
    exact ⟨2 * c, mul_pos (by norm_num) hc, (halfSum_limit_iff f c).mp hlim⟩

noncomputable def polynomialRootCount (f : ℤ[X]) (q : ℕ) : ℕ :=
  Nat.card {r : ZMod q // f.eval₂ (Int.castRingHom (ZMod q)) r = 0}

def divisibleValueCount (f : ℤ[X]) (q N : ℕ) : ℕ :=
  {n ∈ Ioc 0 N | (q : ℤ) ∣ f.eval ((n : ℕ) : ℤ)}.card

lemma dvd_eval_iff_zmod (f : ℤ[X]) (q n : ℕ) :
    (q : ℤ) ∣ f.eval (n : ℤ) ↔ f.eval₂ (Int.castRingHom (ZMod q)) (n : ZMod q) = 0 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have heq := Polynomial.eval₂_at_apply (p := f) (Int.castRingHom (ZMod q)) (n : ℤ)
  simpa using congrArg (fun x : ZMod q => x = 0) heq.symm

lemma polynomial_root_count_error (f : ℤ[X]) {q : ℕ} (hq : 0 < q) (N : ℕ) :
    |(divisibleValueCount f q N : ℝ) - (N : ℝ) / q * polynomialRootCount f q| ≤
      2 * polynomialRootCount f q := by
  letI : NeZero q := ⟨hq.ne'⟩
  let R : Finset (ZMod q) := univ.filter (fun r => f.eval₂ (Int.castRingHom (ZMod q)) r = 0)
  have hcard : R.card = polynomialRootCount f q := by
    simp only [polynomialRootCount, Nat.card_eq_fintype_card, Fintype.card_subtype, R]
  have heq : divisibleValueCount f q N =
      ∑ r ∈ R, {n ∈ Ioc 0 N | n ≡ r.val [MOD q]}.card := by
    have hh := sum_card_fiberwise_eq_card_filter (Ioc 0 N) R (fun n : ℕ => (n : ZMod q))
    have hf (r : ZMod q) : {n ∈ Ioc (0 : ℕ) N | ((n : ℕ) : ZMod q) = r} =
        {n ∈ Ioc 0 N | n ≡ r.val [MOD q]} := by
      ext n
      simp only [mem_filter, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
    simp only [hf, R, mem_filter, mem_univ, true_and, ← dvd_eval_iff_zmod] at hh
    exact hh.symm
  have hmain : (N : ℝ) / q * R.card = ∑ _r ∈ R, (N : ℝ) / q := by simp [mul_comm]
  rw [heq, Nat.cast_sum, ← hcard, hmain, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _r ∈ R, (2 : ℝ) := by
      apply sum_le_sum
      intro r hr
      obtain ⟨hl, hu⟩ := Aux.LinearCount.residue_count_bounds hq N r.val
      rw [abs_le]
      constructor <;> linarith
    _ = _ := by simp [mul_comm]

lemma polynomial_root_density (f : ℤ[X]) {q : ℕ} (hq : 0 < q) :
    Tendsto (fun N : ℕ => (divisibleValueCount f q N : ℝ) / N) atTop
      (𝓝 ((polynomialRootCount f q : ℝ) / q)) := by
  have he : Tendsto (fun N : ℕ => ((divisibleValueCount f q N : ℝ) -
      (N : ℝ) / q * polynomialRootCount f q) / N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ => (2 * polynomialRootCount f q : ℝ) / N)
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
      have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hNr]
      exact div_le_div_of_nonneg_right (polynomial_root_count_error f hq N) hNr.le
    · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := he.add_const ((polynomialRootCount f q : ℝ) / q)
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hqr : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  field_simp
  ring

noncomputable def truncatedDivisorSum (f : ℤ[X]) (N Y : ℕ) : ℝ :=
  ∑ q ∈ Ioc 0 Y, (divisibleValueCount f q N : ℝ)

lemma truncatedDivisorSum_error (f : ℤ[X]) (N Y : ℕ) :
    |truncatedDivisorSum f N Y - (N : ℝ) *
      ∑ q ∈ Ioc 0 Y, (polynomialRootCount f q : ℝ) / q| ≤
      2 * ∑ q ∈ Ioc 0 Y, (polynomialRootCount f q : ℝ) := by
  simp only [truncatedDivisorSum, mul_sum, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro q hq
  simpa only [mul_div_assoc, div_mul_eq_mul_div, mul_comm (N : ℝ)] using
    polynomial_root_count_error f (mem_Ioc.mp hq).1 N

lemma truncatedDivisorSum_limit (f : ℤ[X]) (Y : ℕ → ℕ) (c : ℝ)
    (hcount : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 (Y N), (polynomialRootCount f q : ℝ)) / ((N : ℝ) * log N)) atTop (𝓝 0))
    (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 (Y N), (polynomialRootCount f q : ℝ) / q) / log N) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ => truncatedDivisorSum f N (Y N) / ((N : ℝ) * log N)) atTop (𝓝 c) := by
  have he : Tendsto (fun N : ℕ => (truncatedDivisorSum f N (Y N) - (N : ℝ) *
      ∑ q ∈ Ioc 0 (Y N), (polynomialRootCount f q : ℝ) / q) / ((N : ℝ) * log N))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ => 2 *
      ((∑ q ∈ Ioc 0 (Y N), (polynomialRootCount f q : ℝ)) / ((N : ℝ) * log N)))
    · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
      have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
      have hlog : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hNr hlog), ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (truncatedDivisorSum_error f N (Y N)) (mul_pos hNr hlog).le
    · simpa only [mul_zero] using hcount.const_mul 2
  have hh := hmean.add he
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlog : log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  field_simp
  ring

/-- A sufficient condition for the conjectured asymptotic. The third limit is the
contribution not accounted for by the chosen uniform divisor cutoff. -/
lemma limit_of_root_count_and_remainder (f : ℤ[X]) (Y : ℕ → ℕ) (a b : ℝ)
    (hpos : 0 < a + b)
    (hcount : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 (Y N), (polynomialRootCount f q : ℝ)) / ((N : ℝ) * log N)) atTop (𝓝 0))
    (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 (Y N), (polynomialRootCount f q : ℝ) / q) / log N) atTop (𝓝 a))
    (hrem : Tendsto (fun N : ℕ => (halfSum f N - truncatedDivisorSum f N (Y N)) /
      ((N : ℝ) * log N)) atTop (𝓝 b)) :
    ∃ c > (0 : ℝ), Tendsto (fun x : ℝ => Erdos975Sum f x / (x * log x)) atTop (𝓝 c) := by
  apply (positive_limit_iff_halfSum f).mpr
  refine ⟨a + b, hpos, ?_⟩
  have hh := (truncatedDivisorSum_limit f Y a hcount hmean).add hrem
  simpa only [← add_div, add_sub_cancel] using hh

end GeneralDivisors
namespace MeanTransfer

open Finset Asymptotics

lemma harmonic_range (N : ℕ) : ∑ i ∈ range N, (1 : ℝ) / (i + 1) = (harmonic N : ℝ) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Rat.cast_add, Rat.cast_one,
    one_div, Nat.cast_add, Nat.cast_one]

lemma harmonic_tendsto_atTop : Tendsto (fun N : ℕ => (harmonic N : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono _ (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  intro N
  simpa using log_le_harmonic_floor (N : ℝ) (Nat.cast_nonneg N)

lemma harmonic_log_limit : Tendsto (fun N : ℕ => (harmonic N : ℝ) / log N) atTop (𝓝 1) := by
  simpa only [Nat.div_one] using QuadraticRoots.nat_div_harmonic_log_limit (by norm_num : 0 < 1)

lemma weighted_cesaro {u : ℕ → ℝ} {c : ℝ} (hu : Tendsto u atTop (𝓝 c)) :
    Tendsto (fun N : ℕ => (∑ i ∈ range N, u i / (i + 1)) / log N) atTop (𝓝 c) := by
  have ho : (fun i : ℕ => (u i - c) / (i + 1)) =o[atTop] fun i : ℕ => 1 / ((i : ℝ) + 1) := by
    have hh := ((isLittleO_one_iff ℝ).mpr (tendsto_sub_nhds_zero_iff.mpr hu)).mul_isBigO
      (isBigO_refl (fun i : ℕ => 1 / ((i : ℝ) + 1)) atTop)
    simpa only [one_mul, mul_one_div] using hh
  have hs := ho.sum_range (fun i => by positivity) (by simpa only [harmonic_range] using harmonic_tendsto_atTop)
  have hz := hs.tendsto_div_nhds_zero.mul harmonic_log_limit
  simp only [zero_mul, harmonic_range] at hz
  have hz' : Tendsto (fun N : ℕ => (∑ i ∈ range N, (u i - c) / (i + 1)) / log N)
      atTop (𝓝 0) := by
    apply hz.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hH : (harmonic N : ℝ) ≠ 0 := by exact_mod_cast (harmonic_pos hN.ne').ne'
    rw [div_mul_div_cancel₀ hH]
  have hh := hz'.add (harmonic_log_limit.const_mul c)
  simp only [zero_add, mul_one] at hh
  convert hh using 1
  ext N
  rw [← harmonic_range, ← mul_div_assoc, ← add_div, mul_sum, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro i hi
  ring

lemma weighted_partial_summation (u : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ range N, u i / (i + 1) = (∑ i ∈ range N, u i) / N +
      ∑ i ∈ range N, ((∑ j ∈ range i, u j) / (i : ℝ)) / (i + 1) := by
  cases N with
  | zero => simp
  | succ N =>
    have heq := sum_range_by_parts (fun i : ℕ => (1 : ℝ) / (i + 1)) u (N + 1)
    simp only [smul_eq_mul, Nat.add_sub_cancel, one_div, inv_mul_eq_div] at heq
    rw [heq, sum_range_succ' (fun i : ℕ => ((∑ j ∈ range i, u j) / (i : ℝ)) / (i + 1))]
    simp only [sum_range_zero, Nat.cast_zero, div_zero, zero_div, add_zero, Nat.cast_add, Nat.cast_one]
    rw [sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    apply sum_congr rfl
    intro i hi
    have hi1 : (i : ℝ) + 1 ≠ 0 := by positivity
    have hi2 : (i : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp
    ring

lemma logarithmic_mean_of_mean {u : ℕ → ℝ} {c : ℝ}
    (hu : Tendsto (fun N : ℕ => (∑ i ∈ range N, u i) / (N : ℝ)) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ => (∑ i ∈ range N, u i / (i + 1)) / log N) atTop (𝓝 c) := by
  have htlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := (hu.div_atTop htlog).add (weighted_cesaro hu)
  simpa only [zero_add, ← add_div, ← weighted_partial_summation] using hh

lemma logarithmic_mean_Ioc_of_mean {u : ℕ → ℝ} {c : ℝ}
    (hu : Tendsto (fun N : ℕ => (∑ i ∈ Ioc 0 N, u i) / (N : ℝ)) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ => (∑ i ∈ Ioc 0 N, u i / i) / log N) atTop (𝓝 c) := by
  have heq (v : ℕ → ℝ) (N : ℕ) : ∑ i ∈ Ioc 0 N, v i = ∑ i ∈ range N, v (i + 1) := by
    rw [show Ioc 0 N = Ico 1 (N + 1) by ext i; simp only [mem_Ioc, mem_Ico]; omega,
      sum_Ico_eq_sum_range]
    simp [add_comm]
  simp only [heq] at hu ⊢
  simpa only [Nat.cast_add, Nat.cast_one] using logarithmic_mean_of_mean hu

open scoped nonZeroDivisors
open Ideal NumberField

lemma ideal_count_mean (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Ioc 0 N, (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ)) / N)
      atTop (𝓝 (NumberField.dedekindZeta_residue K)) := by
  refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
    (fun N => ?_)
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← _root_.Ideal.card_norm_le_eq_card_norm_le_add_one,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (N.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => finite_setOf_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

lemma ideal_harmonic_mean (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Ioc 0 N, (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ) / n) / log N)
      atTop (𝓝 (NumberField.dedekindZeta_residue K)) :=
  logarithmic_mean_Ioc_of_mean (ideal_count_mean K)

end MeanTransfer
namespace GeneralDivisors

lemma truncatedDivisorSum_limit_of_root_mean (f : ℤ[X]) (a : ℝ)
    (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Finset.Ioc 0 N, (polynomialRootCount f q : ℝ)) / N) atTop (𝓝 a)) :
    Tendsto (fun N : ℕ => truncatedDivisorSum f N N / ((N : ℝ) * log N)) atTop (𝓝 a) := by
  apply truncatedDivisorSum_limit f id a
  · have htlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    simpa only [id_eq, div_div] using hmean.div_atTop htlog
  · exact MeanTransfer.logarithmic_mean_Ioc_of_mean hmean

/-- Given the ordinary mean of the modular root counts, the conjecture is equivalent
 to convergence of the remainder after divisors up to `N` have been counted. -/
lemma positive_limit_iff_remainder (f : ℤ[X]) (a : ℝ)
    (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Finset.Ioc 0 N, (polynomialRootCount f q : ℝ)) / N) atTop (𝓝 a)) :
    (∃ c > (0 : ℝ), Tendsto (fun x : ℝ => Erdos975Sum f x / (x * log x)) atTop (𝓝 c)) ↔
      ∃ b : ℝ, 0 < a + b ∧ Tendsto (fun N : ℕ =>
        (halfSum f N - truncatedDivisorSum f N N) / ((N : ℝ) * log N)) atTop (𝓝 b) := by
  rw [positive_limit_iff_halfSum]
  have ht := truncatedDivisorSum_limit_of_root_mean f a hmean
  constructor
  · rintro ⟨c, hc, hlim⟩
    refine ⟨c - a, by linarith, ?_⟩
    simpa only [sub_div] using hlim.sub ht
  · rintro ⟨b, hab, hlim⟩
    refine ⟨a + b, hab, ?_⟩
    simpa only [← add_div, add_sub_cancel] using ht.add hlim

end GeneralDivisors
namespace MeanTransfer

open Finset

lemma convolution_mean (f g : ArithmeticFunction ℝ) {a : ℝ}
    (hf : Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, f n) / (N : ℝ)) atTop (𝓝 a))
    (hg : Summable (fun n : ℕ => g n / (n : ℝ))) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, (g * f) n) / (N : ℝ)) atTop
      (𝓝 (a * ∑' n : ℕ, g n / (n : ℝ))) := by
  let A : ℕ → ℝ := fun N => ∑ n ∈ Ioc 0 N, f n
  have hA0 : A 0 = 0 := by simp [A]
  obtain ⟨M, hM⟩ := hf.norm.bddAbove_range
  have hbound (N : ℕ) : |A N| ≤ M * N := by
    have hb : ‖A N / (N : ℝ)‖ ≤ M := hM (Set.mem_range_self N)
    by_cases hN : N = 0
    · simp [hN, hA0]
    · have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hNr, div_le_iff₀ hNr] at hb
      exact hb
  have hM0 : 0 ≤ M := by
    have hb := hM (Set.mem_range_self 0)
    simpa using hb
  have hpoint (d : ℕ) : Tendsto (fun N : ℕ => g d * A (N / d) / (N : ℝ)) atTop
      (𝓝 (a * (g d / (d : ℝ)))) := by
    by_cases hd : d = 0
    · subst d
      simp only [ArithmeticFunction.map_zero, zero_mul, zero_div, mul_zero]
      exact tendsto_const_nhds
    · have h1 := hf.comp (Nat.tendsto_div_const_atTop hd)
      have h2 := QuadraticRoots.nat_div_ratio_limit d
      have hh := (h1.mul h2).const_mul (g d)
      have hlim : g d * (a * (1 / (d : ℝ))) = a * (g d / (d : ℝ)) := by ring
      rw [hlim] at hh
      apply hh.congr'
      filter_upwards [eventually_ge_atTop d] with N hN
      have hK : (0 : ℝ) < (N / d : ℕ) := by
        exact_mod_cast Nat.div_pos hN (Nat.pos_of_ne_zero hd)
      change g d * (A (N / d) / (N / d : ℕ) * ((N / d : ℕ) / (N : ℝ))) = _
      rw [div_mul_div_cancel₀ hK.ne', mul_div_assoc]
  have hh := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (hg.norm.mul_left M) hpoint ?_
  · simp only [tsum_mul_left] at hh
    apply hh.congr'
    filter_upwards [] with N
    rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum, sum_div]
    exact tsum_eq_sum (fun d hd => by
      by_cases hd0 : d = 0
      · simp [hd0]
      · have hNd : N < d := by simpa [mem_Ioc, Nat.pos_of_ne_zero hd0] using hd
        simp [Nat.div_eq_of_lt hNd, hA0])
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN d
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    by_cases hd : d = 0
    · subst d
      simp
    · have hdr : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd)
      have hcast : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
      calc
        ‖g d * A (N / d) / (N : ℝ)‖ = |g d| * |A (N / d)| / N := by
          rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hNr]
        _ ≤ |g d| * (M * ((N : ℝ) / d)) / N := by
          apply div_le_div_of_nonneg_right _ hNr.le
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact (hbound (N / d)).trans (mul_le_mul_of_nonneg_left hcast hM0)
        _ = M * ‖g d / (d : ℝ)‖ := by
          rw [Real.norm_eq_abs, abs_div, abs_of_pos hdr]
          field_simp

end MeanTransfer
namespace GeneralDivisors

lemma map_int_eval {R S : Type*} [Ring R] [Ring S] (f : ℤ[X]) (g : R →+* S) (x : R) :
    g (f.eval₂ (Int.castRingHom R) x) = f.eval₂ (Int.castRingHom S) (g x) := by
  rw [Polynomial.hom_eval₂, RingHom.ext_int (g.comp (Int.castRingHom R)) (Int.castRingHom S)]

noncomputable def polynomialRootsEquiv {R S : Type*} [Ring R] [Ring S]
    (f : ℤ[X]) (e : R ≃+* S) :
    {x : R // f.eval₂ (Int.castRingHom R) x = 0} ≃
      {x : S // f.eval₂ (Int.castRingHom S) x = 0} :=
  e.toEquiv.subtypeEquiv fun x => by
    constructor
    · intro h
      change f.eval₂ (Int.castRingHom S) (e.toRingHom x) = 0
      rw [← map_int_eval f e.toRingHom, h, map_zero]
    · intro h
      apply e.injective
      change e.toRingHom (f.eval₂ (Int.castRingHom R) x) = e.toRingHom 0
      rw [map_int_eval f e.toRingHom, map_zero]
      exact h

noncomputable def polynomialRootsProdEquiv (f : ℤ[X]) (R S : Type*) [Ring R] [Ring S] :
    {x : R × S // f.eval₂ (Int.castRingHom (R × S)) x = 0} ≃
      ({x : R // f.eval₂ (Int.castRingHom R) x = 0} ×
        {x : S // f.eval₂ (Int.castRingHom S) x = 0}) where
  toFun x := (⟨x.1.1, by
    have hh := congrArg (RingHom.fst R S) x.2
    simpa only [map_int_eval, map_zero] using hh⟩,
    ⟨x.1.2, by
      have hh := congrArg (RingHom.snd R S) x.2
      simpa only [map_int_eval, map_zero] using hh⟩)
  invFun x := ⟨(x.1.1, x.2.1), by
    apply Prod.ext
    · change (RingHom.fst R S) _ = 0
      rw [map_int_eval]
      exact x.1.2
    · change (RingHom.snd R S) _ = 0
      rw [map_int_eval]
      exact x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma polynomialRootCount_mul (f : ℤ[X]) {m n : ℕ} (h : m.Coprime n) :
    polynomialRootCount f (m * n) = polynomialRootCount f m * polynomialRootCount f n := by
  unfold polynomialRootCount
  rw [Nat.card_congr ((polynomialRootsEquiv f (ZMod.chineseRemainder h)).trans
    (polynomialRootsProdEquiv f (ZMod m) (ZMod n))), Nat.card_prod]

lemma polynomialRootCount_one (f : ℤ[X]) : polynomialRootCount f 1 = 1 := by
  have h (r : ZMod 1) : f.eval₂ (Int.castRingHom (ZMod 1)) r = 0 := Subsingleton.elim _ _
  simp [polynomialRootCount, Nat.card_eq_fintype_card, Fintype.card_subtype, h]

noncomputable def rootFunction (f : ℤ[X]) : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else polynomialRootCount f n
  map_zero' := rfl

lemma rootFunction_apply (f : ℤ[X]) {n : ℕ} (hn : n ≠ 0) :
    rootFunction f n = (polynomialRootCount f n : ℝ) := by simp [rootFunction, hn]

lemma rootFunction_multiplicative (f : ℤ[X]) : (rootFunction f).IsMultiplicative := by
  constructor
  · simp [rootFunction_apply, polynomialRootCount_one]
  · intro m n hmn
    by_cases hm : m = 0
    · subst m
      simp
    by_cases hn : n = 0
    · subst n
      simp
    simp only [rootFunction_apply f hm, rootFunction_apply f hn,
      rootFunction_apply f (mul_ne_zero hm hn), polynomialRootCount_mul f hmn, Nat.cast_mul]

lemma primitive_map_zmod_ne_zero {f : ℤ[X]} (hf : f.IsPrimitive) {q : ℕ} (hq : q ≠ 1) :
    f.map (Int.castRingHom (ZMod q)) ≠ 0 := by
  intro hz
  have hd : C (q : ℤ) ∣ f := by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro i
    have heq := congrArg (fun g : (ZMod q)[X] => g.coeff i) hz
    simp only [coeff_map, coeff_zero] at heq
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp heq
  have hu := Int.isUnit_iff_natAbs_eq.mp (hf (q : ℤ) hd)
  exact hq (by simpa using hu)

lemma polynomialRootCount_prime_le {f : ℤ[X]} (hf : f.IsPrimitive) {p : ℕ} (hp : p.Prime) :
    polynomialRootCount f p ≤ f.natDegree := by
  letI : Fact p.Prime := ⟨hp⟩
  have hmap := primitive_map_zmod_ne_zero hf hp.ne_one
  unfold polynomialRootCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hset : (Finset.univ.filter (fun r : ZMod p => f.eval₂ (Int.castRingHom (ZMod p)) r = 0)) =
      (f.map (Int.castRingHom (ZMod p))).roots.toFinset := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Multiset.mem_toFinset,
      Polynomial.mem_roots hmap, Polynomial.IsRoot.def, Polynomial.eval_map]
  rw [hset]
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots_map_le_natDegree f)

end GeneralDivisors
namespace MeanTransfer

open NumberField
noncomputable def idealNormFunction (K : Type*) [Field K] [NumberField K] : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  map_zero' := rfl

lemma idealNormFunction_mean (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Ioc 0 N, idealNormFunction K n) / N) atTop
      (𝓝 (NumberField.dedekindZeta_residue K)) := by
  apply (ideal_count_mean K).congr
  intro N
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  simp only [idealNormFunction, ArithmeticFunction.coe_mk, if_neg (Finset.mem_Ioc.mp hn).1.ne']

end MeanTransfer

namespace GeneralDivisors

lemma root_mean_of_ideal_convolution (f : ℤ[X]) (K : Type*) [Field K] [NumberField K]
    (g : ArithmeticFunction ℝ) (heq : rootFunction f = g * MeanTransfer.idealNormFunction K)
    (hg : Summable (fun n : ℕ => g n / (n : ℝ))) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Ioc 0 N, (polynomialRootCount f n : ℝ)) / N) atTop
      (𝓝 (NumberField.dedekindZeta_residue K * ∑' n : ℕ, g n / (n : ℝ))) := by
  have hh := MeanTransfer.convolution_mean (MeanTransfer.idealNormFunction K) g
    (MeanTransfer.idealNormFunction_mean K) hg
  rw [← heq] at hh
  apply hh.congr
  intro N
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact rootFunction_apply f (Finset.mem_Ioc.mp hn).1.ne'

end GeneralDivisors
namespace GeneralDivisors

lemma isUnit_of_map_of_square_zero {R S : Type*} [CommRing R] [CommRing S]
    (φ : S →+* R) (hφ : Function.Surjective φ)
    (hker : ∀ x : S, φ x = 0 → x ^ 2 = 0) {x : S} (hx : IsUnit (φ x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨y, hy⟩ := hφ (↑u⁻¹)
  have hzero : φ (x * y - 1) = 0 := by
    rw [map_sub, map_mul, map_one, ← hu, hy]
    simp
  have hnil : IsNilpotent (x * y - 1) := ⟨2, hker _ hzero⟩
  have hunit : IsUnit (x * y) := by simpa using hnil.isUnit_add_one
  exact isUnit_of_mul_isUnit_left hunit

lemma int_eval_add_of_sq_eq_zero {R : Type*} [CommRing R] (f : ℤ[X]) (x y : R) (hy : y ^ 2 = 0) :
    f.eval₂ (Int.castRingHom R) (x + y) = f.eval₂ (Int.castRingHom R) x +
      f.derivative.eval₂ (Int.castRingHom R) x * y := by
  simpa only [Polynomial.eval_map, Polynomial.derivative_map] using
    Polynomial.eval_add_of_sq_eq_zero (f.map (Int.castRingHom R)) x y hy

lemma existsUnique_root_lift_of_square_zero {R S : Type*} [CommRing R] [CommRing S]
    (f : ℤ[X]) (φ : S →+* R) (hφ : Function.Surjective φ)
    (hker : ∀ x : S, φ x = 0 → x ^ 2 = 0) (r : R)
    (hr : f.eval₂ (Int.castRingHom R) r = 0)
    (hder : IsUnit (f.derivative.eval₂ (Int.castRingHom R) r)) :
    ∃! x : S, φ x = r ∧ f.eval₂ (Int.castRingHom S) x = 0 := by
  obtain ⟨x, hx⟩ := hφ r
  have heval : φ (f.eval₂ (Int.castRingHom S) x) = 0 := by rw [map_int_eval, hx, hr]
  have hunit : IsUnit (f.derivative.eval₂ (Int.castRingHom S) x) := by
    apply isUnit_of_map_of_square_zero φ hφ hker
    rwa [map_int_eval, hx]
  obtain ⟨u, hu⟩ := hunit
  let b : S := ↑u⁻¹
  have hb : f.derivative.eval₂ (Int.castRingHom S) x * b = 1 := by rw [← hu]; simp [b]
  let ε : S := -(f.eval₂ (Int.castRingHom S) x) * b
  have hε : φ ε = 0 := by simp only [ε, map_mul, map_neg, heval, neg_zero, zero_mul]
  refine ⟨x + ε, ⟨by simp only [map_add, hx, hε, add_zero], ?_⟩, ?_⟩
  · rw [int_eval_add_of_sq_eq_zero f x ε (hker ε hε)]
    dsimp only [ε]
    linear_combination -(f.eval₂ (Int.castRingHom S) x) * hb
  · intro y hy
    have hδ : φ (y - x) = 0 := by rw [map_sub, hy.1, hx, sub_self]
    have ht := int_eval_add_of_sq_eq_zero f x (y - x) (hker _ hδ)
    rw [add_sub_cancel, hy.2] at ht
    dsimp only [ε]
    linear_combination -b * ht - (y - x) * hb

noncomputable def rootReduction {R S : Type*} [CommRing R] [CommRing S]
    (f : ℤ[X]) (φ : S →+* R) :
    {x : S // f.eval₂ (Int.castRingHom S) x = 0} →
      {x : R // f.eval₂ (Int.castRingHom R) x = 0} :=
  fun x => ⟨φ x.1, by rw [← map_int_eval, x.2, map_zero]⟩

lemma rootReduction_bijective {R S : Type*} [CommRing R] [CommRing S]
    (f : ℤ[X]) (φ : S →+* R) (hφ : Function.Surjective φ)
    (hker : ∀ x : S, φ x = 0 → x ^ 2 = 0)
    (hsimple : ∀ r : R, f.eval₂ (Int.castRingHom R) r = 0 →
      IsUnit (f.derivative.eval₂ (Int.castRingHom R) r)) :
    Function.Bijective (rootReduction f φ) := by
  constructor
  · intro x y hxy
    have heq : φ x.1 = φ y.1 := congrArg Subtype.val hxy
    obtain ⟨z, hz, huniq⟩ := existsUnique_root_lift_of_square_zero f φ hφ hker (φ y.1)
      (rootReduction f φ y).2 (hsimple _ (rootReduction f φ y).2)
    apply Subtype.ext
    exact (huniq x.1 ⟨heq, x.2⟩).trans (huniq y.1 ⟨rfl, y.2⟩).symm
  · intro r
    obtain ⟨x, hx, -⟩ := existsUnique_root_lift_of_square_zero f φ hφ hker r.1 r.2 (hsimple _ r.2)
    exact ⟨⟨x, hx.2⟩, Subtype.ext hx.1⟩

lemma simple_roots_lift_of_square_zero {R S : Type*} [CommRing R] [CommRing S]
    (f : ℤ[X]) (φ : S →+* R) (hφ : Function.Surjective φ)
    (hker : ∀ x : S, φ x = 0 → x ^ 2 = 0)
    (hsimple : ∀ r : R, f.eval₂ (Int.castRingHom R) r = 0 →
      IsUnit (f.derivative.eval₂ (Int.castRingHom R) r)) :
    ∀ x : S, f.eval₂ (Int.castRingHom S) x = 0 →
      IsUnit (f.derivative.eval₂ (Int.castRingHom S) x) := by
  intro x hx
  apply isUnit_of_map_of_square_zero φ hφ hker
  rw [map_int_eval]
  apply hsimple
  rw [← map_int_eval, hx, map_zero]

lemma zmod_square_zero_kernel {m n : ℕ} [NeZero n] (hmn : m ∣ n) (hnm : n ∣ m ^ 2)
    (x : ZMod n) (hx : ZMod.castHom hmn (ZMod m) x = 0) : x ^ 2 = 0 := by
  have hval : (x.val : ZMod m) = 0 := by
    calc
      _ = ZMod.castHom hmn (ZMod m) (x.val : ZMod n) := (map_natCast _ _).symm
      _ = ZMod.castHom hmn (ZMod m) x := by rw [ZMod.natCast_zmod_val]
      _ = 0 := hx
  have hd : m ∣ x.val := (ZMod.natCast_eq_zero_iff _ _).mp hval
  have hdiv : n ∣ x.val ^ 2 := hnm.trans (pow_dvd_pow_of_dvd hd 2)
  have heq : (x.val : ZMod n) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact hdiv
  simpa only [ZMod.natCast_zmod_val] using heq

lemma polynomialRootCount_pow_and_simple (f : ℤ[X]) {q : ℕ} (hq : 0 < q)
    (hsimple : ∀ r : ZMod q, f.eval₂ (Int.castRingHom (ZMod q)) r = 0 →
      IsUnit (f.derivative.eval₂ (Int.castRingHom (ZMod q)) r)) (k : ℕ) :
    polynomialRootCount f (q ^ (k + 1)) = polynomialRootCount f q ∧
      ∀ r : ZMod (q ^ (k + 1)), f.eval₂ (Int.castRingHom (ZMod (q ^ (k + 1)))) r = 0 →
        IsUnit (f.derivative.eval₂ (Int.castRingHom (ZMod (q ^ (k + 1)))) r) := by
  induction k with
  | zero =>
    rw [show q ^ (0 + 1) = q by simp]
    exact ⟨rfl, hsimple⟩
  | succ k ih =>
    have hd : q ^ (k + 1) ∣ q ^ (k + 1 + 1) := pow_dvd_pow q (by omega)
    have hd' : q ^ (k + 1 + 1) ∣ (q ^ (k + 1)) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow q (by omega)
    letI : NeZero (q ^ (k + 1 + 1)) := ⟨pow_ne_zero _ hq.ne'⟩
    let φ : ZMod (q ^ (k + 1 + 1)) →+* ZMod (q ^ (k + 1)) := ZMod.castHom hd _
    have hφ : Function.Surjective φ := ZMod.castHom_surjective hd
    have hker : ∀ x, φ x = 0 → x ^ 2 = 0 := zmod_square_zero_kernel hd hd'
    refine ⟨?_, simple_roots_lift_of_square_zero f φ hφ hker ih.2⟩
    calc
      polynomialRootCount f (q ^ (k + 1 + 1)) = polynomialRootCount f (q ^ (k + 1)) := by
        unfold polynomialRootCount
        exact Nat.card_congr (Equiv.ofBijective (rootReduction f φ)
          (rootReduction_bijective f φ hφ hker ih.2))
      _ = polynomialRootCount f q := ih.1

lemma polynomialRootCount_pow_of_simple (f : ℤ[X]) {q : ℕ} (hq : 0 < q)
    (hsimple : ∀ r : ZMod q, f.eval₂ (Int.castRingHom (ZMod q)) r = 0 →
      IsUnit (f.derivative.eval₂ (Int.castRingHom (ZMod q)) r)) {k : ℕ} (hk : 0 < k) :
    polynomialRootCount f (q ^ k) = polynomialRootCount f q := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  exact (polynomialRootCount_pow_and_simple f hq hsimple j).1

lemma polynomialRootCount_prime_pow_of_separable (f : ℤ[X]) {p : ℕ} (hp : p.Prime)
    (hsep : (f.map (Int.castRingHom (ZMod p))).Separable) {k : ℕ} (hk : 0 < k) :
    polynomialRootCount f (p ^ k) = polynomialRootCount f p := by
  letI : Fact p.Prime := ⟨hp⟩
  apply polynomialRootCount_pow_of_simple f hp.pos _ hk
  intro r hr
  apply isUnit_iff_ne_zero.mpr
  have hr' : (f.map (Int.castRingHom (ZMod p))).eval₂ (RingHom.id (ZMod p)) r = 0 := by
    simpa only [Polynomial.eval₂_id, Polynomial.eval_map] using hr
  have hder := hsep.eval₂_derivative_ne_zero (RingHom.id (ZMod p)) hr'
  simpa only [Polynomial.eval₂_id, Polynomial.derivative_map, Polynomial.eval_map] using hder

lemma irreducible_resultant_derivative_ne_zero {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) : f.resultant f.derivative ≠ 0 := by
  have hprim := hirr.isPrimitive hdeg
  have hQ : Irreducible (f.map (Int.castRingHom ℚ)) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hirr
  have hsep := PerfectField.separable_of_irreducible hQ
  have hr := Polynomial.resultant_ne_zero _ _ ((Polynomial.separable_def _).mp hsep)
  rw [Polynomial.derivative_map] at hr
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  simp only [Polynomial.natDegree_map_eq_of_injective hinj] at hr
  rw [Polynomial.resultant_map_map] at hr
  change ((f.resultant f.derivative : ℤ) : ℚ) ≠ 0 at hr
  exact_mod_cast hr

lemma polynomialRootCount_prime_pow_of_not_dvd_resultant (f : ℤ[X]) (hdeg : f.natDegree ≠ 0)
    {p : ℕ} (hp : p.Prime) (hbad : ¬(p : ℤ) ∣ f.resultant f.derivative) {k : ℕ} (hk : 0 < k) :
    polynomialRootCount f (p ^ k) = polynomialRootCount f p := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, B, _, _, hbez⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    f f.derivative le_rfl le_rfl (Or.inl hdeg)
  have hres : ((f.resultant f.derivative : ℤ) : ZMod p) ≠ 0 :=
    fun h => hbad ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  apply polynomialRootCount_pow_of_simple f hp.pos _ hk
  intro r hr
  apply isUnit_iff_ne_zero.mpr
  intro hder
  have heq := congrArg (fun g : ℤ[X] => g.eval₂ (Int.castRingHom (ZMod p)) r) hbez
  simp only [eval₂_add, eval₂_mul, eval₂_C, hr, hder, zero_mul, zero_add] at heq
  exact hres heq.symm

lemma finite_bad_primes {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) :
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ k : ℕ, 0 < k →
      polynomialRootCount f (p ^ k) = polynomialRootCount f p ∧
        polynomialRootCount f (p ^ k) ≤ f.natDegree := by
  let D : ℤ := f.resultant f.derivative
  have hD : D ≠ 0 := irreducible_resultant_derivative_ne_zero hdeg hirr
  refine ⟨D.natAbs.primeFactors, ?_⟩
  intro p hp hnot k hk
  have hbad : ¬(p : ℤ) ∣ D := by
    intro h
    apply hnot
    exact Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp h, Int.natAbs_ne_zero.mpr hD⟩
  have heq := polynomialRootCount_prime_pow_of_not_dvd_resultant f hdeg hp hbad hk
  exact ⟨heq, heq ▸ polynomialRootCount_prime_le (hirr.isPrimitive hdeg) hp⟩

lemma polynomialRootCount_eq_prod_of_coprime_resultant {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    {n : ℕ} (hn : n ≠ 0) (hcop : n.Coprime (f.resultant f.derivative).natAbs) :
    polynomialRootCount f n = ∏ p ∈ n.primeFactors, polynomialRootCount f p := by
  have heq := ArithmeticFunction.IsMultiplicative.multiplicative_factorization (rootFunction f)
    (rootFunction_multiplicative f) hn
  rw [rootFunction_apply f hn, Finsupp.prod, Nat.support_factorization] at heq
  have hh : (polynomialRootCount f n : ℝ) = ∏ p ∈ n.primeFactors, (polynomialRootCount f p : ℝ) := by
    rw [heq]
    apply Finset.prod_congr rfl
    intro p hp
    obtain ⟨hprime, hdiv, _⟩ := Nat.mem_primeFactors.mp hp
    have hk : 0 < n.factorization p := hprime.factorization_pos_of_dvd hn hdiv
    have hbad : ¬(p : ℤ) ∣ f.resultant f.derivative := by
      intro h
      exact hprime.ne_one (Nat.eq_one_of_dvd_coprimes hcop hdiv (Int.natCast_dvd.mp h))
    rw [rootFunction_apply f (pow_ne_zero _ hprime.ne_zero),
      polynomialRootCount_prime_pow_of_not_dvd_resultant f hdeg hprime hbad hk]
  exact_mod_cast hh

lemma polynomialRootCount_bound_of_coprime_resultant {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) {n : ℕ} (hn : n ≠ 0)
    (hcop : n.Coprime (f.resultant f.derivative).natAbs) :
    polynomialRootCount f n ≤ f.natDegree ^ n.primeFactors.card := by
  rw [polynomialRootCount_eq_prod_of_coprime_resultant hdeg hn hcop]
  calc
    _ ≤ ∏ _p ∈ n.primeFactors, f.natDegree := Finset.prod_le_prod
      (fun _ _ => Nat.zero_le _) (fun p hp => polynomialRootCount_prime_le
        (hirr.isPrimitive hdeg) (Nat.prime_of_mem_primeFactors hp))
    _ = _ := Finset.prod_const _

end GeneralDivisors
namespace GeneralDivisors

lemma polynomial_eval_sub_taylor_two (f : ℤ[X]) (x y : ℤ) :
    ∃ z : ℤ, f.eval x - f.eval y = (x - y) * f.derivative.eval y + (x - y) ^ 2 * z := by
  let P : ℤ[X] := f.taylor y - C (f.eval y) - C (f.derivative.eval y) * X
  have hdiv : X ^ 2 ∣ P := by
    rw [Polynomial.X_pow_dvd_iff]
    intro i hi
    interval_cases i <;> simp only [P, coeff_sub, coeff_C, coeff_C_mul, coeff_X,
      Polynomial.taylor_coeff_zero, Polynomial.taylor_coeff_one] <;> norm_num
  have heval := map_dvd (Polynomial.evalRingHom (x - y)) hdiv
  change (X ^ 2 : ℤ[X]).eval (x - y) ∣ P.eval (x - y) at heval
  simp only [P, eval_sub, eval_pow, eval_X, eval_C, eval_mul, Polynomial.taylor_eval_sub] at heval
  obtain ⟨z, hz⟩ := heval
  exact ⟨z, by linarith⟩

lemma derivative_not_dvd_of_resultant {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    {m x : ℤ} (hm : ¬m ∣ f.resultant f.derivative) (hx : m ∣ f.eval x) :
    ¬m ∣ f.derivative.eval x := by
  intro hder
  obtain ⟨A, B, _, _, hbez⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    f f.derivative le_rfl le_rfl (Or.inl hdeg)
  have heq := congrArg (Polynomial.eval x) hbez
  simp only [eval_add, eval_mul, eval_C] at heq
  apply hm
  rw [← heq]
  exact dvd_add (dvd_mul_of_dvd_left hx _) (dvd_mul_of_dvd_left hder _)

lemma root_spacing_of_resultant {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) {p : ℕ} (hp : p.Prime)
    {t k : ℕ} (hD : ¬(p : ℤ) ^ (t + 1) ∣ f.resultant f.derivative) (htk : t < k)
    {x y : ℤ} (hx : (p : ℤ) ^ k ∣ f.eval x) (hy : (p : ℤ) ^ k ∣ f.eval y)
    (hxy : (p : ℤ) ^ (t + 1) ∣ x - y) : (p : ℤ) ^ (k - t) ∣ x - y := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hδ : x - y = 0
  · rw [hδ]
    exact dvd_zero _
  have hlow : (p : ℤ) ^ (t + 1) ∣ f.eval y := (pow_dvd_pow (p : ℤ) (by omega)).trans hy
  have hd := derivative_not_dvd_of_resultant hdeg hD hlow
  obtain ⟨z, hz⟩ := polynomial_eval_sub_taylor_two f x y
  let w : ℤ := f.derivative.eval y + (x - y) * z
  have hw : ¬(p : ℤ) ^ (t + 1) ∣ w := by
    intro h
    apply hd
    have hh := dvd_sub h (dvd_mul_of_dvd_left hxy z)
    simpa only [w, add_sub_cancel_right] using hh
  have hw0 : w ≠ 0 := by intro h; exact hw (h ▸ dvd_zero _)
  have hwval : padicValInt p w ≤ t := by
    by_contra h
    apply hw
    exact (padicValInt_dvd_iff _ _).mpr (Or.inr (by omega))
  have hprod : (p : ℤ) ^ k ∣ (x - y) * w := by
    convert dvd_sub hx hy using 1
    dsimp only [w]
    rw [hz]
    ring
  have hval : k ≤ padicValInt p (x - y) + padicValInt p w := by
    have hh := ((padicValInt_dvd_iff _ _).mp hprod).resolve_left (mul_ne_zero hδ hw0)
    rwa [padicValInt.mul hδ hw0] at hh
  exact (padicValInt_dvd_iff _ _).mpr (Or.inr (by omega))

lemma polynomialRootCount_le_modulus (f : ℤ[X]) {q : ℕ} (hq : 0 < q) :
    polynomialRootCount f q ≤ q := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hh := Nat.card_le_card_of_injective
    (fun x : {r : ZMod q // f.eval₂ (Int.castRingHom (ZMod q)) r = 0} => x.1)
    Subtype.val_injective
  simpa only [Nat.card_zmod] using hh

lemma root_representative_dvd (f : ℤ[X]) {q : ℕ} [NeZero q]
    (x : {r : ZMod q // f.eval₂ (Int.castRingHom (ZMod q)) r = 0}) :
    (q : ℤ) ∣ f.eval (x.1.val : ℤ) := by
  apply (dvd_eval_iff_zmod f q x.1.val).mpr
  simpa only [ZMod.natCast_zmod_val] using x.2

lemma polynomialRootCount_prime_pow_bound {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) {p : ℕ} (hp : p.Prime)
    {t : ℕ} (hD : ¬(p : ℤ) ^ (t + 1) ∣ f.resultant f.derivative) (k : ℕ) :
    polynomialRootCount f (p ^ k) ≤ p ^ (2 * t + 1) := by
  by_cases hk : k ≤ 2 * t + 1
  · exact (polynomialRootCount_le_modulus f (pow_pos hp.pos k)).trans (Nat.pow_le_pow_right hp.pos hk)
  have htk : t < k := by omega
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero (p ^ (t + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hpow : p ^ t * p ^ (k - t) = p ^ k := by rw [← pow_add]; congr 1; omega
  let F : {r : ZMod (p ^ k) // f.eval₂ (Int.castRingHom (ZMod (p ^ k))) r = 0} →
      ZMod (p ^ (t + 1)) × Fin (p ^ t) := fun x =>
    ((x.1.val : ZMod (p ^ (t + 1))), ⟨x.1.val / p ^ (k - t),
      (Nat.div_lt_iff_lt_mul (pow_pos hp.pos _)).mpr (by rw [hpow]; exact ZMod.val_lt _)⟩)
  have hF : Function.Injective F := by
    intro x y hxy
    have hfirst := congrArg Prod.fst hxy
    change (x.1.val : ZMod (p ^ (t + 1))) = (y.1.val : ZMod (p ^ (t + 1))) at hfirst
    have hmodlow := (ZMod.natCast_eq_natCast_iff _ _ _).mp hfirst
    have hx : (p : ℤ) ^ k ∣ f.eval (x.1.val : ℤ) := by simpa only [Nat.cast_pow] using root_representative_dvd f x
    have hy : (p : ℤ) ^ k ∣ f.eval (y.1.val : ℤ) := by simpa only [Nat.cast_pow] using root_representative_dvd f y
    have hlow : (p : ℤ) ^ (t + 1) ∣ (y.1.val : ℤ) - (x.1.val : ℤ) := by
      simpa only [Nat.cast_pow] using hmodlow.dvd
    have hs := root_spacing_of_resultant hdeg hp hD htk hy hx hlow
    have hmodhigh : x.1.val % p ^ (k - t) = y.1.val % p ^ (k - t) := by
      apply Nat.modEq_iff_dvd.mpr
      simpa only [Nat.cast_pow] using hs
    have hquot := congrArg (fun z : ZMod (p ^ (t + 1)) × Fin (p ^ t) => z.2.val) hxy
    change x.1.val / p ^ (k - t) = y.1.val / p ^ (k - t) at hquot
    apply Subtype.ext
    apply ZMod.val_injective (p ^ k)
    have hxm := Nat.mod_add_div x.1.val (p ^ (k - t))
    have hym := Nat.mod_add_div y.1.val (p ^ (k - t))
    rw [hmodhigh, hquot] at hxm
    omega
  have hb := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_zmod, Nat.card_fin, ← pow_add] at hb
  simpa only [show t + 1 + t = 2 * t + 1 by omega] using hb

lemma polynomialRootCount_prime_pow_uniform_bound {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    polynomialRootCount f (p ^ k) ≤ p ^ (2 * padicValInt p (f.resultant f.derivative) + 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply polynomialRootCount_prime_pow_bound hdeg hp _ k
  rw [padicValInt_dvd_iff]
  have hne := irreducible_resultant_derivative_ne_zero hdeg hirr
  simp [hne]

lemma summable_polynomialRootCount_prime_powers {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => (polynomialRootCount f (p ^ k) : ℝ) / (p : ℝ) ^ k) := by
  have hpr : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hg : Summable (fun k : ℕ => ((p : ℝ)⁻¹) ^ k) :=
    summable_geometric_of_lt_one (by positivity) ((inv_lt_one₀ (by positivity)).mpr hpr)
  let B : ℕ := p ^ (2 * padicValInt p (f.resultant f.derivative) + 1)
  apply (hg.mul_left (B : ℝ)).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (B : ℝ) / (p : ℝ) ^ k := div_le_div_of_nonneg_right
      (by exact_mod_cast polynomialRootCount_prime_pow_uniform_bound hdeg hirr hp k) (by positivity)
    _ = _ := by rw [inv_pow, div_eq_mul_inv]

lemma polynomialRootCount_factorization (f : ℤ[X]) {n : ℕ} (hn : n ≠ 0) :
    polynomialRootCount f n = ∏ p ∈ n.primeFactors, polynomialRootCount f (p ^ n.factorization p) := by
  have heq := ArithmeticFunction.IsMultiplicative.multiplicative_factorization (rootFunction f)
    (rootFunction_multiplicative f) hn
  rw [rootFunction_apply f hn, Finsupp.prod, Nat.support_factorization] at heq
  have hh : (polynomialRootCount f n : ℝ) =
      ∏ p ∈ n.primeFactors, (polynomialRootCount f (p ^ n.factorization p) : ℝ) := by
    rw [heq]
    apply Finset.prod_congr rfl
    intro p hp
    exact rootFunction_apply f (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)
  exact_mod_cast hh

lemma polynomialRootCount_global_bound {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) : ∃ B > (0 : ℕ), ∀ n : ℕ, n ≠ 0 →
      polynomialRootCount f n ≤ B * f.natDegree ^ n.primeFactors.card := by
  classical
  obtain ⟨S, hS⟩ := finite_bad_primes hdeg hirr
  let b : ℕ → ℕ := fun p => max 1 (p ^ (2 * padicValInt p (f.resultant f.derivative) + 1))
  let B : ℕ := ∏ p ∈ S, b p
  have hb1 (p : ℕ) : 1 ≤ b p := le_max_left _ _
  have hB : 0 < B := lt_of_lt_of_le Nat.zero_lt_one (Finset.one_le_prod' (fun p _ => hb1 p))
  refine ⟨B, hB, ?_⟩
  intro n hn
  rw [polynomialRootCount_factorization f hn]
  have hlocal (p : ℕ) (hp : p ∈ n.primeFactors) :
      polynomialRootCount f (p ^ n.factorization p) ≤ (if p ∈ S then b p else 1) * f.natDegree := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hk := hprime.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
    by_cases hps : p ∈ S
    · rw [if_pos hps]
      exact ((polynomialRootCount_prime_pow_uniform_bound hdeg hirr hprime _).trans
        (le_max_right _ _)).trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hdeg))
    · simpa only [if_neg hps, one_mul] using (hS p hprime hps _ hk).2
  have hprod : (∏ p ∈ n.primeFactors, if p ∈ S then b p else 1) ≤ B := by
    rw [← Finset.prod_filter]
    exact Finset.prod_le_prod_of_subset_of_one_le'
      (fun p hp => (Finset.mem_filter.mp hp).2) (fun p _ _ => hb1 p)
  calc
    _ ≤ ∏ p ∈ n.primeFactors, (if p ∈ S then b p else 1) * f.natDegree :=
      Finset.prod_le_prod' hlocal
    _ = (∏ p ∈ n.primeFactors, if p ∈ S then b p else 1) * f.natDegree ^ n.primeFactors.card := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ ≤ B * f.natDegree ^ n.primeFactors.card := Nat.mul_le_mul_right _ hprod

end GeneralDivisors
namespace DivisorMajorant
open ArithmeticFunction

lemma zeta_pow_multiplicative (d : ℕ) :
    IsMultiplicative ((zeta : ArithmeticFunction ℕ) ^ d) := by
  induction d with
  | zero => simpa using (isMultiplicative_one (R := ℕ))
  | succ d ih => simpa only [pow_succ] using ih.mul isMultiplicative_zeta

lemma zeta_pow_apply_one (d : ℕ) :
    ((zeta : ArithmeticFunction ℕ) ^ d) 1 = 1 := (zeta_pow_multiplicative d).1

lemma zeta_pow_ge_exponent (d n : ℕ) (hn : 1 < n) :
    d ≤ ((zeta : ArithmeticFunction ℕ) ^ d) n := by
  induction d with
  | zero => exact Nat.zero_le _
  | succ d ih =>
    rw [pow_succ, mul_zeta_apply]
    have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with hx | hx
      · subst x
        exact Nat.one_mem_divisors.mpr (by omega)
      · subst x
        exact Nat.mem_divisors_self n (by omega)
    have h := Finset.sum_le_sum_of_subset hsub (f := fun i => ((zeta : ArithmeticFunction ℕ) ^ d) i)
    rw [sum_pair (by omega : (1 : ℕ) ≠ n), zeta_pow_apply_one] at h
    dsimp only at h
    omega

lemma pow_primeFactors_card_le_zeta_pow (d n : ℕ) (hn : n ≠ 0) :
    d ^ n.primeFactors.card ≤ ((zeta : ArithmeticFunction ℕ) ^ d) n := by
  rw [(zeta_pow_multiplicative d).multiplicative_factorization _ hn,
    Finsupp.prod, Nat.support_factorization]
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod'
  intro p hp
  apply zeta_pow_ge_exponent
  have hprime := Nat.prime_of_mem_primeFactors hp
  exact one_lt_pow₀ hprime.one_lt (Nat.ne_of_gt (hprime.factorization_pos_of_dvd hn
    (Nat.dvd_of_mem_primeFactors hp)))

lemma harmonic_real_mono {M N : ℕ} (hMN : M ≤ N) :
    (harmonic M : ℝ) ≤ harmonic N := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hMN)
    (fun _ _ _ => by positivity)

lemma harmonic_real_nonneg (N : ℕ) : 0 ≤ (harmonic N : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  exact Finset.sum_nonneg (fun _ _ => by positivity)

lemma sum_zeta_pow_bound (d N : ℕ) :
    (∑ n ∈ Ioc 0 N, (((zeta : ArithmeticFunction ℕ) ^ (d+1)) n : ℝ)) ≤
      N * (harmonic N : ℝ) ^ d := by
  induction d generalizing N with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, mul_one, ← Nat.cast_sum, sum_Ioc_zeta]
    exact le_rfl
  | succ d ih =>
    have heq :
        ∑ n ∈ Ioc 0 N, (((zeta : ArithmeticFunction ℕ) ^ (d+1+1)) n : ℝ) =
        ∑ n ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N/n), (((zeta : ArithmeticFunction ℕ) ^ (d+1)) m : ℝ) := by
      rw [← Nat.cast_sum, pow_succ', sum_Ioc_mul_eq_sum_sum, Nat.cast_sum]
      apply sum_congr rfl
      intro n hn
      rw [zeta_apply_ne (Nat.ne_of_gt (mem_Ioc.mp hn).1), one_mul, Nat.cast_sum]
    rw [heq]
    calc
      _ ≤ ∑ n ∈ Ioc 0 N, (N / n : ℕ) * (harmonic (N/n) : ℝ) ^ d :=
        sum_le_sum (fun n _ => ih (N/n))
      _ ≤ ∑ n ∈ Ioc 0 N, ((N : ℝ) / n) * (harmonic N : ℝ) ^ d := by
        apply sum_le_sum
        intro n hn
        apply mul_le_mul
        · exact Nat.cast_div_le
        · exact pow_le_pow_left₀ (harmonic_real_nonneg _) (harmonic_real_mono (Nat.div_le_self N n)) _
        · exact pow_nonneg (harmonic_real_nonneg _) _
        · positivity
      _ = N * (harmonic N : ℝ) ^ (d+1) := by
        have hsum : ∑ n ∈ Ioc 0 N, (n : ℝ)⁻¹ = (harmonic N : ℝ) := by
          simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
          rw [← Finset.Icc_add_one_left_eq_Ioc]
          rfl
        simp only [div_eq_mul_inv, ← mul_sum, ← sum_mul]
        rw [hsum, pow_succ]
        ring

end DivisorMajorant

namespace GeneralDivisors

lemma polynomialRootCount_sum_bound {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) : ∃ B > (0 : ℝ), ∀ N : ℕ,
      ∑ n ∈ Finset.Ioc 0 N, (polynomialRootCount f n : ℝ) ≤
        B * N * (harmonic N : ℝ) ^ (f.natDegree - 1) := by
  obtain ⟨B, hB, hb⟩ := polynomialRootCount_global_bound hdeg hirr
  refine ⟨(B : ℝ), by exact_mod_cast hB, ?_⟩
  intro N
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 N, (B : ℝ) * (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ f.natDegree) n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 := Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1
      exact_mod_cast (hb n hn0).trans (Nat.mul_le_mul_left B
        (DivisorMajorant.pow_primeFactors_card_le_zeta_pow f.natDegree n hn0))
    _ = (B : ℝ) * ∑ n ∈ Finset.Ioc 0 N, (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ f.natDegree) n : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (B : ℝ) * (N * (harmonic N : ℝ) ^ (f.natDegree - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hdeg)] using
        DivisorMajorant.sum_zeta_pow_bound (f.natDegree-1) N
    _ = _ := by ring


lemma polynomialRootCount_cutoff_negligible {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) (Y : ℕ → ℕ)
    (hY : ∀ᶠ N in atTop, Y N ≤ N ∧
      (Y N : ℝ) * (harmonic N : ℝ) ^ (f.natDegree - 1) ≤ N) :
    Tendsto (fun N : ℕ =>
      (∑ q ∈ Finset.Ioc 0 (Y N), (polynomialRootCount f q : ℝ)) /
        ((N : ℝ) * log N)) atTop (𝓝 0) := by
  obtain ⟨B, hB, hb⟩ := polynomialRootCount_sum_bound hdeg hirr
  have htlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero_norm' (a := fun N : ℕ => B / log N)
  · filter_upwards [hY, eventually_gt_atTop (1 : ℕ)] with N hYN hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hlog : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hmajor : ∑ q ∈ Finset.Ioc 0 (Y N), (polynomialRootCount f q : ℝ) ≤ B * N := by
      calc
        _ ≤ B * Y N * (harmonic (Y N) : ℝ) ^ (f.natDegree - 1) := hb _
        _ ≤ B * Y N * (harmonic N : ℝ) ^ (f.natDegree - 1) := by
          apply mul_le_mul_of_nonneg_left
          · exact pow_le_pow_left₀ (DivisorMajorant.harmonic_real_nonneg _)
              (DivisorMajorant.harmonic_real_mono hYN.1) _
          · positivity
        _ ≤ B * N := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hYN.2 hB.le
    calc
      _ ≤ (B * N) / ((N : ℝ) * log N) := div_le_div_of_nonneg_right hmajor (by positivity)
      _ = B / log N := by field_simp
  · exact tendsto_const_nhds.div_atTop htlog

noncomputable def logarithmicCutoff (f : ℤ[X]) (N : ℕ) : ℕ :=
  ⌊(N : ℝ) / (1 + log (N : ℝ)) ^ (f.natDegree - 1)⌋₊

lemma logarithmicCutoff_bound (f : ℤ[X]) {N : ℕ} (hN : 1 ≤ N) :
    logarithmicCutoff f N ≤ N ∧
      (logarithmicCutoff f N : ℝ) * (harmonic N : ℝ) ^ (f.natDegree - 1) ≤ N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog := Real.log_nonneg hNr
  have hbase : 1 ≤ 1 + log (N : ℝ) := by linarith
  have hp1 : (1 : ℝ) ≤ (1 + log (N : ℝ)) ^ (f.natDegree - 1) := one_le_pow₀ hbase
  have hpos : 0 < (1 + log (N : ℝ)) ^ (f.natDegree - 1) := lt_of_lt_of_le zero_lt_one hp1
  have hfloor : (logarithmicCutoff f N : ℝ) ≤
      (N : ℝ) / (1 + log (N : ℝ)) ^ (f.natDegree - 1) := Nat.floor_le (by positivity)
  constructor
  · exact_mod_cast hfloor.trans (div_le_self (by positivity) hp1)
  · calc
      _ ≤ (logarithmicCutoff f N : ℝ) * (1 + log (N : ℝ)) ^ (f.natDegree - 1) := by
        apply mul_le_mul_of_nonneg_left
        · exact pow_le_pow_left₀ (DivisorMajorant.harmonic_real_nonneg _)
            (harmonic_le_one_add_log N) _
        · positivity
      _ ≤ N := (le_div_iff₀ hpos).mp hfloor

lemma polynomialRootCount_logarithmicCutoff_negligible {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) :
    Tendsto (fun N : ℕ =>
      (∑ q ∈ Finset.Ioc 0 (logarithmicCutoff f N), (polynomialRootCount f q : ℝ)) /
        ((N : ℝ) * log N)) atTop (𝓝 0) := by
  apply polynomialRootCount_cutoff_negligible hdeg hirr (logarithmicCutoff f)
  exact (eventually_ge_atTop 1).mono (fun N hN => logarithmicCutoff_bound f hN)

lemma truncatedDivisorSum_logarithmicCutoff_error_tendsto {f : ℤ[X]}
    (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) :
    Tendsto (fun N : ℕ =>
      (truncatedDivisorSum f N (logarithmicCutoff f N) - (N : ℝ) *
        ∑ q ∈ Finset.Ioc 0 (logarithmicCutoff f N), (polynomialRootCount f q : ℝ) / q) /
        ((N : ℝ) * log N)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun N : ℕ => 2 *
    ((∑ q ∈ Finset.Ioc 0 (logarithmicCutoff f N), (polynomialRootCount f q : ℝ)) /
      ((N : ℝ) * log N)))
  · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hlog : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hNr hlog), ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (truncatedDivisorSum_error f N _) (mul_pos hNr hlog).le
  · simpa only [mul_zero] using
      (polynomialRootCount_logarithmicCutoff_negligible hdeg hirr).const_mul 2

end GeneralDivisors

namespace GeneralDivisors

open Finset

lemma floor_eval_cast {f : ℤ[X]} {n : ℕ} (h : 0 ≤ f.eval (n : ℤ)) :
    (⌊f.eval (n : ℤ)⌋₊ : ℤ) = f.eval (n : ℤ) := by
  rw [Nat.floor_int]
  exact Int.toNat_of_nonneg h

lemma halfDivisorCount_eq_filter {m Y : ℕ} (hm : 0 < m) (hY : m ≤ Y*Y) :
    halfDivisorCount m = {q ∈ Ioc 0 Y | q ∣ m ∧ q*q ≤ m}.card := by
  unfold halfDivisorCount
  congr 1
  ext q
  simp only [mem_filter, Nat.mem_divisors, mem_Ioc]
  constructor
  · rintro ⟨⟨hqm, hm0⟩, hq⟩
    refine ⟨⟨Nat.pos_of_dvd_of_pos hqm hm, ?_⟩, hqm, hq⟩
    nlinarith
  · rintro ⟨⟨_, _⟩, hqm, hq⟩
    exact ⟨⟨hqm, hm.ne'⟩, hq⟩

lemma halfSum_remove_zero (f : ℤ[X]) (N : ℕ) :
    halfSum f N = halfDivisorCount ⌊f.eval 0⌋₊ +
      ∑ n ∈ Ioc 0 N, (halfDivisorCount ⌊f.eval (n : ℤ)⌋₊ : ℝ) := by
  have h := Finset.sum_Ioc_add_eq_sum_Icc
    (f := fun n : ℕ => (halfDivisorCount ⌊f.eval (n : ℤ)⌋₊ : ℝ)) (Nat.zero_le N)
  simpa [halfSum, add_comm] using h.symm

lemma halfSum_quadratic_upper (f : ℤ[X]) (C N : ℕ)
    (hval : ∀ n : ℕ, 0 < n → 0 < f.eval (n : ℤ))
    (hupper : ∀ n : ℕ, 0 < n → ⌊f.eval (n : ℤ)⌋₊ ≤ (C*n)*(C*n)) :
    halfSum f N ≤ halfDivisorCount ⌊f.eval 0⌋₊ + truncatedDivisorSum f N (C*N) := by
  rw [halfSum_remove_zero]
  apply add_le_add le_rfl
  have heq : truncatedDivisorSum f N (C*N) =
      ∑ n ∈ Ioc 0 N, ({q ∈ Ioc 0 (C*N) | ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)}.card : ℝ) := by
    simp only [truncatedDivisorSum, divisibleValueCount, card_filter, Nat.cast_sum]
    rw [sum_comm]
  rw [heq]
  apply sum_le_sum
  intro n hn
  have hn0 := (mem_Ioc.mp hn).1
  have hnm : 0 < ⌊f.eval (n : ℤ)⌋₊ := by
    have : 1 ≤ ⌊f.eval (n : ℤ)⌋₊ := Nat.le_floor (show (1 : ℤ) ≤ f.eval (n : ℤ) by linarith [hval n hn0])
    omega
  have hnm' : ⌊f.eval (n : ℤ)⌋₊ ≤ (C*N)*(C*N) :=
    (hupper n hn0).trans (Nat.mul_le_mul (Nat.mul_le_mul_left C (mem_Ioc.mp hn).2)
      (Nat.mul_le_mul_left C (mem_Ioc.mp hn).2))
  rw [halfDivisorCount_eq_filter hnm hnm']
  exact_mod_cast card_le_card (show {q ∈ Ioc 0 (C*N) | q ∣ ⌊f.eval (n : ℤ)⌋₊ ∧ q*q ≤ ⌊f.eval (n : ℤ)⌋₊} ⊆
      {q ∈ Ioc 0 (C*N) | ((q : ℕ) : ℤ) ∣ f.eval (n : ℤ)} from by
    intro q hq
    refine mem_filter.mpr ⟨(mem_filter.mp hq).1, ?_⟩
    rw [← floor_eval_cast (hval n hn0).le, Int.natCast_dvd_natCast]
    exact (mem_filter.mp hq).2.1)


lemma halfSum_quadratic_lower (f : ℤ[X]) (C N : ℕ)
    (hval : ∀ n : ℕ, 0 < n → 0 < f.eval (n : ℤ))
    (hlower : ∀ n : ℕ, 0 < n → n*n ≤ C*C*⌊f.eval (n : ℤ)⌋₊) :
    truncatedDivisorSum f N N ≤ halfSum f N +
      ∑ q ∈ Ioc 0 N, (divisibleValueCount f q (C*q) : ℝ) := by
  have heq : truncatedDivisorSum f N N =
      ∑ n ∈ Ioc 0 N, ({q ∈ Ioc 0 N | ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)}.card : ℝ) := by
    simp only [truncatedDivisorSum, divisibleValueCount, card_filter, Nat.cast_sum]
    rw [sum_comm]
  have hrow (n : ℕ) (hn : n ∈ Ioc 0 N) :
      {q ∈ Ioc 0 N | ((q : ℕ) : ℤ) ∣ f.eval (n : ℤ)}.card ≤
      halfDivisorCount ⌊f.eval (n : ℤ)⌋₊ +
        {q ∈ Ioc 0 N | n ≤ C*q ∧ ((q : ℕ) : ℤ) ∣ f.eval (n : ℤ)}.card := by
    have hn0 := (mem_Ioc.mp hn).1
    let B := {q ∈ (⌊f.eval (n : ℤ)⌋₊).divisors | q*q ≤ ⌊f.eval (n : ℤ)⌋₊}
    let D := {q ∈ Ioc 0 N | n ≤ C*q ∧ ((q : ℕ) : ℤ) ∣ f.eval (n : ℤ)}
    have hsub : {q ∈ Ioc 0 N | ((q : ℕ) : ℤ) ∣ f.eval (n : ℤ)} ⊆ B ∪ D := by
      intro q hq
      obtain ⟨hqN, hqd⟩ := mem_filter.mp hq
      by_cases hqm : q*q ≤ ⌊f.eval (n : ℤ)⌋₊
      · apply mem_union_left
        apply mem_filter.mpr
        refine ⟨Nat.mem_divisors.mpr ⟨?_, ?_⟩, hqm⟩
        · rw [← Int.natCast_dvd_natCast, floor_eval_cast (hval n hn0).le]
          exact hqd
        · have h : 1 ≤ ⌊f.eval (n : ℤ)⌋₊ := Nat.le_floor (by norm_num only [Nat.cast_one]; have := hval n hn0; omega)
          omega
      · apply mem_union_right
        refine mem_filter.mpr ⟨hqN, ?_, hqd⟩
        have hb := hlower n hn0
        have hh := Nat.mul_le_mul_left (C*C) (Nat.le_of_lt (Nat.lt_of_not_ge hqm))
        apply Nat.mul_self_le_mul_self_iff.mp
        calc
          n*n ≤ C*C*⌊f.eval (n : ℤ)⌋₊ := hb
          _ ≤ C*C*(q*q) := hh
          _ = (C*q)*(C*q) := by ring
    exact (card_le_card hsub).trans (card_union_le _ _)
  have hsum : ∑ n ∈ Ioc 0 N,
      ({q ∈ Ioc 0 N | n ≤ C*q ∧ ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)}.card : ℝ) ≤
      ∑ q ∈ Ioc 0 N, (divisibleValueCount f q (C*q) : ℝ) := by
    simp only [card_filter, Nat.cast_sum]
    rw [sum_comm]
    apply sum_le_sum
    intro q hq
    rw [← Nat.cast_sum, ← card_filter]
    apply Nat.cast_le.mpr
    apply card_le_card
    intro n hn
    obtain ⟨hnN, hnq, hnd⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hnN).1, hnq⟩, hnd⟩
  rw [heq, halfSum_remove_zero]
  have hsumrow :
      (∑ n ∈ Ioc 0 N, ({q ∈ Ioc 0 N | ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)}.card : ℝ)) ≤
      (∑ n ∈ Ioc 0 N, (halfDivisorCount ⌊f.eval (n : ℤ)⌋₊ : ℝ)) +
      ∑ n ∈ Ioc 0 N,
        ({q ∈ Ioc 0 N | n ≤ C*q ∧ ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)}.card : ℝ) := by
    rw [← sum_add_distrib]
    exact sum_le_sum (fun n hn => by exact_mod_cast hrow n hn)
  have hc : (0 : ℝ) ≤ halfDivisorCount ⌊f.eval 0⌋₊ := by positivity
  linarith

lemma divisibleValueCount_mul_bound (f : ℤ[X]) {q : ℕ} (hq : 0 < q) (C : ℕ) :
    (divisibleValueCount f q (C*q) : ℝ) ≤ ((C : ℝ) + 2) * polynomialRootCount f q := by
  have h := (abs_le.mp (polynomial_root_count_error f hq (C*q))).2
  have hqr : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  rw [Nat.cast_mul, mul_div_cancel_right₀ _ hqr] at h
  linarith

lemma truncatedDivisorSum_tail_bound (f : ℤ[X]) {N Y : ℕ} (hNY : N ≤ Y) :
    truncatedDivisorSum f N Y - truncatedDivisorSum f N N ≤
      3 * ∑ q ∈ Ioc 0 Y, (polynomialRootCount f q : ℝ) := by
  have heq : truncatedDivisorSum f N Y = truncatedDivisorSum f N N +
      ∑ q ∈ Ioc N Y, (divisibleValueCount f q N : ℝ) := by
    exact (Finset.sum_Ioc_consecutive (fun q => (divisibleValueCount f q N : ℝ))
      (Nat.zero_le N) hNY).symm
  rw [heq, add_sub_cancel_left]
  calc
    _ ≤ ∑ q ∈ Ioc N Y, (3 : ℝ) * polynomialRootCount f q := by
      apply sum_le_sum
      intro q hq
      have hNq := (mem_Ioc.mp hq).1
      have hq0 : 0 < q := by omega
      have h := (abs_le.mp (polynomial_root_count_error f hq0 N)).2
      have hh : (N : ℝ) / q ≤ 1 := (div_le_one (Nat.cast_pos.mpr hq0)).mpr (by exact_mod_cast hNq.le)
      have hmul := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (polynomialRootCount f q) (α := ℝ))
      linarith
    _ ≤ ∑ q ∈ Ioc 0 Y, (3 : ℝ) * polynomialRootCount f q :=
      sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc (Nat.zero_le N) le_rfl)
        (fun _ _ _ => by positivity)
    _ = _ := (mul_sum _ _ _).symm


lemma halfSum_quadratic_error (f : ℤ[X]) {C : ℕ} (hC : 0 < C) (N : ℕ)
    (hval : ∀ n : ℕ, 0 < n → 0 < f.eval (n : ℤ))
    (hlower : ∀ n : ℕ, 0 < n → n*n ≤ C*C*⌊f.eval (n : ℤ)⌋₊)
    (hupper : ∀ n : ℕ, 0 < n → ⌊f.eval (n : ℤ)⌋₊ ≤ (C*n)*(C*n)) :
    |halfSum f N - truncatedDivisorSum f N N| ≤
      halfDivisorCount ⌊f.eval 0⌋₊ +
      ((C : ℝ) + 5) * ∑ q ∈ Ioc 0 (C*N), (polynomialRootCount f q : ℝ) := by
  have hNC : N ≤ C*N := Nat.le_mul_of_pos_left N hC
  have hu := halfSum_quadratic_upper f C N hval hupper
  have hl := halfSum_quadratic_lower f C N hval hlower
  have ht := truncatedDivisorSum_tail_bound f hNC
  have hsum : (∑ q ∈ Ioc 0 N, (divisibleValueCount f q (C*q) : ℝ)) ≤
      ((C : ℝ)+2) * ∑ q ∈ Ioc 0 (C*N), (polynomialRootCount f q : ℝ) := by
    calc
      _ ≤ ∑ q ∈ Ioc 0 N, ((C : ℝ)+2) * polynomialRootCount f q :=
        sum_le_sum (fun q hq => divisibleValueCount_mul_bound f (mem_Ioc.mp hq).1 C)
      _ ≤ ∑ q ∈ Ioc 0 (C*N), ((C : ℝ)+2) * polynomialRootCount f q :=
        sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc le_rfl hNC) (fun _ _ _ => by positivity)
      _ = _ := (mul_sum _ _ _).symm
  have hr : (0 : ℝ) ≤ ∑ q ∈ Ioc 0 (C*N), (polynomialRootCount f q : ℝ) := by positivity
  have hc : (0 : ℝ) ≤ halfDivisorCount ⌊f.eval 0⌋₊ := by positivity
  have hCr : (0 : ℝ) ≤ C := by positivity
  rw [abs_le]
  constructor <;> nlinarith

lemma polynomialRootCount_linear_bound_of_mean (f : ℤ[X]) {a : ℝ}
    (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)) / N) atTop (𝓝 a)) :
    ∃ B > (0 : ℝ), ∀ N : ℕ,
      ∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ) ≤ B*N := by
  obtain ⟨M, hM⟩ := hmean.norm.bddAbove_range
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro N
  by_cases hN : N = 0
  · simp [hN]
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hb := hM (Set.mem_range_self N)
  have hsum0 : (0 : ℝ) ≤ ∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hsum0 hNr.le)] at hb
  exact (div_le_iff₀ hNr).mp (hb.trans (le_max_left _ _))

lemma halfSum_quadratic_error_tendsto (f : ℤ[X]) {C : ℕ} (hC : 0 < C)
    (hval : ∀ n : ℕ, 0 < n → 0 < f.eval (n : ℤ))
    (hlower : ∀ n : ℕ, 0 < n → n*n ≤ C*C*⌊f.eval (n : ℤ)⌋₊)
    (hupper : ∀ n : ℕ, 0 < n → ⌊f.eval (n : ℤ)⌋₊ ≤ (C*n)*(C*n))
    {a : ℝ} (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)) / N) atTop (𝓝 a)) :
    Tendsto (fun N : ℕ => (halfSum f N - truncatedDivisorSum f N N) /
      ((N : ℝ) * log N)) atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := polynomialRootCount_linear_bound_of_mean f hmean
  let K : ℝ := halfDivisorCount ⌊f.eval 0⌋₊ + ((C : ℝ)+5)*B*C
  have htlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero_norm' (a := fun N : ℕ => K / log N)
  · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
    have hlog : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hNr hlog)]
    have hh : |halfSum f N - truncatedDivisorSum f N N| ≤ K*N := by
      calc
        _ ≤ halfDivisorCount ⌊f.eval 0⌋₊ +
            ((C : ℝ) + 5) * ∑ q ∈ Ioc 0 (C*N), (polynomialRootCount f q : ℝ) :=
          halfSum_quadratic_error f hC N hval hlower hupper
        _ ≤ halfDivisorCount ⌊f.eval 0⌋₊ + ((C : ℝ)+5)*(B*(C*N)) := by
          apply add_le_add le_rfl
          exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_mul] using hbound (C*N)) (by positivity)
        _ ≤ K*N := by
          have hh := mul_le_mul_of_nonneg_left hNr1 (Nat.cast_nonneg (halfDivisorCount ⌊f.eval 0⌋₊) (α := ℝ))
          dsimp [K]
          nlinarith
    calc
      _ ≤ (K*N)/((N : ℝ)*log N) := div_le_div_of_nonneg_right hh (by positivity)
      _ = K/log N := by field_simp
  · exact tendsto_const_nhds.div_atTop htlog

lemma limit_of_quadratic_growth_and_root_mean (f : ℤ[X]) {C : ℕ} (hC : 0 < C)
    (hval : ∀ n : ℕ, 0 < n → 0 < f.eval (n : ℤ))
    (hlower : ∀ n : ℕ, 0 < n → n*n ≤ C*C*⌊f.eval (n : ℤ)⌋₊)
    (hupper : ∀ n : ℕ, 0 < n → ⌊f.eval (n : ℤ)⌋₊ ≤ (C*n)*(C*n))
    {a : ℝ} (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)) / N) atTop (𝓝 a)) :
    Tendsto (fun x : ℝ => Erdos975Sum f x / (x * log x)) atTop (𝓝 (2*a)) := by
  apply (halfSum_limit_iff f a).mp
  have h := (truncatedDivisorSum_limit_of_root_mean f a hmean).add
    (halfSum_quadratic_error_tendsto f hC hval hlower hupper hmean)
  simpa only [add_zero, ← add_div, add_sub_cancel] using h


lemma polynomialRootCount_comp_X_add_C (f : ℤ[X]) (t : ℤ) (q : ℕ) :
    polynomialRootCount (f.comp (X + Polynomial.C t)) q = polynomialRootCount f q := by
  let F : {r : ZMod q // (f.comp (X + Polynomial.C t)).eval₂ (Int.castRingHom (ZMod q)) r = 0} ≃
      {r : ZMod q // f.eval₂ (Int.castRingHom (ZMod q)) r = 0} := {
    toFun := fun r => ⟨r.val + (t : ZMod q), by
      simpa only [eval₂_comp, eval₂_add, eval₂_X, eval₂_C] using r.property⟩
    invFun := fun r => ⟨r.val - (t : ZMod q), by
      simp only [eval₂_comp, eval₂_add, eval₂_X, eval₂_C]
      change f.eval₂ (Int.castRingHom (ZMod q)) (r.val - (t : ZMod q) + (t : ZMod q)) = 0
      simpa only [sub_add_cancel] using r.property⟩
    left_inv := fun r => by apply Subtype.ext; simp
    right_inv := fun r => by apply Subtype.ext; simp
  }
  exact Nat.card_congr F

lemma eval_quadratic {f : ℤ[X]} (hd : f.natDegree = 2) (n : ℤ) :
    f.eval n = f.coeff 2*n^2 + f.coeff 1*n + f.coeff 0 := by
  rw [eval_eq_sum_range, hd]
  norm_num [Finset.sum_range_succ]
  ring

lemma quadratic_lead_pos {f : ℤ[X]} (hd : f.natDegree = 2)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) : 0 < f.coeff 2 := by
  have ha0 : f.coeff 2 ≠ 0 := by
    rw [← hd, coeff_natDegree]
    apply leadingCoeff_ne_zero.mpr
    intro hf
    simp [hf] at hd
  by_contra hna
  have han : f.coeff 2 ≤ -1 := by omega
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpos
  let n : ℤ := max N (|f.coeff 1| + |f.coeff 0| + 2)
  have hnN : N ≤ n := le_max_left _ _
  have hnb : |f.coeff 1| + |f.coeff 0| + 2 ≤ n := le_max_right _ _
  have hn1 : 1 ≤ n := by linarith [abs_nonneg (f.coeff 1), abs_nonneg (f.coeff 0)]
  have he := hN n hnN
  rw [eval_quadratic hd] at he
  have ham := mul_le_mul_of_nonneg_right han (sq_nonneg n)
  have hbm := mul_le_mul_of_nonneg_right (le_abs_self (f.coeff 1)) (show 0 ≤ n by omega)
  have hcm := le_abs_self (f.coeff 0)
  have hh1 := mul_nonneg (show 0 ≤ n - |f.coeff 1| - |f.coeff 0| - 2 by omega) (show 0 ≤ n by omega)
  have hh2 := mul_nonneg (abs_nonneg (f.coeff 0)) (show 0 ≤ n - 1 by omega)
  nlinarith

lemma quadratic_shift_coeffs_nonneg {a : ℤ} (ha : 0 < a) (b c : ℤ) :
    ∃ t : ℤ, 0 ≤ 2*a*t+b ∧ 0 ≤ a*t^2+b*t+c := by
  let t : ℤ := |b|+|c|+1
  have ht1 : 1 ≤ t := by dsimp [t]; linarith [abs_nonneg b, abs_nonneg c]
  have ht : t = |b|+|c|+1 := rfl
  have ha1 : 1 ≤ a := ha
  have hb := neg_abs_le b
  have hc := neg_abs_le c
  have ham := mul_le_mul_of_nonneg_right ha1 (show 0 ≤ t by omega)
  have ha2 := mul_le_mul_of_nonneg_right ha1 (sq_nonneg t)
  have hbm := mul_le_mul_of_nonneg_right hb (show 0 ≤ t by omega)
  have hcm := mul_nonneg (abs_nonneg c) (show 0 ≤ t-1 by omega)
  refine ⟨t, ?_, ?_⟩
  · nlinarith [abs_nonneg c]
  · nlinarith

lemma quadratic_nonneg_coeff_growth (f : ℤ[X]) (a b c : ℤ)
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hf : ∀ n : ℤ, f.eval n = a*n^2 + b*n+c) :
    ∃ K > (0 : ℕ),
      (∀ n : ℕ, 0 < n → 0 < f.eval (n : ℤ)) ∧
      (∀ n : ℕ, 0 < n → n*n ≤ K*K*⌊f.eval (n : ℤ)⌋₊) ∧
      (∀ n : ℕ, 0 < n → ⌊f.eval (n : ℤ)⌋₊ ≤ (K*n)*(K*n)) := by
  let K : ℕ := a.toNat+b.toNat+c.toNat+1
  have hK : 0 < K := by dsimp [K]; omega
  have hKcast : (K : ℤ) = a+b+c+1 := by
    simp only [K, Nat.cast_add, Nat.cast_one, Int.toNat_of_nonneg ha.le,
      Int.toNat_of_nonneg hb, Int.toNat_of_nonneg hc]
  have hK1 : (1 : ℤ) ≤ K := by exact_mod_cast hK
  have hquad (n : ℕ) (hn : 0 < n) :
      (n : ℤ)^2 ≤ f.eval (n : ℤ) ∧ f.eval (n : ℤ) ≤ (K : ℤ)^2*(n : ℤ)^2 := by
    have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
    have hnn : (n : ℤ) ≤ (n : ℤ)^2 := by nlinarith
    have hnsq : (1 : ℤ) ≤ (n : ℤ)^2 := by nlinarith
    have ha1 : (1 : ℤ) ≤ a := ha
    rw [hf]
    constructor
    · have ham := mul_le_mul_of_nonneg_right ha1 (sq_nonneg (n : ℤ))
      have hbn := mul_nonneg hb (show (0 : ℤ) ≤ n by positivity)
      nlinarith
    · have hbm := mul_le_mul_of_nonneg_left hnn hb
      have hcm := mul_le_mul_of_nonneg_left hnsq hc
      have hk2 : a+b+c ≤ (K : ℤ)^2 := by nlinarith
      have hkm := mul_le_mul_of_nonneg_right hk2 (sq_nonneg (n : ℤ))
      nlinarith
  have hval (n : ℕ) (hn : 0 < n) : 0 < f.eval (n : ℤ) := by
    have hnn : (0 : ℤ) < n := by exact_mod_cast hn
    exact lt_of_lt_of_le (sq_pos_of_pos hnn) (hquad n hn).1
  have hcast (n : ℕ) (hn : 0 < n) : (⌊f.eval (n : ℤ)⌋₊ : ℤ) = f.eval (n : ℤ) := by
    rw [Nat.floor_int]
    exact Int.toNat_of_nonneg (hval n hn).le
  refine ⟨K, hK, hval, ?_, ?_⟩
  · intro n hn
    have hl : n*n ≤ ⌊f.eval (n : ℤ)⌋₊ := by
      exact_mod_cast (show (n : ℤ)*(n : ℤ) ≤ (⌊f.eval (n : ℤ)⌋₊ : ℤ) by
        rw [hcast n hn]; simpa only [pow_two] using (hquad n hn).1)
    exact hl.trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos hK hK))
  · intro n hn
    have hu : (⌊f.eval (n : ℤ)⌋₊ : ℤ) ≤ ((K : ℤ)*n)*((K : ℤ)*n) := by
      rw [hcast n hn]
      convert (hquad n hn).2 using 1 <;> ring
    exact_mod_cast hu

lemma quadratic_growth_after_shift {f : ℤ[X]} (hd : f.natDegree = 2)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    ∃ (t : ℤ) (K : ℕ), 0 < K ∧
      (∀ n : ℕ, 0 < n → 0 < (f.comp (X+C t)).eval (n : ℤ)) ∧
      (∀ n : ℕ, 0 < n → n*n ≤ K*K*⌊(f.comp (X+C t)).eval (n : ℤ)⌋₊) ∧
      (∀ n : ℕ, 0 < n → ⌊(f.comp (X+C t)).eval (n : ℤ)⌋₊ ≤ (K*n)*(K*n)) := by
  have ha := quadratic_lead_pos hd hpos
  obtain ⟨t, hb, hc⟩ := quadratic_shift_coeffs_nonneg ha (f.coeff 1) (f.coeff 0)
  obtain ⟨K, hK, hrest⟩ := quadratic_nonneg_coeff_growth (f.comp (X+C t))
    (f.coeff 2) (2*f.coeff 2*t+f.coeff 1) (f.coeff 2*t^2+f.coeff 1*t+f.coeff 0)
    ha hb hc (by
      intro n
      simp only [eval_comp, eval_add, eval_X, eval_C, eval_quadratic hd]
      ring)
  exact ⟨t, K, hK, hrest⟩


lemma limit_of_degree_two_and_root_mean (f : ℤ[X]) (hd : f.natDegree = 2)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n)
    {a : ℝ} (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)) / N) atTop (𝓝 a)) :
    Tendsto (fun x : ℝ => Erdos975Sum f x / (x * log x)) atTop (𝓝 (2*a)) := by
  obtain ⟨t, K, hK, hval, hl, hu⟩ := quadratic_growth_after_shift hd hpos
  apply (int_shift_limit_iff f t (2*a)).mp
  apply limit_of_quadratic_growth_and_root_mean (f.comp (X+Polynomial.C t)) hK hval hl hu
  simpa only [polynomialRootCount_comp_X_add_C] using hmean

end GeneralDivisors
namespace EulerComparison

noncomputable def fromPrimePowers {R : Type*} [CommMonoidWithZero R] (F : ℕ → ℕ → R) :
    ArithmeticFunction R where
  toFun n := if n = 0 then 0 else n.factorization.prod F
  map_zero' := by simp

lemma fromPrimePowers_apply {R : Type*} [CommMonoidWithZero R] (F : ℕ → ℕ → R)
    {n : ℕ} (hn : n ≠ 0) : fromPrimePowers F n = n.factorization.prod F := by
  simp only [fromPrimePowers, ArithmeticFunction.coe_mk, if_neg hn]

lemma fromPrimePowers_multiplicative {R : Type*} [CommMonoidWithZero R] (F : ℕ → ℕ → R) :
    (fromPrimePowers F).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [fromPrimePowers_apply]
  · intro m n hm hn hmn
    rw [fromPrimePowers_apply F (mul_ne_zero hm hn), fromPrimePowers_apply F hm,
      fromPrimePowers_apply F hn, Nat.factorization_mul hm hn]
    apply Finsupp.prod_add_index_of_disjoint
    simpa only [Nat.support_factorization] using hmn.disjoint_primeFactors

lemma fromPrimePowers_prime_pow {R : Type*} [CommMonoidWithZero R] (F : ℕ → ℕ → R)
    {p : ℕ} (hp : p.Prime) (hF0 : F p 0 = 1) (k : ℕ) :
    fromPrimePowers F (p^k) = F p k := by
  rw [fromPrimePowers_apply F (pow_ne_zero _ hp.ne_zero), hp.factorization_pow,
    Finsupp.prod_single_index hF0]

noncomputable def localSeries {R : Type*} [Semiring R] (f : ArithmeticFunction R) (p : ℕ) :
    PowerSeries R := PowerSeries.mk (fun k => f (p^k))

@[simp] lemma localSeries_coeff {R : Type*} [Semiring R] (f : ArithmeticFunction R) (p k : ℕ) :
    PowerSeries.coeff k (localSeries f p) = f (p^k) := PowerSeries.coeff_mk _ _

@[simp] lemma localSeries_constantCoeff {R : Type*} [Semiring R] (f : ArithmeticFunction R) (p : ℕ) :
    PowerSeries.constantCoeff (localSeries f p) = f 1 := by
  simp [localSeries, PowerSeries.constantCoeff_mk]

lemma localSeries_mul {R : Type*} [Semiring R] (f g : ArithmeticFunction R)
    {p : ℕ} (hp : p.Prime) : localSeries (f*g) p = localSeries f p * localSeries g p := by
  ext k
  rw [localSeries_coeff, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b => f a*g b), Nat.sum_divisors_prime_pow hp, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
      PowerSeries.coeff i (localSeries f p)*PowerSeries.coeff j (localSeries g p))]
  apply sum_congr rfl
  intro i hi
  rw [localSeries_coeff, localSeries_coeff, Nat.pow_div (by simpa using hi) hp.pos]

lemma localSeries_one {R : Type*} [Semiring R] {p : ℕ} (hp : p.Prime) :
    localSeries (1 : ArithmeticFunction R) p = 1 := by
  ext k
  simp only [localSeries_coeff, ArithmeticFunction.one_apply, PowerSeries.coeff_one]
  by_cases hk : k = 0
  · simp [hk]
  · have hpk : p^k ≠ 1 := (one_lt_pow₀ hp.one_lt hk).ne'
    simp only [if_neg hk, if_neg hpk]

noncomputable def dirichletInverse (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  fromPrimePowers (fun p k => PowerSeries.coeff k (localSeries f p)⁻¹)

lemma dirichletInverse_multiplicative (f : ArithmeticFunction ℝ) :
    (dirichletInverse f).IsMultiplicative := fromPrimePowers_multiplicative _

lemma dirichletInverse_localSeries (f : ArithmeticFunction ℝ) (hf1 : f 1 = 1)
    {p : ℕ} (hp : p.Prime) : localSeries (dirichletInverse f) p = (localSeries f p)⁻¹ := by
  ext k
  rw [localSeries_coeff, dirichletInverse, fromPrimePowers_prime_pow _ hp]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv, hf1]

lemma dirichletInverse_mul (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative) :
    dirichletInverse f * f = 1 := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((dirichletInverse_multiplicative f).mul hf) 1 ArithmeticFunction.isMultiplicative_one).mpr
  intro p k hp
  have hs : localSeries (dirichletInverse f*f) p = 1 := by
    rw [localSeries_mul _ _ hp, dirichletInverse_localSeries f hf.1 hp]
    exact PowerSeries.inv_mul_cancel _ (by simp [hf.1])
  have he := congrArg (PowerSeries.coeff k) hs
  rw [localSeries_coeff, ← localSeries_one hp, localSeries_coeff] at he
  exact he

noncomputable def correction (r a : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  r * dirichletInverse a

lemma correction_multiplicative {r a : ArithmeticFunction ℝ}
    (hr : r.IsMultiplicative) : (correction r a).IsMultiplicative :=
  hr.mul (dirichletInverse_multiplicative a)

lemma correction_mul (r a : ArithmeticFunction ℝ) (ha : a.IsMultiplicative) :
    correction r a * a = r := by
  rw [correction, mul_assoc, dirichletInverse_mul a ha, mul_one]

lemma mul_apply_prime (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) :
    (f*g) p = f 1*g p + f p*g 1 := by
  have he := congrArg (PowerSeries.coeff 1) (localSeries_mul f g hp)
  simpa [PowerSeries.coeff_mul, show Finset.antidiagonal 1 = {(0,1),(1,0)} by decide] using he

lemma correction_apply_prime (r a : ArithmeticFunction ℝ)
    (hr : r.IsMultiplicative) (ha : a.IsMultiplicative) {p : ℕ} (hp : p.Prime) :
    correction r a p = r p-a p := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f p) (correction_mul r a ha)
  dsimp only at h
  rw [mul_apply_prime _ _ hp, (correction_multiplicative hr).1, ha.1, one_mul, mul_one] at h
  linarith

lemma summable_of_prime_power_tails (f : ℕ → ℝ)
    (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hfn : ∀ n, 0 ≤ f n)
    (hmul : ∀ {m n}, m.Coprime n → f (m*n) = f m*f n)
    (hlocal : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ => f (p^k)))
    (htails : Summable (fun p : ℕ => if p.Prime then ∑' k : ℕ, f (p^(k+1)) else 0)) :
    Summable f := by
  classical
  let E : ℕ → ℝ := fun p => if p.Prime then ∑' k : ℕ, f (p^(k+1)) else 0
  have hE : ∀ p, 0 ≤ E p := by
    intro p
    dsimp [E]
    split_ifs
    · exact tsum_nonneg (fun k => hfn _)
    · exact le_rfl
  have hloc (p : ℕ) (hp : p.Prime) : ∑' k : ℕ, f (p^k) = 1 + E p := by
    rw [(hlocal p hp).tsum_eq_zero_add]
    simp only [pow_zero, hf1, E, if_pos hp]
  have hexp (N : ℕ) : (∏ p ∈ N.primesBelow, ∑' k : ℕ, f (p^k)) ≤ exp (∑' p, E p) := by
    calc
      _ ≤ ∏ p ∈ N.primesBelow, exp (E p) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact tsum_nonneg (fun k => hfn _)
        · intro p hp
          rw [hloc p (Nat.prime_of_mem_primesBelow hp)]
          simpa only [add_comm] using Real.add_one_le_exp (E p)
      _ = exp (∑ p ∈ N.primesBelow, E p) := (Real.exp_sum _ _).symm
      _ ≤ exp (∑' p, E p) := Real.exp_le_exp.mpr
        (htails.sum_le_tsum _ (fun p _ => hE p))
  apply summable_of_sum_range_le hfn
  intro N
  have hs := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hf1 hmul
    (fun {p} hp => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hfn _)] using hlocal p hp) N
  have hmem (n : ℕ) (hn : n ∈ (range N).erase 0) : n ∈ N.smoothNumbers :=
    Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero (mem_erase.mp hn).1) (mem_range.mp (mem_erase.mp hn).2)
  calc
    _ = ∑ n ∈ (range N).erase 0, f n := (sum_erase _ hf0).symm
    _ = ∑ n ∈ ((range N).erase 0).subtype (· ∈ N.smoothNumbers), f n :=
      (sum_subtype_of_mem f hmem).symm
    _ ≤ ∑' n : N.smoothNumbers, f n := hs.2.summable.sum_le_tsum _ (fun n _ => hfn n)
    _ = ∏ p ∈ N.primesBelow, ∑' k : ℕ, f (p^k) := hs.2.tsum_eq
    _ ≤ exp (∑' p, E p) := hexp N

lemma summable_norm_of_prime_power_tails (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative)
    (hlocal : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ => ‖f (p^k)‖))
    (htails : Summable (fun p : ℕ => if p.Prime then ∑' k : ℕ, ‖f (p^(k+1))‖ else 0)) :
    Summable (fun n : ℕ => ‖f n‖) := by
  apply summable_of_prime_power_tails (fun n => ‖f n‖) (by simp) (by simp [hf.1])
    (fun _ => norm_nonneg _) _ hlocal htails
  intro m n hmn
  dsimp only
  rw [hf.map_mul_of_coprime hmn, norm_mul]


noncomputable def divideByNat (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := f n / (n : ℝ)
  map_zero' := by simp

@[simp] lemma divideByNat_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    divideByNat f n = f n / (n : ℝ) := rfl

lemma divideByNat_multiplicative {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative) :
    (divideByNat f).IsMultiplicative := by
  constructor
  · simp [hf.1]
  · intro m n hmn
    simp only [divideByNat_apply, hf.map_mul_of_coprime hmn, Nat.cast_mul, div_mul_div_comm]

lemma prime_power_tail_bound (f : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime)
    {B : ℝ} (hB : 0 ≤ B) (hfp : f p = 0)
    (hbound : ∀ k : ℕ, 2 ≤ k → ‖f (p^k)‖ ≤ B)
    (hlocal : Summable (fun k : ℕ => ‖f (p^k)‖ / (p : ℝ)^k)) :
    (∑' k : ℕ, ‖f (p^(k+1))‖ / (p : ℝ)^(k+1)) ≤ 2*B/(p : ℝ)^2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hi0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hi1 : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp1
  have hi2 : (p : ℝ)⁻¹ ≤ 1/2 := (inv_le_comm₀ hp0 (by norm_num)).mpr (by simpa using hp2)
  have hg := summable_geometric_of_lt_one hi0 hi1
  have hshift : (∑' k : ℕ, ‖f (p^(k+1))‖ / (p : ℝ)^(k+1)) =
      ∑' k : ℕ, ‖f (p^(k+2))‖ / (p : ℝ)^(k+2) := by
    rw [((summable_nat_add_iff 1).mpr hlocal).tsum_eq_zero_add]
    simp only [zero_add, pow_one, hfp, norm_zero, zero_div, Nat.add_assoc]
  rw [hshift]
  calc
    _ ≤ ∑' k : ℕ, (B/(p : ℝ)^2) * ((p : ℝ)⁻¹)^k := by
      apply Summable.tsum_le_tsum _ ((summable_nat_add_iff 2).mpr hlocal) (hg.mul_left _)
      intro k
      calc
        _ ≤ B/(p : ℝ)^(k+2) := div_le_div_of_nonneg_right (hbound _ (by omega)) (by positivity)
        _ = (B/(p : ℝ)^2) * ((p : ℝ)⁻¹)^k := by
          simp only [pow_add, div_eq_mul_inv, mul_inv_rev, inv_pow]
          ring
    _ = (B/(p : ℝ)^2) * (1-(p : ℝ)⁻¹)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hi0 hi1]
    _ ≤ (B/(p : ℝ)^2)*2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (inv_le_comm₀ (sub_pos.mpr hi1) (by norm_num : (0 : ℝ) < 2)).mpr
      norm_num
      linarith
    _ = 2*B/(p : ℝ)^2 := by ring

lemma summable_divideByNat_of_good_primes (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (S : Finset ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ S → f p = 0 ∧ ∀ k : ℕ, 2 ≤ k → ‖f (p^k)‖ ≤ B)
    (hlocal : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ => f (p^k)/(p : ℝ)^k)) :
    Summable (fun n : ℕ => f n/(n : ℝ)) := by
  have hnorm (p : ℕ) (k : ℕ) : ‖divideByNat f (p^k)‖ = ‖f (p^k)‖/(p : ℝ)^k := by
    simp [divideByNat_apply, norm_div]
  have hlocal' (p : ℕ) (hp : p.Prime) : Summable (fun k : ℕ => ‖divideByNat f (p^k)‖) := by
    convert (hlocal p hp).norm using 1
    ext k
    simp [hnorm, norm_div]
  have hs : Summable (fun p : ℕ => if p.Prime then ∑' k : ℕ, ‖divideByNat f (p^(k+1))‖ else 0) := by
    apply ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left (2*B)).of_norm_bounded_eventually
    filter_upwards [S.eventually_cofinite_notMem] with p hpS
    by_cases hp : p.Prime
    · rw [if_pos hp, Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
      simp only [hnorm]
      obtain ⟨hfp, hb⟩ := hgood p hp hpS
      have hl : Summable (fun k : ℕ => ‖f (p^k)‖/(p : ℝ)^k) := by
        simpa only [hnorm] using hlocal' p hp
      simpa only [mul_one_div] using prime_power_tail_bound f hp hB hfp hb hl
    · simp only [if_neg hp, norm_zero]
      positivity
  exact (summable_norm_of_prime_power_tails _ (divideByNat_multiplicative hf) hlocal' hs).of_norm


lemma mul_prime_pow (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f*g) (p^k) = ∑ i ∈ range (k+1), f (p^i)*g (p^(k-i)) := by
  have he := congrArg (PowerSeries.coeff k) (localSeries_mul f g hp)
  simp only [localSeries_coeff, PowerSeries.coeff_mul] at he
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f (p^i)*g (p^j))] at he
  exact he

lemma divideByNat_mul (f g : ArithmeticFunction ℝ) :
    divideByNat (f*g) = divideByNat f * divideByNat g := by
  ext n
  simp only [divideByNat_apply, ArithmeticFunction.mul_apply, sum_div]
  apply sum_congr rfl
  intro x hx
  have hn := (Nat.mem_divisorsAntidiagonal.mp hx).1
  simp only [divideByNat_apply, div_mul_div_comm, ← Nat.cast_mul, hn]

lemma local_summable_mul (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime)
    (hf : Summable (fun k : ℕ => f (p^k)))
    (hg : Summable (fun k : ℕ => g (p^k))) :
    Summable (fun k : ℕ => (f*g) (p^k)) := by
  simpa only [mul_prime_pow f g hp] using
    (summable_norm_sum_mul_range_of_summable_norm hf.norm hg.norm).of_norm

lemma mul_prime_pow_bound (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime)
    (D : ℕ) {B R : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hfzero : ∀ i : ℕ, D < i → f (p^i) = 0)
    (hfbound : ∀ i : ℕ, ‖f (p^i)‖ ≤ B)
    (hgbound : ∀ i : ℕ, ‖g (p^i)‖ ≤ R) (k : ℕ) :
    ‖(f*g) (p^k)‖ ≤ (D+1 : ℕ)*B*R := by
  rw [mul_prime_pow f g hp]
  calc
    _ ≤ ∑ i ∈ range (k+1), ‖f (p^i)*g (p^(k-i))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range (k+1), if i ≤ D then B*R else 0 := by
      apply sum_le_sum
      intro i hi
      by_cases hiD : i ≤ D
      · rw [if_pos hiD, norm_mul]
        exact mul_le_mul (hfbound i) (hgbound _) (norm_nonneg _) hB
      · simp only [if_neg hiD, hfzero i (by omega), zero_mul, norm_zero, le_refl]
    _ = ({i ∈ range (k+1) | i ≤ D}.card : ℝ)*(B*R) := by
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ (D+1 : ℕ)*B*R := by
      have hcard : {i ∈ range (k+1) | i ≤ D}.card ≤ D+1 := by
        calc
          _ ≤ (range (D+1)).card := card_le_card (fun i hi => mem_range.mpr (by
            have := (mem_filter.mp hi).2; omega))
          _ = _ := card_range _
      have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (mul_nonneg hB hR)
      simpa only [mul_assoc] using hh

lemma correction_summable_of_local_inverse_bounds (r a : ArithmeticFunction ℝ)
    (hr : r.IsMultiplicative) (ha : a.IsMultiplicative)
    (S : Finset ℕ) (D : ℕ) {B R : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hlocalr : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ => r (p^k)/(p : ℝ)^k))
    (hinvzero : ∀ p : ℕ, p.Prime → ∀ k : ℕ, D < k → dirichletInverse a (p^k) = 0)
    (hinvbound : ∀ p : ℕ, p.Prime → ∀ k : ℕ, ‖dirichletInverse a (p^k)‖ ≤ B)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ S → r p = a p ∧ ∀ k : ℕ, ‖r (p^k)‖ ≤ R) :
    Summable (fun n : ℕ => correction r a n/(n : ℝ)) := by
  apply summable_divideByNat_of_good_primes _ (correction_multiplicative hr) S
    (show 0 ≤ (D+1 : ℕ)*B*R by positivity)
  · intro p hp hpS
    obtain ⟨he, hb⟩ := hgood p hp hpS
    constructor
    · rw [correction_apply_prime r a hr ha hp, he, sub_self]
    · intro k hk
      rw [correction, mul_comm r]
      exact mul_prime_pow_bound _ _ hp D hB hR (hinvzero p hp) (hinvbound p hp) hb k
  · intro p hp
    have hi : Summable (fun k : ℕ => divideByNat (dirichletInverse a) (p^k)) := by
      apply summable_of_ne_finset_zero (s := range (D+1))
      intro k hk
      rw [divideByNat_apply, hinvzero p hp k (by simpa using hk), zero_div]
    have hr' : Summable (fun k : ℕ => divideByNat r (p^k)) := by
      simpa only [divideByNat_apply, Nat.cast_pow] using hlocalr p hp
    have hh := local_summable_mul _ _ hp hr' hi
    simpa only [← divideByNat_mul, divideByNat_apply, Nat.cast_pow, correction] using hh


lemma prime_power_index_injective :
    Function.Injective (fun x : Nat.Primes × ℕ => (x.1 : ℕ)^(x.2+1)) := by
  intro x y hxy
  obtain ⟨hp, hk⟩ := x.1.property.pow_inj y.1.property hxy
  exact Prod.ext (Subtype.ext hp) hk

lemma summable_prime_power_tails_of_summable (f : ArithmeticFunction ℝ)
    (hs : Summable (fun n : ℕ => ‖f n‖)) :
    Summable (fun p : Nat.Primes => ∑' k : ℕ, f ((p : ℕ)^(k+1))) := by
  have hh := hs.comp_injective prime_power_index_injective
  have hn : Summable (fun p : Nat.Primes => ∑' k : ℕ, ‖f ((p : ℕ)^(k+1))‖) := hh.prod
  apply hn.of_norm_bounded
  intro p
  apply norm_tsum_le_tsum_norm
  exact (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mp hh |>.1 p

lemma tsum_pos_of_local_factors (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative)
    (hs : Summable (fun n : ℕ => ‖f n‖))
    (hpos : ∀ p : ℕ, p.Prime → 0 < ∑' k : ℕ, f (p^k)) :
    0 < ∑' n : ℕ, f n := by
  have ht := summable_prime_power_tails_of_summable f hs
  have he (p : Nat.Primes) : (∑' k : ℕ, f ((p : ℕ)^k)) =
      1 + ∑' k : ℕ, f ((p : ℕ)^(k+1)) := by
    have hlocal : Summable (fun k : ℕ => f ((p : ℕ)^k)) :=
      hs.of_norm.comp_injective (Nat.pow_right_injective p.property.two_le)
    rw [hlocal.tsum_eq_zero_add, pow_zero, hf.1]
  have hnz : (∑' n : ℕ, f n) ≠ 0 := by
    rw [← hf.eulerProduct_tprod hs]
    simp_rw [he]
    exact tprod_one_add_ne_zero_of_summable (fun p => by rw [← he p]; exact (hpos p p.property).ne') ht.norm
  have hprod := EulerProduct.eulerProduct_hasProd hf.1 hf.2 hs f.map_zero
  have hnonneg : 0 ≤ ∑' n : ℕ, f n := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hprod
    exact Filter.Eventually.of_forall (fun s => Finset.prod_nonneg (fun p hp => (hpos p p.property).le))
  exact lt_of_le_of_ne hnonneg hnz.symm

lemma local_tsum_mul (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime)
    (hf : Summable (fun k : ℕ => f (p^k)))
    (hg : Summable (fun k : ℕ => g (p^k))) :
    (∑' k : ℕ, (f*g) (p^k)) = (∑' k : ℕ, f (p^k))*(∑' k : ℕ, g (p^k)) := by
  simp_rw [mul_prime_pow f g hp]
  exact (tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf.norm hg.norm).symm

lemma local_tsum_pos (f : ArithmeticFunction ℝ) (hf1 : f 1 = 1)
    (hnonneg : ∀ n, 0 ≤ f n) (p : ℕ)
    (hs : Summable (fun k : ℕ => f (p^k))) : 0 < ∑' k : ℕ, f (p^k) := by
  have hh := hs.le_tsum 0 (fun k _ => hnonneg _)
  rw [pow_zero, hf1] at hh
  linarith

lemma correction_tsum_pos (r a : ArithmeticFunction ℝ)
    (hr : r.IsMultiplicative) (ha : a.IsMultiplicative)
    (hrnonneg : ∀ n : ℕ, 0 ≤ r n) (hanonneg : ∀ n : ℕ, 0 ≤ a n)
    (hlocalr : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ => r (p^k)/(p : ℝ)^k))
    (hlocala : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ => a (p^k)/(p : ℝ)^k))
    (hs : Summable (fun n : ℕ => correction r a n/(n : ℝ))) :
    0 < ∑' n : ℕ, correction r a n/(n : ℝ) := by
  apply tsum_pos_of_local_factors (divideByNat (correction r a))
    (divideByNat_multiplicative (correction_multiplicative hr)) hs.norm
  intro p hp
  have hrc : Summable (fun k : ℕ => divideByNat r (p^k)) := by
    simpa only [divideByNat_apply, Nat.cast_pow] using hlocalr p hp
  have hac : Summable (fun k : ℕ => divideByNat a (p^k)) := by
    simpa only [divideByNat_apply, Nat.cast_pow] using hlocala p hp
  have hgc : Summable (fun k : ℕ => divideByNat (correction r a) (p^k)) :=
    hs.comp_injective (Nat.pow_right_injective hp.two_le)
  have hp_r := local_tsum_pos (divideByNat r) (by simp [hr.1])
    (fun n => div_nonneg (hrnonneg n) (Nat.cast_nonneg n)) p hrc
  have hp_a := local_tsum_pos (divideByNat a) (by simp [ha.1])
    (fun n => div_nonneg (hanonneg n) (Nat.cast_nonneg n)) p hac
  have he := local_tsum_mul _ _ hp hgc hac
  rw [← divideByNat_mul, correction_mul r a ha] at he
  nlinarith

end EulerComparison

namespace GeneralDivisors

open Finset

lemma root_mean_of_local_model {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) (a : ArithmeticFunction ℝ)
    (ha : a.IsMultiplicative) (hanonneg : ∀ n : ℕ, 0 ≤ a n)
    {A : ℝ} (hA : 0 < A)
    (hmean : Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, a n)/(N : ℝ)) atTop (𝓝 A))
    (hlocala : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ => a (p^k)/(p : ℝ)^k))
    (D : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hinvzero : ∀ p : ℕ, p.Prime → ∀ k : ℕ, D < k → EulerComparison.dirichletInverse a (p^k) = 0)
    (hinvbound : ∀ p : ℕ, p.Prime → ∀ k : ℕ, ‖EulerComparison.dirichletInverse a (p^k)‖ ≤ B)
    (S : Finset ℕ) (hmatch : ∀ p : ℕ, p.Prime → p ∉ S → a p = polynomialRootCount f p) :
    ∃ c > (0 : ℝ), Tendsto (fun N : ℕ =>
      (∑ n ∈ Ioc 0 N, (polynomialRootCount f n : ℝ))/(N : ℝ)) atTop (𝓝 c) := by
  obtain ⟨T, hT⟩ := finite_bad_primes hdeg hirr
  let r := rootFunction f
  have hr : r.IsMultiplicative := rootFunction_multiplicative f
  have hrnonneg (n : ℕ) : 0 ≤ r n := by
    by_cases hn : n = 0
    · subst n
      simp [r]
    · rw [show r n = (polynomialRootCount f n : ℝ) from rootFunction_apply f hn]
      positivity
  have hlocalr (p : ℕ) (hp : p.Prime) : Summable (fun k : ℕ => r (p^k)/(p : ℝ)^k) := by
    have he (k : ℕ) : r (p^k) = (polynomialRootCount f (p^k) : ℝ) :=
      rootFunction_apply f (pow_ne_zero _ hp.ne_zero)
    simpa only [he] using summable_polynomialRootCount_prime_powers hdeg hirr hp
  have hgood (p : ℕ) (hp : p.Prime) (hpS : p ∉ S ∪ T) :
      r p = a p ∧ ∀ k : ℕ, ‖r (p^k)‖ ≤ (f.natDegree : ℝ) := by
    have hpS' : p ∉ S := fun h => hpS (mem_union_left _ h)
    have hpT : p ∉ T := fun h => hpS (mem_union_right _ h)
    constructor
    · rw [show r p = (polynomialRootCount f p : ℝ) from rootFunction_apply f hp.ne_zero]
      exact (hmatch p hp hpS').symm
    · intro k
      rw [Real.norm_eq_abs, abs_of_nonneg (hrnonneg _)]
      by_cases hk : k = 0
      · subst k
        rw [pow_zero, hr.1]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hdeg
      · rw [show r (p^k) = (polynomialRootCount f (p^k) : ℝ) from rootFunction_apply f (pow_ne_zero _ hp.ne_zero)]
        exact_mod_cast (hT p hp hpT k (Nat.pos_of_ne_zero hk)).2
  have hs := EulerComparison.correction_summable_of_local_inverse_bounds r a hr ha
    (S ∪ T) D hB (Nat.cast_nonneg f.natDegree) hlocalr hinvzero hinvbound hgood
  have hc := EulerComparison.correction_tsum_pos r a hr ha hrnonneg hanonneg hlocalr hlocala hs
  refine ⟨A * ∑' n : ℕ, EulerComparison.correction r a n/(n : ℝ), mul_pos hA hc, ?_⟩
  have hh := MeanTransfer.convolution_mean a (EulerComparison.correction r a) hmean hs
  rw [EulerComparison.correction_mul r a ha] at hh
  convert hh using 1
  ext N
  congr 1
  apply sum_congr rfl
  intro n hn
  exact (rootFunction_apply f (Nat.ne_of_gt (mem_Ioc.mp hn).1)).symm

lemma degree_two_limit_of_local_model {f : ℤ[X]} (hd : f.natDegree = 2)
    (hirr : Irreducible f) (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n)
    (a : ArithmeticFunction ℝ) (ha : a.IsMultiplicative) (hanonneg : ∀ n : ℕ, 0 ≤ a n)
    {A : ℝ} (hA : 0 < A)
    (hmean : Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, a n)/(N : ℝ)) atTop (𝓝 A))
    (hlocala : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ => a (p^k)/(p : ℝ)^k))
    (D : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hinvzero : ∀ p : ℕ, p.Prime → ∀ k : ℕ, D < k → EulerComparison.dirichletInverse a (p^k) = 0)
    (hinvbound : ∀ p : ℕ, p.Prime → ∀ k : ℕ, ‖EulerComparison.dirichletInverse a (p^k)‖ ≤ B)
    (S : Finset ℕ) (hmatch : ∀ p : ℕ, p.Prime → p ∉ S → a p = polynomialRootCount f p) :
    ∃ c > (0 : ℝ), Tendsto (fun x : ℝ => Erdos975Sum f x/(x*log x)) atTop (𝓝 c) := by
  obtain ⟨c, hc, hroot⟩ := root_mean_of_local_model (by omega : f.natDegree ≠ 0) hirr a ha hanonneg
    hA hmean hlocala D hB hinvzero hinvbound S hmatch
  exact ⟨2*c, mul_pos (by norm_num) hc, limit_of_degree_two_and_root_mean f hd hpos hroot⟩

end GeneralDivisors
namespace IdealEuler

open Ideal UniqueFactorizationMonoid
open scoped NumberField Classical

variable (K : Type*) [Field K] [NumberField K]

lemma prime_norm_prime_power (P : Ideal (𝓞 K)) (hP : Prime P) :
    ∃ p : ℕ, p.Prime ∧ ∃ e > (0 : ℕ), absNorm P = p^e := by
  letI : P.IsPrime := Ideal.isPrime_of_prime hP
  letI : NeZero P := ⟨hP.ne_zero⟩
  let p : ℕ := absNorm (Ideal.under ℤ P)
  have hp : p.Prime := Nat.absNorm_under_prime P
  letI : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    dsimp [p]
    rw [Int.ideal_span_absNorm_eq_self]
    infer_instance
  have he := Ideal.absNorm_eq_pow_inertiaDeg' P hp
  refine ⟨p, hp, _, ?_, he⟩
  by_contra h
  have he0 : (Ideal.span {(p : ℤ)}).inertiaDeg P = 0 := by omega
  rw [he0, pow_zero, Ideal.absNorm_eq_one_iff] at he
  exact hP.not_unit (Ideal.isUnit_iff.mpr he)

lemma norm_coprime_isRelPrime {I J : Ideal (𝓞 K)} (h : (absNorm I).Coprime (absNorm J)) :
    IsRelPrime I J := by
  intro D hDI hDJ
  apply Ideal.isUnit_iff.mpr
  apply Ideal.absNorm_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes h (map_dvd absNorm hDI) (map_dvd absNorm hDJ)

lemma norm_multiset_prod_coprime (s : Multiset (Ideal (𝓞 K))) (n : ℕ)
    (h : ∀ P ∈ s, (absNorm P).Coprime n) : (absNorm s.prod).Coprime n := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons P s ih =>
    rw [Multiset.prod_cons, map_mul]
    exact (h P (Multiset.mem_cons_self _ _)).mul_left (ih (fun Q hQ => h Q (Multiset.mem_cons_of_mem hQ)))

lemma split_norm_coprime {m n : ℕ} (hmn : m.Coprime n)
    (I : Ideal (𝓞 K)) (hI : absNorm I = m*n) (hm : m ≠ 0) (hn : n ≠ 0) :
    ∃ J L : Ideal (𝓞 K), J*L = I ∧ absNorm J = m ∧ absNorm L = n := by
  classical
  have hI0 : I ≠ 0 := by
    intro h
    have hmn0 : m*n ≠ 0 := mul_ne_zero hm hn
    exact hmn0 (by simpa [h] using hI.symm)
  let s := normalizedFactors I
  let J := (s.filter (fun P => (absNorm P).Coprime n)).prod
  let L := (s.filter (fun P => ¬(absNorm P).Coprime n)).prod
  have he : J*L = I := by
    rw [show J*L = s.prod from Multiset.prod_filter_mul_prod_filter_not _]
    exact associated_iff_eq.mp (prod_normalizedFactors hI0)
  have hJn : (absNorm J).Coprime n := by
    apply norm_multiset_prod_coprime K
    intro P hP
    exact (Multiset.mem_filter.mp hP).2
  have hLm : (absNorm L).Coprime m := by
    apply norm_multiset_prod_coprime K
    intro P hP
    obtain ⟨hPs, hPn⟩ := Multiset.mem_filter.mp hP
    obtain ⟨p, hp, e, hepos, heq⟩ := prime_norm_prime_power K P (prime_of_normalized_factor P hPs)
    rw [heq] at hPn ⊢
    rw [Nat.coprime_pow_left_iff hepos] at hPn
    have hpn : p ∣ n := by simpa only [hp.coprime_iff_not_dvd, not_not] using hPn
    exact (Nat.Coprime.of_dvd_right hpn hmn).symm.pow_left e
  have hprod : absNorm J*absNorm L = m*n := by rw [← map_mul, he, hI]
  have hJm : absNorm J = m := by
    apply Nat.dvd_antisymm
    · exact hJn.dvd_of_dvd_mul_right (by rw [← hprod]; exact dvd_mul_right _ _)
    · exact hLm.symm.dvd_of_dvd_mul_right (by rw [hprod]; exact dvd_mul_right _ _)
  have hLn : absNorm L = n := by
    rw [hJm] at hprod
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) hprod
  exact ⟨J, L, he, hJm, hLn⟩

lemma mul_norm_pair_injective {m n : ℕ} (hmn : m.Coprime n) :
    Function.Injective (fun x : {I : Ideal (𝓞 K) // absNorm I = m} ×
      {I : Ideal (𝓞 K) // absNorm I = n} => x.1.val*x.2.val) := by
  intro x y hxy
  dsimp only at hxy
  have hcop : IsRelPrime x.1.val y.2.val := norm_coprime_isRelPrime K (by simpa [x.1.property, y.2.property])
  have hcop' : IsRelPrime y.1.val x.2.val := norm_coprime_isRelPrime K (by simpa [y.1.property, x.2.property])
  have h1 : x.1.val = y.1.val := by
    apply le_antisymm
    · apply Ideal.dvd_iff_le.mp
      exact hcop'.dvd_of_dvd_mul_right (by rw [hxy]; exact dvd_mul_right _ _)
    · apply Ideal.dvd_iff_le.mp
      exact hcop.dvd_of_dvd_mul_right (by rw [← hxy]; exact dvd_mul_right _ _)
  have h2 : x.2.val = y.2.val := by
    have hc : IsRelPrime x.2.val y.1.val := hcop'.symm
    have hc' : IsRelPrime y.2.val x.1.val := hcop.symm
    apply le_antisymm
    · apply Ideal.dvd_iff_le.mp
      exact hc'.dvd_of_dvd_mul_left (by rw [hxy]; exact dvd_mul_left _ _)
    · apply Ideal.dvd_iff_le.mp
      exact hc.dvd_of_dvd_mul_left (by rw [← hxy]; exact dvd_mul_left _ _)
  exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)

lemma norm_count_mul {m n : ℕ} (hmn : m.Coprime n) (hm : m ≠ 0) (hn : n ≠ 0) :
    Nat.card {I : Ideal (𝓞 K) // absNorm I = m*n} =
      Nat.card {I : Ideal (𝓞 K) // absNorm I = m} * Nat.card {I : Ideal (𝓞 K) // absNorm I = n} := by
  let F : ({I : Ideal (𝓞 K) // absNorm I = m} × {I : Ideal (𝓞 K) // absNorm I = n}) →
      {I : Ideal (𝓞 K) // absNorm I = m*n} :=
    fun x => ⟨x.1.val*x.2.val, by rw [map_mul, x.1.property, x.2.property]⟩
  have hFinj : Function.Injective F := by
    intro x y hxy
    apply mul_norm_pair_injective K hmn
    exact congrArg Subtype.val hxy
  have hFsurj : Function.Surjective F := by
    intro I
    obtain ⟨J, L, he, hJ, hL⟩ := split_norm_coprime K hmn I.val I.property hm hn
    exact ⟨(⟨J,hJ⟩,⟨L,hL⟩), Subtype.ext he⟩
  rw [← Nat.card_congr (Equiv.ofBijective F ⟨hFinj, hFsurj⟩), Nat.card_prod]


lemma norm_prime_power_support {p : ℕ} (hp : p.Prime) {k : ℕ}
    {I : Ideal (𝓞 K)} (hI : absNorm I = p^k) {P : Ideal (𝓞 K)}
    (hP : P ∈ normalizedFactors I) : P ∈ normalizedFactors (span {(p : 𝓞 K)}) := by
  have hpr := prime_of_normalized_factor P hP
  have hPi : P.IsPrime := Ideal.isPrime_of_prime hpr
  have hIP : I ≤ P := Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hP)
  have hpmem : (p : 𝓞 K)^k ∈ P := by
    apply hIP
    simpa only [hI, Nat.cast_pow] using Ideal.absNorm_mem I
  have hPmem : (p : 𝓞 K) ∈ P := hPi.mem_of_pow_mem k hpmem
  apply (UniqueFactorizationMonoid.mem_normalizedFactors_iff _).mpr
  · exact ⟨hpr, Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hPmem)⟩
  · intro h
    have hh : (p : 𝓞 K) = 0 := Ideal.span_singleton_eq_bot.mp h
    exact (Nat.cast_ne_zero.mpr hp.ne_zero : (p : 𝓞 K) ≠ 0) hh

lemma norm_prime_power_count_le {p : ℕ} (hp : p.Prime) {k : ℕ}
    {I : Ideal (𝓞 K)} (hI : absNorm I = p^k) (P : Ideal (𝓞 K)) :
    (normalizedFactors I).count P ≤ k := by
  classical
  by_cases hP : P ∈ normalizedFactors I
  · have hpr := prime_of_normalized_factor P hP
    have hI0 : I ≠ 0 := by
      intro h
      have hh := pow_ne_zero k hp.ne_zero
      exact hh (by simpa [h] using hI.symm)
    have hdiv : absNorm P ∣ p^k := by
      rw [← hI]
      exact map_dvd absNorm (dvd_of_mem_normalizedFactors hP)
    obtain ⟨e, he, heq⟩ := (Nat.dvd_prime_pow hp).mp hdiv
    have he0 : 0 < e := by
      by_contra h
      have hezero : e = 0 := by omega
      rw [hezero, pow_zero, Ideal.absNorm_eq_one_iff] at heq
      exact hpr.not_unit (Ideal.isUnit_iff.mpr heq)
    have hpdiv : p ∣ absNorm P := by
      rw [heq]
      exact dvd_pow_self _ (Nat.ne_of_gt he0)
    have hpd : P^((normalizedFactors I).count P) ∣ I := by
      have hh := Multiset.prod_dvd_prod_of_le
        (Multiset.le_count_iff_replicate_le.mp (le_refl ((normalizedFactors I).count P)))
      rw [Multiset.prod_replicate] at hh
      exact hh.trans (Associated.dvd (prod_normalizedFactors hI0))
    have hnormdiv : p^((normalizedFactors I).count P) ∣ p^k := by
      rw [← hI]
      apply (pow_dvd_pow_of_dvd hpdiv _).trans
      simpa only [map_pow] using map_dvd absNorm hpd
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hnormdiv
  · simp [Multiset.count_eq_zero_of_notMem hP]

lemma norm_count_prime_power_bound {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // absNorm I = p^k} ≤
      (k+1)^((normalizedFactors (span {(p : 𝓞 K)})).toFinset.card) := by
  classical
  let S := (normalizedFactors (span {(p : 𝓞 K)})).toFinset
  let F : {I : Ideal (𝓞 K) // absNorm I = p^k} → (S → Fin (k+1)) :=
    fun I P => ⟨(normalizedFactors I.val).count P.val,
      Nat.lt_succ_of_le (norm_prime_power_count_le K hp I.property P.val)⟩
  have hF : Function.Injective F := by
    intro I J hIJ
    apply Subtype.ext
    have hI0 : I.val ≠ 0 := by
      intro h
      exact pow_ne_zero k hp.ne_zero (by simpa [h] using I.property.symm)
    have hJ0 : J.val ≠ 0 := by
      intro h
      exact pow_ne_zero k hp.ne_zero (by simpa [h] using J.property.symm)
    apply associated_iff_eq.mp
    apply (associated_iff_normalizedFactors_eq_normalizedFactors hI0 hJ0).mpr
    apply Multiset.ext.mpr
    intro P
    by_cases hP : P ∈ S
    · exact congrArg (fun z => (z ⟨P,hP⟩).val) hIJ
    · have hPi : P ∉ normalizedFactors I.val := fun h => hP (Multiset.mem_toFinset.mpr
        (norm_prime_power_support K hp I.property h))
      have hPj : P ∉ normalizedFactors J.val := fun h => hP (Multiset.mem_toFinset.mpr
        (norm_prime_power_support K hp J.property h))
      simp only [Multiset.count_eq_zero_of_notMem hPi, Multiset.count_eq_zero_of_notMem hPj]
  have hb := Nat.card_le_card_of_injective F hF
  rw [Nat.card_fun, Nat.card_fin] at hb
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, S] using hb

lemma norm_count_prime_power_summable {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => (Nat.card {I : Ideal (𝓞 K) // absNorm I = p^k} : ℝ)/(p : ℝ)^k) := by
  classical
  let d := (normalizedFactors (span {(p : 𝓞 K)})).toFinset.card
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hi : ‖(p : ℝ)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp0)]
    exact (inv_lt_one₀ hp0).mpr hp1
  have hs := (summable_nat_add_iff 1).mpr (summable_pow_mul_geometric_of_norm_lt_one d hi)
  have hs' : Summable (fun k : ℕ => ((k : ℝ)+1)^d/(p : ℝ)^k) := by
    convert hs.mul_left (p : ℝ) using 1
    ext k
    simp only [Nat.cast_add, Nat.cast_one, pow_succ, inv_pow]
    field_simp
  apply hs'.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast norm_count_prime_power_bound K hp k

end IdealEuler

namespace MeanTransfer

open Finset

lemma idealNormFunction_multiplicative (K : Type*) [Field K] [NumberField K] :
    (idealNormFunction K).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [idealNormFunction, Ideal.absNorm_eq_one_iff]
  · intro m n hm hn hmn
    simp only [idealNormFunction, ArithmeticFunction.coe_mk, if_neg hm, if_neg hn,
      if_neg (mul_ne_zero hm hn)]
    exact_mod_cast IdealEuler.norm_count_mul K hmn hm hn

lemma idealNormFunction_nonneg (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    0 ≤ idealNormFunction K n := by
  dsimp [idealNormFunction]
  split_ifs <;> positivity

lemma idealNormFunction_local_summable (K : Type*) [Field K] [NumberField K]
    {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => idealNormFunction K (p^k)/(p : ℝ)^k) := by
  simpa only [idealNormFunction, ArithmeticFunction.coe_mk, if_neg (pow_ne_zero _ hp.ne_zero)] using
    IdealEuler.norm_count_prime_power_summable K hp

end MeanTransfer
namespace GeneralDivisors

lemma root_mean_of_numberField_local_data {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) (K : Type*) [Field K] [NumberField K]
    (D : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hinvzero : ∀ p : ℕ, p.Prime → ∀ k : ℕ, D < k →
      EulerComparison.dirichletInverse (MeanTransfer.idealNormFunction K) (p^k) = 0)
    (hinvbound : ∀ p : ℕ, p.Prime → ∀ k : ℕ,
      ‖EulerComparison.dirichletInverse (MeanTransfer.idealNormFunction K) (p^k)‖ ≤ B)
    (S : Finset ℕ) (hmatch : ∀ p : ℕ, p.Prime → p ∉ S →
      MeanTransfer.idealNormFunction K p = polynomialRootCount f p) :
    ∃ c > (0 : ℝ), Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Ioc 0 N, (polynomialRootCount f n : ℝ))/(N : ℝ)) atTop (𝓝 c) := by
  exact root_mean_of_local_model hdeg hirr (MeanTransfer.idealNormFunction K)
    (MeanTransfer.idealNormFunction_multiplicative K) (MeanTransfer.idealNormFunction_nonneg K)
    (NumberField.dedekindZeta_residue_pos K) (MeanTransfer.idealNormFunction_mean K)
    (fun p hp => MeanTransfer.idealNormFunction_local_summable K hp)
    D hB hinvzero hinvbound S hmatch

end GeneralDivisors

namespace IdealEuler

open Finset Ideal UniqueFactorizationMonoid
open scoped NumberField Classical
variable (K : Type*) [Field K] [NumberField K]

lemma ideal_eq_prod_count {I : Ideal (𝓞 K)} (hI : I ≠ 0) (S : Finset (Ideal (𝓞 K)))
    (hs : (normalizedFactors I).toFinset ⊆ S) :
    I = ∏ P ∈ S, P^((normalizedFactors I).count P) := by
  rw [← Finset.prod_multiset_count_of_subset _ S hs]
  exact (associated_iff_eq.mp (prod_normalizedFactors hI)).symm

lemma factors_count_prod (S : Finset (Ideal (𝓞 K))) (e : Ideal (𝓞 K) → ℕ)
    (hS : ∀ P ∈ S, Prime P) (Q : Ideal (𝓞 K)) :
    (normalizedFactors (∏ P ∈ S, P^(e P))).count Q = if Q ∈ S then e Q else 0 := by
  induction S using Finset.induction with
  | empty => simp only [prod_empty, normalizedFactors_one, Multiset.count_zero, notMem_empty, if_false]
  | insert P S hPS ih =>
    have hP : Prime P := hS P (mem_insert_self _ _)
    have hS' : ∀ Q ∈ S, Prime Q := fun Q hQ => hS Q (mem_insert_of_mem hQ)
    rw [prod_insert hPS, normalizedFactors_mul (pow_ne_zero _ hP.ne_zero)
      (Finset.prod_ne_zero_iff.mpr (fun Q hQ => pow_ne_zero _ (hS' Q hQ).ne_zero)),
      normalizedFactors_of_irreducible_pow hP.irreducible, normalize_eq, Multiset.count_add,
      Multiset.count_replicate, ih hS']
    by_cases hPQ : P = Q
    · subst Q
      simp [hPS]
    · simp [hPQ, Ne.symm hPQ]

noncomputable def weightedFactorCount (w : Ideal (𝓞 K) → ℕ) (I : Ideal (𝓞 K)) :
    Ideal (𝓞 K) →₀ ℕ :=
  Finsupp.onFinset (normalizedFactors I).toFinset (fun P => w P*(normalizedFactors I).count P)
    (fun P hP => Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (Nat.pos_of_ne_zero
      (right_ne_zero_of_mul hP))))

@[simp] lemma weightedFactorCount_apply (w : Ideal (𝓞 K) → ℕ) (I P : Ideal (𝓞 K)) :
    weightedFactorCount K w I P = w P*(normalizedFactors I).count P := rfl

lemma norm_eq_pow_sum_count {p : ℕ} (S : Finset (Ideal (𝓞 K))) (w : Ideal (𝓞 K) → ℕ)
    (hw : ∀ P ∈ S, absNorm P = p^(w P)) {I : Ideal (𝓞 K)} (hI : I ≠ 0)
    (hs : (normalizedFactors I).toFinset ⊆ S) :
    absNorm I = p^(∑ P ∈ S, w P*(normalizedFactors I).count P) := by
  conv_lhs => rw [ideal_eq_prod_count K hI S hs]
  rw [map_prod]
  simp only [map_pow]
  calc
    _ = ∏ P ∈ S, p^(w P*(normalizedFactors I).count P) := by
      apply prod_congr rfl
      intro P hP
      rw [hw P hP, ← pow_mul]
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

lemma norm_prod_powers {p : ℕ} (S : Finset (Ideal (𝓞 K))) (w e : Ideal (𝓞 K) → ℕ)
    (hw : ∀ P ∈ S, absNorm P = p^(w P)) :
    absNorm (∏ P ∈ S, P^(e P)) = p^(∑ P ∈ S, w P*e P) := by
  rw [map_prod]
  simp only [map_pow]
  calc
    _ = ∏ P ∈ S, p^(w P*e P) := by
      apply prod_congr rfl
      intro P hP
      rw [hw P hP, ← pow_mul]
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _


noncomputable def idealWeightedEquiv {p : ℕ} (hp : p.Prime) (k : ℕ)
    (S : Finset (Ideal (𝓞 K))) (w : Ideal (𝓞 K) → ℕ)
    (hS : ∀ P ∈ S, Prime P) (hwpos : ∀ P ∈ S, 0 < w P)
    (hwnorm : ∀ P ∈ S, absNorm P = p^(w P))
    (hsupport : ∀ I : Ideal (𝓞 K), absNorm I = p^k → (normalizedFactors I).toFinset ⊆ S) :
    {I : Ideal (𝓞 K) // absNorm I = p^k} ≃
      {F ∈ S.finsuppAntidiag k | ∀ P ∈ S, w P ∣ F P} := by
  classical
  have hne (I : Ideal (𝓞 K)) (hI : absNorm I = p^k) : I ≠ 0 := by
    intro h
    exact pow_ne_zero k hp.ne_zero (by simpa [h] using hI.symm)
  let F : {I : Ideal (𝓞 K) // absNorm I = p^k} →
      {F ∈ S.finsuppAntidiag k | ∀ P ∈ S, w P ∣ F P} := fun I =>
    ⟨weightedFactorCount K w I.val, by
      simp only [mem_filter]
      refine ⟨mem_finsuppAntidiag.mpr ⟨?_, ?_⟩, ?_⟩
      · simp only [weightedFactorCount_apply]
        apply Nat.pow_right_injective hp.two_le
        exact (norm_eq_pow_sum_count K S w hwnorm (hne I I.property)
          (hsupport I I.property)).symm.trans I.property
      · intro P hP
        have hPc : (normalizedFactors I.val).count P ≠ 0 := by
          have hh := Finsupp.mem_support_iff.mp hP
          rw [weightedFactorCount_apply] at hh
          exact right_ne_zero_of_mul hh
        exact hsupport I I.property (Multiset.mem_toFinset.mpr
          (Multiset.count_pos.mp (Nat.pos_of_ne_zero hPc)))
      · intro P hP
        rw [weightedFactorCount_apply]
        exact dvd_mul_right _ _⟩
  apply Equiv.ofBijective F
  constructor
  · intro I J hIJ
    apply Subtype.ext
    apply associated_iff_eq.mp
    apply (associated_iff_normalizedFactors_eq_normalizedFactors (hne I I.property) (hne J J.property)).mpr
    apply Multiset.ext.mpr
    intro P
    by_cases hP : P ∈ S
    · have he := congrArg (fun z => z.val P) hIJ
      change w P*(normalizedFactors I.val).count P = w P*(normalizedFactors J.val).count P at he
      exact Nat.eq_of_mul_eq_mul_left (hwpos P hP) he
    · have hPi : P ∉ normalizedFactors I.val := fun h => hP (hsupport I I.property (Multiset.mem_toFinset.mpr h))
      have hPj : P ∉ normalizedFactors J.val := fun h => hP (hsupport J J.property (Multiset.mem_toFinset.mpr h))
      simp only [Multiset.count_eq_zero_of_notMem hPi, Multiset.count_eq_zero_of_notMem hPj]
  · intro b
    have hb : b.val ∈ S.finsuppAntidiag k ∧ ∀ P ∈ S, w P ∣ b.val P := by
      simpa only [mem_filter] using b.property
    obtain ⟨hbmem, hbdiv⟩ := hb
    obtain ⟨hbsum, hbsub⟩ := mem_finsuppAntidiag.mp hbmem
    let e : Ideal (𝓞 K) → ℕ := fun P => b.val P/w P
    let I : Ideal (𝓞 K) := ∏ P ∈ S, P^(e P)
    have hI : absNorm I = p^k := by
      rw [norm_prod_powers K S w e hwnorm]
      congr 1
      calc
        ∑ P ∈ S, w P*e P = ∑ P ∈ S, b.val P :=
          sum_congr rfl (fun P hP => Nat.mul_div_cancel' (hbdiv P hP))
        _ = k := hbsum
    refine ⟨⟨I,hI⟩, ?_⟩
    apply Subtype.ext
    apply Finsupp.ext
    intro P
    change weightedFactorCount K w I P = b.val P
    rw [weightedFactorCount_apply, factors_count_prod K S e hS]
    by_cases hP : P ∈ S
    · rw [if_pos hP]
      exact Nat.mul_div_cancel' (hbdiv P hP)
    · rw [if_neg hP, mul_zero]
      exact (Finsupp.notMem_support_iff.mp (fun h => hP (hbsub h))).symm

lemma norm_count_eq_weightedAntidiag {p : ℕ} (hp : p.Prime) (k : ℕ)
    (S : Finset (Ideal (𝓞 K))) (w : Ideal (𝓞 K) → ℕ)
    (hS : ∀ P ∈ S, Prime P) (hwpos : ∀ P ∈ S, 0 < w P)
    (hwnorm : ∀ P ∈ S, absNorm P = p^(w P))
    (hsupport : ∀ I : Ideal (𝓞 K), absNorm I = p^k → (normalizedFactors I).toFinset ⊆ S) :
    Nat.card {I : Ideal (𝓞 K) // absNorm I = p^k} =
      {F ∈ S.finsuppAntidiag k | ∀ P ∈ S, w P ∣ F P}.card := by
  rw [Nat.card_congr (idealWeightedEquiv K hp k S w hS hwpos hwnorm hsupport),
    Nat.card_eq_fintype_card, Fintype.card_coe]

noncomputable def geomFactor (w : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (fun k => if w ∣ k then 1 else 0)

@[simp] lemma geomFactor_coeff (w k : ℕ) :
    PowerSeries.coeff k (geomFactor w) = if w ∣ k then 1 else 0 := PowerSeries.coeff_mk _ _

lemma geomFactor_mul_one_sub {w : ℕ} (hw : 0 < w) :
    geomFactor w * (1-PowerSeries.X^w) = 1 := by
  ext k
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow', geomFactor_coeff, PowerSeries.coeff_one]
  by_cases hk : k = 0
  · subst k
    simp [show ¬w ≤ 0 by omega]
  · rw [if_neg hk]
    by_cases hwk : w ≤ k
    · rw [if_pos hwk, geomFactor_coeff]
      simp only [Nat.dvd_sub_iff_left hwk (dvd_refl w)]
      exact sub_self _
    · have hnot : ¬w ∣ k := fun h => hwk (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) h)
      simp [hwk, hnot]

lemma geomFactor_prod_coeff {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℕ) (k : ℕ) :
    PowerSeries.coeff k (∏ i ∈ S, geomFactor (w i)) =
      ({F ∈ S.finsuppAntidiag k | ∀ i ∈ S, w i ∣ F i}.card : ℝ) := by
  rw [PowerSeries.coeff_prod]
  simp only [geomFactor_coeff, Finset.prod_ite_zero, prod_const_one]
  rw [card_filter, Nat.cast_sum]
  apply sum_congr rfl
  intro i hi
  split_ifs <;> simp

lemma inverseFactor_prod_coeff_bound {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℕ) :
    ∀ k : ℕ, ‖PowerSeries.coeff k (∏ i ∈ S, (1-PowerSeries.X^(w i) : PowerSeries ℝ))‖ ≤ 2^S.card := by
  induction S using Finset.induction with
  | empty => intro k; simp [PowerSeries.coeff_one]; split_ifs <;> norm_num
  | insert i S hi ih =>
    intro k
    rw [prod_insert hi, mul_comm (1-PowerSeries.X^(w i)), mul_sub, mul_one, map_sub,
      PowerSeries.coeff_mul_X_pow', card_insert_of_notMem hi, pow_succ]
    calc
      _ ≤ ‖PowerSeries.coeff k (∏ j ∈ S, (1-PowerSeries.X^(w j) : PowerSeries ℝ))‖ +
          ‖if w i ≤ k then PowerSeries.coeff (k-w i) (∏ j ∈ S, (1-PowerSeries.X^(w j) : PowerSeries ℝ)) else 0‖ := norm_sub_le _ _
      _ ≤ 2^S.card + 2^S.card := by
        apply add_le_add (ih k)
        split_ifs
        · exact ih _
        · simp
      _ = _ := by ring

lemma inverseFactor_prod_coeff_zero {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℕ) :
    ∀ k : ℕ, (∑ i ∈ S, w i) < k →
      PowerSeries.coeff k (∏ i ∈ S, (1-PowerSeries.X^(w i) : PowerSeries ℝ)) = 0 := by
  induction S using Finset.induction with
  | empty => intro k hk; simp only [sum_empty] at hk; simp [PowerSeries.coeff_one, hk.ne']
  | insert i S hi ih =>
    intro k hk
    rw [sum_insert hi] at hk
    rw [prod_insert hi, mul_comm (1-PowerSeries.X^(w i)), mul_sub, mul_one, map_sub,
      PowerSeries.coeff_mul_X_pow', ih k (by omega)]
    split_ifs with hik
    · rw [ih (k-w i) (by omega), sub_zero]
    · exact sub_zero _

lemma geomFactor_prod_mul_inverse {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℕ)
    (hw : ∀ i ∈ S, 0 < w i) :
    (∏ i ∈ S, geomFactor (w i)) * (∏ i ∈ S, (1-PowerSeries.X^(w i) : PowerSeries ℝ)) = 1 := by
  rw [← prod_mul_distrib]
  exact prod_eq_one (fun i hi => geomFactor_mul_one_sub (hw i hi))


lemma norm_span_natCast (p : ℕ) :
    absNorm (span {(p : 𝓞 K)}) = p^(Module.finrank ℚ K) := by
  rw [Ideal.absNorm_span_singleton]
  have he : Algebra.norm ℤ (p : 𝓞 K) = (p : ℤ)^(Module.finrank ℤ (𝓞 K)) := by
    simpa only [map_natCast, ← Module.finrank_eq_card_basis (Module.Free.chooseBasis ℤ (𝓞 K))] using
      Algebra.norm_algebraMap_of_basis (Module.Free.chooseBasis ℤ (𝓞 K)) (p : ℤ)
  rw [he, Int.natAbs_pow, Int.natAbs_natCast, NumberField.RingOfIntegers.rank K]

lemma exists_local_ideal_weights {p : ℕ} (hp : p.Prime) :
    ∃ (S : Finset (Ideal (𝓞 K))) (w : Ideal (𝓞 K) → ℕ),
      (∀ P ∈ S, Prime P) ∧ (∀ P ∈ S, 0 < w P) ∧
      (∀ P ∈ S, absNorm P = p^(w P)) ∧
      (∑ P ∈ S, w P) ≤ Module.finrank ℚ K ∧
      (∀ k : ℕ, ∀ I : Ideal (𝓞 K), absNorm I = p^k → (normalizedFactors I).toFinset ⊆ S) := by
  classical
  let J : Ideal (𝓞 K) := span {(p : 𝓞 K)}
  let S := (normalizedFactors J).toFinset
  have hJ0 : J ≠ 0 := by
    intro h
    exact (Nat.cast_ne_zero.mpr hp.ne_zero : (p : 𝓞 K) ≠ 0) (Ideal.span_singleton_eq_bot.mp h)
  have hprime (P : Ideal (𝓞 K)) (hP : P ∈ S) : Prime P :=
    prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)
  have hex (P : Ideal (𝓞 K)) (hP : P ∈ S) : ∃ e > (0 : ℕ), absNorm P = p^e := by
    have hdiv : absNorm P ∣ p^(Module.finrank ℚ K) := by
      rw [← norm_span_natCast K]
      exact map_dvd absNorm (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP))
    obtain ⟨e, he, heq⟩ := (Nat.dvd_prime_pow hp).mp hdiv
    refine ⟨e, ?_, heq⟩
    by_contra h
    have he0 : e = 0 := by omega
    rw [he0, pow_zero, Ideal.absNorm_eq_one_iff] at heq
    exact (hprime P hP).not_unit (Ideal.isUnit_iff.mpr heq)
  let w : Ideal (𝓞 K) → ℕ := fun P => if h : P ∈ S then (hex P h).choose else 0
  have hw (P : Ideal (𝓞 K)) (hP : P ∈ S) : 0 < w P ∧ absNorm P = p^(w P) := by
    dsimp only [w]
    rw [dif_pos hP]
    exact (hex P hP).choose_spec
  have hsum : (∑ P ∈ S, w P*(normalizedFactors J).count P) = Module.finrank ℚ K := by
    apply Nat.pow_right_injective hp.two_le
    dsimp only
    rw [← norm_eq_pow_sum_count K S w (fun P hP => (hw P hP).2) hJ0 (subset_refl S)]
    exact norm_span_natCast K p
  refine ⟨S,w,hprime,(fun P hP => (hw P hP).1),(fun P hP => (hw P hP).2),?_,?_⟩
  · calc
      ∑ P ∈ S, w P ≤ ∑ P ∈ S, w P*(normalizedFactors J).count P := by
        apply sum_le_sum
        intro P hP
        exact Nat.le_mul_of_pos_right _ (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hP))
      _ = _ := hsum
  · intro k I hI P hP
    exact Multiset.mem_toFinset.mpr (norm_prime_power_support K hp hI (Multiset.mem_toFinset.mp hP))

noncomputable def normCountLocalSeries (p : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (fun k => (Nat.card {I : Ideal (𝓞 K) // absNorm I = p^k} : ℝ))

lemma normCountLocalSeries_eq_geom_prod {p : ℕ} (hp : p.Prime)
    (S : Finset (Ideal (𝓞 K))) (w : Ideal (𝓞 K) → ℕ)
    (hS : ∀ P ∈ S, Prime P) (hwpos : ∀ P ∈ S, 0 < w P)
    (hwnorm : ∀ P ∈ S, absNorm P = p^(w P))
    (hsupport : ∀ k : ℕ, ∀ I : Ideal (𝓞 K), absNorm I = p^k → (normalizedFactors I).toFinset ⊆ S) :
    normCountLocalSeries K p = ∏ P ∈ S, geomFactor (w P) := by
  ext k
  rw [normCountLocalSeries, PowerSeries.coeff_mk, geomFactor_prod_coeff]
  rw [norm_count_eq_weightedAntidiag K hp k S w hS hwpos hwnorm (hsupport k)]
  congr 2
  ext F
  simp only [mem_filter]

lemma normCountLocalSeries_inverse_bounds {p : ℕ} (hp : p.Prime) :
    (∀ k : ℕ, Module.finrank ℚ K < k → PowerSeries.coeff k (normCountLocalSeries K p)⁻¹ = 0) ∧
    (∀ k : ℕ, ‖PowerSeries.coeff k (normCountLocalSeries K p)⁻¹‖ ≤ (2 : ℝ)^(Module.finrank ℚ K)) := by
  obtain ⟨S,w,hS,hwpos,hwnorm,hwsum,hsupport⟩ := exists_local_ideal_weights K hp
  have he := normCountLocalSeries_eq_geom_prod K hp S w hS hwpos hwnorm hsupport
  have hmul : normCountLocalSeries K p * (∏ P ∈ S, (1-PowerSeries.X^(w P) : PowerSeries ℝ)) = 1 := by
    rw [he]
    exact geomFactor_prod_mul_inverse S w hwpos
  have hconst : PowerSeries.constantCoeff (normCountLocalSeries K p) ≠ 0 := by
    simp [normCountLocalSeries, PowerSeries.constantCoeff_mk, Ideal.absNorm_eq_one_iff]
  have hinv : (normCountLocalSeries K p)⁻¹ = ∏ P ∈ S, (1-PowerSeries.X^(w P) : PowerSeries ℝ) := by
    calc
      _ = (normCountLocalSeries K p)⁻¹ * 1 := (mul_one _).symm
      _ = (normCountLocalSeries K p)⁻¹ *
          (normCountLocalSeries K p * (∏ P ∈ S, (1-PowerSeries.X^(w P) : PowerSeries ℝ))) := by rw [hmul]
      _ = _ := by rw [← mul_assoc, PowerSeries.inv_mul_cancel _ hconst, one_mul]
  have hcard : S.card ≤ Module.finrank ℚ K := by
    calc
      _ = ∑ _P ∈ S, 1 := card_eq_sum_ones S
      _ ≤ ∑ P ∈ S, w P := sum_le_sum (fun P hP => hwpos P hP)
      _ ≤ _ := hwsum
  constructor
  · intro k hk
    rw [hinv]
    exact inverseFactor_prod_coeff_zero S w k (lt_of_le_of_lt hwsum hk)
  · intro k
    rw [hinv]
    exact (inverseFactor_prod_coeff_bound S w k).trans (pow_le_pow_right₀ (by norm_num) hcard)


end IdealEuler
namespace MeanTransfer

lemma localSeries_idealNormFunction (K : Type*) [Field K] [NumberField K]
    {p : ℕ} (hp : p.Prime) :
    EulerComparison.localSeries (idealNormFunction K) p = IdealEuler.normCountLocalSeries K p := by
  ext k
  simp only [EulerComparison.localSeries_coeff, IdealEuler.normCountLocalSeries,
    PowerSeries.coeff_mk, idealNormFunction, ArithmeticFunction.coe_mk, if_neg (pow_ne_zero _ hp.ne_zero)]

lemma idealNormFunction_inverse_bounds (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    (∀ k : ℕ, Module.finrank ℚ K < k → EulerComparison.dirichletInverse (idealNormFunction K) (p^k) = 0) ∧
    (∀ k : ℕ, ‖EulerComparison.dirichletInverse (idealNormFunction K) (p^k)‖ ≤ (2 : ℝ)^(Module.finrank ℚ K)) := by
  have he (k : ℕ) : EulerComparison.dirichletInverse (idealNormFunction K) (p^k) =
      PowerSeries.coeff k (IdealEuler.normCountLocalSeries K p)⁻¹ := by
    rw [← EulerComparison.localSeries_coeff,
      EulerComparison.dirichletInverse_localSeries _ (idealNormFunction_multiplicative K).1 hp,
      localSeries_idealNormFunction K hp]
  simpa only [he] using IdealEuler.normCountLocalSeries_inverse_bounds K hp

end MeanTransfer
namespace GeneralDivisors

lemma root_mean_of_numberField_match {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) (K : Type*) [Field K] [NumberField K]
    (S : Finset ℕ) (hmatch : ∀ p : ℕ, p.Prime → p ∉ S →
      MeanTransfer.idealNormFunction K p = polynomialRootCount f p) :
    ∃ c > (0 : ℝ), Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Ioc 0 N, (polynomialRootCount f n : ℝ))/(N : ℝ)) atTop (𝓝 c) := by
  exact root_mean_of_numberField_local_data hdeg hirr K (Module.finrank ℚ K)
    (show 0 ≤ (2 : ℝ)^(Module.finrank ℚ K) by positivity)
    (fun p hp => (MeanTransfer.idealNormFunction_inverse_bounds K hp).1)
    (fun p hp => (MeanTransfer.idealNormFunction_inverse_bounds K hp).2) S hmatch

lemma degree_two_limit_of_numberField_match {f : ℤ[X]} (hd : f.natDegree = 2)
    (hirr : Irreducible f) (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n)
    (K : Type*) [Field K] [NumberField K] (S : Finset ℕ)
    (hmatch : ∀ p : ℕ, p.Prime → p ∉ S →
      MeanTransfer.idealNormFunction K p = polynomialRootCount f p) :
    ∃ c > (0 : ℝ), Tendsto (fun x : ℝ => Erdos975Sum f x/(x*log x)) atTop (𝓝 c) := by
  obtain ⟨c,hc,hmean⟩ := root_mean_of_numberField_match (by omega : f.natDegree ≠ 0) hirr K S hmatch
  exact ⟨2*c,mul_pos (by norm_num) hc,limit_of_degree_two_and_root_mean f hd hpos hmean⟩

end GeneralDivisors
namespace KummerRoots

open Finset Polynomial Ideal UniqueFactorizationMonoid
open scoped NumberField Classical

noncomputable def rootsEquivLinearFactors {R : Type*} [Field R] [DecidableEq R] (g : R[X]) (hg : g ≠ 0) :
    {x : R // g.eval x = 0} ≃
      {Q : (normalizedFactors g).toFinset // Q.val.natDegree = 1} := by
  classical
  let F : {x : R // g.eval x = 0} →
      {Q : (normalizedFactors g).toFinset // Q.val.natDegree = 1} := fun x =>
    ⟨⟨X-C x.val, Multiset.mem_toFinset.mpr ((Polynomial.mem_normalizedFactors_iff hg).mpr
      ⟨irreducible_X_sub_C _, monic_X_sub_C _, Polynomial.dvd_iff_isRoot.mpr x.property⟩)⟩,
      natDegree_X_sub_C _⟩
  apply Equiv.ofBijective F
  constructor
  · intro x y hxy
    have h := congrArg (fun Q => Q.val.val.coeff 0) hxy
    change (X-C x.val : R[X]).coeff 0 = (X-C y.val : R[X]).coeff 0 at h
    simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_inj] at h
    exact Subtype.ext h
  · intro Q
    have hQ := (Polynomial.mem_normalizedFactors_iff hg).mp (Multiset.mem_toFinset.mp Q.val.property)
    have he : Q.val.val = X-C (-Q.val.val.coeff 0) := by
      rw [hQ.2.1.eq_X_add_C Q.property]
      simp
    have hr : g.eval (-Q.val.val.coeff 0) = 0 := by
      apply Polynomial.dvd_iff_isRoot.mp
      rw [← he]
      exact hQ.2.2
    refine ⟨⟨_,hr⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact he.symm

variable (K : Type*) [Field K] [NumberField K]

noncomputable def idealsNormPrimeEquivInertiaOne {p : ℕ} (hp : p.Prime) :
    {I : Ideal (𝓞 K) // absNorm I = p} ≃
      {I : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) //
        (Ideal.span {(p : ℤ)}).inertiaDeg I.val = 1} := by
  classical
  let F : {I : Ideal (𝓞 K) // absNorm I = p} →
      {I : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) //
        (Ideal.span {(p : ℤ)}).inertiaDeg I.val = 1} := fun I => by
    have hprime : I.val.IsPrime := Ideal.isPrime_of_irreducible_absNorm
      (by rw [I.property]; exact (Nat.prime_iff.mp hp).irreducible)
    letI : I.val.LiesOver (span {(p : ℤ)}) := by
      apply (Ideal.liesOver_iff _ _).mpr
      rw [Ideal.under_def]
      simpa only [I.property] using Ideal.span_singleton_absNorm (show (absNorm I.val).Prime by rw [I.property]; exact hp)
    have he : (span {(p : ℤ)}).inertiaDeg I.val = 1 := by
      apply Nat.pow_right_injective hp.two_le
      dsimp only
      rw [← Ideal.absNorm_eq_pow_inertiaDeg' I.val hp, I.property, pow_one]
    exact ⟨⟨I.val,⟨hprime,inferInstance⟩⟩,he⟩
  apply Equiv.ofBijective F
  constructor
  · intro I J hIJ
    exact Subtype.ext (congrArg (fun x => x.val.val) hIJ)
  · intro I
    letI : I.val.val.LiesOver (span {(p : ℤ)}) := I.val.property.2
    have hnorm : absNorm I.val.val = p := by
      rw [Ideal.absNorm_eq_pow_inertiaDeg' _ hp, I.property, pow_one]
    exact ⟨⟨I.val.val,hnorm⟩,rfl⟩

lemma norm_prime_eq_roots_minpoly {p : ℕ} (hp : p.Prime) (θ : 𝓞 K)
    (hex : ¬p ∣ RingOfIntegers.exponent θ) :
    Nat.card {I : Ideal (𝓞 K) // absNorm I = p} =
      Nat.card {x : ZMod p // (minpoly ℤ θ).eval₂ (Int.castRingHom (ZMod p)) x = 0} := by
  letI : Fact p.Prime := ⟨hp⟩
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hex
  have hinertia (I : (span {(p : ℤ)}).primesOver (𝓞 K)) :
      (span {(p : ℤ)}).inertiaDeg I.val = (e I).val.natDegree := by
    have h := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hex (e I).property
    change (span {(p : ℤ)}).inertiaDeg (e.symm (e I)).val = _ at h
    simpa only [Equiv.symm_apply_apply] using h
  let e' : {I : (span {(p : ℤ)}).primesOver (𝓞 K) // (span {(p : ℤ)}).inertiaDeg I.val = 1} ≃
      {Q : RingOfIntegers.monicFactorsMod θ p // Q.val.natDegree = 1} :=
    e.subtypeEquiv (fun I => by rw [hinertia I])
  let g : (ZMod p)[X] := (minpoly ℤ θ).map (Int.castRingHom (ZMod p))
  have hg : g ≠ 0 := (minpoly.monic θ.isIntegral).map _ |>.ne_zero
  let er := rootsEquivLinearFactors g hg
  calc
    _ = Nat.card {I : (span {(p : ℤ)}).primesOver (𝓞 K) //
        (span {(p : ℤ)}).inertiaDeg I.val = 1} := Nat.card_congr (idealsNormPrimeEquivInertiaOne K hp)
    _ = Nat.card {Q : RingOfIntegers.monicFactorsMod θ p // Q.val.natDegree = 1} := Nat.card_congr e'
    _ = Nat.card {Q : (normalizedFactors g).toFinset // Q.val.natDegree = 1} := by rfl
    _ = Nat.card {x : ZMod p // g.eval x = 0} := (Nat.card_congr er).symm
    _ = _ := by simp only [g, Polynomial.eval_map]


lemma exponent_ne_zero_of_powerBasis (θ : 𝓞 K) (B : PowerBasis ℚ K) (hB : B.gen = (θ : K)) :
    RingOfIntegers.exponent θ ≠ 0 := by
  have hgen : IsIntegral ℤ B.gen := hB ▸ θ.property
  have hdisc : IsIntegral ℤ (Algebra.discr ℚ B.basis) :=
    Algebra.discr_isIntegral ℚ (fun i => by rw [B.basis_eq_pow]; exact hgen.pow _)
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdisc
  have hd0 : d ≠ 0 := by
    intro h
    have hh := (Algebra.discr_isUnit_of_basis ℚ B.basis).ne_zero
    apply hh
    simpa [h] using hd.symm
  have hcond : (d : 𝓞 K) ∈ conductor ℤ θ := by
    rw [mem_conductor_iff]
    intro b
    have hm := Algebra.discr_mul_isIntegral_mem_adjoin ℚ hgen b.property
    rw [← hd, hB] at hm
    have hm' : ((d : 𝓞 K)*b : K) ∈ Algebra.adjoin ℤ {(θ : K)} := by
      simpa [Algebra.smul_def] using hm
    let e : (𝓞 K) →ₐ[ℤ] K := IsScalarTower.toAlgHom ℤ (𝓞 K) K
    have hmap : (Algebra.adjoin ℤ {θ}).map e = Algebra.adjoin ℤ {(θ : K)} := by
      rw [AlgHom.map_adjoin, Set.image_singleton]
      rfl
    rw [← hmap] at hm'
    obtain ⟨x,hx,hxe⟩ := Subalgebra.mem_map.mp hm'
    have heq : x = (d : 𝓞 K)*b := NumberField.RingOfIntegers.ext hxe
    exact heq ▸ hx
  intro hex
  have hu : Ideal.under ℤ (conductor ℤ θ) = ⊥ := Ideal.absNorm_eq_zero_iff.mp hex
  have hdmem : d ∈ Ideal.under ℤ (conductor ℤ θ) := by
    change (algebraMap ℤ (𝓞 K)) d ∈ conductor ℤ θ
    simpa only [map_intCast] using hcond
  rw [hu, Ideal.mem_bot] at hdmem
  exact hd0 hdmem

lemma finite_exceptional_primes_minpoly (θ : 𝓞 K) (B : PowerBasis ℚ K) (hB : B.gen = (θ : K)) :
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      Nat.card {I : Ideal (𝓞 K) // absNorm I = p} =
        Nat.card {x : ZMod p // (minpoly ℤ θ).eval₂ (Int.castRingHom (ZMod p)) x = 0} := by
  refine ⟨(RingOfIntegers.exponent θ).primeFactors, ?_⟩
  intro p hp hpS
  apply norm_prime_eq_roots_minpoly K hp θ
  intro hdiv
  exact hpS (Nat.mem_primeFactors.mpr ⟨hp,hdiv,exponent_ne_zero_of_powerBasis K θ B hB⟩)


noncomputable def scalePowerBasis (B : PowerBasis ℚ K) (a : ℚ) (ha : a ≠ 0) : PowerBasis ℚ K where
  gen := algebraMap ℚ K a * B.gen
  dim := B.dim
  basis := B.basis.unitsSMul (fun i => Units.mk0 (a^(i.val)) (pow_ne_zero _ ha))
  basis_eq_pow i := by
    rw [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, B.basis_eq_pow,
      Algebra.smul_def, map_pow, mul_pow]

lemma integral_model_of_powerBasis (f : ℤ[X]) (hf : f ≠ 0) (B₀ : PowerBasis ℚ K)
    (hdim : B₀.dim = f.natDegree) (hroot : aeval B₀.gen f = 0) :
    ∃ (θ : 𝓞 K) (B : PowerBasis ℚ K), B.gen = (θ : K) ∧ minpoly ℤ θ = f.integralNormalization := by
  have ha : (f.leadingCoeff : ℚ) ≠ 0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hf
  let B := scalePowerBasis K B₀ (f.leadingCoeff : ℚ) ha
  have hBm : B.dim = f.natDegree := hdim
  have hqmonic : f.integralNormalization.Monic := monic_integralNormalization hf
  have hqroot : aeval B.gen f.integralNormalization = 0 := by
    have h := integralNormalization_aeval_eq_zero hroot
      (fun x hx => (FaithfulSMul.algebraMap_injective ℤ K) (by simpa using hx))
    simpa [B, scalePowerBasis] using h
  have hint : IsIntegral ℤ B.gen := ⟨f.integralNormalization,hqmonic,hqroot⟩
  let θ : 𝓞 K := ⟨B.gen,hint⟩
  have hminimal : f.integralNormalization = minpoly ℤ B.gen := by
    apply IsIntegrallyClosed.minpoly.unique hqmonic hqroot
    intro q hqm hqr
    have hqr' : aeval B.gen (q.map (algebraMap ℤ ℚ)) = 0 := by
      rw [Polynomial.aeval_map_algebraMap ℚ]
      exact hqr
    have hh := B.dim_le_natDegree_of_root (hqm.map (algebraMap ℤ ℚ)).ne_zero hqr'
    rw [hBm, Polynomial.natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective ℤ ℚ)] at hh
    rw [degree_integralNormalization, degree_eq_natDegree hf, degree_eq_natDegree hqm.ne_zero]
    exact_mod_cast hh
  have hm : minpoly ℤ (θ : K) = minpoly ℤ θ :=
    minpoly.algHom_eq (IsScalarTower.toAlgHom ℤ (𝓞 K) K) NumberField.RingOfIntegers.coe_injective θ
  exact ⟨θ,B,rfl,hm.symm.trans hminimal.symm⟩


lemma roots_card_integralNormalization (f : ℤ[X]) (hdeg : f.natDegree ≠ 0)
    {p : ℕ} (hp : p.Prime) (hpl : ¬(p : ℤ) ∣ f.leadingCoeff) :
    Nat.card {x : ZMod p // f.integralNormalization.eval₂ (Int.castRingHom (ZMod p)) x = 0} =
      Nat.card {x : ZMod p // f.eval₂ (Int.castRingHom (ZMod p)) x = 0} := by
  letI : Fact p.Prime := ⟨hp⟩
  have ha : (f.leadingCoeff : ZMod p) ≠ 0 := by
    intro h
    exact hpl ((ZMod.intCast_zmod_eq_zero_iff_dvd f.leadingCoeff p).mp h)
  let e : ZMod p ≃ ZMod p := Equiv.mulLeft₀ (f.leadingCoeff : ZMod p) ha
  have he (x : ZMod p) : f.eval₂ (Int.castRingHom (ZMod p)) x = 0 ↔
      f.integralNormalization.eval₂ (Int.castRingHom (ZMod p)) (e x) = 0 := by
    change _ ↔ f.integralNormalization.eval₂ (Int.castRingHom (ZMod p)) ((f.leadingCoeff : ZMod p)*x) = 0
    have hh := integralNormalization_eval₂_leadingCoeff_mul (p := f)
      (Nat.one_le_iff_ne_zero.mpr hdeg) (Int.castRingHom (ZMod p)) x
    change f.integralNormalization.eval₂ (Int.castRingHom (ZMod p)) ((f.leadingCoeff : ZMod p)*x) =
      (f.leadingCoeff : ZMod p)^(f.natDegree-1)*f.eval₂ (Int.castRingHom (ZMod p)) x at hh
    rw [hh]
    simp only [mul_eq_zero, show (f.leadingCoeff : ZMod p) ^ (f.natDegree-1) ≠ 0 from pow_ne_zero _ ha,
      false_or]
  exact (Nat.card_congr (e.subtypeEquiv he)).symm

end KummerRoots

namespace GeneralDivisors

open Finset

lemma polynomialRootCount_mean_positive (f : ℤ[X]) (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) :
    ∃ c > (0 : ℝ), Tendsto (fun N : ℕ =>
      (∑ n ∈ Ioc 0 N, (polynomialRootCount f n : ℝ))/(N : ℝ)) atTop (𝓝 c) := by
  let fQ := f.map (Int.castRingHom ℚ)
  have hQirr : Irreducible fQ :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hirr.isPrimitive hdeg)).mp hirr
  letI : Fact (Irreducible fQ) := ⟨hQirr⟩
  let K := AdjoinRoot fQ
  letI : Field K := AdjoinRoot.instField
  let B₀ : PowerBasis ℚ K := AdjoinRoot.powerBasis hQirr.ne_zero
  letI : Module.Finite ℚ K := B₀.finite
  letI : NumberField K := NumberField.of_module_finite ℚ K
  have hdim : B₀.dim = f.natDegree := by
    simpa only [B₀, AdjoinRoot.powerBasis_dim, fQ] using
      Polynomial.natDegree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective) f
  have hroot : aeval B₀.gen f = 0 := by
    rw [← Polynomial.aeval_map_algebraMap ℚ]
    change aeval (AdjoinRoot.root fQ) fQ = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  obtain ⟨θ,B,hB,hmin⟩ := KummerRoots.integral_model_of_powerBasis K f hirr.ne_zero B₀ hdim hroot
  obtain ⟨S,hS⟩ := KummerRoots.finite_exceptional_primes_minpoly K θ B hB
  apply root_mean_of_numberField_match hdeg hirr K (S ∪ f.leadingCoeff.natAbs.primeFactors)
  intro p hp hpS
  have hpS' : p ∉ S := fun h => hpS (mem_union_left _ h)
  have hpL : ¬(p : ℤ) ∣ f.leadingCoeff := by
    intro h
    apply hpS
    apply mem_union_right
    exact Nat.mem_primeFactors.mpr ⟨hp,Int.natCast_dvd.mp h,
      Int.natAbs_ne_zero.mpr (leadingCoeff_ne_zero.mpr hirr.ne_zero)⟩
  have hc := hS p hp hpS'
  rw [hmin] at hc
  have hn := hc.trans (KummerRoots.roots_card_integralNormalization f hdeg hp hpL)
  simp only [MeanTransfer.idealNormFunction, ArithmeticFunction.coe_mk, if_neg hp.ne_zero, polynomialRootCount]
  exact_mod_cast hn

end GeneralDivisors

lemma erdos_975_degree_two (f : ℤ[X]) (hd : f.natDegree = 2)
    (hirr : Irreducible f) (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    ∃ c > (0 : ℝ), Tendsto (fun x : ℝ => Erdos975Sum f x/(x*log x)) atTop (𝓝 c) := by
  obtain ⟨c,hc,hmean⟩ := GeneralDivisors.polynomialRootCount_mean_positive f (by omega) hirr
  exact ⟨2*c,mul_pos (by norm_num) hc,
    GeneralDivisors.limit_of_degree_two_and_root_mean f hd hpos hmean⟩

namespace GeneralDivisors


lemma higher_degree_eventual_lower {f : ℤ[X]} (hdeg : 3 ≤ f.natDegree)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    ∀ᶠ n : ℕ in atTop, n*n ≤ ⌊f.eval (n : ℤ)⌋₊ := by
  let F : ℝ[X] := f.map (Int.castRingHom ℝ)
  have hF : F.natDegree = f.natDegree :=
    natDegree_map_eq_of_injective Int.cast_injective f
  have hX : (X^2 : ℝ[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hdegree : (X^2 : ℝ[X]).degree < F.degree := by
    rw [← natDegree_lt_natDegree_iff hX, natDegree_X_pow, hF]
    omega
  have ht := (F.abs_div_tendsto_atTop_of_degree_gt (X^2) hdegree hX).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have heval (n : ℕ) : F.eval (n : ℝ) = ((f.eval (n : ℤ) : ℤ) : ℝ) := by
    simpa only [Int.cast_natCast] using
      Polynomial.eval_intCast_map (Int.castRingHom ℝ) f (n : ℤ)
  filter_upwards [ht.eventually (eventually_ge_atTop (1 : ℝ)),
    (tendsto_natCast_atTop_atTop (R := ℤ)).eventually hpos,
    eventually_gt_atTop (0 : ℕ)] with n hn hp hn0
  simp only [Function.comp_apply, eval_pow, eval_X, heval] at hn
  have hp' : (0 : ℝ) ≤ ((f.eval (n : ℤ) : ℤ) : ℝ) := by exact_mod_cast (by omega : 0 ≤ f.eval (n : ℤ))
  rw [abs_of_nonneg (div_nonneg hp' (sq_nonneg _)), le_div_iff₀ (sq_pos_of_pos (Nat.cast_pos.mpr hn0))] at hn
  have hi : (n : ℤ)*(n : ℤ) ≤ f.eval (n : ℤ) := by
    have hi' : (n : ℝ)*(n : ℝ) ≤ ((f.eval (n : ℤ) : ℤ) : ℝ) := by
      simpa only [one_mul, pow_two] using hn
    exact_mod_cast hi'
  exact Nat.le_floor (by simpa only [Nat.cast_mul] using hi)

lemma higher_degree_lower_after_shift {f : ℤ[X]} (hdeg : 3 ≤ f.natDegree)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    ∃ t : ℕ,
      (∀ n : ℕ, 0 < n → 0 < (f.comp (X+C (t : ℤ))).eval (n : ℤ)) ∧
      (∀ n : ℕ, 0 < n → n*n ≤ ⌊(f.comp (X+C (t : ℤ))).eval (n : ℤ)⌋₊) := by
  obtain ⟨t,ht⟩ := eventually_atTop.mp (higher_degree_eventual_lower hdeg hpos)
  refine ⟨t, ?_, ?_⟩
  · intro n hn
    have he := ht (n+t) (by omega)
    have he' : (n+t)*(n+t) ≤ ⌊(f.comp (X+C (t : ℤ))).eval (n : ℤ)⌋₊ := by
      simpa only [eval_comp, eval_add, eval_X, eval_C, Nat.cast_add] using he
    have hfloor : 0 < ⌊(f.comp (X+C (t : ℤ))).eval (n : ℤ)⌋₊ := by
      exact lt_of_lt_of_le (Nat.mul_pos (by omega) (by omega)) he'
    have h := Nat.floor_pos.mp hfloor
    omega
  · intro n hn
    have he := ht (n+t) (by omega)
    simp only [eval_comp, eval_add, eval_X, eval_C]
    calc
      n*n ≤ (n+t)*(n+t) := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ ⌊f.eval ((n : ℤ)+(t : ℤ))⌋₊ := by simpa only [Nat.cast_add] using he

open Finset

lemma lower_limit_of_quadratic_lower (f : ℤ[X])
    (hval : ∀ n : ℕ, 0 < n → 0 < f.eval (n : ℤ))
    (hlower : ∀ n : ℕ, 0 < n → n*n ≤ ⌊f.eval (n : ℤ)⌋₊)
    {a c : ℝ} (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)) / N) atTop (𝓝 a))
    (hlim : Tendsto (fun N : ℕ => halfSum f N / ((N : ℝ)*log N)) atTop (𝓝 c)) :
    a ≤ c := by
  have herr : Tendsto (fun N : ℕ => (3 * ∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)) /
      ((N : ℝ)*log N)) atTop (𝓝 0) := by
    have hh := (hmean.const_mul 3).div_atTop
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    simpa only [mul_div_assoc, div_div] using hh
  have hlow := (truncatedDivisorSum_limit_of_root_mean f a hmean).sub herr
  simp only [sub_zero] at hlow
  apply le_of_tendsto_of_tendsto hlow hlim
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  rw [← sub_div]
  apply div_le_div_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg N)
    (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))))
  have hh := halfSum_quadratic_lower f 1 N hval (by simpa using hlower)
  have hb : (∑ q ∈ Ioc 0 N, (divisibleValueCount f q (1*q) : ℝ)) ≤
      3 * ∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro q hq
    convert divisibleValueCount_mul_bound f (mem_Ioc.mp hq).1 1 using 1 <;> norm_num
  linarith

lemma higher_degree_limit_lower_bound {f : ℤ[X]} (hdeg : 3 ≤ f.natDegree)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n)
    {a c : ℝ} (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)) / N) atTop (𝓝 a))
    (hlim : Tendsto (fun x : ℝ => Erdos975Sum f x/(x*log x)) atTop (𝓝 c)) :
    2*a ≤ c := by
  obtain ⟨t,htval,htlower⟩ := higher_degree_lower_after_shift hdeg hpos
  have hshift := (int_shift_limit_iff f (t : ℤ) c).mpr hlim
  have hhalf : Tendsto (fun N : ℕ => halfSum (f.comp (X+C (t : ℤ))) N /
      ((N : ℝ)*log N)) atTop (𝓝 (c/2)) := by
    apply (halfSum_limit_iff (f.comp (X+C (t : ℤ))) (c/2)).mpr
    simpa only [mul_div_cancel₀ c (by norm_num : (2 : ℝ) ≠ 0)] using hshift
  have hm : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 N, (polynomialRootCount (f.comp (X+C (t : ℤ))) q : ℝ)) / N)
      atTop (𝓝 a) := by simpa only [polynomialRootCount_comp_X_add_C] using hmean
  have hh := lower_limit_of_quadratic_lower _ htval htlower hm hhalf
  linarith

lemma higher_degree_remainder_limit_nonneg {f : ℤ[X]} (hdeg : 3 ≤ f.natDegree)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n)
    {a b : ℝ} (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)) / N) atTop (𝓝 a))
    (hlim : Tendsto (fun N : ℕ =>
      (halfSum f N - truncatedDivisorSum f N N) / ((N : ℝ)*log N)) atTop (𝓝 b)) :
    0 ≤ b := by
  have hs : Tendsto (fun N : ℕ => halfSum f N / ((N : ℝ)*log N)) atTop (𝓝 (a+b)) := by
    have hh := (truncatedDivisorSum_limit_of_root_mean f a hmean).add hlim
    simpa only [← add_div, add_sub_cancel] using hh
  have hb := higher_degree_limit_lower_bound hdeg hpos hmean ((halfSum_limit_iff f (a+b)).mp hs)
  linarith

lemma higher_degree_positive_limit_iff_remainder_exists {f : ℤ[X]} (hdeg : 3 ≤ f.natDegree)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n)
    {a : ℝ} (ha : 0 < a) (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)) / N) atTop (𝓝 a)) :
    (∃ c > (0 : ℝ), Tendsto (fun x : ℝ => Erdos975Sum f x/(x*log x)) atTop (𝓝 c)) ↔
      ∃ b : ℝ, Tendsto (fun N : ℕ =>
        (halfSum f N - truncatedDivisorSum f N N) / ((N : ℝ)*log N)) atTop (𝓝 b) := by
  rw [positive_limit_iff_remainder f a hmean]
  constructor
  · rintro ⟨b,_,hb⟩
    exact ⟨b,hb⟩
  · rintro ⟨b,hb⟩
    exact ⟨b,add_pos_of_pos_of_nonneg ha (higher_degree_remainder_limit_nonneg hdeg hpos hmean hb),hb⟩


end GeneralDivisors

namespace GeneralDivisors


/-- Divisors of `f(n)` that do not exceed the input `n`. -/
def inputDivisorCount (f : ℤ[X]) (n : ℕ) : ℕ :=
  {q ∈ Ioc 0 n | ((q : ℕ) : ℤ) ∣ f.eval (n : ℤ)}.card

noncomputable def inputDivisorSum (f : ℤ[X]) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, (inputDivisorCount f n : ℝ)

/-- Half-divisors strictly larger than the input. -/
def largeDivisorCount (f : ℤ[X]) (n : ℕ) : ℕ :=
  {q ∈ (⌊f.eval (n : ℤ)⌋₊).divisors | n < q ∧ q*q ≤ ⌊f.eval (n : ℤ)⌋₊}.card

noncomputable def largeDivisorSum (f : ℤ[X]) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, (largeDivisorCount f n : ℝ)

lemma largeDivisorSum_nonneg (f : ℤ[X]) (N : ℕ) : 0 ≤ largeDivisorSum f N := by
  exact sum_nonneg (fun _ _ => Nat.cast_nonneg _)

lemma largeDivisorSum_mono (f : ℤ[X]) : Monotone (largeDivisorSum f) := by
  intro M N hMN
  exact sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right hMN)
    (fun _ _ _ => Nat.cast_nonneg _)

lemma inputDivisorSum_decomposition (f : ℤ[X]) (N : ℕ) :
    truncatedDivisorSum f N N = inputDivisorSum f N +
      ∑ q ∈ Ioc 0 N, (divisibleValueCount f q (q-1) : ℝ) := by
  have heq : inputDivisorSum f N =
      ∑ q ∈ Ioc 0 N, ({n ∈ Ioc 0 N | q ≤ n ∧ ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)}.card : ℝ) := by
    simp only [inputDivisorSum, inputDivisorCount, card_filter, Nat.cast_sum]
    have hrow (n : ℕ) (hn : n ∈ Ioc 0 N) :
        (∑ q ∈ Ioc 0 n, if (q : ℤ) ∣ f.eval (n : ℤ) then (1 : ℝ) else 0) =
        ∑ q ∈ Ioc 0 N, if q ≤ n ∧ ((q : ℕ) : ℤ) ∣ f.eval (n : ℤ) then (1 : ℝ) else 0 := by
      rw [← sum_filter, ← sum_filter]
      have hfin : {q ∈ Ioc 0 N | q ≤ n ∧ ((q : ℕ) : ℤ) ∣ f.eval (n : ℤ)} =
          {q ∈ Ioc 0 n | ((q : ℕ) : ℤ) ∣ f.eval (n : ℤ)} := by
        ext q
        simp only [mem_filter, mem_Ioc]
        have := (mem_Ioc.mp hn).2
        omega
      rw [hfin]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [sum_congr rfl hrow, sum_comm]
  rw [heq, ← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  rw [← Nat.cast_add]
  congr 1
  have hsplit : {n ∈ Ioc 0 N | ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)} =
      {n ∈ Ioc 0 N | q ≤ n ∧ ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)} ∪
      {n ∈ Ioc 0 (q-1) | ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)} := by
    ext n
    simp only [mem_union, mem_filter, mem_Ioc]
    have := mem_Ioc.mp hq
    omega
  have hdis : Disjoint
      {n ∈ Ioc 0 N | q ≤ n ∧ ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)}
      {n ∈ Ioc 0 (q-1) | ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)} := by
    rw [disjoint_left]
    intro n hn hm
    simp only [mem_filter, mem_Ioc] at hn hm
    have := mem_Ioc.mp hq
    omega
  exact (congrArg Finset.card hsplit).trans (card_union_of_disjoint hdis)

lemma inputDivisorSum_error (f : ℤ[X]) (N : ℕ) :
    |inputDivisorSum f N - truncatedDivisorSum f N N| ≤
      3 * ∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ) := by
  rw [inputDivisorSum_decomposition, sub_add_cancel_left, abs_neg,
    abs_of_nonneg (show (0 : ℝ) ≤ ∑ q ∈ Ioc 0 N, (divisibleValueCount f q (q-1) : ℝ) from by positivity),
    mul_sum]
  apply sum_le_sum
  intro q hq
  have hm : divisibleValueCount f q (q-1) ≤ divisibleValueCount f q q := by
    apply card_le_card
    intro n hn
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp (mem_filter.mp hn).1).1,
      ((mem_Ioc.mp (mem_filter.mp hn).1).2).trans (Nat.sub_le q 1)⟩, (mem_filter.mp hn).2⟩
  have hb := divisibleValueCount_mul_bound f (mem_Ioc.mp hq).1 1
  norm_num only [Nat.cast_one, one_mul] at hb
  exact (Nat.cast_le.mpr hm).trans (by nlinarith)

lemma inputDivisorSum_error_tendsto (f : ℤ[X]) {a : ℝ}
    (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)) / N) atTop (𝓝 a)) :
    Tendsto (fun N : ℕ => (inputDivisorSum f N - truncatedDivisorSum f N N) /
      ((N : ℝ)*log N)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun N : ℕ =>
    (3 * ∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ))/((N : ℝ)*log N))
  · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    have hd : 0 < (N : ℝ)*log N := mul_pos (Nat.cast_pos.mpr (by omega))
      (Real.log_pos (by exact_mod_cast hN))
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hd]
    exact div_le_div_of_nonneg_right (inputDivisorSum_error f N) hd.le
  · have hh := (hmean.const_mul 3).div_atTop
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    simpa only [mul_div_assoc, div_div] using hh

lemma inputDivisorSum_limit (f : ℤ[X]) {a : ℝ}
    (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)) / N) atTop (𝓝 a)) :
    Tendsto (fun N : ℕ => inputDivisorSum f N / ((N : ℝ)*log N)) atTop (𝓝 a) := by
  have hh := (inputDivisorSum_error_tendsto f hmean).add
    (truncatedDivisorSum_limit_of_root_mean f a hmean)
  simpa only [zero_add, ← add_div, sub_add_cancel] using hh

lemma halfDivisorCount_eq_input_add_large (f : ℤ[X]) {n : ℕ} (hn : 0 < n)
    (hval : n*n ≤ ⌊f.eval (n : ℤ)⌋₊) :
    halfDivisorCount ⌊f.eval (n : ℤ)⌋₊ = inputDivisorCount f n + largeDivisorCount f n := by
  have hm : 0 < ⌊f.eval (n : ℤ)⌋₊ := lt_of_lt_of_le (Nat.mul_pos hn hn) hval
  have hfpos : 0 ≤ f.eval (n : ℤ) := by have hh := Nat.floor_pos.mp hm; omega
  let S := {q ∈ (⌊f.eval (n : ℤ)⌋₊).divisors | q*q ≤ ⌊f.eval (n : ℤ)⌋₊}
  have hs : S.filter (fun q => q ≤ n) = {q ∈ Ioc 0 n | ((q : ℕ) : ℤ) ∣ f.eval (n : ℤ)} := by
    ext q
    simp only [S, mem_filter, Nat.mem_divisors, mem_Ioc]
    constructor
    · rintro ⟨⟨⟨hqm,_⟩,_⟩,hqn⟩
      refine ⟨⟨Nat.pos_of_dvd_of_pos hqm hm,hqn⟩,?_⟩
      rw [← floor_eval_cast hfpos, Int.natCast_dvd_natCast]
      exact hqm
    · rintro ⟨⟨hq,hqn⟩,hqd⟩
      refine ⟨⟨⟨?_,hm.ne'⟩,(Nat.mul_le_mul hqn hqn).trans hval⟩,hqn⟩
      rw [← floor_eval_cast hfpos, Int.natCast_dvd_natCast] at hqd
      exact hqd
  have hl : S.filter (fun q => ¬q ≤ n) =
      {q ∈ (⌊f.eval (n : ℤ)⌋₊).divisors | n < q ∧ q*q ≤ ⌊f.eval (n : ℤ)⌋₊} := by
    ext q
    simp only [S, mem_filter, not_le]
    tauto
  have hc := card_filter_add_card_filter_not (s := S) (p := fun q => q ≤ n)
  rw [hs,hl] at hc
  exact hc.symm

lemma halfSum_eq_input_add_large_eventually (f : ℤ[X])
    (hlower : ∀ᶠ n : ℕ in atTop, n*n ≤ ⌊f.eval (n : ℤ)⌋₊) :
    ∃ K : ℝ, ∀ᶠ N : ℕ in atTop,
      halfSum f N = inputDivisorSum f N + largeDivisorSum f N + K := by
  let e : ℕ → ℝ := fun n => halfDivisorCount ⌊f.eval (n : ℤ)⌋₊ -
    (inputDivisorCount f n : ℝ) - (largeDivisorCount f n : ℝ)
  obtain ⟨T,hT⟩ := eventually_atTop.mp hlower
  let K : ℝ := halfDivisorCount ⌊f.eval 0⌋₊ + ∑ n ∈ Ioc 0 T, e n
  refine ⟨K, ?_⟩
  filter_upwards [eventually_ge_atTop T] with N hN
  have he : ∑ n ∈ Ioc 0 N, e n = ∑ n ∈ Ioc 0 T, e n := by
    rw [← sum_Ioc_consecutive e (Nat.zero_le T) hN]
    have hz : ∑ n ∈ Ioc T N, e n = 0 := by
      apply sum_eq_zero
      intro n hn
      have h := halfDivisorCount_eq_input_add_large f (by have := (mem_Ioc.mp hn).1; omega)
        (hT n (mem_Ioc.mp hn).1.le)
      simp only [e, h, Nat.cast_add, add_sub_cancel_left, sub_self]
    rw [hz, add_zero]
  rw [halfSum_remove_zero]
  dsimp only [inputDivisorSum, largeDivisorSum, K]
  rw [← he]
  simp only [e, sum_sub_distrib]
  ring

lemma halfSum_input_large_error_tendsto (f : ℤ[X])
    (hlower : ∀ᶠ n : ℕ in atTop, n*n ≤ ⌊f.eval (n : ℤ)⌋₊) :
    Tendsto (fun N : ℕ => (halfSum f N - inputDivisorSum f N - largeDivisorSum f N) /
      ((N : ℝ)*log N)) atTop (𝓝 0) := by
  obtain ⟨K,hK⟩ := halfSum_eq_input_add_large_eventually f hlower
  have ht : Tendsto (fun N : ℕ => K / ((N : ℝ)*log N)) atTop (𝓝 0) := by
    have hk : Tendsto (fun N : ℕ => K/(N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
    have hh := hk.div_atTop (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    simpa only [div_div] using hh
  apply ht.congr'
  filter_upwards [hK] with N hN
  rw [hN]
  congr 1
  ring

lemma remainder_large_error_tendsto (f : ℤ[X])
    (hlower : ∀ᶠ n : ℕ in atTop, n*n ≤ ⌊f.eval (n : ℤ)⌋₊)
    {a : ℝ} (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)) / N) atTop (𝓝 a)) :
    Tendsto (fun N : ℕ =>
      ((halfSum f N - truncatedDivisorSum f N N) - largeDivisorSum f N) /
        ((N : ℝ)*log N)) atTop (𝓝 0) := by
  have hh := (halfSum_input_large_error_tendsto f hlower).add
    (inputDivisorSum_error_tendsto f hmean)
  simp only [zero_add, ← add_div] at hh
  convert hh using 1
  ext N
  congr 1
  ring

lemma remainder_limit_iff_large_limit (f : ℤ[X])
    (hlower : ∀ᶠ n : ℕ in atTop, n*n ≤ ⌊f.eval (n : ℤ)⌋₊)
    {a b : ℝ} (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)) / N) atTop (𝓝 a)) :
    Tendsto (fun N : ℕ => (halfSum f N - truncatedDivisorSum f N N) /
      ((N : ℝ)*log N)) atTop (𝓝 b) ↔
    Tendsto (fun N : ℕ => largeDivisorSum f N / ((N : ℝ)*log N)) atTop (𝓝 b) := by
  have herr := remainder_large_error_tendsto f hlower hmean
  constructor
  · intro h
    have hh := h.sub herr
    simpa only [sub_zero, ← sub_div, sub_sub_cancel] using hh
  · intro h
    have hh := herr.add h
    simpa only [zero_add, ← add_div, sub_add_cancel] using hh

lemma higher_degree_positive_limit_iff_large_limit {f : ℤ[X]} (hdeg : 3 ≤ f.natDegree)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n)
    {a : ℝ} (ha : 0 < a) (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)) / N) atTop (𝓝 a)) :
    (∃ c > (0 : ℝ), Tendsto (fun x : ℝ => Erdos975Sum f x/(x*log x)) atTop (𝓝 c)) ↔
      ∃ b : ℝ, Tendsto (fun N : ℕ => largeDivisorSum f N / ((N : ℝ)*log N)) atTop (𝓝 b) := by
  rw [higher_degree_positive_limit_iff_remainder_exists hdeg hpos ha hmean]
  exact exists_congr (fun b => remainder_limit_iff_large_limit f (higher_degree_eventual_lower hdeg hpos) hmean)


end GeneralDivisors

namespace GeneralDivisors

lemma sum_without_large_nat_tendsto (f : ℤ[X])
    (hlower : ∀ᶠ n : ℕ in atTop, n*n ≤ ⌊f.eval (n : ℤ)⌋₊)
    {a : ℝ} (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)) / N) atTop (𝓝 a)) :
    Tendsto (fun N : ℕ => (Erdos975Sum f N - 2*largeDivisorSum f N) /
      ((N : ℝ)*log N)) atTop (𝓝 (2*a)) := by
  have hh := ((halfSum_input_large_error_tendsto f hlower).add
    (inputDivisorSum_limit f hmean)).const_mul 2
  have ht := (halfSum_error_tendsto f).add hh
  simp only [zero_add] at ht
  convert ht using 1
  ext N
  ring

lemma sum_without_large_real_tendsto (f : ℤ[X])
    (hlower : ∀ᶠ n : ℕ in atTop, n*n ≤ ⌊f.eval (n : ℤ)⌋₊)
    {a : ℝ} (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)) / N) atTop (𝓝 a)) :
    Tendsto (fun x : ℝ => (Erdos975Sum f x - 2*largeDivisorSum f ⌊x⌋₊) /
      (x*log x)) atTop (𝓝 (2*a)) := by
  have hf : Asymptotics.IsEquivalent atTop (fun x : ℝ => (⌊x⌋₊ : ℝ)) id :=
    Asymptotics.isEquivalent_nat_floor
  have hg := hf.mul (hf.log tendsto_id)
  have heq : Asymptotics.IsEquivalent atTop
      (fun x : ℝ => (Erdos975Sum f x - 2*largeDivisorSum f ⌊x⌋₊) /
        ((⌊x⌋₊ : ℝ)*log (⌊x⌋₊ : ℝ)))
      (fun x : ℝ => (Erdos975Sum f x - 2*largeDivisorSum f ⌊x⌋₊) / (x*log x)) :=
    Asymptotics.IsEquivalent.refl.div hg
  apply heq.tendsto_nhds_iff.mp
  have h := (sum_without_large_nat_tendsto f hlower hmean).comp
    (tendsto_nat_floor_atTop (α := ℝ))
  simpa only [Function.comp_apply, Erdos975Sum, Nat.floor_natCast] using h

lemma eventually_lower_of_root_mean (f : ℤ[X])
    (hlower : ∀ᶠ n : ℕ in atTop, n*n ≤ ⌊f.eval (n : ℤ)⌋₊)
    {a : ℝ} (hmean : Tendsto (fun N : ℕ =>
      (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)) / N) atTop (𝓝 a))
    {c : ℝ} (hc : c < 2*a) :
    ∀ᶠ x : ℝ in atTop, c < Erdos975Sum f x / (x*log x) := by
  have hh := (sum_without_large_real_tendsto f hlower hmean).eventually
    (eventually_gt_nhds hc)
  filter_upwards [hh,eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hd : 0 < x*log x := mul_pos (by linarith) (Real.log_pos hx1)
  apply hx.trans_le
  apply div_le_div_of_nonneg_right _ hd.le
  have h := largeDivisorSum_nonneg f ⌊x⌋₊
  linarith

lemma largeDivisorCount_eq_factorPairs (f : ℤ[X]) (n : ℕ) :
    largeDivisorCount f n =
      {p ∈ (⌊f.eval (n : ℤ)⌋₊).divisorsAntidiagonal | n < p.1 ∧ p.1 ≤ p.2}.card := by
  rw [card_filter, Nat.sum_divisorsAntidiagonal (fun d e => if n < d ∧ d ≤ e then (1 : ℕ) else 0)]
  unfold largeDivisorCount
  rw [card_filter]
  apply sum_congr rfl
  intro q hq
  simp only [Nat.le_div_iff_mul_le (Nat.pos_of_mem_divisors hq)]

end GeneralDivisors

lemma erdos_975_lower_bound (f : ℤ[X]) (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    ∃ c > (0 : ℝ), ∀ᶠ x : ℝ in atTop, c*x*log x ≤ Erdos975Sum f x := by
  by_cases hsmall : f.natDegree ≤ 2
  · have hlim : ∃ c > (0 : ℝ), Tendsto (fun x : ℝ => Erdos975Sum f x/(x*log x)) atTop (𝓝 c) := by
      by_cases hlin : f.natDegree = 1
      · exact erdos_975_degree_one f hlin hirr hpos
      · exact erdos_975_degree_two f (by omega) hirr hpos
    obtain ⟨c,hc,hlim⟩ := hlim
    refine ⟨c/2,div_pos hc (by norm_num),?_⟩
    filter_upwards [hlim.eventually (eventually_gt_nhds (show c/2 < c by linarith)),
      eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hd : 0 < x*log x := mul_pos (by linarith) (Real.log_pos hx1)
    have hh := (lt_div_iff₀ hd).mp hx
    nlinarith
  · obtain ⟨a,ha,hm⟩ := GeneralDivisors.polynomialRootCount_mean_positive f hdeg hirr
    have hlow := GeneralDivisors.eventually_lower_of_root_mean f
      (GeneralDivisors.higher_degree_eventual_lower (by omega) hpos) hm
      (show a < 2*a by linarith)
    refine ⟨a,ha,?_⟩
    filter_upwards [hlow,eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hd : 0 < x*log x := mul_pos (by linarith) (Real.log_pos hx1)
    have hh := (lt_div_iff₀ hd).mp hx
    nlinarith


namespace Sieve
open Finset Real Filter Polynomial


/-- A finite orthogonal-family form of Selberg's upper-bound argument. -/
lemma orthogonal_family_bound {α κ : Type*} [DecidableEq α] [DecidableEq κ]
    (A B : Finset α) (F : Finset κ) (hBA : B ⊆ A) (hF : F.Nonempty)
    (φ : κ → α → ℝ) (g : κ → ℝ) (Z E : ℝ)
    (hg : ∀ r ∈ F, 0 < g r)
    (hB : ∀ r ∈ F, ∀ n ∈ B, φ r n = 1)
    (hcorr : ∀ r ∈ F, ∀ t ∈ F,
      (∑ n ∈ A, φ r n * φ t n) ≤ (if r = t then Z*g r else 0) + E) :
    (B.card : ℝ) ≤ Z/(∑ r ∈ F, (g r)⁻¹) + E := by
  let G : ℝ := ∑ r ∈ F, (g r)⁻¹
  have hG : 0 < G := sum_pos (fun r hr => inv_pos.mpr (hg r hr)) hF
  let w : κ → ℝ := fun r => (g r)⁻¹/G
  have hw (r : κ) (hr : r ∈ F) : 0 ≤ w r := div_nonneg (inv_nonneg.mpr (hg r hr).le) hG.le
  have hsumw : ∑ r ∈ F, w r = 1 := by
    dsimp [w]
    rw [← sum_div]
    exact div_self hG.ne'
  let W : α → ℝ := fun n => ∑ r ∈ F, w r*φ r n
  have hWB (n : α) (hn : n ∈ B) : W n = 1 := by
    dsimp [W]
    calc
      _ = ∑ r ∈ F, w r := sum_congr rfl (fun r hr => by rw [hB r hr n hn, mul_one])
      _ = 1 := hsumw
  have hbasic : (B.card : ℝ) ≤ ∑ n ∈ A, W n ^ 2 := by
    calc
      _ = ∑ n ∈ B, W n ^ 2 := by
        calc
          _ = ∑ _n ∈ B, (1 : ℝ) := by simp
          _ = _ := sum_congr rfl (fun n hn => by rw [hWB n hn, one_pow])
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hBA (fun n _ _ => sq_nonneg (W n))
  have hexpand : ∑ n ∈ A, W n ^ 2 =
      ∑ r ∈ F, ∑ t ∈ F, w r*w t*(∑ n ∈ A, φ r n*φ t n) := by
    simp only [W, pow_two, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro r hr
    rw [sum_comm]
    apply sum_congr rfl
    intro t ht
    apply sum_congr rfl
    intro n hn
    ring
  have hupper : ∑ r ∈ F, ∑ t ∈ F, w r*w t*(∑ n ∈ A, φ r n*φ t n) ≤
      ∑ r ∈ F, ∑ t ∈ F, w r*w t*((if r = t then Z*g r else 0)+E) := by
    apply sum_le_sum
    intro r hr
    apply sum_le_sum
    intro t ht
    exact mul_le_mul_of_nonneg_left (hcorr r hr t ht) (mul_nonneg (hw r hr) (hw t ht))
  have hmain : ∑ r ∈ F, ∑ t ∈ F, w r*w t*(if r = t then Z*g r else 0) = Z/G := by
    have hrow (r : κ) (hr : r ∈ F) :
        (∑ t ∈ F, w r*w t*(if r = t then Z*g r else 0)) = Z/G^2*(g r)⁻¹ := by
      rw [sum_eq_single r]
      · simp only [ite_true]
        dsimp [w]
        field_simp [hG.ne', (hg r hr).ne']
        <;> ring
      · intro t ht htr
        rw [if_neg (Ne.symm htr), mul_zero]
      · exact fun h => (h hr).elim
    rw [sum_congr rfl hrow, ← mul_sum]
    change Z/G^2*G = Z/G
    field_simp
  have herr : ∑ r ∈ F, ∑ t ∈ F, w r*w t*E = E := by
    simp only [mul_assoc, ← mul_sum, ← sum_mul, hsumw, one_mul]
  apply hbasic.trans
  rw [hexpand]
  apply hupper.trans_eq
  simp only [mul_add, sum_add_distrib, hmain, herr]
  rfl


variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

def incidenceCount (A : Finset α) (R : α → Finset ι) (U : Finset ι) : ℕ :=
  {n ∈ A | U ⊆ R n}.card

lemma product_incidence_expansion (S T : Finset ι) (c : ι → ℝ) :
    ∏ p ∈ S, (1 + c p*(if p ∈ T then 1 else 0)) =
      ∑ U ∈ S.powerset, if U ⊆ T then ∏ p ∈ U, c p else 0 := by
  rw [prod_one_add]
  apply sum_congr rfl
  intro U hU
  rw [prod_mul_distrib]
  by_cases h : U ⊆ T
  · have hp : ∏ p ∈ U, (if p ∈ T then (1 : ℝ) else 0) = 1 :=
      prod_eq_one (fun p hp => by rw [if_pos (h hp)])
    rw [if_pos h, hp, mul_one]
  · obtain ⟨p,hp,hpT⟩ := not_subset.mp h
    have hz : (∏ p ∈ U, if p ∈ T then (1 : ℝ) else 0) = 0 :=
      prod_eq_zero hp (if_neg hpT)
    rw [if_neg h, hz, mul_zero]

lemma product_incidence_sum (A : Finset α) (R : α → Finset ι) (S : Finset ι) (c : ι → ℝ) :
    (∑ n ∈ A, ∏ p ∈ S, (1+c p*(if p ∈ R n then 1 else 0))) =
      ∑ U ∈ S.powerset, (∏ p ∈ U, c p)*(incidenceCount A R U : ℝ) := by
  simp only [product_incidence_expansion]
  rw [sum_comm]
  apply sum_congr rfl
  intro U hU
  rw [← sum_filter]
  simp [incidenceCount, mul_comm]

lemma product_incidence_main (S : Finset ι) (c ν : ι → ℝ) (Z : ℝ) :
    Z*(∏ p ∈ S, (1+c p*ν p)) =
      ∑ U ∈ S.powerset, (∏ p ∈ U, c p)*(Z*∏ p ∈ U, ν p) := by
  rw [prod_one_add, mul_sum]
  apply sum_congr rfl
  intro U hU
  rw [prod_mul_distrib]
  ring

lemma product_incidence_error (A : Finset α) (R : α → Finset ι) (S : Finset ι)
    (c ν : ι → ℝ) (Z E : ℝ)
    (hcount : ∀ U ⊆ S, |(incidenceCount A R U : ℝ) - Z*∏ p ∈ U, ν p| ≤ E) :
    |(∑ n ∈ A, ∏ p ∈ S, (1+c p*(if p ∈ R n then 1 else 0))) -
      Z*∏ p ∈ S, (1+c p*ν p)| ≤ E*∏ p ∈ S, (1+|c p|) := by
  rw [product_incidence_sum, product_incidence_main, ← sum_sub_distrib]
  calc
    _ ≤ ∑ U ∈ S.powerset,
        |(∏ p ∈ U, c p)*(incidenceCount A R U : ℝ) -
          (∏ p ∈ U, c p)*(Z*∏ p ∈ U, ν p)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ U ∈ S.powerset, E*∏ p ∈ U, |c p| := by
      apply sum_le_sum
      intro U hU
      rw [← mul_sub, abs_mul, abs_prod]
      simpa only [mul_comm E] using mul_le_mul_of_nonneg_left
        (hcount U (mem_powerset.mp hU)) (prod_nonneg (fun p hp => abs_nonneg (c p)))
    _ = E*∏ p ∈ S, (1+|c p|) := by rw [← mul_sum, prod_one_add]

noncomputable def orthogonalBasis (ν : ι → ℝ) (r T : Finset ι) : ℝ :=
  ∏ p ∈ r, (1-(if p ∈ T then 1 else 0)*(ν p)⁻¹)

noncomputable def correlationCoeff (ν : ι → ℝ) (r t : Finset ι) (p : ι) : ℝ :=
  if p ∈ r ∩ t then (ν p)⁻¹^2 - 2*(ν p)⁻¹ else -(ν p)⁻¹

lemma orthogonalBasis_mul (ν : ι → ℝ) (r t T : Finset ι) :
    orthogonalBasis ν r T * orthogonalBasis ν t T =
      ∏ p ∈ r ∪ t, (1+correlationCoeff ν r t p*(if p ∈ T then 1 else 0)) := by
  have hr : orthogonalBasis ν r T =
      ∏ p ∈ r ∪ t, if p ∈ r then (1-(if p ∈ T then 1 else 0)*(ν p)⁻¹) else 1 := by
    rw [prod_ite_mem, union_inter_cancel_left]
    rfl
  have ht : orthogonalBasis ν t T =
      ∏ p ∈ r ∪ t, if p ∈ t then (1-(if p ∈ T then 1 else 0)*(ν p)⁻¹) else 1 := by
    rw [prod_ite_mem, union_inter_cancel_right]
    rfl
  rw [hr,ht,← prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  have hp' := mem_union.mp hp
  dsimp only [correlationCoeff]
  simp only [mem_inter]
  by_cases hpr : p ∈ r <;> by_cases hpt : p ∈ t <;> by_cases hpT : p ∈ T <;>
    simp only [hpr,hpt,hpT,true_and,false_and,and_true,and_false,ite_true,ite_false] <;>
    (try tauto) <;> ring

lemma orthogonalBasis_main (ν : ι → ℝ) (r t : Finset ι)
    (hν : ∀ p ∈ r ∪ t, ν p ≠ 0) :
    (∏ p ∈ r ∪ t, (1+correlationCoeff ν r t p*ν p)) =
      if r = t then ∏ p ∈ r, ((ν p)⁻¹-1) else 0 := by
  by_cases hrt : r = t
  · subst t
    rw [if_pos rfl, union_self]
    apply prod_congr rfl
    intro p hp
    have hpν := hν p (by simpa using hp)
    simp only [correlationCoeff, inter_self, if_pos hp]
    field_simp
    <;> ring
  · rw [if_neg hrt]
    have hdiff : ∃ p ∈ r ∪ t, p ∉ r ∩ t := by
      by_contra! h
      apply hrt
      ext p
      constructor
      · intro hp
        exact (mem_inter.mp (h p (mem_union_left _ hp))).2
      · intro hp
        exact (mem_inter.mp (h p (mem_union_right _ hp))).1
    obtain ⟨p,hp,hpn⟩ := hdiff
    apply prod_eq_zero hp
    simp only [correlationCoeff, if_neg hpn, neg_mul, inv_mul_cancel₀ (hν p hp)]
    ring

lemma orthogonalBasis_correlation (A : Finset α) (R : α → Finset ι)
    (ν : ι → ℝ) (r t : Finset ι) (Z E : ℝ)
    (hν : ∀ p ∈ r ∪ t, ν p ≠ 0)
    (hcount : ∀ U ⊆ r ∪ t, |(incidenceCount A R U : ℝ) - Z*∏ p ∈ U, ν p| ≤ E) :
    |(∑ n ∈ A, orthogonalBasis ν r (R n)*orthogonalBasis ν t (R n)) -
      (if r = t then Z*∏ p ∈ r, ((ν p)⁻¹-1) else 0)| ≤
        E*∏ p ∈ r ∪ t, (1+|correlationCoeff ν r t p|) := by
  have hh := product_incidence_error A R (r ∪ t) (correlationCoeff ν r t) ν Z E hcount
  simpa only [orthogonalBasis_mul, orthogonalBasis_main ν r t hν, mul_ite, mul_zero] using hh


end Sieve

namespace Sieve
open Finset Real Filter Polynomial

open GeneralDivisors

lemma primeProduct_dvd_iff (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (m : ℤ) :
    ((∏ p ∈ S, p : ℕ) : ℤ) ∣ m ↔ ∀ p ∈ S, (p : ℤ) ∣ m := by
  simp only [Int.natCast_dvd]
  constructor
  · intro h p hp
    exact (dvd_prod_of_mem (fun p : ℕ => p) hp).trans h
  · intro h
    exact prod_dvd_of_isRelPrime (fun p hp q hq hpq =>
      Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq)) h

lemma polynomialRootCount_primeProduct (f : ℤ[X]) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    polynomialRootCount f (∏ p ∈ S, p) = ∏ p ∈ S, polynomialRootCount f p := by
  have hprod : ∏ p ∈ S, p ≠ 0 := prod_ne_zero_iff.mpr (fun p hp => (hS p hp).ne_zero)
  have h := ArithmeticFunction.IsMultiplicative.map_prod id (rootFunction_multiplicative f) S
    (fun p hp q hq hpq => (Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq)
  simp only [id_eq, rootFunction_apply f hprod] at h
  have hh : ∏ p ∈ S, rootFunction f p = ∏ p ∈ S, (polynomialRootCount f p : ℝ) :=
    prod_congr rfl (fun p hp => rootFunction_apply f (hS p hp).ne_zero)
  rw [hh] at h
  exact_mod_cast h

noncomputable def rootDensity (f : ℤ[X]) (p : ℕ) : ℝ := (polynomialRootCount f p : ℝ)/p

lemma rootDensity_primeProduct (f : ℤ[X]) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (polynomialRootCount f (∏ p ∈ S, p) : ℝ)/(∏ p ∈ S, p : ℕ) = ∏ p ∈ S, rootDensity f p := by
  simp only [rootDensity, polynomialRootCount_primeProduct f S hS, Nat.cast_prod, prod_div_distrib]

lemma incidenceCount_polynomial (f : ℤ[X]) (N a : ℕ) (S U : Finset ℕ)
    (hUS : U ⊆ S) (hS : ∀ p ∈ S, p.Prime) (haS : ∀ p ∈ S, a.Coprime p) :
    incidenceCount {n ∈ Ioc 0 N | (a : ℤ) ∣ f.eval ((n : ℕ) : ℤ)}
      (fun n => {p ∈ S | ((p : ℕ) : ℤ) ∣ f.eval (n : ℤ)}) U =
      divisibleValueCount f (a*∏ p ∈ U, p) N := by
  unfold incidenceCount divisibleValueCount
  congr 1
  ext n
  simp only [mem_filter]
  have hsub : U ⊆ {p ∈ S | ((p : ℕ) : ℤ) ∣ f.eval (n : ℤ)} ↔
      ∀ p ∈ U, (p : ℤ) ∣ f.eval (n : ℤ) := by
    constructor
    · intro h p hp
      exact (mem_filter.mp (h hp)).2
    · intro h p hp
      exact mem_filter.mpr ⟨hUS hp,h p hp⟩
  rw [hsub, ← primeProduct_dvd_iff U (fun p hp => hS p (hUS hp))]
  have hc : a.Coprime (∏ p ∈ U, p) := Nat.Coprime.prod_right (fun p hp => haS p (hUS hp))
  simp only [Int.natCast_dvd]
  constructor
  · rintro ⟨⟨hn,ha⟩,hU⟩
    exact ⟨hn,hc.mul_dvd_of_dvd_of_dvd ha hU⟩
  · rintro ⟨hn,h⟩
    exact ⟨⟨hn,(dvd_mul_right a _).trans h⟩,(dvd_mul_left _ a).trans h⟩

lemma polynomial_incidence_error (f : ℤ[X]) (N a : ℕ) (ha : 0 < a) (S U : Finset ℕ)
    (hUS : U ⊆ S) (hS : ∀ p ∈ S, p.Prime) (haS : ∀ p ∈ S, a.Coprime p) :
    |(incidenceCount {n ∈ Ioc 0 N | (a : ℤ) ∣ f.eval ((n : ℕ) : ℤ)}
      (fun n => {p ∈ S | ((p : ℕ) : ℤ) ∣ f.eval (n : ℤ)}) U : ℝ) -
      ((N : ℝ)/a*polynomialRootCount f a)*∏ p ∈ U, rootDensity f p| ≤
      2*(a : ℝ)*(∏ p ∈ U, p : ℕ) := by
  have hUpos : 0 < ∏ p ∈ U, p := prod_pos (fun p hp => (hS p (hUS hp)).pos)
  have hc : a.Coprime (∏ p ∈ U, p) := Nat.Coprime.prod_right (fun p hp => haS p (hUS hp))
  rw [incidenceCount_polynomial f N a S U hUS hS haS, ← rootDensity_primeProduct f U (fun p hp => hS p (hUS hp))]
  have hmain : ((N : ℝ)/a*polynomialRootCount f a)*
      ((polynomialRootCount f (∏ p ∈ U, p) : ℝ)/(∏ p ∈ U, p : ℕ)) =
      (N : ℝ)/(a*∏ p ∈ U, p : ℕ)*polynomialRootCount f (a*∏ p ∈ U, p) := by
    rw [polynomialRootCount_mul f hc, Nat.cast_mul, Nat.cast_mul]
    ring
  rw [hmain]
  calc
    _ ≤ 2*(polynomialRootCount f (a*∏ p ∈ U, p) : ℝ) :=
      polynomial_root_count_error f (Nat.mul_pos ha hUpos) N
    _ ≤ 2*(a : ℝ)*(∏ p ∈ U, p : ℕ) := by
      have hh := polynomialRootCount_le_modulus f (Nat.mul_pos ha hUpos)
      exact_mod_cast (show 2*polynomialRootCount f (a*∏ p ∈ U, p) ≤ 2*a*∏ p ∈ U, p by simpa only [mul_assoc] using Nat.mul_le_mul_left 2 hh)

lemma rootDensity_pos_lt_one (f : ℤ[X]) {p : ℕ} (hp : p.Prime)
    (hρ : 0 < polynomialRootCount f p ∧ polynomialRootCount f p < p) :
    0 < rootDensity f p ∧ rootDensity f p < 1 := by
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  constructor
  · exact div_pos (Nat.cast_pos.mpr hρ.1) hp'
  · exact (div_lt_one hp').mpr (Nat.cast_lt.mpr hρ.2)

lemma rootDensity_inv_le (f : ℤ[X]) {p : ℕ} (hp : p.Prime)
    (hρ : 0 < polynomialRootCount f p) : (rootDensity f p)⁻¹ ≤ p := by
  rw [rootDensity, inv_div]
  have hρr : (0 : ℝ) < polynomialRootCount f p := Nat.cast_pos.mpr hρ
  apply (div_le_iff₀ hρr).mpr
  have hρ1 : (1 : ℝ) ≤ polynomialRootCount f p := Nat.one_le_cast.mpr hρ
  nlinarith [Nat.cast_nonneg p (α := ℝ)]

lemma correlationCoeff_root_bound (f : ℤ[X]) (r t : Finset ℕ) {p : ℕ} (hp : p.Prime)
    (hρ : 0 < polynomialRootCount f p) :
    1+|correlationCoeff (rootDensity f) r t p| ≤ (p : ℝ)^4 := by
  have hp2 : (2 : ℝ) ≤ p := Nat.ofNat_le_cast.mpr hp.two_le
  have hv : (rootDensity f p)⁻¹ ≤ p := rootDensity_inv_le f hp hρ
  have hv0 : 0 ≤ (rootDensity f p)⁻¹ := inv_nonneg.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hsq : (rootDensity f p)⁻¹^2 ≤ (p : ℝ)^2 := by nlinarith
  have hab : |correlationCoeff (rootDensity f) r t p| ≤ (p : ℝ)^2 := by
    unfold correlationCoeff
    split_ifs
    · rw [abs_le]
      constructor <;> nlinarith [sq_nonneg ((rootDensity f p)⁻¹-1)]
    · rw [abs_neg, abs_of_nonneg hv0]
      nlinarith
  nlinarith [sq_nonneg ((p : ℝ)^2-1)]

lemma primeProduct_union_bound (r t : Finset ℕ) (D : ℕ)
    (hS : ∀ p ∈ r ∪ t, p.Prime)
    (hr : ∏ p ∈ r, p ≤ D) (ht : ∏ p ∈ t, p ≤ D) :
    ∏ p ∈ r ∪ t, p ≤ D^2 := by
  have hi : 0 < ∏ p ∈ r ∩ t, p := prod_pos (fun p hp => (hS p
    (mem_union_left _ (mem_inter.mp hp).1)).pos)
  calc
    _ ≤ (∏ p ∈ r ∪ t, p)*(∏ p ∈ r ∩ t, p) := Nat.le_mul_of_pos_right _ hi
    _ = (∏ p ∈ r, p)*(∏ p ∈ t, p) := prod_union_inter
    _ ≤ D^2 := by simpa only [pow_two] using Nat.mul_le_mul hr ht

/-- A finite Selberg sieve bound for polynomial values in a fixed divisibility class.
The error term is deliberately coarse, but is uniform in the set of sifting primes. -/
lemma polynomial_sieve_bound (f : ℤ[X]) (N a D : ℕ) (ha : 0 < a) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hρ : ∀ p ∈ S, 0 < polynomialRootCount f p ∧ polynomialRootCount f p < p)
    (haS : ∀ p ∈ S, a.Coprime p) :
    ({n ∈ Ioc 0 N | (a : ℤ) ∣ f.eval ((n : ℕ) : ℤ) ∧
      ∀ p ∈ S, ¬((p : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)}.card : ℝ) ≤
      ((N : ℝ)/a*polynomialRootCount f a) /
        (∑ r ∈ S.powerset with (∏ p ∈ r, p) ≤ D,
          (∏ p ∈ r, ((rootDensity f p)⁻¹-1))⁻¹) + 2*(a : ℝ)*(D : ℝ)^10 := by
  let A := {n ∈ Ioc 0 N | (a : ℤ) ∣ f.eval ((n : ℕ) : ℤ)}
  let B := {n ∈ Ioc 0 N | (a : ℤ) ∣ f.eval ((n : ℕ) : ℤ) ∧
      ∀ p ∈ S, ¬((p : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)}
  let F := {r ∈ S.powerset | (∏ p ∈ r, p) ≤ D}
  let R : ℕ → Finset ℕ := fun n => {p ∈ S | ((p : ℕ) : ℤ) ∣ f.eval (n : ℤ)}
  have hFS (r : Finset ℕ) (hr : r ∈ F) : r ⊆ S := mem_powerset.mp (mem_filter.mp hr).1
  have hFD (r : Finset ℕ) (hr : r ∈ F) : ∏ p ∈ r, p ≤ D := (mem_filter.mp hr).2
  have hBA : B ⊆ A := by
    intro n hn
    exact mem_filter.mpr ⟨(mem_filter.mp hn).1,(mem_filter.mp hn).2.1⟩
  have hF : F.Nonempty := ⟨∅,by simp [F,hD]⟩
  apply orthogonal_family_bound A B F hBA hF
    (fun r n => orthogonalBasis (rootDensity f) r (R n))
    (fun r => ∏ p ∈ r, ((rootDensity f p)⁻¹-1))
    ((N : ℝ)/a*polynomialRootCount f a) (2*(a : ℝ)*(D : ℝ)^10)
  · intro r hr
    apply prod_pos
    intro p hp
    have hh := rootDensity_pos_lt_one f (hS p (hFS r hr hp)) (hρ p (hFS r hr hp))
    exact sub_pos.mpr ((one_lt_inv₀ hh.1).mpr hh.2)
  · intro r hr n hn
    apply prod_eq_one
    intro p hp
    have hpnd := (mem_filter.mp hn).2.2 p (hFS r hr hp)
    have hpn : p ∉ R n := fun hh => hpnd (mem_filter.mp hh).2
    simp only [if_neg hpn, zero_mul, sub_zero]
  · intro r hr t ht
    have hrtS : r ∪ t ⊆ S := union_subset (hFS r hr) (hFS t ht)
    have hrt : ∏ p ∈ r ∪ t, p ≤ D^2 :=
      primeProduct_union_bound r t D (fun p hp => hS p (hrtS hp)) (hFD r hr) (hFD t ht)
    have hcount (U : Finset ℕ) (hU : U ⊆ r ∪ t) :
        |(incidenceCount A R U : ℝ) - ((N : ℝ)/a*polynomialRootCount f a)*
          ∏ p ∈ U, rootDensity f p| ≤ 2*(a : ℝ)*(D : ℝ)^2 := by
      have hprod : ∏ p ∈ U, p ≤ D^2 := (prod_le_prod_of_subset_of_one_le' hU
        (fun p hp _ => (hS p (hrtS hp)).one_le)).trans hrt
      exact (polynomial_incidence_error f N a ha S U (hU.trans hrtS) hS haS).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hprod) (by positivity))
    have hcorr := orthogonalBasis_correlation A R (rootDensity f) r t
      ((N : ℝ)/a*polynomialRootCount f a) (2*(a : ℝ)*(D : ℝ)^2)
      (fun p hp => (rootDensity_pos_lt_one f (hS p (hrtS hp)) (hρ p (hrtS hp))).1.ne') hcount
    have hcoeff : ∏ p ∈ r ∪ t, (1+|correlationCoeff (rootDensity f) r t p|) ≤ (D : ℝ)^8 := by
      calc
        _ ≤ ∏ p ∈ r ∪ t, (p : ℝ)^4 := prod_le_prod
          (fun p hp => by positivity)
          (fun p hp => correlationCoeff_root_bound f r t (hS p (hrtS hp)) (hρ p (hrtS hp)).1)
        _ = ((∏ p ∈ r ∪ t, p : ℕ) : ℝ)^4 := by rw [Nat.cast_prod, prod_pow]
        _ ≤ ((D : ℝ)^2)^4 := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hrt) _
        _ = (D : ℝ)^8 := by ring
    have he : (2*(a : ℝ)*(D : ℝ)^2) *
        (∏ p ∈ r ∪ t, (1+|correlationCoeff (rootDensity f) r t p|)) ≤
        2*(a : ℝ)*(D : ℝ)^10 := by
      have hh := mul_le_mul_of_nonneg_left hcoeff (by positivity : 0 ≤ 2*(a : ℝ)*(D : ℝ)^2)
      convert hh using 1 <;> ring
    have hh := (le_abs_self _).trans (hcorr.trans he)
    linarith


end Sieve

namespace Sieve
open Finset Real Filter Polynomial

open EulerComparison GeneralDivisors

lemma fromPrimePowers_nonneg (F : ℕ → ℕ → ℝ) (hF : ∀ p k, 0 ≤ F p k) (n : ℕ) :
    0 ≤ fromPrimePowers F n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [fromPrimePowers_apply F hn, Finsupp.prod]
    exact prod_nonneg (fun p hp => hF p _)

noncomputable def squarefreePart (r : ArithmeticFunction ℝ) (S : Finset ℕ) : ArithmeticFunction ℝ :=
  fromPrimePowers (fun p k => if k = 0 then 1 else if k = 1 ∧ p ∉ S then r p else 0)

noncomputable def powerfulPart (r : ArithmeticFunction ℝ) (S : Finset ℕ) : ArithmeticFunction ℝ :=
  fromPrimePowers (fun p k => if k = 0 then 1 else if k = 1 ∧ p ∉ S then 0 else r (p^k))

lemma squarefreePart_multiplicative (r : ArithmeticFunction ℝ) (S : Finset ℕ) :
    (squarefreePart r S).IsMultiplicative := fromPrimePowers_multiplicative _

lemma powerfulPart_multiplicative (r : ArithmeticFunction ℝ) (S : Finset ℕ) :
    (powerfulPart r S).IsMultiplicative := fromPrimePowers_multiplicative _

lemma squarefreePart_prime_pow (r : ArithmeticFunction ℝ) (S : Finset ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    squarefreePart r S (p^k) = if k = 0 then 1 else if k = 1 ∧ p ∉ S then r p else 0 :=
  fromPrimePowers_prime_pow _ hp (by simp) k

lemma powerfulPart_prime_pow (r : ArithmeticFunction ℝ) (S : Finset ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    powerfulPart r S (p^k) = if k = 0 then 1 else if k = 1 ∧ p ∉ S then 0 else r (p^k) :=
  fromPrimePowers_prime_pow _ hp (by simp) k

lemma squarefreePart_nonneg (r : ArithmeticFunction ℝ) (S : Finset ℕ) (hr : ∀ n, 0 ≤ r n) (n : ℕ) :
    0 ≤ squarefreePart r S n := by
  apply fromPrimePowers_nonneg
  intro p k
  split_ifs <;> first | positivity | exact hr _

lemma powerfulPart_nonneg (r : ArithmeticFunction ℝ) (S : Finset ℕ) (hr : ∀ n, 0 ≤ r n) (n : ℕ) :
    0 ≤ powerfulPart r S n := by
  apply fromPrimePowers_nonneg
  intro p k
  split_ifs <;> first | positivity | exact hr _

lemma arithmeticFunction_mul_nonneg (r t : ArithmeticFunction ℝ)
    (hr : ∀ n, 0 ≤ r n) (ht : ∀ n, 0 ≤ t n) (n : ℕ) : 0 ≤ (r*t) n := by
  rw [ArithmeticFunction.mul_apply]
  exact sum_nonneg (fun x hx => mul_nonneg (hr x.1) (ht x.2))

lemma multiplicative_le_of_prime_powers (r t : ArithmeticFunction ℝ)
    (hr : r.IsMultiplicative) (ht : t.IsMultiplicative) (hrn : ∀ n, 0 ≤ r n)
    (hp : ∀ p : ℕ, p.Prime → ∀ k : ℕ, r (p^k) ≤ t (p^k)) (n : ℕ) : r n ≤ t n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [hr.multiplicative_factorization r hn, ht.multiplicative_factorization t hn,
      Finsupp.prod, Finsupp.prod]
    apply prod_le_prod (fun p hp => hrn _)
    intro p hpn
    exact hp p (Nat.prime_of_mem_primeFactors (by simpa only [Nat.support_factorization] using hpn)) _

lemma le_squarefreePart_mul_powerfulPart (r : ArithmeticFunction ℝ) (S : Finset ℕ)
    (hr : r.IsMultiplicative) (hrn : ∀ n, 0 ≤ r n) (n : ℕ) :
    r n ≤ (squarefreePart r S * powerfulPart r S) n := by
  apply multiplicative_le_of_prime_powers r _ hr
    ((squarefreePart_multiplicative r S).mul (powerfulPart_multiplicative r S)) hrn _ n
  intro p hp k
  have hs := squarefreePart_nonneg r S hrn
  have hg := powerfulPart_nonneg r S hrn
  rw [mul_prime_pow _ _ hp]
  by_cases hk : k = 0
  · subst k
    simp [squarefreePart_prime_pow _ _ hp, (powerfulPart_multiplicative r S).1, hr.1]
  · by_cases hkp : k = 1 ∧ p ∉ S
    · have hh := single_le_sum (s := range (k+1))
        (f := fun i => squarefreePart r S (p^i)*powerfulPart r S (p^(k-i)))
        (fun i hi => mul_nonneg (hs _) (hg _)) (mem_range.mpr (Nat.lt_succ_self k))
      dsimp only at hh
      rw [Nat.sub_self, pow_zero, (powerfulPart_multiplicative r S).1, mul_one,
        squarefreePart_prime_pow _ _ hp, if_neg hk, if_pos hkp] at hh
      simpa only [hkp.1, pow_one] using hh
    · have hh := single_le_sum (s := range (k+1))
        (f := fun i => squarefreePart r S (p^i)*powerfulPart r S (p^(k-i)))
        (fun i hi => mul_nonneg (hs _) (hg _)) (mem_range.mpr (Nat.zero_lt_succ k))
      simpa only [Nat.sub_zero, pow_zero, (squarefreePart_multiplicative r S).1, one_mul,
        powerfulPart_prime_pow _ _ hp, if_neg hk, if_neg hkp] using hh

lemma rootFunction_nonneg (f : ℤ[X]) (n : ℕ) : 0 ≤ rootFunction f n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [rootFunction_apply f hn]
    positivity

lemma powerfulPart_root_summable {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) (S : Finset ℕ) :
    Summable (fun n : ℕ => powerfulPart (rootFunction f) S n/(n : ℝ)) := by
  obtain ⟨T,hT⟩ := finite_bad_primes hdeg hirr
  apply summable_divideByNat_of_good_primes _ (powerfulPart_multiplicative _ S) (S ∪ T)
    (Nat.cast_nonneg f.natDegree)
  · intro p hp hpST
    have hpS : p ∉ S := fun h => hpST (mem_union_left _ h)
    have hpT : p ∉ T := fun h => hpST (mem_union_right _ h)
    constructor
    · simpa [hpS] using powerfulPart_prime_pow (rootFunction f) S hp 1
    · intro k hk
      rw [powerfulPart_prime_pow _ _ hp, if_neg (by omega : k ≠ 0), if_neg (by omega : ¬(k = 1 ∧ p ∉ S)),
        rootFunction_apply f (pow_ne_zero _ hp.ne_zero), Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (hT p hp hpT k (by omega)).2
  · intro p hp
    apply Summable.of_nonneg_of_le
      (fun k => div_nonneg (powerfulPart_nonneg _ S (rootFunction_nonneg f) _) (by positivity))
      (fun k => ?_) (summable_polynomialRootCount_prime_powers hdeg hirr hp)
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [powerfulPart_prime_pow _ _ hp]
    split_ifs with hk hkS
    · subst k
      simp [polynomialRootCount_one]
    · positivity
    · rw [rootFunction_apply f (pow_ne_zero _ hp.ne_zero)]

lemma convolution_harmonic_le (h g : ArithmeticFunction ℝ)
    (hh : ∀ n, 0 ≤ h n) (hg : ∀ n, 0 ≤ g n)
    (hs : Summable (fun n : ℕ => g n/(n : ℝ))) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (h*g) n/(n : ℝ)) ≤
      (∑' n : ℕ, g n/(n : ℝ)) * (∑ n ∈ Ioc 0 N, h n/(n : ℝ)) := by
  change (∑ n ∈ Ioc 0 N, divideByNat (h*g) n) ≤ _
  rw [divideByNat_mul, mul_comm (divideByNat h), ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  simp only [divideByNat_apply]
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, (g n/(n : ℝ))*(∑ m ∈ Ioc 0 N, h m/(m : ℝ)) := by
      apply sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (hg n) (Nat.cast_nonneg n))
      exact sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right (Nat.div_le_self N n))
        (fun m _ _ => div_nonneg (hh m) (Nat.cast_nonneg m))
    _ = (∑ n ∈ Ioc 0 N, g n/(n : ℝ))*(∑ m ∈ Ioc 0 N, h m/(m : ℝ)) := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (hs.sum_le_tsum _ (fun n hn => div_nonneg (hg n) (Nat.cast_nonneg n)))
      (sum_nonneg (fun n hn => div_nonneg (hh n) (Nat.cast_nonneg n)))

lemma squarefreePart_root_harmonic_lower {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) (S : Finset ℕ) :
    ∃ c > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      c*log N ≤ ∑ n ∈ Ioc 0 N, squarefreePart (rootFunction f) S n/(n : ℝ) := by
  obtain ⟨a,ha,hmean⟩ := polynomialRootCount_mean_positive f hdeg hirr
  let g := powerfulPart (rootFunction f) S
  let h := squarefreePart (rootFunction f) S
  let C : ℝ := ∑' n : ℕ, g n/(n : ℝ)
  have hg : ∀ n, 0 ≤ g n := powerfulPart_nonneg _ S (rootFunction_nonneg f)
  have hh : ∀ n, 0 ≤ h n := squarefreePart_nonneg _ S (rootFunction_nonneg f)
  have hgs : Summable (fun n : ℕ => g n/(n : ℝ)) := powerfulPart_root_summable hdeg hirr S
  have hC : 0 < C := by
    have ht := hgs.le_tsum 1 (fun n hn => div_nonneg (hg n) (Nat.cast_nonneg n))
    simp only [Nat.cast_one, div_one, show g 1 = 1 from (powerfulPart_multiplicative _ S).1] at ht
    exact lt_of_lt_of_le zero_lt_one ht
  have hmean' := MeanTransfer.logarithmic_mean_Ioc_of_mean hmean
  refine ⟨a/(2*C),div_pos ha (mul_pos (by norm_num) hC),?_⟩
  filter_upwards [hmean'.eventually (eventually_gt_nhds (show a/2 < a by linarith)),
    eventually_gt_atTop (1 : ℕ)] with N hN hN1
  have hlog : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
  have hl := (lt_div_iff₀ hlog).mp hN
  have hroot : (∑ n ∈ Ioc 0 N, (polynomialRootCount f n : ℝ)/(n : ℝ)) ≤
      ∑ n ∈ Ioc 0 N, (h*g) n/(n : ℝ) := by
    apply sum_le_sum
    intro n hn
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    rw [← rootFunction_apply f (mem_Ioc.mp hn).1.ne']
    exact le_squarefreePart_mul_powerfulPart _ S (rootFunction_multiplicative f) (rootFunction_nonneg f) n
  have hu := convolution_harmonic_le h g hh hg hgs N
  change _ ≤ C*(∑ n ∈ Ioc 0 N, h n/(n : ℝ)) at hu
  change a/(2*C)*log N ≤ ∑ n ∈ Ioc 0 N, h n/(n : ℝ)
  apply le_of_mul_le_mul_right (a := C) (a0 := hC)
  change a/(2*C)*log N*C ≤ (∑ n ∈ Ioc 0 N, h n/(n : ℝ))*C
  have he : a/(2*C)*log N*C = a/2*log N := by field_simp
  rw [he]
  nlinarith


lemma fromPrimePowers_binary_support (F : ℕ → ℕ → ℝ)
    (hF : ∀ p k, 2 ≤ k → F p k = 0) {n : ℕ} (hn : fromPrimePowers F n ≠ 0) :
    n = ∏ p ∈ n.primeFactors, p ∧
    (∀ p ∈ n.primeFactors, n.factorization p = 1 ∧ F p 1 ≠ 0) ∧
    fromPrimePowers F n = ∏ p ∈ n.primeFactors, F p 1 := by
  have hn0 : n ≠ 0 := by intro h; subst n; simp at hn
  have hne : ∀ p ∈ n.primeFactors, F p (n.factorization p) ≠ 0 := by
    rw [fromPrimePowers_apply F hn0, Finsupp.prod, Nat.support_factorization] at hn
    exact prod_ne_zero_iff.mp hn
  have hk (p : ℕ) (hp : p ∈ n.primeFactors) : n.factorization p = 1 := by
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hpos := hp'.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp)
    have hnz := hne p hp
    by_contra hk1
    exact hnz (hF p _ (by omega))
  refine ⟨?_,fun p hp => ⟨hk p hp,by simpa only [hk p hp] using hne p hp⟩,?_⟩
  · calc
      n = n.factorization.prod (fun p k => p^k) := (Nat.factorization_prod_pow_eq_self hn0).symm
      _ = ∏ p ∈ n.primeFactors, p := by
        rw [Finsupp.prod, Nat.support_factorization]
        exact prod_congr rfl (fun p hp => by rw [hk p hp, pow_one])
  · rw [fromPrimePowers_apply F hn0, Finsupp.prod, Nat.support_factorization]
    exact prod_congr rfl (fun p hp => by rw [hk p hp])

noncomputable def supportedSquarefree (r : ArithmeticFunction ℝ) (A : Finset ℕ) : ArithmeticFunction ℝ :=
  fromPrimePowers (fun p k => if k = 0 then 1 else if k = 1 ∧ p ∈ A then r p else 0)

lemma supportedSquarefree_multiplicative (r : ArithmeticFunction ℝ) (A : Finset ℕ) :
    (supportedSquarefree r A).IsMultiplicative := fromPrimePowers_multiplicative _

lemma supportedSquarefree_prime_pow (r : ArithmeticFunction ℝ) (A : Finset ℕ)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    supportedSquarefree r A (p^k) = if k = 0 then 1 else if k = 1 ∧ p ∈ A then r p else 0 :=
  fromPrimePowers_prime_pow _ hp (by simp) k

lemma supportedSquarefree_nonneg (r : ArithmeticFunction ℝ) (A : Finset ℕ)
    (hr : ∀ n, 0 ≤ r n) (n : ℕ) : 0 ≤ supportedSquarefree r A n := by
  apply fromPrimePowers_nonneg
  intro p k
  split_ifs <;> first | positivity | exact hr _

lemma supportedSquarefree_zero_of_not_dvd (r : ArithmeticFunction ℝ) (A : Finset ℕ)
    {n : ℕ} (hn : ¬ n ∣ ∏ p ∈ A, p) : supportedSquarefree r A n = 0 := by
  by_contra hnz
  obtain ⟨he,hp,hv⟩ := fromPrimePowers_binary_support
    (fun p k => if k = 0 then 1 else if k = 1 ∧ p ∈ A then r p else 0)
    (by intro p k hk; simp [show k ≠ 0 by omega,show k ≠ 1 by omega]) hnz
  have hsub : n.primeFactors ⊆ A := by
    intro p hpn
    have hh := (hp p hpn).2
    by_contra hpA
    simp [hpA] at hh
  apply hn
  rw [he]
  exact prod_dvd_prod_of_subset _ _ _ hsub

lemma supportedSquarefree_summable (r : ArithmeticFunction ℝ) (A : Finset ℕ)
    (hA : ∀ p ∈ A, p.Prime) :
    Summable (fun n : ℕ => supportedSquarefree r A n/(n : ℝ)) := by
  have hP : (∏ p ∈ A, p) ≠ 0 := prod_ne_zero_iff.mpr (fun p hp => (hA p hp).ne_zero)
  apply summable_of_ne_finset_zero (s := (∏ p ∈ A, p).divisors)
  intro n hn
  have hnd : ¬ n ∣ ∏ p ∈ A, p := fun hd => hn (Nat.mem_divisors.mpr ⟨hd,hP⟩)
  rw [supportedSquarefree_zero_of_not_dvd r A hnd,zero_div]


lemma supportedSquarefree_tsum (r : ArithmeticFunction ℝ) (A : Finset ℕ)
    (hA : ∀ p ∈ A, p.Prime) :
    (∑' n : ℕ, supportedSquarefree r A n/(n : ℝ)) =
      ∏ p ∈ A, (1+r p/(p : ℝ)) := by
  have hP : (∏ p ∈ A, p) ≠ 0 := prod_ne_zero_iff.mpr (fun p hp => (hA p hp).ne_zero)
  have hsq : Squarefree (∏ p ∈ A, p) := squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hA p hp) (hA q hq)).mpr hpq))
    (fun p hp => (hA p hp).squarefree)
  rw [tsum_eq_sum (s := (∏ p ∈ A, p).divisors) (fun n hn => by
    rw [supportedSquarefree_zero_of_not_dvd r A (fun hd => hn (Nat.mem_divisors.mpr ⟨hd,hP⟩)),zero_div])]
  change (∑ n ∈ (∏ p ∈ A, p).divisors, divideByNat (supportedSquarefree r A) n) = _
  rw [← (divideByNat_multiplicative (supportedSquarefree_multiplicative r A)).prodPrimeFactors_one_add_of_squarefree hsq,
    Nat.primeFactors_prod hA]
  apply prod_congr rfl
  intro p hp
  have hpp : supportedSquarefree r A p = r p := by
    simpa [hp] using supportedSquarefree_prime_pow r A (hA p hp) 1
  simp only [divideByNat_apply, hpp]

lemma squarefreePart_prime (r : ArithmeticFunction ℝ) (S : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    squarefreePart r S p = if p ∉ S then r p else 0 := by
  simpa using squarefreePart_prime_pow r S hp 1

lemma supportedSquarefree_prime (r : ArithmeticFunction ℝ) (A : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    supportedSquarefree r A p = if p ∈ A then r p else 0 := by
  simpa using supportedSquarefree_prime_pow r A hp 1

lemma squarefreePart_remove_le (r : ArithmeticFunction ℝ) (S A : Finset ℕ)
    (hr : ∀ n, 0 ≤ r n) (n : ℕ) :
    squarefreePart r S n ≤ (squarefreePart r (S ∪ A) * supportedSquarefree r A) n := by
  have hnonneg := arithmeticFunction_mul_nonneg _ _
    (squarefreePart_nonneg r (S ∪ A) hr) (supportedSquarefree_nonneg r A hr)
  apply multiplicative_le_of_prime_powers _ _ (squarefreePart_multiplicative r S)
    ((squarefreePart_multiplicative r (S ∪ A)).mul (supportedSquarefree_multiplicative r A))
    (squarefreePart_nonneg r S hr) _ n
  intro p hp k
  by_cases hk0 : k = 0
  · subst k
    simp only [pow_zero, (squarefreePart_multiplicative r S).1,
      ArithmeticFunction.IsMultiplicative.map_one ((squarefreePart_multiplicative r (S ∪ A)).mul (supportedSquarefree_multiplicative r A))]
    exact le_rfl
  · by_cases hk1 : k = 1
    · subst k
      rw [pow_one, mul_apply_prime, (squarefreePart_multiplicative r (S ∪ A)).1,
        (supportedSquarefree_multiplicative r A).1, one_mul, mul_one,
        squarefreePart_prime _ _ hp, squarefreePart_prime _ _ hp, supportedSquarefree_prime _ _ hp]
      · by_cases hpS : p ∈ S <;> by_cases hpA : p ∈ A <;> simp [hpS,hpA,hr p]
      · exact hp
    · rw [squarefreePart_prime_pow r S hp k, if_neg hk0, if_neg (by tauto : ¬(k = 1 ∧ p ∉ S))]
      exact hnonneg _

lemma squarefreePart_harmonic_remove_le (r : ArithmeticFunction ℝ) (S A : Finset ℕ)
    (hr : ∀ n, 0 ≤ r n) (hA : ∀ p ∈ A, p.Prime) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, squarefreePart r S n/(n : ℝ)) ≤
      (∏ p ∈ A, (1+r p/(p : ℝ)))*(∑ n ∈ Ioc 0 N, squarefreePart r (S ∪ A) n/(n : ℝ)) := by
  have hh := convolution_harmonic_le (squarefreePart r (S ∪ A)) (supportedSquarefree r A)
    (squarefreePart_nonneg r (S ∪ A) hr) (supportedSquarefree_nonneg r A hr)
    (supportedSquarefree_summable r A hA) N
  rw [supportedSquarefree_tsum r A hA] at hh
  apply le_trans _ hh
  exact sum_le_sum (fun n hn => div_le_div_of_nonneg_right (squarefreePart_remove_le r S A hr n)
    (Nat.cast_nonneg n))

lemma squarefreePart_uniform_harmonic_lower {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) (S : Finset ℕ) :
    ∃ c > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ A : Finset ℕ, (∀ p ∈ A, p.Prime) →
        (c/(∏ p ∈ A, (1+(polynomialRootCount f p : ℝ)/p)))*log N ≤
          ∑ n ∈ Ioc 0 N, squarefreePart (rootFunction f) (S ∪ A) n/(n : ℝ) := by
  obtain ⟨c,hc,hlim⟩ := squarefreePart_root_harmonic_lower hdeg hirr S
  refine ⟨c,hc,?_⟩
  filter_upwards [hlim] with N hN
  intro A hA
  have hcost : 0 < ∏ p ∈ A, (1+(polynomialRootCount f p : ℝ)/p) := by
    apply prod_pos
    intro p hp
    have hh : (0 : ℝ) ≤ (polynomialRootCount f p : ℝ)/p := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith
  have hh := squarefreePart_harmonic_remove_le (rootFunction f) S A (rootFunction_nonneg f) hA N
  have heq : ∏ p ∈ A, (1+rootFunction f p/(p : ℝ)) = ∏ p ∈ A, (1+(polynomialRootCount f p : ℝ)/p) := by
    apply prod_congr rfl
    intro p hp
    rw [rootFunction_apply f (hA p hp).ne_zero]
  rw [heq] at hh
  apply le_of_mul_le_mul_right (a := ∏ p ∈ A, (1+(polynomialRootCount f p : ℝ)/p)) (a0 := hcost)
  rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hcost.ne']
  nlinarith


end Sieve

namespace Sieve
open Finset Real Filter Polynomial

open GeneralDivisors EulerComparison

noncomputable def sieveDenominator (f : ℤ[X]) (S : Finset ℕ) (D : ℕ) : ℝ :=
  ∑ r ∈ S.powerset with (∏ p ∈ r, p) ≤ D, (∏ p ∈ r, ((rootDensity f p)⁻¹-1))⁻¹

lemma squarefreePart_root_support (f : ℤ[X]) (T : Finset ℕ) {n : ℕ}
    (hn : squarefreePart (rootFunction f) T n ≠ 0) :
    n = ∏ p ∈ n.primeFactors, p ∧
    (∀ p ∈ n.primeFactors, p ∉ T ∧ 0 < polynomialRootCount f p) ∧
    squarefreePart (rootFunction f) T n = ∏ p ∈ n.primeFactors, (polynomialRootCount f p : ℝ) := by
  obtain ⟨he,hp,hv⟩ := fromPrimePowers_binary_support
    (fun p k => if k = 0 then 1 else if k = 1 ∧ p ∉ T then rootFunction f p else 0)
    (by intro p k hk; simp [show k ≠ 0 by omega,show k ≠ 1 by omega]) hn
  have hdata (p : ℕ) (hpn : p ∈ n.primeFactors) : p ∉ T ∧ 0 < polynomialRootCount f p := by
    have hh := (hp p hpn).2
    have hpp := Nat.prime_of_mem_primeFactors hpn
    simp only [show ¬(1 : ℕ) = 0 by omega, if_false, true_and, rootFunction_apply f hpp.ne_zero] at hh
    by_cases hpT : p ∈ T
    · simp [hpT] at hh
    · have hρ : (polynomialRootCount f p : ℝ) ≠ 0 := by simpa [hpT] using hh
      exact ⟨hpT,Nat.pos_of_ne_zero (by exact_mod_cast hρ)⟩
  refine ⟨he,hdata,?_⟩
  unfold squarefreePart
  rw [hv]
  apply prod_congr rfl
  intro p hpn
  simp only [show ¬(1 : ℕ) = 0 by omega, if_false, true_and, if_pos (hdata p hpn).1,
    rootFunction_apply f (Nat.prime_of_mem_primeFactors hpn).ne_zero]

lemma density_le_sieve_weight {v : ℝ} (hv : 0 < v) (hv1 : v < 1) : v ≤ (v⁻¹-1)⁻¹ := by
  have hg : 0 < v⁻¹-1 := sub_pos.mpr ((one_lt_inv₀ hv).mpr hv1)
  apply le_of_mul_le_mul_right (a := v⁻¹-1) (a0 := hg)
  rw [inv_mul_cancel₀ hg.ne', mul_sub, mul_inv_cancel₀ hv.ne', mul_one]
  linarith

lemma squarefreePart_harmonic_le_sieveDenominator (f : ℤ[X]) (T S : Finset ℕ) (D : ℕ)
    (hS : ∀ p ∈ S, p.Prime)
    (hρ : ∀ p ∈ S, 0 < polynomialRootCount f p ∧ polynomialRootCount f p < p)
    (hinclude : ∀ p : ℕ, p.Prime → p ≤ D → p ∉ T → 0 < polynomialRootCount f p → p ∈ S) :
    (∑ n ∈ Ioc 0 D, squarefreePart (rootFunction f) T n/(n : ℝ)) ≤ sieveDenominator f S D := by
  let E := {n ∈ Ioc 0 D | squarefreePart (rootFunction f) T n ≠ 0}
  let F := {r ∈ S.powerset | (∏ p ∈ r, p) ≤ D}
  let W : Finset ℕ → ℝ := fun r => (∏ p ∈ r, ((rootDensity f p)⁻¹-1))⁻¹
  have hmap (n : ℕ) (hn : n ∈ E) : n.primeFactors ∈ F := by
    obtain ⟨hnD,hnz⟩ := mem_filter.mp hn
    obtain ⟨he,hp,hv⟩ := squarefreePart_root_support f T hnz
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (fun p hpn => ?_),by rw [← he]; exact (mem_Ioc.mp hnD).2⟩
    exact hinclude p (Nat.prime_of_mem_primeFactors hpn)
      ((Nat.le_of_dvd (mem_Ioc.mp hnD).1 (Nat.dvd_of_mem_primeFactors hpn)).trans (mem_Ioc.mp hnD).2)
      (hp p hpn).1 (hp p hpn).2
  have hinj : Set.InjOn (fun n : ℕ => n.primeFactors) E := by
    intro n hn m hm hnm
    change n ∈ E at hn
    change m ∈ E at hm
    have hne := (squarefreePart_root_support f T (n := n) (mem_filter.mp hn).2).1
    have hme := (squarefreePart_root_support f T (n := m) (mem_filter.mp hm).2).1
    dsimp only at hnm
    rw [hne,hme,hnm]
  have hval (n : ℕ) (hn : n ∈ E) :
      squarefreePart (rootFunction f) T n/(n : ℝ) ≤ W n.primeFactors := by
    obtain ⟨he,hp,hv⟩ := squarefreePart_root_support f T (mem_filter.mp hn).2
    have hpnS : n.primeFactors ⊆ S := mem_powerset.mp (mem_filter.mp (hmap n hn)).1
    rw [hv]
    have hden : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
      simpa only [Nat.cast_prod] using congrArg (fun k : ℕ => (k : ℝ)) he
    rw [hden, ← prod_div_distrib]
    change (∏ p ∈ n.primeFactors, rootDensity f p) ≤ (∏ p ∈ n.primeFactors, ((rootDensity f p)⁻¹-1))⁻¹
    rw [← prod_inv_distrib]
    apply Finset.prod_le_prod
    · intro p hpn
      exact (rootDensity_pos_lt_one f (hS p (hpnS hpn)) (hρ p (hpnS hpn))).1.le
    · intro p hpn
      obtain ⟨hv,hv1⟩ := rootDensity_pos_lt_one f (hS p (hpnS hpn)) (hρ p (hpnS hpn))
      exact density_le_sieve_weight hv hv1
  have hW (r : Finset ℕ) (hr : r ∈ F) : 0 ≤ W r := by
    apply inv_nonneg.mpr
    apply prod_nonneg
    intro p hp
    have hpS := mem_powerset.mp (mem_filter.mp hr).1 hp
    obtain ⟨hv,hv1⟩ := rootDensity_pos_lt_one f (hS p hpS) (hρ p hpS)
    exact (sub_pos.mpr ((one_lt_inv₀ hv).mpr hv1)).le
  calc
    _ = ∑ n ∈ E, squarefreePart (rootFunction f) T n/(n : ℝ) := by
      symm
      apply sum_subset (filter_subset _ _)
      intro n hn hnE
      have hz : squarefreePart (rootFunction f) T n = 0 := by
        by_contra hz
        exact hnE (mem_filter.mpr ⟨hn,hz⟩)
      rw [hz,zero_div]
    _ ≤ ∑ n ∈ E, W n.primeFactors := sum_le_sum hval
    _ = ∑ r ∈ E.image (fun n => n.primeFactors), W r := (sum_image hinj).symm
    _ ≤ ∑ r ∈ F, W r := sum_le_sum_of_subset_of_nonneg
      (by rintro r hr; obtain ⟨n,hn,rfl⟩ := mem_image.mp hr; exact hmap n hn)
      (fun r hr _ => hW r hr)

/-- The usable sifting primes: primes exceeding the polynomial degree, with a root,
and coprime to the fixed divisibility modulus. -/
noncomputable def siftingPrimes (f : ℤ[X]) (a Y : ℕ) : Finset ℕ :=
  {p ∈ Ioc 0 Y | p.Prime ∧ f.natDegree < p ∧ 0 < polynomialRootCount f p ∧ a.Coprime p}

lemma siftingPrimes_data {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f)
    (a Y : ℕ) {p : ℕ} (hp : p ∈ siftingPrimes f a Y) :
    p.Prime ∧ (0 < polynomialRootCount f p ∧ polynomialRootCount f p < p) ∧ a.Coprime p := by
  obtain ⟨hpY,hpp,hpd,hpr,hpa⟩ := mem_filter.mp hp
  exact ⟨hpp,⟨hpr,(polynomialRootCount_prime_le (hirr.isPrimitive hdeg) hpp).trans_lt hpd⟩,hpa⟩

lemma siftingPrimes_include (f : ℤ[X]) {a D Y : ℕ} (ha : 0 < a) (hDY : D ≤ Y)
    {p : ℕ} (hp : p.Prime) (hpD : p ≤ D) (hpT : p ∉ Iic f.natDegree ∪ a.primeFactors)
    (hρ : 0 < polynomialRootCount f p) : p ∈ siftingPrimes f a Y := by
  have hpd : f.natDegree < p := by
    by_contra h
    exact hpT (mem_union_left _ (mem_Iic.mpr (by omega)))
  have hpa : ¬p ∣ a := fun h => hpT (mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp,h,ha.ne'⟩))
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp.pos,hpD.trans hDY⟩,hp,hpd,hρ,
    (hp.coprime_iff_not_dvd.mpr hpa).symm⟩

lemma sieveDenominator_uniform_lower {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) :
    ∃ c > (0 : ℝ), ∀ᶠ D : ℕ in atTop, ∀ a : ℕ, 0 < a → ∀ Y : ℕ, D ≤ Y →
      (c/(∏ p ∈ a.primeFactors, (1+(polynomialRootCount f p : ℝ)/p)))*log D ≤
        sieveDenominator f (siftingPrimes f a Y) D := by
  obtain ⟨c,hc,hN⟩ := squarefreePart_uniform_harmonic_lower hdeg hirr (Iic f.natDegree)
  refine ⟨c,hc,?_⟩
  filter_upwards [hN] with D hD
  intro a ha Y hDY
  exact (hD a.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)).trans
    (squarefreePart_harmonic_le_sieveDenominator f (Iic f.natDegree ∪ a.primeFactors)
      (siftingPrimes f a Y) D
      (fun p hp => (siftingPrimes_data hdeg hirr a Y hp).1)
      (fun p hp => (siftingPrimes_data hdeg hirr a Y hp).2.1)
      (fun p hp hpD hpT hρ => siftingPrimes_include f ha hDY hp hpD hpT hρ))


lemma polynomial_rough_count_bound {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) :
    ∃ C > (0 : ℝ), ∃ D₀ : ℕ, ∀ D ≥ D₀, ∀ N a : ℕ, 0 < a → ∀ Y : ℕ, D ≤ Y →
      ({n ∈ Ioc 0 N | (a : ℤ) ∣ f.eval ((n : ℕ) : ℤ) ∧
        ∀ p ∈ siftingPrimes f a Y, ¬((p : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)}.card : ℝ) ≤
      C*((N : ℝ)/a*polynomialRootCount f a)*
        (∏ p ∈ a.primeFactors, (1+(polynomialRootCount f p : ℝ)/p))/log D + 2*(a : ℝ)*(D : ℝ)^10 := by
  obtain ⟨c,hc,hbound⟩ := sieveDenominator_uniform_lower hdeg hirr
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.mp hbound
  refine ⟨c⁻¹,inv_pos.mpr hc,max D₀ 2,?_⟩
  intro D hD N a ha Y hDY
  have hD2 : 2 ≤ D := (le_max_right D₀ 2).trans hD
  have hlog : 0 < log (D : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < D))
  let B : ℝ := ∏ p ∈ a.primeFactors, (1+(polynomialRootCount f p : ℝ)/p)
  have hB : 0 < B := by
    apply prod_pos
    intro p hp
    have hh : (0 : ℝ) ≤ (polynomialRootCount f p : ℝ)/p := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith
  have hden := hD₀ D ((le_max_left D₀ 2).trans hD) a ha Y hDY
  have hden0 : 0 < (c/B)*log D := mul_pos (div_pos hc hB) hlog
  have hs := polynomial_sieve_bound f N a D ha (by omega) (siftingPrimes f a Y)
    (fun p hp => (siftingPrimes_data hdeg hirr a Y hp).1)
    (fun p hp => (siftingPrimes_data hdeg hirr a Y hp).2.1)
    (fun p hp => (siftingPrimes_data hdeg hirr a Y hp).2.2)
  change _ ≤ ((N : ℝ)/a*polynomialRootCount f a)/sieveDenominator f (siftingPrimes f a Y) D + _ at hs
  apply hs.trans
  apply add_le_add _ le_rfl
  calc
    _ ≤ ((N : ℝ)/a*polynomialRootCount f a)/((c/B)*log D) :=
      div_le_div_of_nonneg_left (by positivity) hden0 hden
    _ = c⁻¹*((N : ℝ)/a*polynomialRootCount f a)*B/log D := by
      field_simp


end Sieve

namespace Sieve
open Finset Real Filter Polynomial

open GeneralDivisors

lemma sum_Ioc_zero_eq_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, f n = ∑ i ∈ range N, f (i+1) := by
  rw [show Ioc 0 N = Ico 1 (N+1) by ext i; simp only [mem_Ioc,mem_Ico]; omega,
    sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel,add_comm 1]

lemma harmonic_weight_bound (u : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ N : ℕ, (∑ i ∈ range N, u i) ≤ B*N) (N : ℕ) :
    (∑ i ∈ range N, u i/(i+1)) ≤ B*(1+(harmonic N : ℝ)) := by
  have hb (i : ℕ) : (∑ j ∈ range i, u j)/(i : ℝ) ≤ B := by
    by_cases hi : i = 0
    · subst i
      simpa using hB
    · exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hi))).mpr (hA i)
  rw [MeanTransfer.weighted_partial_summation]
  calc
    _ ≤ B + ∑ i ∈ range N, B/((i : ℝ)+1) := add_le_add (hb N)
      (sum_le_sum (fun i hi => div_le_div_of_nonneg_right (hb i) (by positivity)))
    _ = B*(1+(harmonic N : ℝ)) := by
      simp only [div_eq_mul_inv, ← mul_sum]
      have he := MeanTransfer.harmonic_range N
      simp only [one_div] at he
      rw [he]
      ring

lemma prime_log_reciprocal_bound :
    ∃ B > (0 : ℝ), ∀ N : ℕ, 2 ≤ N → (∑ p ∈ Ioc 0 N with p.Prime, log p/(p : ℝ)) ≤ B*log N := by
  let u : ℕ → ℝ := fun i => if (i+1).Prime then log (i+1) else 0
  have heq (N : ℕ) : (∑ i ∈ range N, u i) = Chebyshev.theta N := by
    rw [Chebyshev.theta, Nat.floor_natCast, sum_filter, sum_Ioc_zero_eq_range]
    simp only [u,Nat.cast_add,Nat.cast_one]
  have hA (N : ℕ) : (∑ i ∈ range N, u i) ≤ log 4*N := by
    rw [heq]
    exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N)
  have hlog4 : 0 < log (4 : ℝ) := Real.log_pos (by norm_num)
  have hlog2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨log 4*(1+2/log 2),mul_pos hlog4 (by positivity),?_⟩
  intro N hN
  have hlogN : log (2 : ℝ) ≤ log (N : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hh := harmonic_weight_bound u hlog4.le hA N
  have hl := harmonic_le_one_add_log N
  have hsmall : (2 : ℝ) ≤ (2/log 2)*log N := by
    have ht := mul_le_mul_of_nonneg_left hlogN (by positivity : 0 ≤ 2/log (2 : ℝ))
    simpa only [div_mul_cancel₀ _ hlog2.ne'] using ht
  have hm := mul_le_mul_of_nonneg_left (show 1+(harmonic N : ℝ) ≤ (1+2/log 2)*log N by nlinarith)
    hlog4.le
  have hsum : (∑ p ∈ Ioc 0 N with p.Prime, log p/(p : ℝ)) = ∑ i ∈ range N, u i/(i+1) := by
    rw [sum_filter,sum_Ioc_zero_eq_range]
    apply sum_congr rfl
    intro i hi
    simp only [u,Nat.cast_add,Nat.cast_one,ite_div,zero_div]
  rw [hsum]
  nlinarith

/-- A first-moment bound for a finite positive Euler product. -/
lemma powerset_weighted_moment_bound {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (w ℓ : ι → ℝ) (hw : ∀ p ∈ S, 0 ≤ w p) (hℓ : ∀ p ∈ S, 0 ≤ ℓ p) :
    (∑ U ∈ S.powerset, (∏ p ∈ U, w p)*(∑ p ∈ U, ℓ p)) ≤
      (∏ p ∈ S, (1+w p))*(∑ p ∈ S, w p*ℓ p) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have hwp := hw p (mem_insert_self _ _)
    have hℓp := hℓ p (mem_insert_self _ _)
    have hws : ∀ q ∈ S, 0 ≤ w q := fun q hq => hw q (mem_insert_of_mem hq)
    have hℓs : ∀ q ∈ S, 0 ≤ ℓ q := fun q hq => hℓ q (mem_insert_of_mem hq)
    have hM := ih hws hℓs
    let E := ∏ q ∈ S, (1+w q)
    let M := ∑ U ∈ S.powerset, (∏ q ∈ U, w q)*(∑ q ∈ U, ℓ q)
    let L := ∑ q ∈ S, w q*ℓ q
    have hE : 0 ≤ E := prod_nonneg (fun q hq => by linarith [hws q hq])
    have hex : (∑ U ∈ S.powerset, (∏ q ∈ insert p U, w q)*(∑ q ∈ insert p U, ℓ q)) =
        w p*ℓ p*E+w p*M := by
      have hterm (U : Finset ι) (hU : U ∈ S.powerset) :
          (∏ q ∈ insert p U, w q)*(∑ q ∈ insert p U, ℓ q) =
          w p*ℓ p*(∏ q ∈ U, w q) + w p*((∏ q ∈ U, w q)*(∑ q ∈ U, ℓ q)) := by
        have hpU : p ∉ U := fun h => hp (mem_powerset.mp hU h)
        rw [prod_insert hpU,sum_insert hpU]
        ring
      rw [sum_congr rfl hterm,sum_add_distrib,← mul_sum,← mul_sum,← prod_one_add]
    rw [sum_powerset_insert hp,prod_insert hp,sum_insert hp,hex]
    change M+(w p*ℓ p*E+w p*M) ≤ (1+w p)*E*(w p*ℓ p+L)
    have hh := mul_le_mul_of_nonneg_left hM (by linarith : 0 ≤ 1+w p)
    have hn := mul_nonneg (mul_nonneg (mul_nonneg hwp hwp) hℓp) hE
    dsimp [M,L,E] at *
    nlinarith

lemma root_harmonic_upper {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) :
    ∃ B > (0 : ℝ), ∀ N : ℕ, 2 ≤ N →
      (∑ n ∈ Ioc 0 N, (polynomialRootCount f n : ℝ)/n) ≤ B*log N := by
  obtain ⟨a,ha,hm⟩ := polynomialRootCount_mean_positive f hdeg hirr
  obtain ⟨B,hB⟩ := (MeanTransfer.logarithmic_mean_Ioc_of_mean hm).bddAbove_range
  refine ⟨max B 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro N hN
  have hlog : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  apply (div_le_iff₀ hlog).mp
  exact (hB (Set.mem_range_self N)).trans (le_max_left _ _)


lemma squarefree_root_product_upper {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) :
    ∃ C > (0 : ℝ), ∀ M : ℕ, 2 ≤ M →
      (∏ p ∈ Ioc 0 M with p.Prime, (1+(polynomialRootCount f p : ℝ)/p)) ≤ C*log M := by
  obtain ⟨B,hB,hMertens⟩ := prime_log_reciprocal_bound
  obtain ⟨H,hH,hHbound⟩ := root_harmonic_upper hdeg hirr
  obtain ⟨K,hK⟩ := exists_nat_gt (2*B*(f.natDegree : ℝ)+1)
  have hd : (0 : ℝ) < f.natDegree := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hdeg)
  have hKr : (0 : ℝ) < K := by nlinarith [mul_pos hB hd]
  have hKn : 0 < K := Nat.cast_pos.mp hKr
  refine ⟨2*H*K,by positivity,?_⟩
  intro M hM
  let S : Finset ℕ := {p ∈ Ioc 0 M | p.Prime}
  let w : ℕ → ℝ := rootDensity f
  let E : ℝ := ∏ p ∈ S, (1+w p)
  let F : Finset (Finset ℕ) := {U ∈ S.powerset | (∏ p ∈ U, p) ≤ M^K}
  let T : Finset (Finset ℕ) := {U ∈ S.powerset | ¬(∏ p ∈ U, p) ≤ M^K}
  let W : Finset ℕ → ℝ := fun U => ∏ p ∈ U, w p
  let small : ℝ := ∑ U ∈ F, W U
  let big : ℝ := ∑ U ∈ T, W U
  let moment : ℝ := ∑ U ∈ S.powerset, W U*(∑ p ∈ U, log p)
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime := (mem_filter.mp hp).2
  have hw (p : ℕ) : 0 ≤ w p := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hW (U : Finset ℕ) : 0 ≤ W U := prod_nonneg (fun p hp => hw p)
  have hℓ (p : ℕ) (hp : p ∈ S) : 0 ≤ log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (hS p hp).one_le)
  have hE : 0 < E := prod_pos (fun p hp => by linarith [hw p])
  have hlog : 0 < log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hsplit : small+big = E := by
    dsimp only [small,big,F,T]
    rw [sum_filter_add_sum_filter_not]
    exact (prod_one_add S).symm
  have hsmall0 : 0 ≤ small := sum_nonneg (fun U hU => hW U)
  have hbig0 : 0 ≤ big := sum_nonneg (fun U hU => hW U)
  have hL : (∑ p ∈ S, w p*log p) ≤ (f.natDegree : ℝ)*B*log M := by
    calc
      _ ≤ (f.natDegree : ℝ)*(∑ p ∈ S, log p/(p : ℝ)) := by
        rw [mul_sum]
        apply sum_le_sum
        intro p hp
        have hρ : (polynomialRootCount f p : ℝ) ≤ f.natDegree :=
          Nat.cast_le.mpr (polynomialRootCount_prime_le (hirr.isPrimitive hdeg) (hS p hp))
        have hh := mul_le_mul_of_nonneg_right hρ (div_nonneg (hℓ p hp) (Nat.cast_nonneg p))
        dsimp only [w,rootDensity]
        convert hh using 1 <;> ring
      _ ≤ (f.natDegree : ℝ)*(B*log M) := mul_le_mul_of_nonneg_left (hMertens M hM) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hmom : moment ≤ E*(f.natDegree : ℝ)*B*log M := by
    have hh := powerset_weighted_moment_bound S w (fun p => log p) (fun p hp => hw p) hℓ
    exact hh.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hL hE.le)
  have hlogU (U : Finset ℕ) (hU : U ∈ T) : (K : ℝ)*log M ≤ ∑ p ∈ U, log p := by
    have hUS := mem_powerset.mp (mem_filter.mp hU).1
    have hsize : M^K ≤ ∏ p ∈ U, p := (Nat.lt_of_not_ge (mem_filter.mp hU).2).le
    have hMp : (0 : ℝ) < (M : ℝ)^K := pow_pos (Nat.cast_pos.mpr (by omega)) _
    have hh := Real.log_le_log hMp (show (M : ℝ)^K ≤ ((∏ p ∈ U, p : ℕ) : ℝ) by exact_mod_cast hsize)
    rw [Real.log_pow, Nat.cast_prod, Real.log_prod (fun p hp => Nat.cast_ne_zero.mpr (hS p (hUS hp)).ne_zero)] at hh
    exact hh
  have hbM : (K : ℝ)*log M*big ≤ moment := by
    calc
      _ = ∑ U ∈ T, W U*((K : ℝ)*log M) := by dsimp [big]; rw [mul_sum]; apply sum_congr rfl; intro U hU; ring
      _ ≤ ∑ U ∈ T, W U*(∑ p ∈ U, log p) := sum_le_sum (fun U hU =>
        mul_le_mul_of_nonneg_left (hlogU U hU) (hW U))
      _ ≤ moment := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun U hU _ =>
        mul_nonneg (hW U) (sum_nonneg (fun p hp => hℓ p (mem_powerset.mp hU hp))))
  have hhalf : E ≤ 2*small := by
    have hkbig : (K : ℝ)*big ≤ E*(f.natDegree : ℝ)*B := by
      apply le_of_mul_le_mul_right (a := log (M : ℝ)) (a0 := hlog)
      convert hbM.trans hmom using 1 <;> ring
    have hKB : 2*(f.natDegree : ℝ)*B ≤ K := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hKB hE.le
    nlinarith
  have hsmall : small ≤ ∑ n ∈ Ioc 0 (M^K), (polynomialRootCount f n : ℝ)/n := by
    let J := F.image (fun U => ∏ p ∈ U, p)
    have hj : J ⊆ Ioc 0 (M^K) := by
      rintro n hn
      obtain ⟨U,hU,rfl⟩ := mem_image.mp hn
      have hUS := mem_powerset.mp (mem_filter.mp hU).1
      exact mem_Ioc.mpr ⟨prod_pos (fun p hp => (hS p (hUS hp)).pos),(mem_filter.mp hU).2⟩
    have hinj : Set.InjOn (fun U : Finset ℕ => ∏ p ∈ U, p) F := by
      intro U hU V hV hUV
      change U ∈ F at hU
      change V ∈ F at hV
      have hUS := mem_powerset.mp (mem_filter.mp hU).1
      have hVS := mem_powerset.mp (mem_filter.mp hV).1
      have hh := congrArg Nat.primeFactors hUV
      dsimp only at hh
      rw [Nat.primeFactors_prod (fun p hp => hS p (hUS hp)),
        Nat.primeFactors_prod (fun p hp => hS p (hVS hp))] at hh
      exact hh
    have heq : small = ∑ n ∈ J, (polynomialRootCount f n : ℝ)/n := by
      rw [sum_image hinj]
      apply sum_congr rfl
      intro U hU
      have hUS := mem_powerset.mp (mem_filter.mp hU).1
      exact (rootDensity_primeProduct f U (fun p hp => hS p (hUS hp))).symm
    rw [heq]
    exact sum_le_sum_of_subset_of_nonneg hj (fun n hn hnJ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hMK : 2 ≤ M^K := hM.trans (by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < M) (show 1 ≤ K by omega))
  have hupper := hHbound (M^K) hMK
  simp only [Nat.cast_pow,Real.log_pow] at hupper
  change E ≤ 2*H*K*log M
  nlinarith


end Sieve

open Finset Real Filter Polynomial
open scoped Topology ArithmeticFunction.sigma

namespace Sieve
open GeneralDivisors EulerComparison

noncomputable def rootCost (f : ℤ[X]) : ArithmeticFunction ℝ :=
  fromPrimePowers (fun p k => if k = 0 then 1 else 1+rootDensity f p)

lemma rootCost_multiplicative (f : ℤ[X]) : (rootCost f).IsMultiplicative :=
  fromPrimePowers_multiplicative _

lemma rootCost_nonneg (f : ℤ[X]) (n : ℕ) : 0 ≤ rootCost f n := by
  apply fromPrimePowers_nonneg
  intro p k
  have hρ : 0 ≤ rootDensity f p := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  split_ifs <;> positivity

lemma rootCost_apply (f : ℤ[X]) {n : ℕ} (hn : n ≠ 0) :
    rootCost f n = ∏ p ∈ n.primeFactors, (1+(polynomialRootCount f p : ℝ)/p) := by
  rw [rootCost,fromPrimePowers_apply _ hn,Finsupp.prod,Nat.support_factorization]
  apply prod_congr rfl
  intro p hp
  have hk := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
  rw [if_neg hk.ne']
  rfl

lemma rootCost_prime_pow (f : ℤ[X]) {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) :
    rootCost f (p^k) = 1+rootDensity f p := by
  rw [rootCost,fromPrimePowers_prime_pow _ hp (by simp) k,if_neg hk]

noncomputable def divisorRootWeight (f : ℤ[X]) : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul (σ 0 : ArithmeticFunction ℝ) ((rootFunction f).pmul (rootCost f))

lemma divisorRootWeight_multiplicative (f : ℤ[X]) : (divisorRootWeight f).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_sigma.natCast.pmul
    ((rootFunction_multiplicative f).pmul (rootCost_multiplicative f))

lemma divisorRootWeight_nonneg (f : ℤ[X]) (n : ℕ) : 0 ≤ divisorRootWeight f n := by
  exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (rootFunction_nonneg f n) (rootCost_nonneg f n))

lemma divisorRootWeight_apply (f : ℤ[X]) {n : ℕ} (hn : n ≠ 0) :
    divisorRootWeight f n = (σ 0 n : ℝ)*(polynomialRootCount f n : ℝ)*
      ∏ p ∈ n.primeFactors, (1+(polynomialRootCount f p : ℝ)/p) := by
  simp only [divisorRootWeight,ArithmeticFunction.pmul_apply,ArithmeticFunction.natCoe_apply,
    rootFunction_apply f hn,rootCost_apply f hn,mul_assoc]

lemma divisorRootWeight_prime_pow (f : ℤ[X]) {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) :
    divisorRootWeight f (p^k) = (k+1 : ℕ)*(polynomialRootCount f (p^k) : ℝ)*(1+rootDensity f p) := by
  simp only [divisorRootWeight,ArithmeticFunction.pmul_apply,ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.sigma_zero_apply_prime_pow hp,rootFunction_apply f (pow_ne_zero _ hp.ne_zero),
    rootCost_prime_pow f hp hk,mul_assoc]

lemma root_prime_powers_uniform {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ p : ℕ, p.Prime → ∀ k : ℕ, (polynomialRootCount f (p^k) : ℝ) ≤ R := by
  obtain ⟨B,hB,hbound⟩ := polynomialRootCount_global_bound hdeg hirr
  have hprod : (0 : ℝ) ≤ (B : ℝ)*f.natDegree := by positivity
  refine ⟨B*f.natDegree+1,by linarith,?_⟩
  intro p hp k
  by_cases hk : k = 0
  · subst k
    simp only [pow_zero,polynomialRootCount_one,Nat.cast_one]
    linarith
  · have hh := hbound (p^k) (pow_ne_zero _ hp.ne_zero)
    rw [Nat.primeFactors_prime_pow hk hp,card_singleton,pow_one] at hh
    have hh' : (polynomialRootCount f (p^k) : ℝ) ≤ (B : ℝ)*f.natDegree := by exact_mod_cast hh
    linarith

lemma divisorRootWeight_prime_pow_bound (f : ℤ[X]) {R : ℝ} (hR : 1 ≤ R)
    (hbound : ∀ p : ℕ, p.Prime → ∀ k : ℕ, (polynomialRootCount f (p^k) : ℝ) ≤ R)
    {p : ℕ} (hp : p.Prime) (k : ℕ) : divisorRootWeight f (p^k) ≤ 2*R*((k : ℝ)+1) := by
  by_cases hk : k = 0
  · subst k
    rw [pow_zero,(divisorRootWeight_multiplicative f).1]
    norm_num
    linarith
  · rw [divisorRootWeight_prime_pow f hp hk,Nat.cast_add,Nat.cast_one]
    have hρ : rootDensity f p ≤ 1 := (div_le_one (Nat.cast_pos.mpr hp.pos)).mpr
      (Nat.cast_le.mpr (polynomialRootCount_le_modulus f hp.pos))
    have hρ0 : 0 ≤ rootDensity f p := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hm := mul_le_mul (hbound p hp k) (show 1+rootDensity f p ≤ 2 by linarith)
      (by linarith : 0 ≤ 1+rootDensity f p) (by linarith : 0 ≤ R)
    have hh := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (k : ℝ)+1)
    nlinarith

lemma summable_linear_geometric {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (b : ℝ) :
    Summable (fun k : ℕ => ((k : ℝ)+b)*q^k) := by
  have hnorm : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg hq0] using hq1
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have h0 := (summable_geometric_of_lt_one hq0 hq1).mul_left b
  simpa only [pow_one,add_mul] using h1.add h0

noncomputable def linearGeomConstant : ℝ := ∑' k : ℕ, ((k : ℝ)+3)*(3/4 : ℝ)^k

lemma linearGeomConstant_pos : 0 < linearGeomConstant := by
  have hs := summable_linear_geometric (q := (3/4 : ℝ)) (by norm_num) (by norm_num) 3
  have hh := hs.le_tsum 0 (fun k hk => by positivity)
  norm_num at hh
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) hh

lemma bounded_linear_geometric_summable {a : ℕ → ℝ} {M q : ℝ}
    (ha : ∀ k, 0 ≤ a k) (hbound : ∀ k, a k ≤ M*((k : ℝ)+1))
    (hq0 : 0 ≤ q) (hq1 : q < 1) : Summable (fun k : ℕ => a k*q^k) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (ha k) (pow_nonneg hq0 k))
    (fun k => ?_) ((summable_linear_geometric hq0 hq1 1).mul_left M)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound k) (pow_nonneg hq0 k)

lemma bounded_linear_geometric_tsum_bound {a : ℕ → ℝ} {M q : ℝ}
    (ha : ∀ k, 0 ≤ a k) (ha0 : a 0 = 1) (hM : 0 ≤ M)
    (hbound : ∀ k, a k ≤ M*((k : ℝ)+1)) (hq0 : 0 ≤ q) (hq : q ≤ 3/4) :
    (∑' k : ℕ, a k*q^k) ≤ 1+a 1*q+M*linearGeomConstant*q^2 := by
  have hq1 : q < 1 := by linarith
  have hs := bounded_linear_geometric_summable ha hbound hq0 hq1
  have ht : Summable (fun k : ℕ => a (k+2)*q^(k+2)) := (summable_nat_add_iff 2).mpr hs
  have hsref := (summable_linear_geometric (q := (3/4 : ℝ)) (by norm_num) (by norm_num) 3).mul_left (M*q^2)
  have htail : (∑' k : ℕ, a (k+2)*q^(k+2)) ≤ M*linearGeomConstant*q^2 := by
    calc
      _ ≤ ∑' k : ℕ, (M*q^2)*(((k : ℝ)+3)*(3/4 : ℝ)^k) := by
        apply ht.tsum_le_tsum _ hsref
        intro k
        have hbk := hbound (k+2)
        have hpw := pow_le_pow_left₀ hq0 hq k
        have hstep := mul_le_mul_of_nonneg_right hbk (pow_nonneg hq0 (k+2))
        have hstep2 := mul_le_mul_of_nonneg_left hpw (by positivity : 0 ≤ M*((k : ℝ)+3)*q^2)
        simp only [Nat.cast_add,Nat.cast_ofNat,pow_add,pow_two] at hstep hstep2 ⊢
        nlinarith
      _ = _ := by rw [tsum_mul_left]; dsimp [linearGeomConstant]; ring
  have he : (∑' k : ℕ, a k*q^k) = 1+a 1*q+∑' k : ℕ, a (k+2)*q^(k+2) := by
    rw [hs.tsum_eq_zero_add,((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
    simp only [ha0,pow_zero,mul_one,Nat.zero_add,pow_one,Nat.add_assoc,add_assoc]
  rw [he]
  exact add_le_add le_rfl htail

lemma rpow_shift_sq {p : ℝ} (hp : 0 ≤ p) (α : ℝ) :
    (p^(α-1))^2 = p^(2*α-2) := by
  rw [← Real.rpow_mul_natCast hp]
  congr 1
  norm_num
  ring

lemma prime_rpow_shift_bounds {p : ℕ} (hp : p.Prime) {α : ℝ} (hα : α ≤ 1/4) :
    0 ≤ (p : ℝ)^(α-1) ∧ (p : ℝ)^(α-1) ≤ 3/4 ∧ ((p : ℝ)^(α-1))^2 ≤ (p : ℝ)^(-3/2 : ℝ) := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hp1 : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr hp.one_le
  have hp2 : (2 : ℝ) ≤ p := Nat.ofNat_le_cast.mpr hp.two_le
  have hq0 : 0 ≤ (p : ℝ)^(α-1) := Real.rpow_nonneg hp0.le _
  have hsq : ((p : ℝ)^(α-1))^2 ≤ (p : ℝ)^(-3/2 : ℝ) := by
    rw [rpow_shift_sq hp0.le]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hsq' : ((p : ℝ)^(α-1))^2 ≤ 1/2 := by
    calc
      _ ≤ (p : ℝ)^(-3/2 : ℝ) := hsq
      _ ≤ (p : ℝ)^(-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
      _ = (p : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1/2 := (inv_le_comm₀ hp0 (by norm_num : (0 : ℝ) < 1/2)).mpr (by simpa using hp2)
  exact ⟨hq0,by nlinarith,hsq⟩

lemma exp_sub_one_le_mul_exp {x c : ℝ} (hx : 0 ≤ x) (hxc : x ≤ c) :
    exp x-1 ≤ x*exp c := by
  have hh := mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg x) (Real.exp_pos x).le
  rw [Real.exp_neg,inv_mul_cancel₀ (Real.exp_pos x).ne'] at hh
  have hm := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hxc) hx
  nlinarith

lemma rpow_sub_one_bound {p : ℝ} (hp : 1 ≤ p) {α c : ℝ} (hα : 0 ≤ α)
    (hc : α*log p ≤ c) : p^α-1 ≤ α*log p*exp c := by
  rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hp)]
  have he := exp_sub_one_le_mul_exp (mul_nonneg hα (Real.log_nonneg hp)) hc
  simpa only [mul_comm α (log p)] using he


noncomputable def localWeightSeries (f : ℤ[X]) (p : ℕ) (α : ℝ) : ℝ :=
  ∑' k : ℕ, divisorRootWeight f (p^k)*((p : ℝ)^(α-1))^k

lemma localWeightSeries_summable (f : ℤ[X]) {R : ℝ} (hR : 1 ≤ R)
    (hbound : ∀ p : ℕ, p.Prime → ∀ k : ℕ, (polynomialRootCount f (p^k) : ℝ) ≤ R)
    {p : ℕ} (hp : p.Prime) {α : ℝ} (hα : α ≤ 1/4) :
    Summable (fun k : ℕ => divisorRootWeight f (p^k)*((p : ℝ)^(α-1))^k) := by
  obtain ⟨hq0,hq,hq2⟩ := prime_rpow_shift_bounds hp hα
  exact bounded_linear_geometric_summable (fun k => divisorRootWeight_nonneg f _)
    (divisorRootWeight_prime_pow_bound f hR hbound hp) hq0 (by linarith)

set_option maxHeartbeats 1000000 in
lemma localWeightSeries_bound {f : ℤ[X]} (hf : f.IsPrimitive) {R : ℝ} (hR : 1 ≤ R)
    (hbound : ∀ p : ℕ, p.Prime → ∀ k : ℕ, (polynomialRootCount f (p^k) : ℝ) ≤ R)
    {p : ℕ} (hp : p.Prime) {α c : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1/4) (hc : α*log p ≤ c) :
    localWeightSeries f p α ≤ (1+rootDensity f p)^2 *
      exp (2*(f.natDegree : ℝ)*α*exp c*(log p/p) +
        (2*(f.natDegree : ℝ)^2+2*R*linearGeomConstant)*(p : ℝ)^(-3/2 : ℝ)) := by
  let d : ℝ := f.natDegree
  let ρ : ℝ := polynomialRootCount f p
  let q : ℝ := (p : ℝ)^(α-1)
  let e : ℝ := 2*d*α*exp c*(log p/p)+(2*d^2+2*R*linearGeomConstant)*(p : ℝ)^(-3/2 : ℝ)
  let b : ℝ := (1+ρ/p)^2
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hp1 : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr hp.one_le
  have hρ0 : 0 ≤ ρ := Nat.cast_nonneg _
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hρd : ρ ≤ d := Nat.cast_le.mpr (polynomialRootCount_prime_le hf hp)
  have hR0 : 0 ≤ R := by linarith
  have hL0 : 0 ≤ linearGeomConstant := linearGeomConstant_pos.le
  have hlog : 0 ≤ log (p : ℝ) := Real.log_nonneg hp1
  obtain ⟨hq0,hq,hq2⟩ := prime_rpow_shift_bounds hp hα
  have hs := bounded_linear_geometric_tsum_bound
    (fun k => divisorRootWeight_nonneg f (p^k))
    (by simp only [pow_zero,(divisorRootWeight_multiplicative f).1])
    (show 0 ≤ 2*R by positivity) (divisorRootWeight_prime_pow_bound f hR hbound hp) hq0 hq
  have hpp : divisorRootWeight f p = 2*ρ*(1+ρ/p) := by
    simpa only [pow_one,Nat.cast_add,Nat.cast_one,show (1 : ℝ)+1 = 2 by norm_num] using
      divisorRootWeight_prime_pow f hp (k := 1) (by omega)
  simp only [pow_one,hpp] at hs
  have hqeq : q = (p : ℝ)^α/p := by
    dsimp only [q]
    rw [Real.rpow_sub hp0,Real.rpow_one]
  have hpow2 : (p : ℝ)^(α-2) = (p : ℝ)^α/(p : ℝ)^2 := by
    rw [Real.rpow_sub hp0,Real.rpow_two]
  have hpe : 1 ≤ (p : ℝ)^α := Real.one_le_rpow hp1 hα0
  have hfirst : 2*ρ/p*((p : ℝ)^α-1) ≤ 2*d*α*exp c*(log p/p) := by
    calc
      _ ≤ (2*d/p)*((p : ℝ)^α-1) := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by linarith) hp0.le) (by linarith)
      _ ≤ (2*d/p)*(α*log p*exp c) := mul_le_mul_of_nonneg_left
        (rpow_sub_one_bound hp1 hα0 hc) (by positivity)
      _ = _ := by ring
  have hsecond : 2*ρ^2*(p : ℝ)^(α-2) ≤ 2*d^2*(p : ℝ)^(-3/2 : ℝ) := by
    have hrpow : (p : ℝ)^(α-2) ≤ (p : ℝ)^(-3/2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    exact mul_le_mul (by nlinarith) hrpow (Real.rpow_nonneg hp0.le _) (by positivity)
  have htail : 2*R*linearGeomConstant*q^2 ≤ 2*R*linearGeomConstant*(p : ℝ)^(-3/2 : ℝ) :=
    mul_le_mul_of_nonneg_left hq2 (by positivity)
  have halg : 1+2*ρ*(1+ρ/p)*q + 2*R*linearGeomConstant*q^2 =
      b+2*ρ/p*((p : ℝ)^α-1)+2*ρ^2*(p : ℝ)^(α-2)-(ρ/p)^2+2*R*linearGeomConstant*q^2 := by
    rw [hqeq,hpow2]
    dsimp [b]
    ring
  have hlocal : localWeightSeries f p α ≤ b+e := by
    change localWeightSeries f p α ≤ 1+2*ρ*(1+ρ/p)*q+2*R*linearGeomConstant*q^2 at hs
    rw [halg] at hs
    dsimp [e]
    nlinarith [sq_nonneg (ρ/p)]
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have hb1 : 1 ≤ b := by
    have ht : 0 ≤ ρ/p := div_nonneg hρ0 hp0.le
    dsimp [b]
    nlinarith [sq_nonneg (ρ/p)]
  have he := Real.add_one_le_exp e
  have hm := mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ b)
  change localWeightSeries f p α ≤ b*exp e
  have hbe := mul_nonneg (by linarith : 0 ≤ b-1) he0
  nlinarith


lemma localWeightProduct_bound {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) (c : ℝ) :
    ∃ A > (0 : ℝ), ∀ M : ℕ, 2 ≤ M → ∀ α : ℝ, 0 ≤ α → α ≤ 1/4 → α*log M ≤ c →
      (∏ p ∈ Ioc 0 M with p.Prime, localWeightSeries f p α) ≤ A*(log M)^2 := by
  obtain ⟨R,hR,hRbound⟩ := root_prime_powers_uniform hdeg hirr
  obtain ⟨B,hB,hMertens⟩ := prime_log_reciprocal_bound
  obtain ⟨H,hH,hHbound⟩ := squarefree_root_product_upper hdeg hirr
  let P : ℝ := ∑' n : ℕ, (n : ℝ)^(-3/2 : ℝ)
  have hPs : Summable (fun n : ℕ => (n : ℝ)^(-3/2 : ℝ)) := Real.summable_nat_rpow.mpr (by norm_num)
  have hP0 : 0 ≤ P := tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  let d : ℝ := f.natDegree
  let K : ℝ := 2*d*c*exp c*B+(2*d^2+2*R*linearGeomConstant)*P
  refine ⟨H^2*exp K,mul_pos (sq_pos_of_pos hH) (Real.exp_pos K),?_⟩
  intro M hM α hα0 hα hc
  let S : Finset ℕ := {p ∈ Ioc 0 M | p.Prime}
  let e : ℕ → ℝ := fun p => 2*d*α*exp c*(log p/p)+(2*d^2+2*R*linearGeomConstant)*(p : ℝ)^(-3/2 : ℝ)
  have hS (p : ℕ) (hp : p ∈ S) : 0 < p ∧ p ≤ M ∧ p.Prime := by
    obtain ⟨hpI,hpp⟩ := mem_filter.mp hp
    exact ⟨(mem_Ioc.mp hpI).1,(mem_Ioc.mp hpI).2,hpp⟩
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hR0 : 0 ≤ R := by linarith
  have hL0 : 0 ≤ linearGeomConstant := linearGeomConstant_pos.le
  have hpc (p : ℕ) (hp : p ∈ S) : α*log p ≤ c := by
    have hlog := Real.log_le_log (Nat.cast_pos.mpr (hS p hp).1) (Nat.cast_le.mpr (hS p hp).2.1)
    exact (mul_le_mul_of_nonneg_left hlog hα0).trans hc
  have hsum : ∑ p ∈ S, e p ≤ K := by
    dsimp only [e,K]
    rw [sum_add_distrib,← mul_sum,← mul_sum]
    apply add_le_add
    · calc
        _ ≤ (2*d*α*exp c)*(B*log M) :=
          mul_le_mul_of_nonneg_left (hMertens M hM) (by positivity)
        _ = (2*d*exp c*B)*(α*log M) := by ring
        _ ≤ (2*d*exp c*B)*c := mul_le_mul_of_nonneg_left hc (by positivity)
        _ = _ := by ring
    · exact mul_le_mul_of_nonneg_left
        (hPs.sum_le_tsum _ (fun n hn => Real.rpow_nonneg (Nat.cast_nonneg n) _)) (by positivity)
  have hprod : (∏ p ∈ S, localWeightSeries f p α) ≤
      (∏ p ∈ S, (1+rootDensity f p))^2 * exp (∑ p ∈ S, e p) := by
    calc
      _ ≤ ∏ p ∈ S, ((1+rootDensity f p)^2*exp (e p)) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact tsum_nonneg (fun k => mul_nonneg (divisorRootWeight_nonneg f _)
            (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) k))
        · intro p hp
          exact localWeightSeries_bound (hirr.isPrimitive hdeg) hR hRbound (hS p hp).2.2 hα0 hα (hpc p hp)
      _ = _ := by rw [prod_mul_distrib,prod_pow,← Real.exp_sum]
  have hbase := hHbound M hM
  have hbase0 : 0 ≤ ∏ p ∈ S, (1+rootDensity f p) := by
    apply prod_nonneg
    intro p hp
    have hh : 0 ≤ rootDensity f p := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith
  have hbase' : (∏ p ∈ S, (1+rootDensity f p))^2 ≤ (H*log M)^2 := by
    apply pow_le_pow_left₀ hbase0
    exact hbase
  calc
    _ ≤ (∏ p ∈ S, (1+rootDensity f p))^2 * exp (∑ p ∈ S, e p) := hprod
    _ ≤ (H*log M)^2 * exp K := mul_le_mul hbase' (Real.exp_le_exp.mpr hsum)
      (Real.exp_pos _).le (sq_nonneg _)
    _ = (H^2*exp K)*(log M)^2 := by ring

lemma natPow_rpow_comm (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (s : ℝ) :
    (x^k)^s = (x^s)^k := by
  rw [← Real.rpow_natCast_mul hx, mul_comm (k : ℝ), Real.rpow_mul_natCast hx]

lemma smooth_weight_hasSum {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f)
    {α : ℝ} (hα : α ≤ 1/4) (M : ℕ) :
    HasSum (fun n : (M+1).smoothNumbers => divisorRootWeight f n * (n : ℝ)^(α-1))
      (∏ p ∈ Ioc 0 M with p.Prime, localWeightSeries f p α) := by
  let v : ℕ → ℝ := fun n => divisorRootWeight f n*(n : ℝ)^(α-1)
  have hv0 (n : ℕ) : 0 ≤ v n := mul_nonneg (divisorRootWeight_nonneg f n)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hv1 : v 1 = 1 := by simp [v,(divisorRootWeight_multiplicative f).1]
  have hvmul {m n : ℕ} (hmn : m.Coprime n) : v (m*n) = v m*v n := by
    simp only [v,(divisorRootWeight_multiplicative f).map_mul_of_coprime hmn,Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  have hpp (p k : ℕ) : v (p^k) = divisorRootWeight f (p^k)*((p : ℝ)^(α-1))^k := by
    dsimp only [v]
    rw [Nat.cast_pow,natPow_rpow_comm _ (Nat.cast_nonneg p)]
  obtain ⟨R,hR,hRbound⟩ := root_prime_powers_uniform hdeg hirr
  have hlocal {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => ‖v (p^k)‖) := by
    simpa only [hpp] using (localWeightSeries_summable f hR hRbound hp hα).norm
  have hh := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hv1
    (fun {_ _} => hvmul) hlocal (M+1)).2
  have heq : (M+1).primesBelow = {p ∈ Ioc 0 M | p.Prime} := by
    ext p
    simp only [Nat.mem_primesBelow,mem_filter,mem_Ioc]
    constructor
    · rintro ⟨hp,hpr⟩
      exact ⟨⟨hpr.pos,by omega⟩,hpr⟩
    · rintro ⟨⟨_,hp⟩,hpr⟩
      exact ⟨by omega,hpr⟩
  simpa only [heq,hpp,localWeightSeries] using hh

lemma smooth_weight_bound {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) (c : ℝ) :
    ∃ A > (0 : ℝ), ∀ M : ℕ, 2 ≤ M → ∀ α : ℝ, 0 ≤ α → α ≤ 1/4 → α*log M ≤ c →
      (∑' n : (M+1).smoothNumbers, divisorRootWeight f n*(n : ℝ)^(α-1)) ≤ A*(log M)^2 := by
  obtain ⟨A,hA,hbound⟩ := localWeightProduct_bound hdeg hirr c
  refine ⟨A,hA,?_⟩
  intro M hM α hα0 hα hc
  rw [(smooth_weight_hasSum hdeg hirr hα M).tsum_eq]
  exact hbound M hM α hα0 hα hc


lemma smooth_weight_rankin {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) (c : ℝ) :
    ∃ A > (0 : ℝ), ∀ M : ℕ, 2 ≤ M → ∀ α : ℝ, 0 ≤ α → α ≤ 1/4 → α*log M ≤ c →
      ∀ X : ℝ, 0 < X → ∀ T : Finset ℕ,
        (∀ n ∈ T, n ∈ (M+1).smoothNumbers ∧ X ≤ (n : ℝ)) →
        (∑ n ∈ T, divisorRootWeight f n/(n : ℝ)) ≤ A*X^(-α)*(log M)^2 := by
  classical
  obtain ⟨A,hA,hbound⟩ := smooth_weight_bound hdeg hirr c
  refine ⟨A,hA,?_⟩
  intro M hM α hα0 hα hc X hX T hT
  let v : ℕ → ℝ := fun n => divisorRootWeight f n*(n : ℝ)^(α-1)
  have hv (n : ℕ) : 0 ≤ v n := mul_nonneg (divisorRootWeight_nonneg f n)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hpoint (n : ℕ) (hn : n ∈ T) : divisorRootWeight f n/(n : ℝ) ≤ X^(-α)*v n := by
    have hn0 : (0 : ℝ) < n := hX.trans_le (hT n hn).2
    have heq : divisorRootWeight f n/(n : ℝ) = v n*(n : ℝ)^(-α) := by
      dsimp only [v]
      rw [mul_assoc,← Real.rpow_add hn0,show α-1+-α = (-1 : ℝ) by ring,Real.rpow_neg_one,div_eq_mul_inv]
    rw [heq]
    have hh := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hX (hT n hn).2 (by linarith : -α ≤ 0)) (hv n)
    simpa only [mul_comm (v n)] using hh
  have hsum : ∑ n ∈ T, v n ≤ ∑' n : (M+1).smoothNumbers, divisorRootWeight f n*(n : ℝ)^(α-1) := by
    rw [← sum_subtype_of_mem v (fun n hn => (hT n hn).1)]
    exact (smooth_weight_hasSum hdeg hirr hα M).summable.sum_le_tsum _ (fun n hn => hv n)
  calc
    _ ≤ ∑ n ∈ T, X^(-α)*v n := sum_le_sum hpoint
    _ = X^(-α)*(∑ n ∈ T, v n) := by rw [mul_sum]
    _ ≤ X^(-α)*(A*(log M)^2) := mul_le_mul_of_nonneg_left (hsum.trans (hbound M hM α hα0 hα hc))
      (Real.rpow_nonneg hX.le _)
    _ = _ := by ring

end Sieve


open Finset Real Filter Polynomial
open scoped Topology ArithmeticFunction.sigma ArithmeticFunction.Omega

namespace Sieve

lemma sigma_zero_eq_prod_superset {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ}
    (hS : n.primeFactors ⊆ S) :
    σ 0 n = ∏ p ∈ S, (n.factorization p+1) := by
  rw [ArithmeticFunction.sigma_zero_apply,Nat.card_divisors hn]
  apply prod_subset hS
  intro p hp hpn
  have hh : n.factorization p = 0 := by
    apply Finsupp.notMem_support_iff.mp
    simpa only [Nat.support_factorization] using hpn
  simp only [hh,zero_add]

lemma sigma_zero_mul_le (a b : ℕ) : σ 0 (a*b) ≤ σ 0 a * σ 0 b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  let S := a.primeFactors ∪ b.primeFactors
  rw [sigma_zero_eq_prod_superset (mul_ne_zero ha hb) (show (a*b).primeFactors ⊆ S by
    rw [Nat.primeFactors_mul ha hb]),
    sigma_zero_eq_prod_superset ha (show a.primeFactors ⊆ S from subset_union_left),
    sigma_zero_eq_prod_superset hb (show b.primeFactors ⊆ S from subset_union_right),
    ← prod_mul_distrib]
  apply prod_le_prod'
  intro p hp
  rw [Nat.factorization_mul ha hb,Finsupp.add_apply]
  nlinarith

lemma succ_le_two_pow (k : ℕ) : k+1 ≤ 2^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    nlinarith [Nat.one_le_pow k 2 (by omega)]

lemma sigma_zero_le_two_pow_cardFactors (n : ℕ) : σ 0 n ≤ 2^(Ω n) := by
  by_cases hn : n = 0
  · simp [hn]
  rw [ArithmeticFunction.sigma_zero_apply,Nat.card_divisors hn,
    ArithmeticFunction.cardFactors_eq_sum_factorization,Finsupp.sum,Nat.support_factorization,
    ← prod_pow_eq_pow_sum]
  exact prod_le_prod' (fun p _ => succ_le_two_pow _)

lemma rough_pow_cardFactors_le {n p : ℕ} (hn : n ≠ 0)
    (hrough : ∀ q ∈ n.primeFactors, p ≤ q) : p^(Ω n) ≤ n := by
  have hp : ∀ q ∈ n.primeFactorsList, p ≤ q := by
    intro q hq
    apply hrough q
    simpa only [Nat.primeFactors, List.mem_toFinset] using hq
  have hlist : ∀ L : List ℕ, (∀ q ∈ L, p ≤ q) → p^L.length ≤ L.prod := by
    intro L hp
    induction L with
    | nil => simp
    | cons a L ih =>
      simp only [List.length_cons,List.prod_cons,pow_succ]
      have hpa := hp a (by simp)
      have hL := ih (fun q hq => hp q (by simp [hq]))
      simpa only [mul_comm] using Nat.mul_le_mul hL hpa
  simpa only [Nat.prod_primeFactorsList hn,ArithmeticFunction.cardFactors_apply] using
    hlist n.primeFactorsList hp

lemma rough_sigma_zero_bound {n p : ℕ} (hn : n ≠ 0) (hp : 1 < p)
    (hrough : ∀ q ∈ n.primeFactors, p ≤ q) :
    (σ 0 n : ℝ) ≤ exp (log 2 * log n / log p) := by
  have hlogp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  have hpow := rough_pow_cardFactors_le hn hrough
  have hlogs : (Ω n : ℝ)*log p ≤ log n := by
    have hh := log_le_log (pow_pos (by exact_mod_cast (by omega : 0 < p)) (Ω n))
      (show (p : ℝ)^(Ω n) ≤ (n : ℝ) by exact_mod_cast hpow)
    simpa only [Real.log_pow] using hh
  have hta : (σ 0 n : ℝ) ≤ (2 : ℝ)^(Ω n) := by
    exact_mod_cast sigma_zero_le_two_pow_cardFactors n
  calc
    _ ≤ (2 : ℝ)^(Ω n) := hta
    _ = exp ((Ω n : ℝ)*log 2) := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
    _ ≤ _ := Real.exp_le_exp.mpr (by
      apply (le_div_iff₀ hlogp).mpr
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)])

lemma sigma_zero_subpower_bound {η : ℝ} (hη : 0 < η) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, (σ 0 n : ℝ) ≤ C*(n : ℝ)^η := by
  classical
  let q : ℝ := 2^(-η)
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hη)
  have hs := summable_linear_geometric hq0.le hq1 1
  let B := ∑' k : ℕ, ((k : ℝ)+1)*q^k
  have hB : 1 ≤ B := by
    simpa only [Nat.cast_zero,zero_add,pow_zero,mul_one] using
      hs.le_tsum 0 (fun j _ => by positivity)
  have hlocal (p : ℕ) (hp : p.Prime) (k : ℕ) :
      (k : ℝ)+1 ≤ B*((p : ℝ)^k)^η := by
    have hterm : ((k : ℝ)+1)*q^k ≤ B := hs.le_tsum k (fun j _ => by positivity)
    have h2 : (0 : ℝ) < (2 : ℝ)^η := Real.rpow_pos_of_pos (by norm_num) _
    have hq : q^k = (((2 : ℝ)^η)^k)⁻¹ := by
      dsimp only [q]
      rw [Real.rpow_neg (by norm_num),inv_pow]
    have hh : (k : ℝ)+1 ≤ B*((2 : ℝ)^η)^k := by
      rw [hq,← div_eq_mul_inv] at hterm
      exact (div_le_iff₀ (pow_pos h2 k)).mp hterm
    have hpp : ((2 : ℝ)^η)^k ≤ ((p : ℝ)^k)^η := by
      rw [← Real.rpow_mul_natCast (by norm_num),mul_comm η,Real.rpow_natCast_mul (by norm_num)]
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.pow_le_pow_left hp.two_le k) hη.le
    exact hh.trans (mul_le_mul_of_nonneg_left hpp (by linarith))
  have hev : ∀ᶠ p : ℕ in atTop, (2 : ℝ) ≤ (p : ℝ)^η :=
    ((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))
  obtain ⟨P,hP⟩ := eventually_atTop.mp hev
  let S := Iio P
  let C := B^S.card
  have hC : 0 < C := pow_pos (by linarith) _
  refine ⟨C,hC,?_⟩
  intro n
  by_cases hn : n = 0
  · simp [hn,Real.zero_rpow hη.ne']
  have hl (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p : ℝ)+1 ≤
        (if p ∈ S then B else 1)*((p : ℝ)^(n.factorization p))^η := by
    split_ifs with hps
    · exact hlocal p (Nat.prime_of_mem_primeFactors hp) _
    · rw [one_mul]
      have hh : (2 : ℝ) ≤ (p : ℝ)^η := hP p (by simpa only [S,mem_Iio,not_lt] using hps)
      calc
        _ ≤ (2 : ℝ)^(n.factorization p) := by exact_mod_cast succ_le_two_pow (n.factorization p)
        _ ≤ ((p : ℝ)^η)^(n.factorization p) := pow_le_pow_left₀ (by norm_num) hh _
        _ = _ := by
          rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p),mul_comm η,
            Real.rpow_natCast_mul (Nat.cast_nonneg p)]
  have hpoly : ∏ p ∈ n.primeFactors, ((p : ℝ)^(n.factorization p))^η = (n : ℝ)^η := by
    rw [Real.finset_prod_rpow _ _ (fun p _ => by positivity)]
    simp_rw [← Nat.cast_pow]
    rw [← Nat.cast_prod]
    exact congrArg (fun x : ℕ => (x : ℝ)^η) (Nat.factorization_prod_pow_eq_self hn)
  have hcoeff : (∏ p ∈ n.primeFactors, if p ∈ S then B else 1) ≤ C := by
    rw [← prod_filter]
    have hsub : {p ∈ n.primeFactors | p ∈ S} ⊆ S := fun _ hp => (mem_filter.mp hp).2
    simpa only [prod_const,C] using (pow_le_pow_right₀ hB (card_le_card hsub))
  calc
    _ = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ)+1) := by
      rw [ArithmeticFunction.sigma_zero_apply,Nat.card_divisors hn,Nat.cast_prod]
      simp only [Nat.cast_add,Nat.cast_one]
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p ∈ S then B else 1)*((p : ℝ)^(n.factorization p))^η :=
      prod_le_prod (fun p _ => by positivity) hl
    _ = (∏ p ∈ n.primeFactors, if p ∈ S then B else 1)*(n : ℝ)^η := by
      rw [prod_mul_distrib,hpoly]
    _ ≤ C*(n : ℝ)^η := mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (Nat.cast_nonneg n) _)

end Sieve


open Finset Real Filter Polynomial
open scoped Topology ArithmeticFunction.sigma

namespace Sieve

lemma list_prefix_crossing (L : List ℕ) (A X : ℕ) (hAX : A ≤ X)
    (hXL : X < A*L.prod) :
    ∃ U p V, L = U ++ p::V ∧ A*U.prod ≤ X ∧ X < (A*U.prod)*p := by
  induction L generalizing A with
  | nil => simp only [List.prod_nil,mul_one] at hXL; omega
  | cons p L ih =>
    by_cases hp : X < A*p
    · exact ⟨[],p,L,by simp,by simpa using hAX,by simpa using hp⟩
    · obtain ⟨U,q,V,hL,hU,hq⟩ := ih (A*p) (by omega) (by simpa [mul_assoc] using hXL)
      refine ⟨p::U,q,V,by simp [hL],?_,?_⟩
      · simpa only [List.prod_cons,mul_assoc] using hU
      · simpa only [List.prod_cons,mul_assoc] using hq

lemma prime_mem_of_dvd_list_prod {L : List ℕ} (hL : ∀ p ∈ L, p.Prime)
    {q : ℕ} (hq : q.Prime) (hd : q ∣ L.prod) : q ∈ L := by
  obtain ⟨p,hp,hqp⟩ := hq.prime.dvd_prod_iff.mp hd
  exact (Nat.prime_dvd_prime_iff_eq hq (hL p hp)).mp hqp ▸ hp

/-- Split a natural number immediately before the first ordered prime factor
that makes the running product exceed `X`. -/
lemma sorted_prime_prefix {m X : ℕ} (hX : 1 ≤ X) (hm : X < m) :
    ∃ a b p : ℕ, 0 < a ∧ 0 < b ∧ p.Prime ∧
      a*b = m ∧ a ≤ X ∧ X < a*p ∧ p ∣ b ∧
      (∀ q ∈ a.primeFactors, q ≤ p) ∧
      (∀ q ∈ b.primeFactors, p ≤ q) := by
  have hm0 : m ≠ 0 := by omega
  obtain ⟨U,p,V,hL,hU,hp⟩ := list_prefix_crossing m.primeFactorsList 1 X hX
    (by simpa only [one_mul,Nat.prod_primeFactorsList hm0] using hm)
  simp only [one_mul] at hU hp
  have hprime : ∀ q ∈ U ++ p::V, q.Prime := by
    intro q hq
    apply Nat.prime_of_mem_primeFactorsList
    rwa [hL]
  have hUprime : ∀ q ∈ U, q.Prime := fun q hq => hprime q (List.mem_append_left _ hq)
  have hVprime : ∀ q ∈ p::V, q.Prime := fun q hq => hprime q (List.mem_append_right _ hq)
  have hpprime := hVprime p (by simp)
  have hprod : U.prod*(p::V).prod = m := by
    rw [← List.prod_append,← hL,Nat.prod_primeFactorsList hm0]
  have hsorted : (U ++ p::V).Pairwise (· ≤ ·) := by
    rw [← hL]
    exact (Nat.primeFactorsList_sorted m).pairwise
  obtain ⟨_,hsV,hUV⟩ := List.pairwise_append.mp hsorted
  refine ⟨U.prod,(p::V).prod,p,
    List.prod_pos (fun q hq => (hUprime q hq).pos),
    List.prod_pos (fun q hq => (hVprime q hq).pos),hpprime,
    hprod,hU,hp,List.dvd_prod (by simp),?_,?_⟩
  · intro q hq
    have hqU := prime_mem_of_dvd_list_prod hUprime (Nat.prime_of_mem_primeFactors hq)
      (Nat.dvd_of_mem_primeFactors hq)
    exact hUV q hqU p (by simp)
  · intro q hq
    have hqV := prime_mem_of_dvd_list_prod hVprime (Nat.prime_of_mem_primeFactors hq)
      (Nat.dvd_of_mem_primeFactors hq)
    rcases List.mem_cons.mp hqV with rfl | hqV
    · exact le_rfl
    · exact (List.pairwise_cons.mp hsV).1 q hqV

lemma prime_avoidance_of_rough_factor {a b m p q : ℕ} (hb : b ≠ 0)
    (hab : a*b = m) (hrough : ∀ r ∈ b.primeFactors, p ≤ r)
    (hq : q.Prime) (hqp : q < p) (hqa : a.Coprime q) : ¬ q ∣ m := by
  rw [← hab]
  intro hqmul
  rcases hq.dvd_mul.mp hqmul with hqd | hqd
  · have hh := Nat.eq_one_of_dvd_coprimes hqa hqd (dvd_refl q)
    exact hq.ne_one hh
  · exact (not_le_of_gt hqp) (hrough q (hq.mem_primeFactors hqd hb))

end Sieve


open Finset Real Filter Polynomial
open scoped Topology ArithmeticFunction.sigma

namespace Sieve
open GeneralDivisors

lemma root_mul_prime_le_of_stable (f : ℤ[X]) {p a : ℕ} (hp : p.Prime) (ha : a ≠ 0)
    (hstable : ∀ k : ℕ, 0 < k → polynomialRootCount f (p^k) = polynomialRootCount f p) :
    polynomialRootCount f (a*p) ≤ polynomialRootCount f a * polynomialRootCount f p := by
  let k := a.factorization p
  let b := ordCompl[p] a
  have hcop : p.Coprime b := Nat.coprime_ordCompl hp ha
  have hab : p^k*b = a := Nat.ordProj_mul_ordCompl_eq_self a p
  have hap : a*p = p^(k+1)*b := by rw [← hab,pow_succ]; ring
  have har : polynomialRootCount f a = polynomialRootCount f (p^k)*polynomialRootCount f b := by
    rw [← hab,polynomialRootCount_mul f (hcop.pow_left k)]
  rw [hap,polynomialRootCount_mul f (hcop.pow_left (k+1)),har,hstable (k+1) (by omega)]
  by_cases hk : k = 0
  · simp only [hk,pow_zero,polynomialRootCount_one,one_mul]
    exact le_of_eq (mul_comm _ _)
  · rw [hstable k (by omega)]
    have hh : polynomialRootCount f p ≤ polynomialRootCount f p * polynomialRootCount f p := by
      nlinarith
    convert Nat.mul_le_mul_right (polynomialRootCount f b) hh using 1 <;> ring

lemma root_mul_prime_le_of_good {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    {p a : ℕ} (hp : p.Prime) (ha : a ≠ 0) (hgood : ¬(p : ℤ) ∣ f.resultant f.derivative) :
    polynomialRootCount f (a*p) ≤ polynomialRootCount f a * polynomialRootCount f p :=
  root_mul_prime_le_of_stable f hp ha (fun _ hk =>
    polynomialRootCount_prime_pow_of_not_dvd_resultant f hdeg hp hgood hk)

lemma rootCost_one_le (f : ℤ[X]) {a : ℕ} (ha : a ≠ 0) : 1 ≤ rootCost f a := by
  rw [rootCost_apply f ha]
  apply one_le_prod
  intro p
  have hh : 0 ≤ (polynomialRootCount f p : ℝ)/p := by positivity
  linarith

lemma rootCost_mul_prime_le (f : ℤ[X]) {a p : ℕ} (ha : a ≠ 0) (hp : p.Prime) :
    rootCost f (a*p) ≤ 2*rootCost f a := by
  rw [rootCost_apply f (mul_ne_zero ha hp.ne_zero),Nat.primeFactors_mul ha hp.ne_zero]
  have hpp : p.primeFactors = {p} := by simp [hp]
  rw [hpp,union_singleton]
  by_cases hpa : p ∈ a.primeFactors
  · rw [insert_eq_of_mem hpa,← rootCost_apply f ha]
    nlinarith [rootCost_nonneg f a]
  · rw [prod_insert hpa,← rootCost_apply f ha]
    have hh : (polynomialRootCount f p : ℝ)/p ≤ 1 := by
      apply (div_le_one (by exact_mod_cast hp.pos)).mpr
      exact_mod_cast polynomialRootCount_le_modulus f hp.pos
    nlinarith [rootCost_nonneg f a]

lemma root_le_divisorRootWeight (f : ℤ[X]) {a : ℕ} (ha : a ≠ 0) :
    (polynomialRootCount f a : ℝ) ≤ divisorRootWeight f a := by
  rw [divisorRootWeight_apply f ha,← rootCost_apply f ha]
  have ht : (1 : ℝ) ≤ (σ 0 a : ℝ) := by exact_mod_cast ArithmeticFunction.sigma_pos 0 a ha
  have hc := rootCost_one_le f ha
  have hρ : 0 ≤ (polynomialRootCount f a : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ (σ 0 a : ℝ)*(polynomialRootCount f a : ℝ) := by nlinarith
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hc

end Sieve


open Finset Real Filter Polynomial
open scoped Topology ArithmeticFunction.sigma

namespace Sieve
open GeneralDivisors

lemma root_reciprocal_dyadic_bound {f : ℤ[X]} (hprim : f.IsPrimitive) {D : ℕ} (hD : 2 ≤ D) :
    (∑ p ∈ Ioc D (2*D) with p.Prime, (polynomialRootCount f p : ℝ)/p)
      ≤ 2*(f.natDegree : ℝ)*log 4/log D := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hlog : 0 < log (D : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < D))
  let T := {p ∈ Ioc D (2*D) | p.Prime}
  have hpoint (p : ℕ) (hp : p ∈ T) :
      (polynomialRootCount f p : ℝ)/p*((D : ℝ)*log D) ≤ (f.natDegree : ℝ)*log p := by
    obtain ⟨hInt,hpr⟩ := mem_filter.mp hp
    obtain ⟨hDp,_⟩ := mem_Ioc.mp hInt
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
    have hρ : (polynomialRootCount f p : ℝ) ≤ f.natDegree := by
      exact_mod_cast polynomialRootCount_prime_le hprim hpr
    have hDp' : (D : ℝ) ≤ p := by exact_mod_cast hDp.le
    have hratio : (polynomialRootCount f p : ℝ)/p*(D : ℝ) ≤ f.natDegree := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hp0).mpr
      exact mul_le_mul hρ hDp' hDpos.le (Nat.cast_nonneg _)
    calc
      _ = ((polynomialRootCount f p : ℝ)/p*D)*log D := by ring
      _ ≤ (f.natDegree : ℝ)*log D := mul_le_mul_of_nonneg_right hratio hlog.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.log_le_log hDpos hDp') (Nat.cast_nonneg _)
  have htheta : (∑ p ∈ T, log p) ≤ log 4*(2*D : ℕ) := by
    calc
      _ ≤ ∑ p ∈ Ioc 0 (2*D) with p.Prime, log p := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hInt,hpr⟩ := mem_filter.mp hp
          obtain ⟨hp1,hp2⟩ := mem_Ioc.mp hInt
          exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpr.pos,hp2⟩,hpr⟩
        · intro p hp _
          exact log_natCast_nonneg p
      _ = Chebyshev.theta ((2*D : ℕ) : ℝ) := by rw [Chebyshev.theta,Nat.floor_natCast]
      _ ≤ _ := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
  have hh : (∑ p ∈ T, (polynomialRootCount f p : ℝ)/p)*((D : ℝ)*log D)
      ≤ (f.natDegree : ℝ)*(log 4*(2*D : ℕ)) := by
    calc
      _ = ∑ p ∈ T, (polynomialRootCount f p : ℝ)/p*((D : ℝ)*log D) := by rw [sum_mul]
      _ ≤ ∑ p ∈ T, (f.natDegree : ℝ)*log p := sum_le_sum hpoint
      _ = (f.natDegree : ℝ)*(∑ p ∈ T, log p) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left htheta (Nat.cast_nonneg _)
  apply (le_div_iff₀ hlog).mpr
  apply le_of_mul_le_mul_right (a := (D : ℝ)) (a0 := hDpos)
  convert hh using 1 <;> push_cast <;> ring

end Sieve


open Finset Real Filter Polynomial
open scoped Topology ArithmeticFunction.sigma

namespace Sieve
open GeneralDivisors

lemma sum_le_weighted_cover {ι ν : Type*} (T : Finset ν) (I : Finset ι)
    (v : ν → ℝ) (w : ι → ℝ) (P : ι → ν → Prop) [∀ i, DecidablePred (P i)]
    (hw : ∀ i ∈ I, 0 ≤ w i)
    (hcover : ∀ n ∈ T, ∃ i ∈ I, P i n ∧ v n ≤ w i) :
    (∑ n ∈ T, v n) ≤ ∑ i ∈ I, w i*({n ∈ T | P i n}.card : ℝ) := by
  classical
  calc
    _ ≤ ∑ n ∈ T, ∑ i ∈ I, if P i n then w i else 0 := by
      apply sum_le_sum
      intro n hn
      obtain ⟨i,hi,hP,hv⟩ := hcover n hn
      exact hv.trans ((by simpa only [if_pos hP] using
        (single_le_sum (f := fun j => if P j n then w j else 0) (fun j hj => by dsimp only; split_ifs <;> [exact hw j hj; exact le_rfl]) hi)))
    _ = ∑ i ∈ I, ∑ n ∈ T, if P i n then w i else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      rw [← sum_filter,sum_const,nsmul_eq_mul,mul_comm]

lemma sum_pow_le_of_subset_Ioc {A : Finset ℕ} {X : ℕ} (hA : A ⊆ Ioc 0 X) (k : ℕ) :
    (∑ a ∈ A, (a : ℝ)^k) ≤ (X : ℝ)^(k+1) := by
  have hc : (A.card : ℝ) ≤ X := by exact_mod_cast (show A.card ≤ X by simpa using card_le_card hA)
  calc
    _ ≤ ∑ a ∈ A, (X : ℝ)^k := sum_le_sum (fun a ha =>
      pow_le_pow_left₀ (Nat.cast_nonneg a) (by exact_mod_cast (mem_Ioc.mp (hA ha)).2) k)
    _ = A.card*(X : ℝ)^k := by rw [sum_const,nsmul_eq_mul]
    _ ≤ (X : ℝ)*(X : ℝ)^k := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [pow_succ]; ring

lemma sum_sigma_mul_self_le_cube {A : Finset ℕ} {X : ℕ} (hA : A ⊆ Ioc 0 X) :
    (∑ a ∈ A, (σ 0 a : ℝ)*(a : ℝ)) ≤ (X : ℝ)^3 := by
  calc
    _ ≤ ∑ a ∈ A, (a : ℝ)^2 := by
      apply sum_le_sum
      intro a ha
      have hh : (σ 0 a : ℝ) ≤ a := by
        exact_mod_cast (show σ 0 a ≤ a by
          rw [ArithmeticFunction.sigma_zero_apply]; exact Nat.card_divisors_le_self a)
      nlinarith [show (0 : ℝ) ≤ a from Nat.cast_nonneg a]
    _ ≤ _ := sum_pow_le_of_subset_Ioc hA 2

noncomputable def roughValueCount (f : ℤ[X]) (a D N : ℕ) : ℕ :=
  {n ∈ Ioc 0 N | (a : ℤ) ∣ f.eval ((n : ℕ) : ℤ) ∧
    ∀ p ∈ siftingPrimes f a D, ¬((p : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)}.card

lemma roughValueCount_uniform_bound {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) :
    ∃ C > (0 : ℝ), ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D ≥ D₀, ∀ N a : ℕ, 0 < a →
      (roughValueCount f a D N : ℝ) ≤
        C*(N : ℝ)/log D*((polynomialRootCount f a : ℝ)*rootCost f a/a) +
          2*(a : ℝ)*(D : ℝ)^10 := by
  obtain ⟨C,hC,D₀,hbound⟩ := polynomial_rough_count_bound hdeg hirr
  refine ⟨C,hC,max D₀ 2,le_max_right _ _,?_⟩
  intro D hD N a ha
  have hh := hbound D ((le_max_left D₀ 2).trans hD) N a ha D le_rfl
  rw [← rootCost_apply f ha.ne'] at hh
  convert hh using 1 <;> dsimp only [roughValueCount] <;> ring

lemma root_cost_density_mul_prime_le {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    {a p : ℕ} (ha : a ≠ 0) (hp : p.Prime) (hgood : ¬(p : ℤ) ∣ f.resultant f.derivative) :
    (polynomialRootCount f (a*p) : ℝ)*rootCost f (a*p)/(a*p : ℕ) ≤
      2*((polynomialRootCount f a : ℝ)*rootCost f a/a)*((polynomialRootCount f p : ℝ)/p) := by
  have hρ : (polynomialRootCount f (a*p) : ℝ) ≤
      (polynomialRootCount f a : ℝ)*(polynomialRootCount f p : ℝ) := by
    exact_mod_cast root_mul_prime_le_of_good hdeg hp ha hgood
  have hh := mul_le_mul hρ (rootCost_mul_prime_le f ha hp)
    (rootCost_nonneg f (a*p)) (by positivity : 0 ≤ (polynomialRootCount f a : ℝ)*polynomialRootCount f p)
  convert div_le_div_of_nonneg_right hh (show (0 : ℝ) ≤ (a*p : ℕ) from Nat.cast_nonneg _) using 1 <;> push_cast <;> ring

lemma weighted_rough_sum_bound {f : ℤ[X]} {C : ℝ} {D N X : ℕ}
    (hbound : ∀ a : ℕ, 0 < a → (roughValueCount f a D N : ℝ) ≤
      C*(N : ℝ)/log D*((polynomialRootCount f a : ℝ)*rootCost f a/a) +
        2*(a : ℝ)*(D : ℝ)^10)
    {A : Finset ℕ} (hA : A ⊆ Ioc 0 X) :
    (∑ a ∈ A, (σ 0 a : ℝ)*roughValueCount f a D N) ≤
      C*(N : ℝ)/log D*(∑ a ∈ A, divisorRootWeight f a/a) + 2*(D : ℝ)^10*(X : ℝ)^3 := by
  have hlocal (a : ℕ) (ha : a ∈ A) :
      (σ 0 a : ℝ)*roughValueCount f a D N ≤
        C*(N : ℝ)/log D*(divisorRootWeight f a/a) + 2*(D : ℝ)^10*((σ 0 a : ℝ)*a) := by
    have ha0 := (mem_Ioc.mp (hA ha)).1
    rw [divisorRootWeight_apply f ha0.ne',← rootCost_apply f ha0.ne']
    convert mul_le_mul_of_nonneg_left (hbound a ha0) (Nat.cast_nonneg (σ 0 a)) using 1 <;> ring
  calc
    _ ≤ ∑ a ∈ A, (C*(N : ℝ)/log D*(divisorRootWeight f a/a) +
        2*(D : ℝ)^10*((σ 0 a : ℝ)*a)) := sum_le_sum hlocal
    _ = C*(N : ℝ)/log D*(∑ a ∈ A, divisorRootWeight f a/a) +
        2*(D : ℝ)^10*(∑ a ∈ A, (σ 0 a : ℝ)*a) := by rw [sum_add_distrib,mul_sum,mul_sum]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_sigma_mul_self_le_cube hA)
      (show 0 ≤ 2*(D : ℝ)^10 by positivity))

lemma weighted_rough_pairs_bound {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) {C : ℝ}
    (hC : 0 ≤ C) {D N X M : ℕ} (hD : 2 ≤ D)
    (hbound : ∀ a : ℕ, 0 < a → (roughValueCount f a D N : ℝ) ≤
      C*(N : ℝ)/log D*((polynomialRootCount f a : ℝ)*rootCost f a/a) +
        2*(a : ℝ)*(D : ℝ)^10)
    {A P : Finset ℕ} (hA : A ⊆ Ioc 0 X) (hP : P ⊆ Ioc 0 M)
    (hprime : ∀ p ∈ P, p.Prime) (hgood : ∀ p ∈ P, ¬(p : ℤ) ∣ f.resultant f.derivative) :
    (∑ a ∈ A, ∑ p ∈ P, (σ 0 a : ℝ)*roughValueCount f (a*p) D N) ≤
      2*C*(N : ℝ)/log D*(∑ a ∈ A, divisorRootWeight f a/a)*
        (∑ p ∈ P, (polynomialRootCount f p : ℝ)/p) + 2*(D : ℝ)^10*(X : ℝ)^3*(M : ℝ)^2 := by
  have hlog : 0 < log (D : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < D))
  have hCN : 0 ≤ C*(N : ℝ)/log D := by positivity
  have hlocal (a : ℕ) (ha : a ∈ A) (p : ℕ) (hp : p ∈ P) :
      (σ 0 a : ℝ)*roughValueCount f (a*p) D N ≤
        2*C*(N : ℝ)/log D*(divisorRootWeight f a/a)*((polynomialRootCount f p : ℝ)/p) +
        2*(D : ℝ)^10*((σ 0 a : ℝ)*a)*(p : ℝ) := by
    have ha0 := (mem_Ioc.mp (hA ha)).1
    have hp0 := (hprime p hp).pos
    have hh := (hbound (a*p) (Nat.mul_pos ha0 hp0)).trans
      (add_le_add (mul_le_mul_of_nonneg_left
        (root_cost_density_mul_prime_le hdeg ha0.ne' (hprime p hp) (hgood p hp)) hCN) le_rfl)
    rw [divisorRootWeight_apply f ha0.ne',← rootCost_apply f ha0.ne']
    convert mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (σ 0 a)) using 1 <;> push_cast <;> ring
  have hM : (∑ p ∈ P, (p : ℝ)) ≤ (M : ℝ)^2 := by simpa only [pow_one] using sum_pow_le_of_subset_Ioc hP 1
  calc
    _ ≤ ∑ a ∈ A, ∑ p ∈ P,
        (2*C*(N : ℝ)/log D*(divisorRootWeight f a/a)*((polynomialRootCount f p : ℝ)/p) +
        2*(D : ℝ)^10*((σ 0 a : ℝ)*a)*(p : ℝ)) := sum_le_sum (fun a ha => sum_le_sum (hlocal a ha))
    _ = 2*C*(N : ℝ)/log D*(∑ a ∈ A, divisorRootWeight f a/a)*
        (∑ p ∈ P, (polynomialRootCount f p : ℝ)/p) +
        2*(D : ℝ)^10*(∑ a ∈ A, (σ 0 a : ℝ)*a)*(∑ p ∈ P, (p : ℝ)) := by
      simp only [sum_add_distrib,← mul_sum,← sum_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul
      (mul_le_mul_of_nonneg_left (sum_sigma_mul_self_le_cube hA)
        (show 0 ≤ 2*(D : ℝ)^10 by positivity)) hM
      (sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (by positivity))

lemma divisible_value_sum_bound (f : ℤ[X]) {N X : ℕ} {A : Finset ℕ} (hA : A ⊆ Ioc 0 X) :
    (∑ a ∈ A, (divisibleValueCount f a N : ℝ)) ≤
      (N : ℝ)*(∑ a ∈ A, divisorRootWeight f a/a) + 2*(X : ℝ)^2 := by
  have hlocal (a : ℕ) (ha : a ∈ A) :
      (divisibleValueCount f a N : ℝ) ≤ (N : ℝ)*(divisorRootWeight f a/a)+2*(a : ℝ) := by
    have ha0 := (mem_Ioc.mp (hA ha)).1
    have hh := (abs_le.mp (polynomial_root_count_error f ha0 N)).2
    have hmain := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (root_le_divisorRootWeight f ha0.ne') (Nat.cast_nonneg a)) (Nat.cast_nonneg N)
    have hρ : (polynomialRootCount f a : ℝ) ≤ a := by exact_mod_cast polynomialRootCount_le_modulus f ha0
    have he : (N : ℝ)/a*polynomialRootCount f a = (N : ℝ)*((polynomialRootCount f a : ℝ)/a) := by ring
    rw [he] at hh
    linarith
  calc
    _ ≤ ∑ a ∈ A, ((N : ℝ)*(divisorRootWeight f a/a)+2*(a : ℝ)) := sum_le_sum hlocal
    _ = (N : ℝ)*(∑ a ∈ A, divisorRootWeight f a/a)+2*(∑ a ∈ A, (a : ℝ)) := by
      rw [sum_add_distrib,mul_sum,mul_sum]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (by simpa only [pow_one] using sum_pow_le_of_subset_Ioc hA 1) (by norm_num : (0 : ℝ) ≤ 2))

end Sieve


open Finset Real Filter Polynomial
open scoped Topology ArithmeticFunction.sigma

namespace Sieve
open GeneralDivisors

lemma log_double_le_two_log {D : ℝ} (hD : 2 ≤ D) : log (2*D) ≤ 2*log D := by
  have hD0 : 0 < D := by linarith
  rw [Real.log_mul (by norm_num) hD0.ne']
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hD
  linarith

lemma rough_factor_rankin_cancel {L X D α c : ℝ} (hX : 1 ≤ X) (hD : 0 < D)
    (hα : L/log D ≤ α) (hc : α*log (2*D) ≤ c) :
    exp (L*log X/log D)*(X/(2*D))^(-α) ≤ exp c := by
  have hX0 : 0 < X := by linarith
  rw [Real.rpow_def_of_pos (div_pos hX0 (by positivity)),← Real.exp_add,
    Real.log_div hX0.ne' (by positivity : 2*D ≠ 0)]
  apply Real.exp_le_exp.mpr
  have hxlog := Real.log_nonneg hX
  have hh := mul_le_mul_of_nonneg_right hα hxlog
  have heq : L*log X/log D+(log X-log (2*D))*(-α) =
      (L/log D)*log X - α*log X+α*log (2*D) := by ring
  rw [heq]
  linarith

lemma rough_factor_le_of_log {L X D : ℝ} (hX : 1 ≤ X) (hD : 1 < D) (hL : L ≤ log D) :
    exp (L*log X/log D) ≤ X := by
  have hlogD := Real.log_pos hD
  have hlogX := Real.log_nonneg hX
  conv_rhs => rw [← Real.exp_log (by linarith : 0 < X)]
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ hlogD).mpr
  nlinarith

lemma dyadic_weighted_sieve_bound {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) {L : ℝ} (hL : 0 < L) :
    ∃ B > (0 : ℝ), ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D ≥ D₀, ∀ N X : ℕ, 2*D ≤ X →
      ∀ A : Finset ℕ, A ⊆ Ioc 0 X →
      (∀ a ∈ A, a ∈ (2*D+1).smoothNumbers ∧ (X : ℝ)/(2*D) ≤ a) →
      exp (L*log X/log D)*(∑ a ∈ A, ∑ p ∈ Ioc D (2*D) with p.Prime,
        (σ 0 a : ℝ)*roughValueCount f (a*p) D N) ≤ B*(N : ℝ)+2*(X : ℝ)^16 := by
  classical
  obtain ⟨C,hC,D₁,hD₁,hcount⟩ := roughValueCount_uniform_bound hdeg hirr
  obtain ⟨H,hH,hrankin⟩ := smooth_weight_rankin hdeg hirr (2*L)
  have hev : ∀ᶠ D : ℕ in atTop, 8*L ≤ log (D : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (8*L))
  obtain ⟨D₂,hD₂⟩ := eventually_atTop.mp hev
  let R := (f.resultant f.derivative).natAbs
  let D₀ := max (max D₁ D₂) R
  let B := 16*C*H*exp (2*L)*(f.natDegree : ℝ)*log 4
  have hB : 0 < B := by
    dsimp only [B]
    have hd : (0 : ℝ) < f.natDegree := by exact_mod_cast Nat.pos_of_ne_zero hdeg
    have hlog4 : (0 : ℝ) < log 4 := Real.log_pos (by norm_num)
    positivity
  refine ⟨B,hB,D₀,le_trans hD₁ (le_trans (le_max_left _ _) (le_max_left _ _)),?_⟩
  intro D hDD N X hDX A hA hsmooth
  have hDcount : D₁ ≤ D := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hDD
  have hD2 : 2 ≤ D := hD₁.trans hDcount
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hlogD : 0 < log (D : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < D))
  have hlogbig : 8*L ≤ log (D : ℝ) := hD₂ D (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hDD)
  have hRD : R ≤ D := (le_max_right _ _).trans hDD
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hX0 : (0 : ℝ) < X := by linarith
  let M := 2*D
  let α := 2*L/log (M : ℝ)
  let W := exp (L*log X/log D)
  let P := {p ∈ Ioc D (2*D) | p.Prime}
  have hM2 : 2 ≤ M := by dsimp only [M]; omega
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hlogM : 0 < log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hlogDM : log (D : ℝ) ≤ log (M : ℝ) := Real.log_le_log hD0 (by dsimp only [M]; push_cast; linarith)
  have hlogMD : log (M : ℝ) ≤ 2*log (D : ℝ) := by
    simpa only [M,Nat.cast_mul,Nat.cast_ofNat] using log_double_le_two_log (by exact_mod_cast hD2)
  have hα0 : 0 ≤ α := by dsimp only [α]; positivity
  have hαq : α ≤ 1/4 := by
    apply (div_le_iff₀ hlogM).mpr
    linarith
  have hαM : α*log (M : ℝ) = 2*L := div_mul_cancel₀ _ hlogM.ne'
  have hαD : L/log (D : ℝ) ≤ α := by
    apply (div_le_div_iff₀ hlogD hlogM).mpr
    nlinarith
  have hW0 : 0 ≤ W := (Real.exp_pos _).le
  have hWX : W ≤ X := rough_factor_le_of_log hX1 (by exact_mod_cast (by omega : 1 < D)) (by linarith)
  have hcancel : W*((X : ℝ)/M)^(-α) ≤ exp (2*L) := by
    simpa only [M,Nat.cast_mul,Nat.cast_ofNat,W] using rough_factor_rankin_cancel hX1 hD0 hαD
      (show α*log (2*(D : ℝ)) ≤ 2*L by simpa only [M,Nat.cast_mul,Nat.cast_ofNat] using hαM.le)
  have hS := hrankin M hM2 α hα0 hαq hαM.le ((X : ℝ)/M) (div_pos hX0 hM0) A
    (by simpa only [M,Nat.cast_mul,Nat.cast_ofNat] using hsmooth)
  have hWS : W*(∑ a ∈ A, divisorRootWeight f a/a) ≤ H*exp (2*L)*(log M)^2 := by
    calc
      _ ≤ W*(H*((X : ℝ)/M)^(-α)*(log M)^2) := mul_le_mul_of_nonneg_left hS hW0
      _ = H*(log M)^2*(W*((X : ℝ)/M)^(-α)) := by ring
      _ ≤ H*(log M)^2*exp (2*L) := mul_le_mul_of_nonneg_left hcancel (by positivity)
      _ = _ := by ring
  have hP : P ⊆ Ioc 0 M := by
    intro p hp
    obtain ⟨hInt,hprime⟩ := mem_filter.mp hp
    exact mem_Ioc.mpr ⟨hprime.pos,(mem_Ioc.mp hInt).2⟩
  have hgood (p : ℕ) (hp : p ∈ P) : ¬(p : ℤ) ∣ f.resultant f.derivative := by
    obtain ⟨hInt,hprime⟩ := mem_filter.mp hp
    intro hdiv
    have hR0 : R ≠ 0 := Int.natAbs_ne_zero.mpr (irreducible_resultant_derivative_ne_zero hdeg hirr)
    have hh : p ≤ R := Nat.le_of_dvd (Nat.pos_of_ne_zero hR0) (Int.natCast_dvd.mp hdiv)
    have hDp := (mem_Ioc.mp hInt).1
    omega
  have hbound := weighted_rough_pairs_bound hdeg hC.le hD2 (hcount D hDcount N)
    hA hP (fun p hp => (mem_filter.mp hp).2) hgood
  have hPr : (∑ p ∈ P, (polynomialRootCount f p : ℝ)/p) ≤ 2*(f.natDegree : ℝ)*log 4/log D :=
    root_reciprocal_dyadic_bound (hirr.isPrimitive hdeg) hD2
  have hPr0 : 0 ≤ ∑ p ∈ P, (polynomialRootCount f p : ℝ)/p := sum_nonneg (fun _ _ => by positivity)
  have hmain : W*(2*C*(N : ℝ)/log D*(∑ a ∈ A, divisorRootWeight f a/a)*
      (∑ p ∈ P, (polynomialRootCount f p : ℝ)/p)) ≤ B*N := by
    have hprod := mul_le_mul hWS hPr hPr0 (by positivity : 0 ≤ H*exp (2*L)*(log M)^2)
    have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2*C*(N : ℝ)/log D by positivity)
    have hratio : (log (M : ℝ))^2/(log (D : ℝ))^2 ≤ 4 := by
      apply (div_le_iff₀ (sq_pos_of_pos hlogD)).mpr
      nlinarith
    calc
      _ ≤ (2*C*(N : ℝ)/log D)*(H*exp (2*L)*(log M)^2*(2*(f.natDegree : ℝ)*log 4/log D)) := by
        convert hh using 1 <;> ring
      _ = (B*(N : ℝ)/4)*((log (M : ℝ))^2/(log (D : ℝ))^2) := by dsimp only [B]; ring
      _ ≤ (B*(N : ℝ)/4)*4 := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  have herror : W*(2*(D : ℝ)^10*(X : ℝ)^3*(M : ℝ)^2) ≤ 2*(X : ℝ)^16 := by
    have hMX : (M : ℝ) ≤ X := by exact_mod_cast hDX
    have hDX' : (D : ℝ) ≤ X := by exact_mod_cast (by omega : D ≤ X)
    calc
      _ ≤ (X : ℝ)*(2*(X : ℝ)^10*(X : ℝ)^3*(X : ℝ)^2) := by gcongr
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_left hbound hW0
  rw [mul_add] at hh
  exact hh.trans (add_le_add hmain herror)

end Sieve


open Finset Real Filter Polynomial
open scoped Topology ArithmeticFunction.sigma

namespace Sieve
open GeneralDivisors

noncomputable def prefixSet (X M : ℕ) : Finset ℕ :=
  {a ∈ Ioc 0 X | a ∈ (M+1).smoothNumbers ∧ X < a*M}

lemma prefixSet_subset (X M : ℕ) : prefixSet X M ⊆ Ioc 0 X := filter_subset _ _

lemma prefixSet_smooth_data {X M : ℕ} (hM : 0 < M) {a : ℕ} (ha : a ∈ prefixSet X M) :
    a ∈ (M+1).smoothNumbers ∧ (X : ℝ)/M ≤ a := by
  have hh := (mem_filter.mp ha).2
  refine ⟨hh.1, (div_le_iff₀ (by exact_mod_cast hM)).mpr ?_⟩
  exact_mod_cast hh.2.le

lemma large_weighted_sieve_bound {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) :
    ∃ B > (0 : ℝ), ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ X ≥ D₀, ∀ N : ℕ,
      (∑ a ∈ Ioc 0 X, (σ 0 a : ℝ)*roughValueCount f a X N) ≤
        B*(N : ℝ)*log X+2*(X : ℝ)^13 := by
  obtain ⟨C,hC,D₀,hD₀,hcount⟩ := roughValueCount_uniform_bound hdeg hirr
  obtain ⟨H,hH,hrankin⟩ := smooth_weight_rankin hdeg hirr 0
  refine ⟨C*H,mul_pos hC hH,D₀,hD₀,?_⟩
  intro X hX N
  have hX2 : 2 ≤ X := hD₀.trans hX
  have hlogX : 0 < log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hs := hrankin X hX2 0 le_rfl (by norm_num) (by simp) 1 (by norm_num) (Ioc 0 X) (by
    intro a ha
    have haa := mem_Ioc.mp ha
    exact ⟨Nat.mem_smoothNumbers_of_lt haa.1 (by omega),by exact_mod_cast haa.1⟩)
  simp only [neg_zero,Real.rpow_zero,mul_one] at hs
  have hh := weighted_rough_sum_bound (hcount X hX N) (Subset.rfl : Ioc 0 X ⊆ Ioc 0 X)
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ C*(N : ℝ)/log X by positivity)
  calc
    _ ≤ C*(N : ℝ)/log X*(H*(log X)^2)+2*(X : ℝ)^10*(X : ℝ)^3 :=
      hh.trans (add_le_add hm le_rfl)
    _ = _ := by field_simp <;> ring

lemma smooth_divisible_count_bound {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f)
    {M : ℕ} (hM : 2 ≤ M) :
    ∃ B > (0 : ℝ), ∀ N X : ℕ, 0 < X →
      (∑ a ∈ prefixSet X M, (divisibleValueCount f a N : ℝ)) ≤
        B*(N : ℝ)*(X : ℝ)^(-(1/4 : ℝ))+2*(X : ℝ)^2 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hlogM : 0 < log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  obtain ⟨H,hH,hrankin⟩ := smooth_weight_rankin hdeg hirr ((1/4 : ℝ)*log M)
  let B := H*(M : ℝ)^(1/4 : ℝ)*(log M)^2
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B,hB,?_⟩
  intro N X hX
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hs := hrankin M hM (1/4) (by norm_num) le_rfl le_rfl ((X : ℝ)/M) (div_pos hX0 hM0)
    (prefixSet X M) (fun _ ha => prefixSet_smooth_data (by omega) ha)
  have heq : ((X : ℝ)/M)^(-(1/4 : ℝ)) = (X : ℝ)^(-(1/4 : ℝ))*(M : ℝ)^(1/4 : ℝ) := by
    rw [Real.div_rpow hX0.le hM0.le,Real.rpow_neg hM0.le,div_inv_eq_mul]
  rw [heq] at hs
  have hh := divisible_value_sum_bound f (N := N) (prefixSet_subset X M)
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg N)
  calc
    _ ≤ (N : ℝ)*(H*((X : ℝ)^(-(1/4 : ℝ))*(M : ℝ)^(1/4 : ℝ))*(log M)^2)+2*(X : ℝ)^2 :=
      hh.trans (add_le_add hm le_rfl)
    _ = _ := by dsimp only [B]; ring

end Sieve


open Finset Real Filter Polynomial
open scoped Topology ArithmeticFunction.sigma

namespace Sieve
open GeneralDivisors

def naturalValue (f : ℤ[X]) (n : ℕ) : ℕ := ⌊f.eval (n : ℤ)⌋₊

lemma naturalValue_cast_of_pos {f : ℤ[X]} {n : ℕ} (h : 0 < naturalValue f n) :
    (naturalValue f n : ℤ) = f.eval (n : ℤ) := by
  apply floor_eval_cast
  have hne : (f.eval (n : ℤ)).toNat ≠ 0 := by simpa only [naturalValue,Nat.floor_int] using h.ne'
  have hh : ¬ f.eval (n : ℤ) ≤ 0 := by simpa only [← Int.toNat_eq_zero] using hne
  omega

lemma dvd_naturalValue_iff {f : ℤ[X]} {n : ℕ} (h : 0 < naturalValue f n) (a : ℕ) :
    a ∣ naturalValue f n ↔ (a : ℤ) ∣ f.eval (n : ℤ) := by
  rw [← naturalValue_cast_of_pos h,Int.natCast_dvd_natCast]

abbrev roughEvent (f : ℤ[X]) (a D n : ℕ) : Prop :=
  (a : ℤ) ∣ f.eval (n : ℤ) ∧ ∀ p ∈ siftingPrimes f a D, ¬((p : ℕ) : ℤ) ∣ f.eval (n : ℤ)

lemma roughValueCount_eq (f : ℤ[X]) (a D N : ℕ) :
    roughValueCount f a D N = {n ∈ Ioc 0 N | roughEvent f a D n}.card := by
  classical
  rfl

lemma prefix_roughEvent {f : ℤ[X]} {n a b p D q : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a*b = naturalValue f n)
    (hrough : ∀ r ∈ b.primeFactors, p ≤ r) (hDp : D < p)
    (haq : a ∣ q) (hqm : q ∣ naturalValue f n) : roughEvent f q D n := by
  have hm : 0 < naturalValue f n := hab ▸ Nat.mul_pos ha hb
  refine ⟨(dvd_naturalValue_iff hm q).mp hqm,?_⟩
  intro r hr hdiv
  obtain ⟨hInt,hprime,_,_,hcop⟩ := mem_filter.mp hr
  have hrD := (mem_Ioc.mp hInt).2
  have hram : ¬r ∣ naturalValue f n := prime_avoidance_of_rough_factor hb.ne' hab hrough hprime
    (hrD.trans_lt hDp) (Nat.Coprime.of_dvd_left haq hcop)
  exact hram ((dvd_naturalValue_iff hm r).mpr hdiv)

lemma prefix_tau_bound {m a b p D X : ℕ} {E : ℝ} (hE : 0 ≤ E)
    (ha : 0 < a) (hb : 0 < b) (hp : p.Prime) (hab : a*b = m)
    (hrough : ∀ q ∈ b.primeFactors, p ≤ q) (hD : 2 ≤ D) (hDp : D < p)
    (hX : 1 ≤ X) (hm : log (m : ℝ) ≤ E*log X) :
    (σ 0 m : ℝ) ≤ exp ((E*log 2)*log X/log D)*(σ 0 a : ℝ) := by
  have hlogD : 0 < log (D : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < D))
  have hlogDp : log (D : ℝ) ≤ log p := Real.log_le_log
    (by exact_mod_cast (by omega : 0 < D)) (by exact_mod_cast hDp.le)
  have hbm : b ≤ m := by rw [← hab]; exact Nat.le_mul_of_pos_left b ha
  have hlogb : log (b : ℝ) ≤ E*log X :=
    (Real.log_le_log (by exact_mod_cast hb) (by exact_mod_cast hbm)).trans hm
  have hlog2 : 0 ≤ log (2 : ℝ) := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hnum0 : 0 ≤ log 2*(E*log (X : ℝ)) := mul_nonneg hlog2 (mul_nonneg hE (Real.log_nonneg (by exact_mod_cast hX)))
  have hdiv := div_le_div₀ hnum0 (mul_le_mul_of_nonneg_left hlogb hlog2) hlogD hlogDp
  have hτ := rough_sigma_zero_bound hb.ne' hp.one_lt hrough
  have he : log 2*(E*log (X : ℝ))/log D = (E*log 2)*log X/log D := by ring
  rw [he] at hdiv
  have htb := hτ.trans (Real.exp_le_exp.mpr hdiv)
  have hmul : (σ 0 m : ℝ) ≤ (σ 0 a : ℝ)*(σ 0 b : ℝ) := by
    rw [← hab]
    exact_mod_cast sigma_zero_mul_le a b
  exact hmul.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left htb (Nat.cast_nonneg (σ 0 a)))

lemma dyadic_interval_cover {u₀ j p : ℕ} (hl : 2^u₀ < p) (hu : p ≤ 2^j) :
    ∃ u ∈ Ico u₀ j, 2^u < p ∧ p ≤ 2^(u+1) := by
  have hpow : 1 ≤ 2^u₀ := Nat.one_le_pow _ _ (by norm_num)
  have hp : p-1 ≠ 0 := by omega
  let u := Nat.log 2 (p-1)
  have hu0 : u₀ ≤ u := (Nat.le_log_iff_pow_le (by norm_num) hp).mpr (by omega)
  have huj : u < j := (Nat.log_lt_iff_lt_pow (by norm_num) hp).mpr (by omega)
  have hlp := Nat.pow_log_le_self 2 hp
  have hup := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (p-1)
  exact ⟨u,mem_Ico.mpr ⟨hu0,huj⟩,by dsimp only [u]; omega,by dsimp only [u]; omega⟩

lemma sum_le_three_filter_cover {ν ι : Type*} (T : Finset ν) (J : Finset ι)
    (v : ν → ℝ) (A B : ν → Prop) (H : ι → ν → Prop)
    [DecidablePred A] [DecidablePred B] [∀ i, DecidablePred (H i)]
    (hv : ∀ n ∈ T, 0 ≤ v n)
    (hc : ∀ n ∈ T, A n ∨ B n ∨ ∃ i ∈ J, H i n) :
    (∑ n ∈ T, v n) ≤ (∑ n ∈ T with A n, v n)+(∑ n ∈ T with B n, v n)+
      ∑ i ∈ J, ∑ n ∈ T with H i n, v n := by
  have hpoint (n : ν) (hn : n ∈ T) : v n ≤
      (if A n then v n else 0)+(if B n then v n else 0)+∑ i ∈ J, if H i n then v n else 0 := by
    have ha0 : 0 ≤ if A n then v n else 0 := by split_ifs <;> [exact hv n hn; exact le_rfl]
    have hb0 : 0 ≤ if B n then v n else 0 := by split_ifs <;> [exact hv n hn; exact le_rfl]
    have hs0 : 0 ≤ ∑ i ∈ J, if H i n then v n else 0 := by
      apply sum_nonneg
      intro i hi
      split_ifs <;> [exact hv n hn; exact le_rfl]
    rcases hc n hn with ha | hb | ⟨i,hi,hH⟩
    · simp only [if_pos ha]
      linarith
    · simp only [if_pos hb]
      linarith
    · have hh : v n ≤ ∑ i ∈ J, if H i n then v n else 0 := by
        simpa only [if_pos hH] using single_le_sum
          (f := fun i => if H i n then v n else 0)
          (fun i hi => by dsimp only; split_ifs <;> [exact hv n hn; exact le_rfl]) hi
      linarith
  calc
    _ ≤ ∑ n ∈ T, ((if A n then v n else 0)+(if B n then v n else 0)+
        ∑ i ∈ J, if H i n then v n else 0) := sum_le_sum hpoint
    _ = _ := by
      simp only [sum_add_distrib]
      rw [sum_comm]
      simp only [← sum_filter]

end Sieve


open Finset Real Filter Polynomial
open scoped Topology ArithmeticFunction.sigma

namespace Sieve
open GeneralDivisors

lemma rough_single_cover_bound (f : ℤ[X]) {D N : ℕ} {T A : Finset ℕ} {W : ℝ}
    (hT : T ⊆ Ioc 0 N) (hW : 0 ≤ W)
    (hc : ∀ n ∈ T, ∃ a ∈ A, roughEvent f a D n ∧ (σ 0 (naturalValue f n) : ℝ) ≤ W*(σ 0 a : ℝ)) :
    (∑ n ∈ T, (σ 0 (naturalValue f n) : ℝ)) ≤ W*(∑ a ∈ A, (σ 0 a : ℝ)*roughValueCount f a D N) := by
  classical
  have hh := sum_le_weighted_cover T A (fun n => (σ 0 (naturalValue f n) : ℝ))
    (fun a => W*(σ 0 a : ℝ)) (fun a n => roughEvent f a D n) (fun _ _ => by positivity) hc
  apply hh.trans
  rw [mul_sum]
  apply sum_le_sum
  intro a ha
  have hcard : ({n ∈ T | roughEvent f a D n}.card : ℝ) ≤ roughValueCount f a D N := by
    rw [roughValueCount_eq]
    exact_mod_cast card_le_card (filter_subset_filter _ hT)
  convert mul_le_mul_of_nonneg_left hcard (show 0 ≤ W*(σ 0 a : ℝ) by positivity) using 1 <;> ring

lemma rough_pair_cover_bound (f : ℤ[X]) {D N : ℕ} {T A P : Finset ℕ} {W : ℝ}
    (hT : T ⊆ Ioc 0 N) (hW : 0 ≤ W)
    (hc : ∀ n ∈ T, ∃ a ∈ A, ∃ p ∈ P, roughEvent f (a*p) D n ∧
      (σ 0 (naturalValue f n) : ℝ) ≤ W*(σ 0 a : ℝ)) :
    (∑ n ∈ T, (σ 0 (naturalValue f n) : ℝ)) ≤
      W*(∑ a ∈ A, ∑ p ∈ P, (σ 0 a : ℝ)*roughValueCount f (a*p) D N) := by
  classical
  have hh := sum_le_weighted_cover T (A ×ˢ P) (fun n => (σ 0 (naturalValue f n) : ℝ))
    (fun ap => W*(σ 0 ap.1 : ℝ)) (fun ap n => roughEvent f (ap.1*ap.2) D n)
    (fun _ _ => by positivity) (by
      intro n hn
      obtain ⟨a,ha,p,hp,he,ht⟩ := hc n hn
      exact ⟨(a,p),mem_product.mpr ⟨ha,hp⟩,he,ht⟩)
  apply hh.trans
  rw [sum_product,mul_sum]
  apply sum_le_sum
  intro a ha
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hcard : ({n ∈ T | roughEvent f (a*p) D n}.card : ℝ) ≤ roughValueCount f (a*p) D N := by
    rw [roughValueCount_eq]
    exact_mod_cast card_le_card (filter_subset_filter _ hT)
  convert mul_le_mul_of_nonneg_left hcard (show 0 ≤ W*(σ 0 a : ℝ) by positivity) using 1 <;> ring

lemma divisible_cover_bound (f : ℤ[X]) {N : ℕ} {T A : Finset ℕ} {Q : ℝ}
    (hT : T ⊆ Ioc 0 N) (hQ : 0 ≤ Q)
    (hc : ∀ n ∈ T, ∃ a ∈ A, (a : ℤ) ∣ f.eval (n : ℤ))
    (ht : ∀ n ∈ T, (σ 0 (naturalValue f n) : ℝ) ≤ Q) :
    (∑ n ∈ T, (σ 0 (naturalValue f n) : ℝ)) ≤ Q*(∑ a ∈ A, (divisibleValueCount f a N : ℝ)) := by
  classical
  have hh := sum_le_weighted_cover T A (fun n => (σ 0 (naturalValue f n) : ℝ))
    (fun _ => Q) (fun a n => (a : ℤ) ∣ f.eval (n : ℤ)) (fun _ _ => hQ) (by
      intro n hn
      obtain ⟨a,ha,hdiv⟩ := hc n hn
      exact ⟨a,ha,hdiv,ht n hn⟩)
  apply hh.trans
  rw [mul_sum]
  apply sum_le_sum
  intro a ha
  apply mul_le_mul_of_nonneg_left _ hQ
  exact_mod_cast card_le_card (filter_subset_filter _ hT)

lemma prime_prefix_cover_sum (f : ℤ[X]) {N j u₀ : ℕ} (hu₀ : 1 ≤ u₀) (huj : u₀ ≤ j)
    {E Q : ℝ} (hE : 0 ≤ E) (hQ : 0 ≤ Q) {T : Finset ℕ} (hT : T ⊆ Ioc 0 N)
    (hlarge : ∀ n ∈ T, 2^j < naturalValue f n)
    (hlog : ∀ n ∈ T, log (naturalValue f n : ℝ) ≤ E*log (2^j : ℕ))
    (htau : ∀ n ∈ T, (σ 0 (naturalValue f n) : ℝ) ≤ Q) :
    (∑ n ∈ T, (σ 0 (naturalValue f n) : ℝ)) ≤
      Q*(∑ a ∈ prefixSet (2^j) (2^u₀), (divisibleValueCount f a N : ℝ)) +
      exp (E*log 2)*(∑ a ∈ Ioc 0 (2^j), (σ 0 a : ℝ)*roughValueCount f a (2^j) N) +
      ∑ u ∈ Ico u₀ j, exp ((E*log 2)*log (2^j : ℕ)/log (2^u : ℕ))*
        (∑ a ∈ prefixSet (2^j) (2*2^u), ∑ p ∈ Ioc (2^u) (2*2^u) with p.Prime,
          (σ 0 a : ℝ)*roughValueCount f (a*p) (2^u) N) := by
  classical
  let X := 2^j
  let P₀ := 2^u₀
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (by norm_num)
  have hX2 : 2 ≤ X := by
    have hj : 1 ≤ j := hu₀.trans huj
    simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : 0 < 2) hj
  have hlogX : log (X : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < X))).ne'
  have hex : ∀ n ∈ T, ∃ a b p : ℕ, 0 < a ∧ 0 < b ∧ p.Prime ∧
      a*b = naturalValue f n ∧ a ≤ X ∧ X < a*p ∧ p ∣ b ∧
      (∀ q ∈ a.primeFactors, q ≤ p) ∧ (∀ q ∈ b.primeFactors, p ≤ q) := by
    intro n hn
    exact sorted_prime_prefix hX1 (hlarge n hn)
  choose! a b p ha hb hp hab haX hXp hpb hsmooth hrough using hex
  have hm (n : ℕ) (hn : n ∈ T) : 0 < naturalValue f n := by have := hlarge n hn; omega
  have hadiv (n : ℕ) (hn : n ∈ T) : a n ∣ naturalValue f n := by
    rw [← hab n hn]
    exact Nat.dvd_mul_right _ _
  have haeval (n : ℕ) (hn : n ∈ T) : (a n : ℤ) ∣ f.eval (n : ℤ) := (dvd_naturalValue_iff (hm n hn) _).mp (hadiv n hn)
  have hprefix (n : ℕ) (hn : n ∈ T) (M : ℕ) (hpM : p n ≤ M) : a n ∈ prefixSet X M := by
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨ha n hn,haX n hn⟩,?_,?_⟩
    · apply Nat.mem_smoothNumbers.mpr
      refine ⟨(ha n hn).ne',?_⟩
      intro q hq
      have hh := (hsmooth n hn q ((Nat.mem_primeFactors_iff_mem_primeFactorsList).mpr hq)).trans hpM
      omega
    · exact (hXp n hn).trans_le (Nat.mul_le_mul_left _ hpM)
  let Ts := {n ∈ T | p n ≤ P₀}
  let Tl := {n ∈ T | X < p n}
  let Tm := fun u => {n ∈ T | 2^u < p n ∧ p n ≤ 2*2^u}
  have hsmall : (∑ n ∈ Ts, (σ 0 (naturalValue f n) : ℝ)) ≤
      Q*(∑ a ∈ prefixSet X P₀, (divisibleValueCount f a N : ℝ)) := by
    apply divisible_cover_bound f ((filter_subset _ _).trans hT) hQ
    · intro n hn
      obtain ⟨hn,hpn⟩ := mem_filter.mp hn
      exact ⟨a n,hprefix n hn _ hpn,haeval n hn⟩
    · intro n hn
      exact htau n (mem_filter.mp hn).1
  have hbig : (∑ n ∈ Tl, (σ 0 (naturalValue f n) : ℝ)) ≤
      exp (E*log 2)*(∑ a ∈ Ioc 0 X, (σ 0 a : ℝ)*roughValueCount f a X N) := by
    apply rough_single_cover_bound f ((filter_subset _ _).trans hT) (Real.exp_pos _).le
    intro n hn
    obtain ⟨hn,hpn⟩ := mem_filter.mp hn
    refine ⟨a n,mem_Ioc.mpr ⟨ha n hn,haX n hn⟩,
      prefix_roughEvent (ha n hn) (hb n hn) (hab n hn) (hrough n hn) hpn (dvd_refl _) (hadiv n hn),?_⟩
    have hh := prefix_tau_bound hE (ha n hn) (hb n hn) (hp n hn) (hab n hn) (hrough n hn)
      hX2 hpn hX1 (hlog n hn)
    simpa only [mul_div_cancel_right₀ _ hlogX] using hh
  have hmid (u : ℕ) (hu : u ∈ Ico u₀ j) :
      (∑ n ∈ Tm u, (σ 0 (naturalValue f n) : ℝ)) ≤
        exp ((E*log 2)*log (X : ℝ)/log (2^u : ℕ))*
          (∑ a ∈ prefixSet X (2*2^u), ∑ p ∈ Ioc (2^u) (2*2^u) with p.Prime,
            (σ 0 a : ℝ)*roughValueCount f (a*p) (2^u) N) := by
    apply rough_pair_cover_bound f ((filter_subset _ _).trans hT) (Real.exp_pos _).le
    intro n hn
    obtain ⟨hn,hpn,hpM⟩ := mem_filter.mp hn
    have hapdiv : a n*p n ∣ naturalValue f n := by
      rw [← hab n hn]
      exact Nat.mul_dvd_mul_left _ (hpb n hn)
    have hD : 2 ≤ 2^u := by
      have hh : 1 ≤ u := hu₀.trans (mem_Ico.mp hu).1
      simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : 0 < 2) hh
    refine ⟨a n,hprefix n hn _ hpM,p n,mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpn,hpM⟩,hp n hn⟩,
      prefix_roughEvent (ha n hn) (hb n hn) (hab n hn) (hrough n hn) hpn
        (Nat.dvd_mul_right _ _) hapdiv,?_⟩
    exact prefix_tau_bound hE (ha n hn) (hb n hn) (hp n hn) (hab n hn) (hrough n hn)
      hD hpn hX1 (hlog n hn)
  have hcover := sum_le_three_filter_cover T (Ico u₀ j) (fun n => (σ 0 (naturalValue f n) : ℝ))
    (fun n => p n ≤ P₀) (fun n => X < p n) (fun u n => 2^u < p n ∧ p n ≤ 2*2^u)
    (fun _ _ => Nat.cast_nonneg _) (by
      intro n hn
      by_cases hs : p n ≤ P₀
      · exact Or.inl hs
      by_cases hl : X < p n
      · exact Or.inr (Or.inl hl)
      obtain ⟨u,hu,hpl,hpu⟩ := dyadic_interval_cover (show 2^u₀ < p n by omega) (show p n ≤ 2^j by omega)
      exact Or.inr (Or.inr ⟨u,hu,hpl,by simpa only [pow_succ,mul_comm] using hpu⟩))
  exact hcover.trans (add_le_add (add_le_add hsmall hbig) (sum_le_sum hmid))

end Sieve


open Finset Real Filter Polynomial
open scoped Topology ArithmeticFunction.sigma

namespace Sieve
open GeneralDivisors

lemma tau_power_bound {E : ℕ} (hE : 0 < E) :
    ∃ C > (0 : ℝ), ∀ X m : ℕ, m ≤ X^E → (σ 0 m : ℝ) ≤ C*(X : ℝ)^(1/8 : ℝ) := by
  have hEr : (0 : ℝ) < E := by exact_mod_cast hE
  let η : ℝ := 1/(8*E)
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨C,hC,hbound⟩ := sigma_zero_subpower_bound hη
  refine ⟨C,hC,?_⟩
  intro X m hm
  have heq : ((X : ℝ)^E)^η = (X : ℝ)^(1/8 : ℝ) := by
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg X)]
    congr 1
    dsimp only [η]
    field_simp
  calc
    _ ≤ C*(m : ℝ)^η := hbound m
    _ ≤ C*((X : ℝ)^E)^η := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hm) hη.le) hC.le
    _ = _ := by rw [heq]

lemma rpow_eighth_cancel {X : ℝ} (hX : 1 ≤ X) :
    X^(1/8 : ℝ)*X^(-(1/4 : ℝ)) ≤ 1 ∧ X^(1/8 : ℝ)*X^2 ≤ X^3 := by
  have hX0 : 0 < X := by linarith
  constructor
  · rw [← Real.rpow_add hX0]
    apply Real.rpow_le_one_of_one_le_of_nonpos hX
    norm_num
  · rw [← Real.rpow_natCast X 2,← Real.rpow_add hX0,← Real.rpow_natCast X 3]
    exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)

lemma polynomial_value_tail_upper {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f)
    {E : ℕ} (hE : 0 < E) :
    ∃ C > (0 : ℝ), ∃ j₀ : ℕ, 1 ≤ j₀ ∧ ∀ j ≥ j₀, ∀ N : ℕ, (2^j)^17 ≤ N →
      ∀ T : Finset ℕ, T ⊆ Ioc 0 N →
      (∀ n ∈ T, 2^j < naturalValue f n ∧ naturalValue f n ≤ (2^j)^E) →
      (∑ n ∈ T, (σ 0 (naturalValue f n) : ℝ)) ≤ C*(N : ℝ)*(j+1 : ℕ) := by
  classical
  have hEr : (0 : ℝ) < E := by exact_mod_cast hE
  have hlog2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨B,hB,Db,hDb,hbin⟩ := dyadic_weighted_sieve_bound hdeg hirr (mul_pos hEr hlog2)
  obtain ⟨G,hG,Dg,hDg,hlarge⟩ := large_weighted_sieve_bound hdeg hirr
  obtain ⟨Cτ,hCτ,htau⟩ := tau_power_bound hE
  let u₀ := max Db Dg+1
  have hu₀ : 1 ≤ u₀ := by dsimp only [u₀]; omega
  have hpowu : u₀ < 2^u₀ := Nat.lt_pow_self (by norm_num)
  have hDbpow : Db ≤ 2^u₀ := by dsimp only [u₀] at *; omega
  have hDgpow : Dg ≤ 2^u₀ := by dsimp only [u₀] at *; omega
  have hP02 : 2 ≤ 2^u₀ := hDb.trans hDbpow
  obtain ⟨H,hH,hsmall⟩ := smooth_divisible_count_bound hdeg hirr hP02
  let W := exp ((E : ℝ)*log 2)
  let Cs := Cτ*H+2*Cτ
  let Cl := W*(G*log 2+2)
  let Cm := B+2
  have hCs : 0 < Cs := by dsimp only [Cs]; positivity
  have hCl : 0 < Cl := by dsimp only [Cl,W]; positivity
  have hCm : 0 < Cm := by dsimp only [Cm]; positivity
  refine ⟨Cs+Cl+Cm,by positivity,u₀,hu₀,?_⟩
  intro j hj N hXN T hT hvalues
  let X := 2^j
  have hj1 : 1 ≤ j := hu₀.trans hj
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (by norm_num)
  have hX0 : 0 < X := Nat.pow_pos (by norm_num)
  have hXr1 : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hXr0 : (0 : ℝ) < X := by exact_mod_cast hX0
  have hX17 : (X : ℝ)^17 ≤ N := by exact_mod_cast hXN
  have hX3 : (X : ℝ)^3 ≤ N := (pow_le_pow_right₀ hXr1 (by norm_num : 3 ≤ 17)).trans hX17
  have hX13 : (X : ℝ)^13 ≤ N := (pow_le_pow_right₀ hXr1 (by norm_num : 13 ≤ 17)).trans hX17
  have hXj : (j : ℝ) ≤ X := by exact_mod_cast (Nat.lt_pow_self (n := j) (by norm_num : 1 < 2)).le
  have hpowuj : 2^u₀ ≤ X := Nat.pow_le_pow_right (by norm_num) hj
  have hXlog : log (X : ℝ) = (j : ℝ)*log 2 := by
    simp only [X,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  let V : ℝ := (N : ℝ)*(j+1 : ℕ)
  have hNV : (N : ℝ) ≤ V := by dsimp only [V]; push_cast; nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N,show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
  have hNjV : (N : ℝ)*j ≤ V := by dsimp only [V]; push_cast; nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]
  have hQ : 0 ≤ Cτ*(X : ℝ)^(1/8 : ℝ) := by positivity
  have ht (n : ℕ) (hn : n ∈ T) : (σ 0 (naturalValue f n) : ℝ) ≤ Cτ*(X : ℝ)^(1/8 : ℝ) :=
    htau X _ (hvalues n hn).2
  have hl (n : ℕ) (hn : n ∈ T) : log (naturalValue f n : ℝ) ≤ (E : ℝ)*log (X : ℝ) := by
    have hm : 0 < naturalValue f n := hX0.trans (hvalues n hn).1
    have hh := Real.log_le_log (by exact_mod_cast hm)
      (show (naturalValue f n : ℝ) ≤ (X : ℝ)^E by exact_mod_cast (hvalues n hn).2)
    simpa only [Real.log_pow] using hh
  have hcover := prime_prefix_cover_sum f hu₀ hj hEr.le hQ hT (fun n hn => (hvalues n hn).1) hl ht
  have hs : (Cτ*(X : ℝ)^(1/8 : ℝ))*(∑ a ∈ prefixSet X (2^u₀), (divisibleValueCount f a N : ℝ)) ≤ Cs*V := by
    have hh := mul_le_mul_of_nonneg_left (hsmall N X hX0) hQ
    have hcancel := rpow_eighth_cancel hXr1
    calc
      _ ≤ (Cτ*(X : ℝ)^(1/8 : ℝ))*(H*(N : ℝ)*(X : ℝ)^(-(1/4 : ℝ))+2*(X : ℝ)^2) := hh
      _ = Cτ*H*(N : ℝ)*((X : ℝ)^(1/8 : ℝ)*(X : ℝ)^(-(1/4 : ℝ)))+
          2*Cτ*((X : ℝ)^(1/8 : ℝ)*(X : ℝ)^2) := by ring
      _ ≤ Cτ*H*(N : ℝ)*1+2*Cτ*(X : ℝ)^3 := add_le_add
        (mul_le_mul_of_nonneg_left hcancel.1 (by positivity))
        (mul_le_mul_of_nonneg_left hcancel.2 (by positivity))
      _ ≤ Cτ*H*(N : ℝ)*1+2*Cτ*(N : ℝ) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hX3 (by positivity))
      _ = Cs*(N : ℝ) := by dsimp only [Cs]; ring
      _ ≤ Cs*V := mul_le_mul_of_nonneg_left hNV hCs.le
  have hg : W*(∑ a ∈ Ioc 0 X, (σ 0 a : ℝ)*roughValueCount f a X N) ≤ Cl*V := by
    have hh := mul_le_mul_of_nonneg_left (hlarge X (hDgpow.trans hpowuj) N) (Real.exp_pos ((E : ℝ)*log 2)).le
    rw [hXlog] at hh
    calc
      _ ≤ W*(G*(N : ℝ)*((j : ℝ)*log 2)+2*(X : ℝ)^13) := hh
      _ ≤ W*(G*log 2*V+2*V) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply add_le_add
        · convert mul_le_mul_of_nonneg_left hNjV (mul_pos hG hlog2).le using 1 <;> ring
        · exact mul_le_mul_of_nonneg_left (hX13.trans hNV) (by norm_num)
      _ = Cl*V := by dsimp only [Cl]; ring
  have hmid : (∑ u ∈ Ico u₀ j, exp (((E : ℝ)*log 2)*log (X : ℝ)/log (2^u : ℕ))*
      (∑ a ∈ prefixSet X (2*2^u), ∑ p ∈ Ioc (2^u) (2*2^u) with p.Prime,
        (σ 0 a : ℝ)*roughValueCount f (a*p) (2^u) N)) ≤ Cm*V := by
    have hi (u : ℕ) (hu : u ∈ Ico u₀ j) :
        exp (((E : ℝ)*log 2)*log (X : ℝ)/log (2^u : ℕ))*
          (∑ a ∈ prefixSet X (2*2^u), ∑ p ∈ Ioc (2^u) (2*2^u) with p.Prime,
            (σ 0 a : ℝ)*roughValueCount f (a*p) (2^u) N) ≤ B*(N : ℝ)+2*(X : ℝ)^16 := by
      have hDu : Db ≤ 2^u := hDbpow.trans (Nat.pow_le_pow_right (by norm_num) (mem_Ico.mp hu).1)
      have hDX : 2*2^u ≤ X := by
        have hh := Nat.pow_le_pow_right (n := 2) (by norm_num) (show u+1 ≤ j by have := (mem_Ico.mp hu).2; omega)
        simpa only [pow_succ,mul_comm] using hh
      exact hbin (2^u) hDu N X hDX _ (prefixSet_subset _ _)
        (fun _ ha => by simpa only [Nat.cast_mul,Nat.cast_ofNat] using prefixSet_smooth_data (by positivity) ha)
    have hcard : ((Ico u₀ j).card : ℝ) ≤ j := by exact_mod_cast (show (Ico u₀ j).card ≤ j by simp)
    have hjerr : (j : ℝ)*(X : ℝ)^16 ≤ N := by
      calc
        _ ≤ (X : ℝ)*(X : ℝ)^16 := mul_le_mul_of_nonneg_right hXj (by positivity)
        _ = (X : ℝ)^17 := by ring
        _ ≤ _ := hX17
    calc
      _ ≤ ∑ _u ∈ Ico u₀ j, (B*(N : ℝ)+2*(X : ℝ)^16) := sum_le_sum hi
      _ = (Ico u₀ j).card*(B*(N : ℝ)+2*(X : ℝ)^16) := by rw [sum_const,nsmul_eq_mul]
      _ ≤ (j : ℝ)*(B*(N : ℝ)+2*(X : ℝ)^16) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = B*((N : ℝ)*j)+2*((j : ℝ)*(X : ℝ)^16) := by ring
      _ ≤ B*V+2*V := add_le_add (mul_le_mul_of_nonneg_left hNjV hB.le)
        (mul_le_mul_of_nonneg_left (hjerr.trans hNV) (by norm_num))
      _ = Cm*V := by dsimp only [Cm]; ring
  convert hcover.trans (add_le_add (add_le_add hs hg) hmid) using 1 <;> dsimp only [V] <;> ring

end Sieve


open Finset Real Filter Polynomial
open scoped Topology ArithmeticFunction.sigma

namespace Sieve
open GeneralDivisors

lemma positive_value_fiber_bound {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (T : Finset ℕ) {m : ℕ} (hm : 0 < m) :
    {n ∈ T | naturalValue f n = m}.card ≤ f.natDegree := by
  classical
  let S := {n ∈ T | naturalValue f n = m}
  let g := f-C (m : ℤ)
  have hg : g ≠ 0 := by
    intro hz
    have hh := congrArg Polynomial.natDegree hz
    simp only [g,natDegree_sub_C,natDegree_zero] at hh
    exact hdeg hh
  have hroots : (S.image (fun n : ℕ => (n : ℤ))).val ⊆ g.roots := by
    intro x hx
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hx
    have hnval := (mem_filter.mp hn).2
    have hnpos : 0 < naturalValue f n := hnval ▸ hm
    apply (Polynomial.mem_roots hg).mpr
    simp only [Polynomial.IsRoot.def,g,Polynomial.eval_sub,Polynomial.eval_C]
    rw [← naturalValue_cast_of_pos hnpos,hnval,sub_self]
  have hh := Polynomial.card_le_degree_of_subset_roots hroots
  rw [card_image_of_injective _ Nat.cast_injective,natDegree_sub_C] at hh
  exact hh

lemma small_value_sum_bound {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (T : Finset ℕ) (X : ℕ)
    (hT : ∀ n ∈ T, naturalValue f n ≤ X) :
    (∑ n ∈ T, (σ 0 (naturalValue f n) : ℝ)) ≤ (f.natDegree : ℝ)*X*(X+1 : ℕ) := by
  classical
  have hmap : ∀ n ∈ T, naturalValue f n ∈ Iic X := fun n hn => mem_Iic.mpr (hT n hn)
  rw [← sum_fiberwise_of_maps_to hmap (fun n => (σ 0 (naturalValue f n) : ℝ))]
  calc
    _ ≤ ∑ _m ∈ Iic X, (f.natDegree : ℝ)*X := by
      apply sum_le_sum
      intro m hm
      have hsum : (∑ n ∈ T with naturalValue f n = m, (σ 0 (naturalValue f n) : ℝ)) =
          ({n ∈ T | naturalValue f n = m}.card : ℝ)*(σ 0 m : ℝ) := by
        have heq : (∑ n ∈ T with naturalValue f n = m, (σ 0 (naturalValue f n) : ℝ)) =
            ∑ n ∈ T with naturalValue f n = m, (σ 0 m : ℝ) :=
          sum_congr rfl (fun n hn => by rw [(mem_filter.mp hn).2])
        rw [heq,sum_const,nsmul_eq_mul]
      rw [hsum]
      by_cases hm0 : m = 0
      · simp only [hm0,ArithmeticFunction.map_zero,Nat.cast_zero,mul_zero]
        positivity
      · have hc : ({n ∈ T | naturalValue f n = m}.card : ℝ) ≤ f.natDegree := by
          exact_mod_cast positive_value_fiber_bound hdeg T (Nat.pos_of_ne_zero hm0)
        have ht : (σ 0 m : ℝ) ≤ X := by
          have hh : σ 0 m ≤ m := by rw [ArithmeticFunction.sigma_zero_apply]; exact Nat.card_divisors_le_self m
          exact_mod_cast hh.trans (mem_Iic.mp hm)
        exact mul_le_mul hc ht (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by rw [sum_const,nsmul_eq_mul,Nat.card_Iic]; ring

lemma naturalValue_polynomial_upper (f : ℤ[X]) :
    ∃ B : ℕ, ∀ N ≥ max B 1, ∀ n ≤ N, naturalValue f n ≤ N^(f.natDegree+1) := by
  let B := ∑ i ∈ range (f.natDegree+1), (f.coeff i).natAbs
  refine ⟨B,?_⟩
  intro N hN n hn
  have hN0 : 0 < N := by omega
  have heval : f.eval (n : ℤ) ≤ ((B*N^f.natDegree : ℕ) : ℤ) := by
    rw [Polynomial.eval_eq_sum_range]
    calc
      _ ≤ ∑ i ∈ range (f.natDegree+1), ((f.coeff i).natAbs : ℤ)*((N : ℤ)^f.natDegree) := by
        apply sum_le_sum
        intro i hi
        have hpow : (n : ℤ)^i ≤ (N : ℤ)^f.natDegree := by
          exact_mod_cast (Nat.pow_le_pow_left hn i).trans (Nat.pow_le_pow_right hN0 (by have := mem_range.mp hi; omega))
        apply mul_le_mul Int.le_natAbs hpow (by positivity) (by positivity)
      _ = _ := by rw [← sum_mul]; dsimp only [B]; push_cast; rfl
  have hfloor : naturalValue f n ≤ B*N^f.natDegree := by
    have hh := Nat.floor_mono heval
    simpa only [naturalValue,Nat.floor_natCast] using hh
  apply hfloor.trans
  calc
    _ ≤ N*N^f.natDegree := Nat.mul_le_mul_right _ ((le_max_left B 1).trans hN)
    _ = _ := by rw [pow_succ]; ring

end Sieve


open Finset Real Filter Polynomial
open scoped Topology ArithmeticFunction.sigma

namespace Sieve
open GeneralDivisors

lemma polynomial_divisor_sum_upper_nat {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Ioc 0 N, (σ 0 (naturalValue f n) : ℝ)) ≤ C*(N : ℝ)*log N := by
  classical
  let E := 40*(f.natDegree+1)
  have hE : 0 < E := by dsimp only [E]; positivity
  obtain ⟨C,hC,j₀,hj₀,htail⟩ := polynomial_value_tail_upper hdeg hirr hE
  obtain ⟨B,hpoly⟩ := naturalValue_polynomial_upper f
  have hlog2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  let K := 2*(C+(f.natDegree : ℝ))/log 2
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_ge_atTop (max (max B 2) (2^(20*j₀)))] with N hN
  have hN2 : 2 ≤ N := le_trans (le_trans (le_max_right B 2) (le_max_left _ _)) hN
  have hNB : max B 1 ≤ N := by omega
  have hN0 : N ≠ 0 := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : log 2 ≤ log (N : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hN2)
  let j := Nat.log 2 N/20
  let X := 2^j
  have hjlower : j₀ ≤ j := by
    have hh : 20*j₀ ≤ Nat.log 2 N := (Nat.le_log_iff_pow_le (by norm_num) hN0).mpr
      ((le_max_right _ _).trans hN)
    dsimp only [j]
    omega
  have hj1 : 1 ≤ j := hj₀.trans hjlower
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (by norm_num)
  have hX0 : 0 < X := Nat.pow_pos (by norm_num)
  have hXr1 : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hXr0 : (0 : ℝ) < X := by exact_mod_cast hX0
  have hX20 : X^20 ≤ N := by
    calc
      _ = 2^(20*j) := by simp only [X,← pow_mul,mul_comm j]
      _ ≤ 2^(Nat.log 2 N) := Nat.pow_le_pow_right (by norm_num) (by dsimp only [j]; omega)
      _ ≤ _ := Nat.pow_log_le_self 2 hN0
  have hX17 : X^17 ≤ N := (Nat.pow_le_pow_right hX0 (by norm_num : 17 ≤ 20)).trans hX20
  have hNX40 : N ≤ X^40 := by
    calc
      _ ≤ 2^((Nat.log 2 N)+1) := (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N).le
      _ ≤ 2^(40*j) := Nat.pow_le_pow_right (by norm_num) (by dsimp only [j] at *; omega)
      _ = _ := by simp only [X,← pow_mul,mul_comm j]
  have hXN : X ≤ N := by
    apply le_trans ?_ hX17
    simpa only [pow_one] using Nat.pow_le_pow_right hX0 (by norm_num : 1 ≤ 17)
  have hjlog : (j+1 : ℕ)*log (2 : ℝ) ≤ 2*log (N : ℝ) := by
    have hh := Real.log_le_log hXr0 (show (X : ℝ) ≤ N by exact_mod_cast hXN)
    simp only [X,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] at hh
    have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    push_cast
    nlinarith
  let T := {n ∈ Ioc 0 N | X < naturalValue f n}
  let S := {n ∈ Ioc 0 N | naturalValue f n ≤ X}
  have ht : (∑ n ∈ T, (σ 0 (naturalValue f n) : ℝ)) ≤ C*(N : ℝ)*(j+1 : ℕ) := by
    apply htail j hjlower N hX17 T (filter_subset _ _)
    intro n hn
    obtain ⟨hnInt,hnval⟩ := mem_filter.mp hn
    refine ⟨hnval,?_⟩
    calc
      _ ≤ N^(f.natDegree+1) := hpoly N hNB n (mem_Ioc.mp hnInt).2
      _ ≤ (X^40)^(f.natDegree+1) := Nat.pow_le_pow_left hNX40 _
      _ = _ := by rw [← pow_mul]
  have hs : (∑ n ∈ S, (σ 0 (naturalValue f n) : ℝ)) ≤ 2*(f.natDegree : ℝ)*N := by
    have hh := small_value_sum_bound hdeg S X (fun n hn => (mem_filter.mp hn).2)
    have hX2 : (X : ℝ)^2 ≤ N := by
      exact_mod_cast (Nat.pow_le_pow_right hX0 (by norm_num : 2 ≤ 17)).trans hX17
    calc
      _ ≤ (f.natDegree : ℝ)*X*(X+1 : ℕ) := hh
      _ ≤ 2*(f.natDegree : ℝ)*(X : ℝ)^2 := by
        push_cast
        have hh := mul_le_mul_of_nonneg_left (show (X : ℝ)+1 ≤ 2*X by linarith)
          (show 0 ≤ (f.natDegree : ℝ)*X by positivity)
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hX2 (by positivity)
  have heq : (∑ n ∈ Ioc 0 N, (σ 0 (naturalValue f n) : ℝ)) =
      (∑ n ∈ S, (σ 0 (naturalValue f n) : ℝ))+(∑ n ∈ T, (σ 0 (naturalValue f n) : ℝ)) := by
    simpa only [S,T,not_le] using (sum_filter_add_sum_filter_not (s := Ioc 0 N)
      (p := fun n => naturalValue f n ≤ X) (f := fun n => (σ 0 (naturalValue f n) : ℝ))).symm
  rw [heq]
  have hh := add_le_add hs ht
  apply hh.trans
  apply le_of_mul_le_mul_right (a := log (2 : ℝ)) (a0 := hlog2)
  have hsmall := mul_le_mul_of_nonneg_left hlogN (show 0 ≤ 2*(f.natDegree : ℝ)*N by positivity)
  have htail := mul_le_mul_of_nonneg_left hjlog (show 0 ≤ C*(N : ℝ) by positivity)
  have he : (K*(N : ℝ)*log N)*log 2 = 2*(C+(f.natDegree : ℝ))*(N : ℝ)*log N := by
    dsimp only [K]
    field_simp
  rw [he]
  nlinarith

lemma polynomial_divisor_sum_upper_Iic {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Iic N, (σ 0 (naturalValue f n) : ℝ)) ≤ C*(N : ℝ)*log N := by
  obtain ⟨C,hC,hbound⟩ := polynomial_divisor_sum_upper_nat hdeg hirr
  let A : ℝ := (σ 0 (naturalValue f 0) : ℝ)
  have hA : 0 ≤ A := Nat.cast_nonneg _
  have hlog2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨C+A/log 2,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (2 : ℕ)] with N hN hN2
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hl : log 2 ≤ log (N : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hN2)
  have heq : (∑ n ∈ Iic N, (σ 0 (naturalValue f n) : ℝ)) =
      (∑ n ∈ Ioc 0 N, (σ 0 (naturalValue f n) : ℝ))+A := by
    simpa only [Icc_bot,bot_eq_zero,A] using
      (sum_Ioc_add_eq_sum_Icc (f := fun n => (σ 0 (naturalValue f n) : ℝ)) (Nat.zero_le N)).symm
  rw [heq]
  have hden : log 2 ≤ (N : ℝ)*log N := hl.trans (by nlinarith)
  have hh := mul_le_mul_of_nonneg_left hden (show 0 ≤ A/log 2 by positivity)
  have he : (A/log 2)*log 2 = A := div_mul_cancel₀ _ hlog2.ne'
  rw [he] at hh
  nlinarith

end Sieve


/-- The uniform order-of-magnitude upper estimate does not assert convergence. -/
lemma erdos_975_upper_bound {f : ℤ[X]} (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) :
    ∃ C > (0 : ℝ), ∀ᶠ x : ℝ in atTop, Erdos975Sum f x ≤ C*x*log x := by
  obtain ⟨C,hC,hbound⟩ := Sieve.polynomial_divisor_sum_upper_Iic hdeg hirr
  refine ⟨C,hC,?_⟩
  filter_upwards [(tendsto_nat_floor_atTop (α := ℝ)).eventually hbound,
    (tendsto_nat_floor_atTop (α := ℝ)).eventually (eventually_ge_atTop (2 : ℕ)),
    eventually_ge_atTop (0 : ℝ)] with x hx hfloor hx0
  have hN0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast (by omega : 0 < ⌊x⌋₊)
  have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hlog : log (⌊x⌋₊ : ℝ) ≤ log x := Real.log_le_log hN0 hle
  have hlog0 : 0 ≤ log (⌊x⌋₊ : ℝ) := Real.log_natCast_nonneg _
  change Erdos975Sum f x ≤ C*(⌊x⌋₊ : ℝ)*log (⌊x⌋₊ : ℝ) at hx
  exact hx.trans (mul_le_mul (mul_le_mul_of_nonneg_left hle hC.le) hlog hlog0 (by positivity))



open Finset Real Filter Polynomial Asymptotics
open scoped Topology ArithmeticFunction.sigma

namespace GeneralDivisors
open Sieve

lemma naturalValue_eventually_real_eval {f : ℤ[X]} (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    ∀ᶠ n : ℕ in atTop, (naturalValue f n : ℝ) =
      (f.map (Int.castRingHom ℝ)).eval (n : ℝ) := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℤ)).eventually hpos] with n hn
  have he : (f.map (Int.castRingHom ℝ)).eval (n : ℝ) = ((f.eval (n : ℤ) : ℤ) : ℝ) := by
    simpa only [Int.cast_natCast] using Polynomial.eval_intCast_map (Int.castRingHom ℝ) f (n : ℤ)
  rw [he]
  exact_mod_cast floor_eval_cast (by omega : 0 ≤ f.eval (n : ℤ))

lemma real_map_leadingCoeff_pos {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    0 < (f.map (Int.castRingHom ℝ)).leadingCoeff := by
  let F := f.map (Int.castRingHom ℝ)
  have hFdeg : F.natDegree = f.natDegree := natDegree_map_eq_of_injective Int.cast_injective f
  have hFd : 0 < F.degree := natDegree_pos_iff_degree_pos.mp (by rw [hFdeg]; exact Nat.pos_of_ne_zero hdeg)
  have hF0 : F ≠ 0 := ne_zero_of_degree_gt hFd
  have hlead : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hF0
  by_contra hnot
  have hnle : F.leadingCoeff ≤ 0 := le_of_not_gt hnot
  have ht := (F.tendsto_atBot_of_leadingCoeff_nonpos hFd hnle).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have he := naturalValue_eventually_real_eval hpos
  obtain ⟨n,hn,hne⟩ := ((ht.eventually (eventually_lt_atBot (0 : ℝ))).and he).exists
  change F.eval (n : ℝ) < 0 at hn
  rw [← hne] at hn
  exact (not_lt_of_ge (Nat.cast_nonneg _)) hn

lemma naturalValue_tendsto_atTop {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) : Tendsto (naturalValue f) atTop atTop := by
  let F := f.map (Int.castRingHom ℝ)
  have hFdeg : F.natDegree = f.natDegree := natDegree_map_eq_of_injective Int.cast_injective f
  have hFd : 0 < F.degree := natDegree_pos_iff_degree_pos.mp (by rw [hFdeg]; exact Nat.pos_of_ne_zero hdeg)
  have ht := (F.tendsto_atTop_of_leadingCoeff_nonneg hFd (real_map_leadingCoeff_pos hdeg hpos).le).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  apply ht.congr'
  filter_upwards [naturalValue_eventually_real_eval hpos] with n hn
  exact hn.symm

lemma naturalValue_log_limit {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    Tendsto (fun n : ℕ => log (naturalValue f n : ℝ)/log n) atTop (𝓝 (f.natDegree : ℝ)) := by
  let F := f.map (Int.castRingHom ℝ)
  let A := F.leadingCoeff
  have hA : 0 < A := real_map_leadingCoeff_pos hdeg hpos
  have hFdeg : F.natDegree = f.natDegree := natDegree_map_eq_of_injective Int.cast_injective f
  have hFd : F.natDegree ≠ 0 := hFdeg ▸ hdeg
  have hg : Tendsto (fun n : ℕ => A*(n : ℝ)^F.natDegree) atTop atTop :=
    (tendsto_const_mul_pow_atTop hFd hA).comp tendsto_natCast_atTop_atTop
  have heq := F.isEquivalent_atTop_lead.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlogeq := heq.log hg
  have hc : Tendsto (fun n : ℕ => log A/log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have htarget : Tendsto (fun n : ℕ => log (A*(n : ℝ)^F.natDegree)/log n)
      atTop (𝓝 (f.natDegree : ℝ)) := by
    have hh := hc.add_const (f.natDegree : ℝ)
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog : log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
    rw [Real.log_mul hA.ne' (pow_ne_zero _ hn0.ne'),Real.log_pow,hFdeg,add_div,mul_div_cancel_right₀ _ hlog]
  have hratio : Tendsto (fun n : ℕ => log (F.eval (n : ℝ))/log n)
      atTop (𝓝 (f.natDegree : ℝ)) := by
    exact (hlogeq.div (IsEquivalent.refl (u := fun n : ℕ => log (n : ℝ)))).tendsto_nhds_iff.mpr htarget
  apply hratio.congr'
  filter_upwards [naturalValue_eventually_real_eval hpos] with n hn
  rw [hn]

/-- The logarithmic size of the actual hyperbola cutoff is half the degree. -/
lemma sqrt_naturalValue_log_limit {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    Tendsto (fun n : ℕ => log ((naturalValue f n).sqrt : ℝ)/log n)
      atTop (𝓝 ((f.natDegree : ℝ)/2)) := by
  have hv := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (naturalValue_tendsto_atTop hdeg hpos)
  have hs := Real.tendsto_sqrt_atTop.comp hv
  have heq := (isEquivalent_nat_floor (R := ℝ)).comp_tendsto hs
  have hlogeq := heq.log hs
  have hmain : Tendsto (fun n : ℕ => log (√(naturalValue f n : ℝ))/log n)
      atTop (𝓝 ((f.natDegree : ℝ)/2)) := by
    have hh := (naturalValue_log_limit hdeg hpos).div_const 2
    convert hh using 1
    ext n
    rw [Real.log_sqrt (Nat.cast_nonneg _)]
    ring
  have hh := (hlogeq.div (IsEquivalent.refl (u := fun n : ℕ => log (n : ℝ)))).tendsto_nhds_iff.mpr hmain
  simpa only [Function.comp_apply,Real.nat_floor_real_sqrt_eq_nat_sqrt] using hh

lemma sqrt_naturalValue_tendsto_atTop {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    Tendsto (fun n : ℕ => (naturalValue f n).sqrt) atTop atTop := by
  have hv := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (naturalValue_tendsto_atTop hdeg hpos)
  have hh := (tendsto_nat_floor_atTop (α := ℝ)).comp (Real.tendsto_sqrt_atTop.comp hv)
  change Tendsto (fun n : ℕ => ⌊√(naturalValue f n : ℝ)⌋₊) atTop atTop at hh
  simpa only [Real.nat_floor_real_sqrt_eq_nat_sqrt] using hh

end GeneralDivisors


open Finset Real Filter Polynomial Asymptotics
open scoped Topology ArithmeticFunction.sigma

namespace MeanTransfer

lemma sum_log_Ioc_eq_log_factorial (N : ℕ) :
    (∑ n ∈ Ioc 0 N, log (n : ℝ)) = log (N.factorial : ℝ) := by
  rw [Sieve.sum_Ioc_zero_eq_range,Nat.factorial_eq_prod_range_add_one,Nat.cast_prod,
    Real.log_prod (fun n hn => by positivity)]

lemma sum_log_Ioc_bounds {N : ℕ} (hN : 0 < N) :
    (N : ℝ)*log N-N ≤ ∑ n ∈ Ioc 0 N, log (n : ℝ) ∧
      (∑ n ∈ Ioc 0 N, log (n : ℝ)) ≤ (N : ℝ)*log N := by
  constructor
  · rw [sum_log_Ioc_eq_log_factorial]
    have hh := Stirling.le_log_factorial_stirling hN.ne'
    have hlogN := Real.log_natCast_nonneg N
    have hlogπ : 0 ≤ log (2*π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  · calc
      _ ≤ ∑ _n ∈ Ioc 0 N, log (N : ℝ) := sum_le_sum (fun n hn =>
        Real.log_le_log (by exact_mod_cast (mem_Ioc.mp hn).1) (by exact_mod_cast (mem_Ioc.mp hn).2))
      _ = _ := by simp

lemma sum_log_Ioc_tendsto_atTop :
    Tendsto (fun N : ℕ => ∑ n ∈ Ioc 0 N, log (n : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [(Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop (2 : ℝ)),eventually_gt_atTop (0 : ℕ)] with N hlog hN
  change (2 : ℝ) ≤ log (N : ℝ) at hlog
  have hh := (sum_log_Ioc_bounds hN).1
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

lemma sum_log_Ioc_limit :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, log (n : ℝ))/((N : ℝ)*log N)) atTop (𝓝 1) := by
  have hzero : Tendsto (fun N : ℕ =>
      ((∑ n ∈ Ioc 0 N, log (n : ℝ))-(N : ℝ)*log N)/((N : ℝ)*log N)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ => 1/log N)
    · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
      have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have hlog : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
      have hbounds := sum_log_Ioc_bounds (by omega : 0 < N)
      have herr : |(∑ n ∈ Ioc 0 N, log (n : ℝ))-(N : ℝ)*log N| ≤ N := by
        apply abs_le.mpr
        constructor <;> linarith
      rw [Real.norm_eq_abs,abs_div,abs_of_pos (mul_pos hN0 hlog)]
      calc
        _ ≤ (N : ℝ)/((N : ℝ)*log N) := div_le_div_of_nonneg_right herr (mul_pos hN0 hlog).le
        _ = _ := by field_simp
    · exact tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hh := hzero.add_const 1
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hlog : log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  field_simp <;> ring

/-- A logarithmically growing sequence has the corresponding summatory asymptotic. -/
lemma summatory_of_log_mean {u : ℕ → ℝ} {c : ℝ}
    (hu : Tendsto (fun n : ℕ => u n/log n) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, u n)/((N : ℝ)*log N)) atTop (𝓝 c) := by
  let e := fun n : ℕ => u n-c*log n
  have he : Tendsto (fun n : ℕ => e n/log n) atTop (𝓝 0) := by
    have hh := hu.sub_const c
    rw [sub_self] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hlog : log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
    dsimp only [e]
    rw [sub_div,mul_div_cancel_right₀ _ hlog]
  have heo : e =o[atTop] (fun n : ℕ => log (n : ℝ)) := by
    apply (isLittleO_iff_tendsto' ?_).mpr he
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn hzero
    exact False.elim ((Real.log_pos (by exact_mod_cast hn)).ne' hzero)
  have heo' := heo.comp_tendsto (tendsto_add_atTop_nat 1)
  have hlogs : Tendsto (fun N : ℕ => ∑ i ∈ range N, log (i+1 : ℕ)) atTop atTop := by
    simpa only [Sieve.sum_Ioc_zero_eq_range] using sum_log_Ioc_tendsto_atTop
  have hsumo := heo'.sum_range (fun n => Real.log_natCast_nonneg _) hlogs
  have hsumratio : Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, e n)/((N : ℝ)*log N)) atTop (𝓝 0) := by
    have hh := hsumo.tendsto_div_nhds_zero.mul sum_log_Ioc_limit
    simp only [zero_mul] at hh
    apply hh.congr'
    filter_upwards [sum_log_Ioc_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with N hN
    simp only [Function.comp_apply,Sieve.sum_Ioc_zero_eq_range] at hN ⊢
    exact div_mul_div_cancel₀ hN.ne'
  have hh := hsumratio.add (sum_log_Ioc_limit.const_mul c)
  simp only [zero_add,mul_one] at hh
  convert hh using 1
  ext N
  simp only [e,sum_sub_distrib,← mul_sum]
  ring

end MeanTransfer


open Finset Real Filter Polynomial Asymptotics
open scoped Topology ArithmeticFunction.sigma

namespace GeneralDivisors
open Sieve

noncomputable def balancedRootTerm (f : ℤ[X]) (n : ℕ) : ℝ :=
  ∑ q ∈ Ioc 0 (naturalValue f n).sqrt, (polynomialRootCount f q : ℝ)/q

noncomputable def balancedRootModel (f : ℤ[X]) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, balancedRootTerm f n

noncomputable def balancedDiscrepancy (f : ℤ[X]) (N : ℕ) : ℝ :=
  halfSum f N-balancedRootModel f N

lemma balancedRootTerm_log_limit {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) {a : ℝ}
    (hmean : Tendsto (fun N : ℕ => (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ))/N)
      atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => balancedRootTerm f n/log n) atTop (𝓝 (a*(f.natDegree : ℝ)/2)) := by
  have hroot := (MeanTransfer.logarithmic_mean_Ioc_of_mean hmean).comp (sqrt_naturalValue_tendsto_atTop hdeg hpos)
  have hh := hroot.mul (sqrt_naturalValue_log_limit hdeg hpos)
  have hlimit : a*((f.natDegree : ℝ)/2) = a*(f.natDegree : ℝ)/2 := by ring
  rw [hlimit] at hh
  apply hh.congr'
  filter_upwards [(sqrt_naturalValue_tendsto_atTop hdeg hpos).eventually (eventually_gt_atTop (1 : ℕ))] with n hn
  have hlog : log ((naturalValue f n).sqrt : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  exact div_mul_div_cancel₀ hlog

lemma balancedRootModel_limit {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) {a : ℝ}
    (hmean : Tendsto (fun N : ℕ => (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ))/N)
      atTop (𝓝 a)) :
    Tendsto (fun N : ℕ => balancedRootModel f N/((N : ℝ)*log N))
      atTop (𝓝 (a*(f.natDegree : ℝ)/2)) :=
  MeanTransfer.summatory_of_log_mean (balancedRootTerm_log_limit hdeg hpos hmean)

lemma halfDivisorCount_eq_sum_sqrt (m : ℕ) :
    (halfDivisorCount m : ℝ) = ∑ q ∈ Ioc 0 m.sqrt, if q ∣ m then (1 : ℝ) else 0 := by
  by_cases hm : m = 0
  · simp [hm,halfDivisorCount]
  have hfin : {q ∈ m.divisors | q*q ≤ m} = {q ∈ Ioc 0 m.sqrt | q ∣ m} := by
    ext q
    simp only [mem_filter,Nat.mem_divisors,mem_Ioc,Nat.le_sqrt]
    constructor
    · rintro ⟨⟨hqm,_⟩,hq2⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hqm (Nat.pos_of_ne_zero hm),hq2⟩,hqm⟩
    · rintro ⟨⟨hq0,hq2⟩,hqm⟩
      exact ⟨⟨hqm,hm⟩,hq2⟩
  simp only [halfDivisorCount,hfin,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

lemma balancedDiscrepancy_expansion (f : ℤ[X]) (N : ℕ) :
    balancedDiscrepancy f N = (halfDivisorCount (naturalValue f 0) : ℝ) +
      ∑ n ∈ Ioc 0 N, ∑ q ∈ Ioc 0 (naturalValue f n).sqrt,
        ((if q ∣ naturalValue f n then (1 : ℝ) else 0)-(polynomialRootCount f q : ℝ)/q) := by
  rw [balancedDiscrepancy,halfSum_remove_zero]
  change (halfDivisorCount (naturalValue f 0) : ℝ)+
    (∑ n ∈ Ioc 0 N, (halfDivisorCount (naturalValue f n) : ℝ))-
      (∑ n ∈ Ioc 0 N, balancedRootTerm f n) = _
  rw [add_sub_assoc,← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro n hn
  rw [halfDivisorCount_eq_sum_sqrt,balancedRootTerm,← sum_sub_distrib]

/-- The signed variable-cutoff error is exactly what is needed for the expected
leading constant; this is a criterion, not an assertion of cancellation. -/
lemma expected_limit_iff_balancedDiscrepancy_zero {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) {a : ℝ}
    (hmean : Tendsto (fun N : ℕ => (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ))/N)
      atTop (𝓝 a)) :
    Tendsto (fun x : ℝ => Erdos975Sum f x/(x*log x)) atTop (𝓝 ((f.natDegree : ℝ)*a)) ↔
      Tendsto (fun N : ℕ => balancedDiscrepancy f N/((N : ℝ)*log N)) atTop (𝓝 0) := by
  have hmodel := balancedRootModel_limit hdeg hpos hmean
  have he : 2*(a*(f.natDegree : ℝ)/2) = (f.natDegree : ℝ)*a := by ring
  rw [← he,← halfSum_limit_iff]
  constructor
  · intro hh
    have ht := hh.sub hmodel
    simpa only [sub_self,balancedDiscrepancy,sub_div] using ht
  · intro hh
    have ht := hh.add hmodel
    simp only [zero_add] at ht
    convert ht using 1
    ext N
    dsimp only [balancedDiscrepancy]
    ring

lemma limit_of_balancedDiscrepancy {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) {a b : ℝ}
    (hmean : Tendsto (fun N : ℕ => (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ))/N)
      atTop (𝓝 a))
    (herr : Tendsto (fun N : ℕ => balancedDiscrepancy f N/((N : ℝ)*log N)) atTop (𝓝 b)) :
    Tendsto (fun x : ℝ => Erdos975Sum f x/(x*log x)) atTop (𝓝 ((f.natDegree : ℝ)*a+2*b)) := by
  have hmodel := balancedRootModel_limit hdeg hpos hmean
  have hh := herr.add hmodel
  have hhalf : Tendsto (fun N : ℕ => halfSum f N/((N : ℝ)*log N))
      atTop (𝓝 (b+a*(f.natDegree : ℝ)/2)) := by
    convert hh using 1
    ext N
    dsimp only [balancedDiscrepancy]
    ring
  convert (halfSum_limit_iff f _).mp hhalf using 1
  congr 1
  ring

lemma balancedDiscrepancy_minus_large_limit {f : ℤ[X]} (hdeg : 3 ≤ f.natDegree)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) {a : ℝ}
    (hmean : Tendsto (fun N : ℕ => (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ))/N)
      atTop (𝓝 a)) :
    Tendsto (fun N : ℕ => (balancedDiscrepancy f N-largeDivisorSum f N)/((N : ℝ)*log N))
      atTop (𝓝 (a-a*(f.natDegree : ℝ)/2)) := by
  have hh := ((halfSum_input_large_error_tendsto f (higher_degree_eventual_lower hdeg hpos)).add
    (inputDivisorSum_limit f hmean)).sub (balancedRootModel_limit (by omega) hpos hmean)
  simp only [zero_add] at hh
  convert hh using 1
  ext N
  dsimp only [balancedDiscrepancy]
  ring

end GeneralDivisors



open Finset Real Filter Polynomial Asymptotics
open scoped Topology ArithmeticFunction.sigma

namespace MeanTransfer

lemma summable_real_dirichlet_of_mean {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) {a : ℝ}
    (hmean : Tendsto (fun N : ℕ => (∑ q ∈ Ioc 0 N, u q)/N) atTop (𝓝 a))
    {s : ℝ} (hs : 0 < s) : Summable (fun q : ℕ => u q/(q : ℝ)^(1+s)) := by
  have hioc (N : ℕ) : Icc 1 N = Ioc 0 N := by ext q; simp only [mem_Icc,mem_Ioc]; omega
  have hO : (fun N : ℕ => ∑ q ∈ Icc 1 N, u q) =O[atTop] fun N : ℕ => (N : ℝ)^(1 : ℝ) :=
    isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa only [hioc,Real.rpow_one] using hmean)
  have hc := LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := ((1+s : ℝ) : ℂ)) hO hu (by norm_num) (by simpa using hs)
  change Summable (LSeries.term (fun n => (u n : ℂ)) ((1+s : ℝ) : ℂ)) at hc
  apply hc.norm.congr
  intro q
  rw [LSeries.norm_term_eq]
  simp only [Complex.ofReal_re,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hu q)]
  by_cases hq : q = 0
  · simp [hq,Real.zero_rpow (show 1+s ≠ 0 by linarith)]
  · simp [hq]

lemma real_dirichlet_ofReal (u : ℕ → ℝ) {t : ℝ} (ht : 0 < t) :
    LSeries (fun n => (u n : ℂ)) (t : ℂ) = ((∑' q : ℕ, u q/(q : ℝ)^t : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro q
  rw [LSeries.term_of_ne_zero' (Complex.ofReal_ne_zero.mpr ht.ne')]
  simp only [Complex.ofReal_div,Complex.ofReal_cpow (Nat.cast_nonneg q),Complex.ofReal_natCast]

lemma real_dirichlet_residue_of_mean {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) {a : ℝ}
    (hmean : Tendsto (fun N : ℕ => (∑ q ∈ Ioc 0 N, u q)/N) atTop (𝓝 a)) :
    Tendsto (fun s : ℝ => s*(∑' q : ℕ, u q/(q : ℝ)^(1+s))) (𝓝[>] 0) (𝓝 a) := by
  have hioc (N : ℕ) : Icc 1 N = Ioc 0 N := by ext q; simp only [mem_Icc,mem_Ioc]; omega
  have hh := LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg u
    (by simpa only [hioc] using hmean) hu
  have hshift : Tendsto (fun s : ℝ => 1+s) (𝓝[>] 0) (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have ht : Tendsto (fun s : ℝ => 1+s) (𝓝 0) (𝓝 (1+0)) := tendsto_const_nhds.add tendsto_id
      simpa only [add_zero] using ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change 0 < s at hs
      change 1 < 1+s
      linarith
  have hc := (Complex.continuous_re.tendsto (a : ℂ)).comp (hh.comp hshift)
  simp only [Complex.ofReal_re] at hc
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change 0 < s at hs
  dsimp only [Function.comp_apply]
  rw [real_dirichlet_ofReal u (by linarith : 0 < 1+s)]
  rw [← Complex.ofReal_one,← Complex.ofReal_sub,← Complex.ofReal_mul,Complex.ofReal_re]
  ring

end MeanTransfer

namespace GeneralDivisors

noncomputable def regularizedRootMean (f : ℤ[X]) (s : ℝ) : ℝ :=
  ∑' q : ℕ, (polynomialRootCount f q : ℝ)/(q : ℝ)^(1+s)

lemma regularizedRootMean_summable {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) {s : ℝ} (hs : 0 < s) :
    Summable (fun q : ℕ => (polynomialRootCount f q : ℝ)/(q : ℝ)^(1+s)) := by
  obtain ⟨a,ha,hmean⟩ := polynomialRootCount_mean_positive f hdeg hirr
  exact MeanTransfer.summable_real_dirichlet_of_mean (fun _ => Nat.cast_nonneg _) hmean hs

lemma regularizedRootMean_residue {f : ℤ[X]} {a : ℝ}
    (hmean : Tendsto (fun N : ℕ => (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ))/N) atTop (𝓝 a)) :
    Tendsto (fun s : ℝ => s*regularizedRootMean f s) (𝓝[>] 0) (𝓝 a) :=
  MeanTransfer.real_dirichlet_residue_of_mean (fun _ => Nat.cast_nonneg _) hmean

end GeneralDivisors


open Finset Real Filter Polynomial Asymptotics
open scoped Topology ArithmeticFunction.sigma

namespace GeneralDivisors
open Sieve

def positiveDivisibleCount (f : ℤ[X]) (q N : ℕ) : ℕ :=
  {n ∈ Ioc 0 N | q ∈ (naturalValue f n).divisors}.card

lemma positiveDivisibleCount_le (f : ℤ[X]) (q N : ℕ) :
    positiveDivisibleCount f q N ≤ divisibleValueCount f q N := by
  apply card_le_card
  intro n hn
  obtain ⟨hn,hq⟩ := mem_filter.mp hn
  have hd := Nat.mem_divisors.mp hq
  exact mem_filter.mpr ⟨hn,(dvd_naturalValue_iff (Nat.pos_of_ne_zero hd.2) q).mp hd.1⟩

lemma positiveDivisibleCount_error {f : ℤ[X]} (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    ∃ K : ℕ, ∀ q N : ℕ, |(positiveDivisibleCount f q N : ℝ)-divisibleValueCount f q N| ≤ K := by
  have hev := (tendsto_natCast_atTop_atTop (R := ℤ)).eventually hpos
  obtain ⟨K,hK⟩ := eventually_atTop.mp hev
  refine ⟨K,?_⟩
  intro q N
  let A := {n ∈ Ioc 0 N | q ∈ (naturalValue f n).divisors}
  let B := {n ∈ Ioc 0 N | (q : ℤ) ∣ f.eval ((n : ℕ) : ℤ)}
  have hsub : B ⊆ A ∪ Ioc 0 K := by
    intro n hn
    obtain ⟨hnInt,hdiv⟩ := mem_filter.mp hn
    by_cases hnK : n ≤ K
    · exact mem_union_right _ (mem_Ioc.mpr ⟨(mem_Ioc.mp hnInt).1,hnK⟩)
    · have hval : 0 < naturalValue f n := by
        have hh : 1 ≤ naturalValue f n := Nat.le_floor (hK n (by omega))
        omega
      exact mem_union_left _ (mem_filter.mpr ⟨hnInt,Nat.mem_divisors.mpr
        ⟨(dvd_naturalValue_iff hval q).mpr hdiv,hval.ne'⟩⟩)
  have hcard : B.card ≤ A.card+K := (card_le_card hsub).trans (by simpa using card_union_le A (Ioc 0 K))
  have hle' : (A.card : ℝ) ≤ B.card := by exact_mod_cast positiveDivisibleCount_le f q N
  have hc : (B.card : ℝ) ≤ (A.card : ℝ)+K := by exact_mod_cast hcard
  change |(A.card : ℝ)-B.card| ≤ K
  rw [abs_of_nonpos (sub_nonpos.mpr hle')]
  linarith

lemma positiveDivisibleCount_limit {f : ℤ[X]} (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n)
    {q : ℕ} (hq : 0 < q) :
    Tendsto (fun N : ℕ => (positiveDivisibleCount f q N : ℝ)/N)
      atTop (𝓝 ((polynomialRootCount f q : ℝ)/q)) := by
  obtain ⟨K,hK⟩ := positiveDivisibleCount_error hpos
  have hz : Tendsto (fun N : ℕ => (positiveDivisibleCount f q N : ℝ)/N-
      (polynomialRootCount f q : ℝ)/q) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ => ((K : ℝ)+2*polynomialRootCount f q)/N)
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hqr : (0 : ℝ) < q := by exact_mod_cast hq
      have he : (positiveDivisibleCount f q N : ℝ)/N-(polynomialRootCount f q : ℝ)/q =
          ((positiveDivisibleCount f q N : ℝ)-(N : ℝ)/q*polynomialRootCount f q)/N := by field_simp
      have hb : |(positiveDivisibleCount f q N : ℝ)-(N : ℝ)/q*polynomialRootCount f q| ≤
          (K : ℝ)+2*polynomialRootCount f q := by
        calc
          _ = |((positiveDivisibleCount f q N : ℝ)-divisibleValueCount f q N)+
              ((divisibleValueCount f q N : ℝ)-(N : ℝ)/q*polynomialRootCount f q)| := by congr 1; ring
          _ ≤ |(positiveDivisibleCount f q N : ℝ)-divisibleValueCount f q N|+
              |(divisibleValueCount f q N : ℝ)-(N : ℝ)/q*polynomialRootCount f q| := abs_add_le _ _
          _ ≤ _ := add_le_add (hK q N) (polynomial_root_count_error f hq N)
      rw [Real.norm_eq_abs,he,abs_div,abs_of_pos hNr]
      exact div_le_div_of_nonneg_right hb hNr.le
    · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := hz.add_const ((polynomialRootCount f q : ℝ)/q)
  simpa only [zero_add,sub_add_cancel] using hh

lemma positiveDivisibleCount_density_bound (f : ℤ[X]) {q N : ℕ} (hq : 0 < q) (hqN : q ≤ N) :
    (positiveDivisibleCount f q N : ℝ)/N ≤ 3*(polynomialRootCount f q : ℝ)/q := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hNr : (0 : ℝ) < N := by exact_mod_cast hq.trans_le hqN
  have hratio : 1 ≤ (N : ℝ)/q := (one_le_div hqr).mpr (by exact_mod_cast hqN)
  have hcount : (positiveDivisibleCount f q N : ℝ) ≤ 3*((N : ℝ)/q)*polynomialRootCount f q := by
    have h0 : (positiveDivisibleCount f q N : ℝ) ≤ divisibleValueCount f q N := by
      exact_mod_cast positiveDivisibleCount_le f q N
    have he := (abs_le.mp (polynomial_root_count_error f hq N)).2
    have hρ : (0 : ℝ) ≤ polynomialRootCount f q := Nat.cast_nonneg _
    nlinarith
  calc
    _ ≤ (3*((N : ℝ)/q)*polynomialRootCount f q)/N := div_le_div_of_nonneg_right hcount hNr.le
    _ = _ := by field_simp

lemma weighted_root_density (f : ℤ[X]) {q : ℕ} (hq : 0 < q) (s : ℝ) :
    (q : ℝ)^(-s)*((polynomialRootCount f q : ℝ)/q) =
      (polynomialRootCount f q : ℝ)/(q : ℝ)^(1+s) := by
  rw [Real.rpow_add (by exact_mod_cast hq),Real.rpow_one,Real.rpow_neg (Nat.cast_nonneg q)]
  ring

noncomputable def truncatedWeightedDivisorSum (f : ℤ[X]) (s : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ Ioc 0 N, (q : ℝ)^(-s)*positiveDivisibleCount f q N

lemma truncatedWeightedDivisorSum_limit {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℕ => truncatedWeightedDivisorSum f s N/N) atTop (𝓝 (regularizedRootMean f s)) := by
  classical
  let g := fun N q : ℕ => if q ∈ Ioc 0 N then
    (q : ℝ)^(-s)*((positiveDivisibleCount f q N : ℝ)/N) else 0
  let bound := fun q : ℕ => 3*((polynomialRootCount f q : ℝ)/(q : ℝ)^(1+s))
  have hsum : Summable bound := (regularizedRootMean_summable hdeg hirr hs).mul_left 3
  have hlim (q : ℕ) : Tendsto (fun N : ℕ => g N q) atTop
      (𝓝 ((polynomialRootCount f q : ℝ)/(q : ℝ)^(1+s))) := by
    by_cases hq : q = 0
    · simp only [hq,mem_Ioc,lt_self_iff_false,false_and,if_false,g,Nat.cast_zero,
        Real.zero_rpow (by linarith : 1+s ≠ 0),div_zero]
      exact tendsto_const_nhds
    · have hh := (positiveDivisibleCount_limit hpos (Nat.pos_of_ne_zero hq)).const_mul ((q : ℝ)^(-s))
      rw [weighted_root_density f (Nat.pos_of_ne_zero hq) s] at hh
      apply hh.congr'
      filter_upwards [eventually_ge_atTop q] with N hN
      simp only [g,if_pos (mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hq,hN⟩)]
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ‖g N q‖ ≤ bound q := by
    apply Eventually.of_forall
    intro N q
    dsimp only [g,bound]
    split_ifs with hq
    · have hqpos := (mem_Ioc.mp hq).1
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have hh := mul_le_mul_of_nonneg_left
        (positiveDivisibleCount_density_bound f hqpos (mem_Ioc.mp hq).2)
        (Real.rpow_nonneg (Nat.cast_nonneg q) (-s))
      convert hh using 1
      rw [← weighted_root_density f hqpos s]
      ring
    · rw [norm_zero]
      positivity
  have hh := tendsto_tsum_of_dominated_convergence hsum hlim hbound
  convert hh using 1
  ext N
  rw [tsum_eq_sum (s := Ioc 0 N) (fun q hq => by simp only [g,if_neg hq])]
  simp only [g]
  rw [truncatedWeightedDivisorSum,sum_div]
  apply sum_congr rfl
  intro q hq
  rw [if_pos hq]
  ring

end GeneralDivisors


open Finset Real Filter Polynomial Asymptotics
open scoped Topology ArithmeticFunction.sigma

namespace GeneralDivisors
open Sieve

noncomputable def weightedDivisorCount (m : ℕ) (s : ℝ) : ℝ :=
  ∑ q ∈ m.divisors, (q : ℝ)^(-s)

noncomputable def weightedDivisorSum (f : ℤ[X]) (s : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, weightedDivisorCount (naturalValue f n) s

lemma weightedDivisorCount_nonneg (m : ℕ) (s : ℝ) : 0 ≤ weightedDivisorCount m s :=
  sum_nonneg (fun q _ => Real.rpow_nonneg (Nat.cast_nonneg q) _)

lemma weightedDivisorCount_zero (m : ℕ) : weightedDivisorCount m 0 = (σ 0 m : ℝ) := by
  simp only [weightedDivisorCount,neg_zero,Real.rpow_zero,sum_const,nsmul_eq_mul,mul_one,
    ArithmeticFunction.sigma_zero_apply]

lemma truncatedWeightedDivisorSum_eq (f : ℤ[X]) (s : ℝ) (N : ℕ) :
    truncatedWeightedDivisorSum f s N = ∑ n ∈ Ioc 0 N,
      ∑ q ∈ (naturalValue f n).divisors with q ≤ N, (q : ℝ)^(-s) := by
  have hcount (q : ℕ) : (q : ℝ)^(-s)*positiveDivisibleCount f q N =
      ∑ n ∈ Ioc 0 N, if q ∈ (naturalValue f n).divisors then (q : ℝ)^(-s) else 0 := by
    simp only [positiveDivisibleCount,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
      mul_sum,mul_ite,mul_one,mul_zero]
  rw [truncatedWeightedDivisorSum]
  simp only [hcount]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  rw [← sum_filter]
  congr 1
  ext q
  simp only [mem_filter,mem_Ioc]
  constructor
  · rintro ⟨⟨_,hqN⟩,hdiv⟩
    exact ⟨hdiv,hqN⟩
  · rintro ⟨hdiv,hqN⟩
    exact ⟨⟨Nat.pos_of_mem_divisors hdiv,hqN⟩,hdiv⟩

lemma weightedDivisorSum_tail_eq (f : ℤ[X]) (s : ℝ) (N : ℕ) :
    weightedDivisorSum f s N-truncatedWeightedDivisorSum f s N =
      ∑ n ∈ Ioc 0 N, ∑ q ∈ (naturalValue f n).divisors with N < q, (q : ℝ)^(-s) := by
  rw [weightedDivisorSum,truncatedWeightedDivisorSum_eq,← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  have hh := sum_filter_add_sum_filter_not (s := (naturalValue f n).divisors)
    (p := fun q => q ≤ N) (f := fun q => (q : ℝ)^(-s))
  simp only [not_le] at hh
  dsimp only [weightedDivisorCount]
  linarith

lemma weightedDivisorSum_tail_nonneg (f : ℤ[X]) (s : ℝ) (N : ℕ) :
    0 ≤ weightedDivisorSum f s N-truncatedWeightedDivisorSum f s N := by
  rw [weightedDivisorSum_tail_eq]
  exact sum_nonneg (fun _ _ => sum_nonneg (fun q _ => Real.rpow_nonneg (Nat.cast_nonneg q) _))

lemma weightedDivisorSum_tail_bound (f : ℤ[X]) {s : ℝ} (hs : 0 ≤ s) {N : ℕ} (hN : 0 < N) :
    weightedDivisorSum f s N-truncatedWeightedDivisorSum f s N ≤
      (N : ℝ)^(-s)*(∑ n ∈ Ioc 0 N, (σ 0 (naturalValue f n) : ℝ)) := by
  rw [weightedDivisorSum_tail_eq,mul_sum]
  apply sum_le_sum
  intro n hn
  calc
    _ ≤ ∑ _q ∈ (naturalValue f n).divisors with N < _q, (N : ℝ)^(-s) := by
      apply sum_le_sum
      intro q hq
      exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hN)
        (by exact_mod_cast (mem_filter.mp hq).2.le) (neg_nonpos.mpr hs)
    _ ≤ ∑ _q ∈ (naturalValue f n).divisors, (N : ℝ)^(-s) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = _ := by rw [sum_const,nsmul_eq_mul,ArithmeticFunction.sigma_zero_apply,mul_comm]

lemma weightedDivisorSum_tail_limit {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℕ => (weightedDivisorSum f s N-truncatedWeightedDivisorSum f s N)/N)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := polynomial_divisor_sum_upper_nat hdeg hirr
  apply squeeze_zero_norm' (a := fun N : ℕ => C*(log (N : ℝ)/(N : ℝ)^s))
  · filter_upwards [hbound,eventually_gt_atTop (0 : ℕ)] with N hN hN0
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (weightedDivisorSum_tail_nonneg f s N) hNr.le)]
    calc
      _ ≤ ((N : ℝ)^(-s)*(∑ n ∈ Ioc 0 N, (σ 0 (naturalValue f n) : ℝ)))/N :=
        div_le_div_of_nonneg_right (weightedDivisorSum_tail_bound f hs.le hN0) hNr.le
      _ ≤ ((N : ℝ)^(-s)*(C*(N : ℝ)*log N))/N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg hNr.le _)) hNr.le
      _ = _ := by rw [Real.rpow_neg hNr.le]; field_simp
  · simpa only [Function.comp_apply, mul_zero] using
      ((isLittleO_log_rpow_atTop hs).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul C

/-- Every fixed positive divisor exponent has an ordinary mean. This does not
assert the uniformity at exponent zero needed for the original conjecture. -/
lemma weightedDivisorSum_limit {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℕ => weightedDivisorSum f s N/N) atTop (𝓝 (regularizedRootMean f s)) := by
  have hh := (truncatedWeightedDivisorSum_limit hdeg hirr hpos hs).add
    (weightedDivisorSum_tail_limit hdeg hirr hs)
  simp only [add_zero] at hh
  convert hh using 1
  ext N
  ring

lemma regularizedRootMean_one_le {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) {s : ℝ} (hs : 0 < s) : 1 ≤ regularizedRootMean f s := by
  have hh := (regularizedRootMean_summable hdeg hirr hs).le_tsum 1 (fun q _ => by positivity)
  simpa only [polynomialRootCount_one,Nat.cast_one,Real.one_rpow,div_one,regularizedRootMean] using hh

lemma weightedDivisor_mean_and_residue {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    (∀ s : ℝ, 0 < s → Tendsto (fun N : ℕ => weightedDivisorSum f s N/N) atTop (𝓝 (regularizedRootMean f s))) ∧
      ∃ a > (0 : ℝ), Tendsto (fun s : ℝ => s*regularizedRootMean f s) (𝓝[>] 0) (𝓝 a) := by
  refine ⟨fun s hs => weightedDivisorSum_limit hdeg hirr hpos hs,?_⟩
  obtain ⟨a,ha,hmean⟩ := polynomialRootCount_mean_positive f hdeg hirr
  exact ⟨a,ha,regularizedRootMean_residue hmean⟩

end GeneralDivisors


/- Uniform regularization outside the critical exponent range. -/

open Finset Real Filter Polynomial Asymptotics
open scoped Topology ArithmeticFunction.sigma

namespace GeneralDivisors
open Sieve

noncomputable def truncatedRootMean (f : ℤ[X]) (s : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)/(q : ℝ)^(1+s)

lemma truncatedWeightedDivisorSum_error {f : ℤ[X]}
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    ∃ K : ℕ, ∀ {s : ℝ}, 0 ≤ s → ∀ {N : ℕ}, 0 < N →
      |truncatedWeightedDivisorSum f s N/N-truncatedRootMean f s N| ≤
        (K : ℝ)+2*(∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ))/N := by
  obtain ⟨K,hK⟩ := positiveDivisibleCount_error hpos
  refine ⟨K,?_⟩
  intro s hs N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : truncatedWeightedDivisorSum f s N/N-truncatedRootMean f s N =
      (∑ q ∈ Ioc 0 N, (q : ℝ)^(-s)*
        ((positiveDivisibleCount f q N : ℝ)-(N : ℝ)/q*polynomialRootCount f q))/N := by
    rw [truncatedWeightedDivisorSum,truncatedRootMean,sum_div,← sum_sub_distrib,sum_div]
    apply sum_congr rfl
    intro q hq
    rw [← weighted_root_density f (mem_Ioc.mp hq).1 s]
    field_simp
  rw [heq,abs_div,abs_of_pos hNr]
  have hb : |∑ q ∈ Ioc 0 N, (q : ℝ)^(-s)*
      ((positiveDivisibleCount f q N : ℝ)-(N : ℝ)/q*polynomialRootCount f q)| ≤
      (K : ℝ)*N+2*(∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)) := by
    calc
      _ ≤ ∑ q ∈ Ioc 0 N, |(q : ℝ)^(-s)*
          ((positiveDivisibleCount f q N : ℝ)-(N : ℝ)/q*polynomialRootCount f q)| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ Ioc 0 N, ((K : ℝ)+2*polynomialRootCount f q) := by
        apply sum_le_sum
        intro q hq
        have hq0 := (mem_Ioc.mp hq).1
        have hqe : |(positiveDivisibleCount f q N : ℝ)-(N : ℝ)/q*polynomialRootCount f q| ≤
            (K : ℝ)+2*polynomialRootCount f q := by
          calc
            _ = |((positiveDivisibleCount f q N : ℝ)-divisibleValueCount f q N)+
                ((divisibleValueCount f q N : ℝ)-(N : ℝ)/q*polynomialRootCount f q)| := by congr 1; ring
            _ ≤ |(positiveDivisibleCount f q N : ℝ)-divisibleValueCount f q N|+
                |(divisibleValueCount f q N : ℝ)-(N : ℝ)/q*polynomialRootCount f q| := abs_add_le _ _
            _ ≤ _ := add_le_add (hK q N) (polynomial_root_count_error f hq0 N)
        rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) _)]
        exact (mul_le_mul_of_nonneg_left hqe (Real.rpow_nonneg (Nat.cast_nonneg q) _)).trans
          (by
            simpa using mul_le_mul_of_nonneg_right
              (Real.rpow_le_one_of_one_le_of_nonpos
                (show (1 : ℝ) ≤ q by exact_mod_cast hq0) (neg_nonpos.mpr hs))
              (show 0 ≤ (K : ℝ)+2*polynomialRootCount f q by positivity))
      _ = _ := by rw [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul]; simp; ring
  calc
    _ ≤ ((K : ℝ)*N+2*(∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ)))/N :=
      div_le_div_of_nonneg_right hb hNr.le
    _ = _ := by field_simp

lemma regularizedRootMean_tail_nonneg {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) {s : ℝ} (hs : 0 < s) (N : ℕ) :
    0 ≤ regularizedRootMean f s-truncatedRootMean f s N := by
  exact sub_nonneg.mpr ((regularizedRootMean_summable hdeg hirr hs).sum_le_tsum _
    (fun q _ => by positivity))

lemma regularizedRootMean_tail_bound {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    regularizedRootMean f s-truncatedRootMean f s N ≤
      (N : ℝ)^(-(s/2))*regularizedRootMean f (s/2) := by
  classical
  let u : ℕ → ℝ := fun q => (polynomialRootCount f q : ℝ)/(q : ℝ)^(1+s)
  let v : ℕ → ℝ := fun q => (polynomialRootCount f q : ℝ)/(q : ℝ)^(1+s/2)
  let S : Set ℕ := (↑(Ioc 0 N) : Set ℕ)ᶜ
  have hu : Summable u := regularizedRootMean_summable hdeg hirr hs
  have hv : Summable v := regularizedRootMean_summable hdeg hirr (half_pos hs)
  have hEq : regularizedRootMean f s-truncatedRootMean f s N = ∑' q : S, u q := by
    have hh := hu.sum_add_tsum_compl (s := Ioc 0 N)
    change truncatedRootMean f s N+(∑' q : S, u q) = regularizedRootMean f s at hh
    linarith
  rw [hEq]
  have hle : ∀ q : S, u q ≤ (N : ℝ)^(-(s/2))*v q := by
    intro q
    by_cases hq0 : (q : ℕ) = 0
    · simp only [u,v,hq0,Nat.cast_zero,Real.zero_rpow (show 1+s ≠ 0 by linarith),
        Real.zero_rpow (show 1+s/2 ≠ 0 by linarith),div_zero,mul_zero,le_refl]
    · have hqN : N < (q : ℕ) := by
        have hh := q.property
        change (q : ℕ) ∉ Ioc 0 N at hh
        simp only [mem_Ioc,not_and,not_le] at hh
        exact hh (Nat.pos_of_ne_zero hq0)
      have hqr : (0 : ℝ) < (q : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
      have hsplit : u q = ((q : ℕ) : ℝ)^(-(s/2))*v q := by
        dsimp only [u,v]
        have hexp : 1+s = (1+s/2)+s/2 := by ring
        rw [hexp,Real.rpow_add hqr,Real.rpow_neg hqr.le]
        ring
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos
        (by exact_mod_cast hN) (by exact_mod_cast hqN.le) (by linarith)) (by dsimp only [v]; positivity)
  calc
    _ ≤ ∑' q : S, (N : ℝ)^(-(s/2))*v q :=
      (hu.subtype S).tsum_le_tsum hle ((hv.subtype S).mul_left _)
    _ = (N : ℝ)^(-(s/2))*(∑' q : S, v q) := tsum_mul_left
    _ ≤ (N : ℝ)^(-(s/2))*regularizedRootMean f (s/2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      have hh := hv.sum_add_tsum_compl (s := Ioc 0 N)
      change truncatedRootMean f (s/2) N+(∑' q : S, v q) = regularizedRootMean f (s/2) at hh
      have hn : 0 ≤ truncatedRootMean f (s/2) N := sum_nonneg (fun q _ => by positivity)
      linarith

end GeneralDivisors


/- Uniform limits outside the critical exponent range. -/

open Finset Real Filter Polynomial Asymptotics
open scoped Topology ArithmeticFunction.sigma

namespace GeneralDivisors
open Sieve

lemma varying_truncatedWeightedDivisorSum_error_limit {f : ℤ[X]}
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) {a : ℝ}
    (hmean : Tendsto (fun N : ℕ => (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ))/N)
      atTop (𝓝 a)) {s : ℕ → ℝ}
    (hs0 : Tendsto s atTop (𝓝 0)) (hspos : ∀ᶠ N in atTop, 0 ≤ s N) :
    Tendsto (fun N : ℕ => s N*(truncatedWeightedDivisorSum f (s N) N/N-
      truncatedRootMean f (s N) N)) atTop (𝓝 0) := by
  obtain ⟨K,hK⟩ := truncatedWeightedDivisorSum_error hpos
  apply squeeze_zero_norm' (a := fun N : ℕ =>
    s N*((K : ℝ)+2*(∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ))/N))
  · filter_upwards [hspos,eventually_gt_atTop (0 : ℕ)] with N hsN hN
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hsN]
    exact mul_le_mul_of_nonneg_left (hK hsN hN) hsN
  · simpa only [zero_mul,mul_div_assoc] using hs0.mul ((hmean.const_mul 2).const_add (K : ℝ))

lemma varying_weightedDivisorSum_tail_limit {f : ℤ[X]}
    (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) {s : ℕ → ℝ}
    (hspos : ∀ᶠ N in atTop, 0 ≤ s N)
    (hscale : Tendsto (fun N : ℕ => s N*log N) atTop atTop) :
    Tendsto (fun N : ℕ => s N*(weightedDivisorSum f (s N) N-
      truncatedWeightedDivisorSum f (s N) N)/N) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := polynomial_divisor_sum_upper_nat hdeg hirr
  apply squeeze_zero_norm' (a := fun N : ℕ => C*((s N*log N)*exp (-(s N*log N))))
  · filter_upwards [hbound,hspos,eventually_gt_atTop (0 : ℕ)] with N hN hsN hN0
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (mul_nonneg hsN
      (weightedDivisorSum_tail_nonneg f (s N) N)) hNr.le)]
    calc
      _ ≤ (s N*((N : ℝ)^(-(s N))*(∑ n ∈ Ioc 0 N, (σ 0 (naturalValue f n) : ℝ))))/N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (weightedDivisorSum_tail_bound f hsN hN0) hsN) hNr.le
      _ ≤ (s N*((N : ℝ)^(-(s N))*(C*(N : ℝ)*log N)))/N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg hNr.le _)) hsN) hNr.le
      _ = _ := by
        rw [Real.rpow_def_of_pos hNr]
        have he : log (N : ℝ)*(-s N) = -(s N*log N) := by ring
        rw [he]
        field_simp
  · simpa only [Function.comp_apply,pow_one,mul_zero] using
      ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale).const_mul C

lemma varying_regularizedRootMean_tail_limit {f : ℤ[X]}
    (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) {a : ℝ}
    (hmean : Tendsto (fun N : ℕ => (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ))/N)
      atTop (𝓝 a)) {s : ℕ → ℝ}
    (hs0 : Tendsto s atTop (𝓝 0)) (hspos : ∀ᶠ N in atTop, 0 < s N)
    (hscale : Tendsto (fun N : ℕ => s N*log N) atTop atTop) :
    Tendsto (fun N : ℕ => s N*(regularizedRootMean f (s N)-
      truncatedRootMean f (s N) N)) atTop (𝓝 0) := by
  have hhalf : Tendsto (fun N => s N/2) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa only [zero_div] using hs0.div_const 2,?_⟩
    filter_upwards [hspos] with N hN
    exact half_pos hN
  have hres := (regularizedRootMean_residue hmean).comp hhalf
  have hpow : Tendsto (fun N : ℕ => (N : ℝ)^(-(s N/2))) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hscale.atTop_mul_const (show (0 : ℝ) < 1/2 by norm_num))
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    rw [Real.rpow_def_of_pos (show (0 : ℝ) < N by exact_mod_cast hN)]
    dsimp only [Function.comp_apply]
    congr 1
    ring
  apply squeeze_zero_norm' (a := fun N : ℕ =>
    2*((N : ℝ)^(-(s N/2)))*((s N/2)*regularizedRootMean f (s N/2)))
  · filter_upwards [hspos,eventually_gt_atTop (0 : ℕ)] with N hsN hN
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hsN.le
      (regularizedRootMean_tail_nonneg hdeg hirr hsN N))]
    have hh := mul_le_mul_of_nonneg_left (regularizedRootMean_tail_bound hdeg hirr hsN hN) hsN.le
    convert hh using 1 <;> ring
  · simpa only [mul_zero,zero_mul,Function.comp_apply] using (hpow.const_mul 2).mul hres

/-- A joint limit for exponents tending to zero more slowly than `1 / log N`.
This does not assert a limit in the critical range `s * log N = O(1)`. -/
lemma weightedDivisorSum_supercritical_limit {f : ℤ[X]}
    (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) {a : ℝ}
    (hmean : Tendsto (fun N : ℕ => (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ))/N)
      atTop (𝓝 a)) {s : ℕ → ℝ}
    (hs0 : Tendsto s atTop (𝓝 0)) (hspos : ∀ᶠ N in atTop, 0 < s N)
    (hscale : Tendsto (fun N : ℕ => s N*log N) atTop atTop) :
    Tendsto (fun N : ℕ => s N*weightedDivisorSum f (s N) N/N) atTop (𝓝 a) := by
  have hsnonneg : ∀ᶠ N in atTop, 0 ≤ s N := hspos.mono (fun _ h => h.le)
  have htail := varying_weightedDivisorSum_tail_limit hdeg hirr hsnonneg hscale
  have herror := varying_truncatedWeightedDivisorSum_error_limit hpos hmean hs0 hsnonneg
  have hroot := varying_regularizedRootMean_tail_limit hdeg hirr hmean hs0 hspos hscale
  have hswithin : Tendsto s atTop (𝓝[>] (0 : ℝ)) := tendsto_nhdsWithin_iff.mpr ⟨hs0,hspos⟩
  have hres := (regularizedRootMean_residue hmean).comp hswithin
  have hh := ((htail.add herror).sub hroot).add hres
  simp only [add_zero,sub_zero,zero_add] at hh
  convert hh using 1
  ext N
  dsimp only [Function.comp_apply]
  ring

end GeneralDivisors


/- Abel summation with a varying bounded decreasing weight. -/

open Finset Real Filter Polynomial Asymptotics
open scoped Topology ArithmeticFunction.sigma

namespace MeanTransfer

lemma abs_weighted_sum_le_of_partial {u w : ℕ → ℝ} {N : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hu : ∀ n ≤ N, |∑ i ∈ range n, u i| ≤ B)
    (hw : Antitone w) (hw0 : ∀ i, 0 ≤ w i) :
    |∑ i ∈ range N, w i*u i| ≤ B*w 0 := by
  by_cases hN : N = 0
  · subst N
    simpa using mul_nonneg hB (hw0 0)
  have heq := sum_range_by_parts w u N
  simp only [smul_eq_mul] at heq
  rw [heq]
  calc
    _ ≤ |w (N-1)*∑ i ∈ range N, u i|+
        |∑ i ∈ range (N-1), (w (i+1)-w i)*∑ j ∈ range (i+1), u j| := abs_sub _ _
    _ ≤ w (N-1)*B+∑ i ∈ range (N-1), (w i-w (i+1))*B := by
      apply add_le_add
      · rw [abs_mul,abs_of_nonneg (hw0 _)]
        exact mul_le_mul_of_nonneg_left (hu N le_rfl) (hw0 _)
      · apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro i hi
        rw [abs_mul,abs_of_nonpos (sub_nonpos.mpr (hw (Nat.le_succ i))),neg_sub]
        exact mul_le_mul_of_nonneg_left (hu (i+1) (by have := mem_range.mp hi; omega))
          (sub_nonneg.mpr (hw (Nat.le_succ i)))
    _ = B*w 0 := by rw [← sum_mul,sum_range_sub']; ring

lemma varying_antitone_log_mean_zero {u : ℕ → ℝ}
    (hu : Tendsto (fun N : ℕ => (∑ i ∈ range N, u i)/log N) atTop (𝓝 0))
    {w : ℕ → ℕ → ℝ}
    (hw : ∀ᶠ N in atTop, Antitone (w N) ∧ (∀ i, 0 ≤ w N i) ∧ w N 0 ≤ 1) :
    Tendsto (fun N : ℕ => (∑ i ∈ range N, w N i*u i)/log N) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have heps : 0 < ε/2 := half_pos hε
  have hun := hu.norm
  simp only [norm_zero] at hun
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    ((hun.eventually (eventually_lt_nhds heps)).and (eventually_ge_atTop (2 : ℕ)))
  let C : ℝ := ∑ k ∈ range K, |∑ i ∈ range k, u i|
  have hC : 0 ≤ C := sum_nonneg (fun _ _ => abs_nonneg _)
  have hct : Tendsto (fun N : ℕ => C/log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((hct.eventually (eventually_lt_nhds heps)).and hw)
  refine ⟨max (max K T) 2,?_⟩
  intro N hN
  have hNK : K ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNT : T ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hlog : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hB : 0 ≤ C+(ε/2)*log N := by positivity
  have hp : ∀ k ≤ N, |∑ i ∈ range k, u i| ≤ C+(ε/2)*log N := by
    intro k hkN
    by_cases hkK : k < K
    · have hk : |∑ i ∈ range k, u i| ≤ C := by
        dsimp only [C]
        exact single_le_sum (fun j _ => abs_nonneg (∑ i ∈ range j, u i)) (mem_range.mpr hkK)
      exact hk.trans (le_add_of_nonneg_right (mul_nonneg heps.le hlog.le))
    · have hh := hK k (by omega)
      have hkl : 0 < log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
      have he' : |∑ i ∈ range k, u i| ≤ (ε/2)*log k := by
        have he' := hh.1
        rw [Real.norm_eq_abs,abs_div,abs_of_pos hkl] at he'
        exact ((div_lt_iff₀ hkl).mp he').le
      have hl : log (k : ℝ) ≤ log N := Real.log_le_log (by exact_mod_cast (by omega : 0 < k))
        (by exact_mod_cast hkN)
      exact (he'.trans (mul_le_mul_of_nonneg_left hl heps.le)).trans (le_add_of_nonneg_left hC)
  have hwt := (hT N hNT).2
  have hab := abs_weighted_sum_le_of_partial hB hp hwt.1 hwt.2.1
  have hab' : |∑ i ∈ range N, w N i*u i| ≤ C+(ε/2)*log N :=
    hab.trans (by simpa using mul_le_mul_of_nonneg_left hwt.2.2 hB)
  rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hlog]
  calc
    _ ≤ (C+(ε/2)*log N)/log N := div_le_div_of_nonneg_right hab' hlog.le
    _ = C/log N+ε/2 := by field_simp
    _ < ε := by have := (hT N hNT).1; linarith

end MeanTransfer


/- A critical-scale profile for truncated power harmonic sums. -/

open Finset Real Filter Polynomial MeasureTheory Asymptotics
open scoped Topology ArithmeticFunction.sigma

namespace MeanTransfer

noncomputable def powerHarmonicSum (s : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ Ioc 0 N, (q : ℝ)^(-1-s)

lemma powerHarmonicSum_integral_bounds {s : ℝ} (hs : 0 ≤ s) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ powerHarmonicSum s N-(∫ x in (1 : ℝ)..N, x^(-1-s)) ∧
      powerHarmonicSum s N-(∫ x in (1 : ℝ)..N, x^(-1-s)) ≤ 1 := by
  have hant : AntitoneOn (fun x : ℝ => x^(-1-s)) (Set.Icc 1 N) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hlo := AntitoneOn.integral_le_sum_Ico (f := fun x : ℝ => x^(-1-s)) hN (by simpa using hant)
  have hup := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => x^(-1-s)) hN (by simpa using hant)
  simp only [Nat.cast_one] at hlo hup
  have hsub : Ico 1 N ⊆ Ioc 0 N := by
    intro q hq
    simp only [mem_Ico,mem_Ioc] at hq ⊢
    omega
  have hlo' : (∫ x in (1 : ℝ)..N, x^(-1-s)) ≤ powerHarmonicSum s N := hlo.trans
    (sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => Real.rpow_nonneg (Nat.cast_nonneg q) _))
  have heq : (∑ q ∈ Ico 1 N, ((q+1 : ℕ) : ℝ)^(-1-s))+1 = powerHarmonicSum s N := by
    rw [sum_Ico_add' (fun q : ℕ => (q : ℝ)^(-1-s)) 1 N 1]
    have hfin : Ico (1+1) (N+1) = Ioc 1 N := by ext q; simp only [mem_Ico,mem_Ioc]; omega
    rw [hfin]
    simpa only [Nat.cast_one,Real.one_rpow,show Icc 1 N = Ioc 0 N by
      ext q; simp only [mem_Icc,mem_Ioc]; omega,powerHarmonicSum] using
      (sum_Ioc_add_eq_sum_Icc (f := fun q : ℕ => (q : ℝ)^(-1-s)) hN)
  constructor <;> linarith

lemma powerHarmonicSum_integral {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in (1 : ℝ)..N, x^(-1-s)) = (1-(N : ℝ)^(-s))/s := by
  rw [integral_rpow (Or.inr ⟨by linarith,?_⟩)]
  · have he : -1-s+1 = -s := by ring
    rw [he,Real.one_rpow]
    ring
  · rw [Set.uIcc_of_le (by exact_mod_cast hN)]
    simp

lemma powerHarmonicSum_critical_limit {s : ℕ → ℝ} {t : ℝ} (ht : 0 < t)
    (hs : ∀ᶠ N in atTop, 0 < s N)
    (hscale : Tendsto (fun N : ℕ => s N*log N) atTop (𝓝 t)) :
    Tendsto (fun N : ℕ => powerHarmonicSum (s N) N/log N)
      atTop (𝓝 ((1-exp (-t))/t)) := by
  have hmodel : Tendsto (fun N : ℕ => (1-exp (-(s N*log N)))/(s N*log N))
      atTop (𝓝 ((1-exp (-t))/t)) :=
    (tendsto_const_nhds.sub (Real.continuous_exp.tendsto (-t) |>.comp hscale.neg)).div hscale ht.ne'
  have herr : Tendsto (fun N : ℕ => powerHarmonicSum (s N) N/log N-
      (1-exp (-(s N*log N)))/(s N*log N)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ => 1/log N)
    · filter_upwards [hs,eventually_gt_atTop (1 : ℕ)] with N hsN hN
      have hlog : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
      have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have hbounds := powerHarmonicSum_integral_bounds hsN.le (by omega : 1 ≤ N)
      rw [powerHarmonicSum_integral hsN (by omega : 1 ≤ N)] at hbounds
      have he : (1-exp (-(s N*log N)))/(s N*log N) =
          ((1-(N : ℝ)^(-(s N)))/(s N))/log N := by
        rw [Real.rpow_def_of_pos hNr]
        have hx : log (N : ℝ)*(-s N) = -(s N*log N) := by ring
        rw [hx,div_div]
      rw [Real.norm_eq_abs,he,← sub_div,abs_div,abs_of_pos hlog,abs_of_nonneg hbounds.1]
      exact div_le_div_of_nonneg_right hbounds.2 hlog.le
    · exact tendsto_const_nhds.div_atTop
        (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hh := herr.add hmodel
  simpa only [sub_add_cancel,zero_add] using hh

end MeanTransfer


/- Critical-scale asymptotics for the divisor cutoff at the input bound. -/

open Finset Real Filter Polynomial Asymptotics
open scoped Topology ArithmeticFunction.sigma

namespace GeneralDivisors
open Sieve MeanTransfer

lemma truncatedRootMean_uniform_log_error {f : ℤ[X]} {a : ℝ}
    (hmean : Tendsto (fun N : ℕ => (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ))/N)
      atTop (𝓝 a)) {s : ℕ → ℝ} (hs : ∀ᶠ N in atTop, 0 ≤ s N) :
    Tendsto (fun N : ℕ => (truncatedRootMean f (s N) N-a*powerHarmonicSum (s N) N)/log N)
      atTop (𝓝 0) := by
  let u : ℕ → ℝ := fun i => (polynomialRootCount f (i+1) : ℝ)/(i+1)-a/(i+1)
  have hu : Tendsto (fun N : ℕ => (∑ i ∈ range N, u i)/log N) atTop (𝓝 0) := by
    have hh := (MeanTransfer.logarithmic_mean_Ioc_of_mean hmean).sub
      (MeanTransfer.harmonic_log_limit.const_mul a)
    simp only [mul_one,sub_self] at hh
    convert hh using 1
    ext N
    rw [sum_Ioc_zero_eq_range,← MeanTransfer.harmonic_range]
    simp only [u,Nat.cast_add,Nat.cast_one,sum_sub_distrib]
    rw [← mul_div_assoc,← sub_div]
    congr 1
    rw [mul_sum]
    congr 1
    apply sum_congr rfl
    intro i hi
    ring
  let w : ℕ → ℕ → ℝ := fun N i => ((i+1 : ℕ) : ℝ)^(-(s N))
  have hw : ∀ᶠ N in atTop, Antitone (w N) ∧ (∀ i, 0 ≤ w N i) ∧ w N 0 ≤ 1 := by
    filter_upwards [hs] with N hsN
    refine ⟨?_,?_,?_⟩
    · intro i j hij
      apply Real.rpow_le_rpow_of_nonpos (by positivity)
        (show ((i+1 : ℕ) : ℝ) ≤ ((j+1 : ℕ) : ℝ) by exact_mod_cast Nat.add_le_add_right hij 1)
        (neg_nonpos.mpr hsN)
    · intro i
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · simp only [w,Nat.zero_add,Nat.cast_one,Real.one_rpow,le_refl]
  have hh := MeanTransfer.varying_antitone_log_mean_zero hu hw
  convert hh using 1
  ext N
  rw [truncatedRootMean,powerHarmonicSum,mul_sum,← sum_sub_distrib,sum_Ioc_zero_eq_range]
  congr 1
  apply sum_congr rfl
  intro i hi
  have hi0 : (0 : ℝ) < (i+1 : ℕ) := by positivity
  have hpower : ((i+1 : ℕ) : ℝ)^(-1-s N) = ((i+1 : ℕ) : ℝ)^(-(s N))/((i+1 : ℕ) : ℝ) := by
    rw [show -1-s N = -(s N)-1 by ring,Real.rpow_sub hi0,Real.rpow_one]
  rw [hpower,← weighted_root_density f (by omega : 0 < i+1) (s N)]
  dsimp only [w,u]
  push_cast
  ring

lemma truncatedRootMean_critical_limit {f : ℤ[X]} {a : ℝ}
    (hmean : Tendsto (fun N : ℕ => (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ))/N)
      atTop (𝓝 a)) {s : ℕ → ℝ} {t : ℝ} (ht : 0 < t)
    (hs : ∀ᶠ N in atTop, 0 < s N)
    (hscale : Tendsto (fun N : ℕ => s N*log N) atTop (𝓝 t)) :
    Tendsto (fun N : ℕ => truncatedRootMean f (s N) N/log N)
      atTop (𝓝 (a*((1-exp (-t))/t))) := by
  have hh := (truncatedRootMean_uniform_log_error hmean (hs.mono (fun _ h => h.le))).add
    ((MeanTransfer.powerHarmonicSum_critical_limit ht hs hscale).const_mul a)
  simp only [zero_add] at hh
  convert hh using 1
  ext N
  ring

lemma truncatedWeightedDivisorSum_critical_limit {f : ℤ[X]}
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) {a : ℝ}
    (hmean : Tendsto (fun N : ℕ => (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ))/N)
      atTop (𝓝 a)) {s : ℕ → ℝ} {t : ℝ} (ht : 0 < t)
    (hs : ∀ᶠ N in atTop, 0 < s N)
    (hscale : Tendsto (fun N : ℕ => s N*log N) atTop (𝓝 t)) :
    Tendsto (fun N : ℕ => truncatedWeightedDivisorSum f (s N) N/((N : ℝ)*log N))
      atTop (𝓝 (a*((1-exp (-t))/t))) := by
  obtain ⟨K,hK⟩ := truncatedWeightedDivisorSum_error hpos
  have herr : Tendsto (fun N : ℕ => (truncatedWeightedDivisorSum f (s N) N/N-
      truncatedRootMean f (s N) N)/log N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ =>
      ((K : ℝ)+2*(∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ))/N)/log N)
    · filter_upwards [hs,eventually_gt_atTop (1 : ℕ)] with N hsN hN
      have hlog : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
      rw [Real.norm_eq_abs,abs_div,abs_of_pos hlog]
      exact div_le_div_of_nonneg_right (hK hsN.le (by omega)) hlog.le
    · have hh := ((hmean.const_mul 2).const_add (K : ℝ)).div_atTop
        (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
      simpa only [mul_div_assoc] using hh
  have hh := herr.add (truncatedRootMean_critical_limit hmean ht hs hscale)
  simp only [zero_add] at hh
  convert hh using 1
  ext N
  ring

lemma truncatedWeightedDivisorSum_log_exponent {f : ℤ[X]}
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) {a : ℝ}
    (hmean : Tendsto (fun N : ℕ => (∑ q ∈ Ioc 0 N, (polynomialRootCount f q : ℝ))/N)
      atTop (𝓝 a)) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => truncatedWeightedDivisorSum f (t/log N) N/((N : ℝ)*log N))
      atTop (𝓝 (a*((1-exp (-t))/t))) := by
  apply truncatedWeightedDivisorSum_critical_limit hpos hmean ht
  · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    exact div_pos ht (Real.log_pos (by exact_mod_cast hN))
  · have he : (fun N : ℕ => (t/log N)*log N) =ᶠ[atTop] fun _ => t := by
      filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
      exact div_mul_cancel₀ _ (Real.log_pos (by exact_mod_cast hN)).ne'
    exact (tendsto_congr' he).mpr tendsto_const_nhds

end GeneralDivisors


/- Exact divisor pairing and stability below the critical regularization scale.
These results do not assert the existence of the unweighted limit. -/

open Finset Real Filter Polynomial
open scoped Topology ArithmeticFunction.sigma

namespace GeneralDivisors
open Sieve

lemma weightedDivisorCount_reflection (m : ℕ) (s : ℝ) :
    weightedDivisorCount m s = (m : ℝ)^(-s)*weightedDivisorCount m (-s) := by
  rw [weightedDivisorCount, ← Nat.sum_div_divisors m (fun q : ℕ => (q : ℝ)^(-s)),
    weightedDivisorCount, mul_sum]
  apply sum_congr rfl
  intro q hq
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hq).ne'
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hq) hq0,
    Real.div_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg q),
    Real.rpow_neg (Nat.cast_nonneg q), div_inv_eq_mul, neg_neg]

lemma weightedDivisorCount_le_zero (m : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    weightedDivisorCount m s ≤ weightedDivisorCount m 0 := by
  simp only [weightedDivisorCount, neg_zero, Real.rpow_zero]
  apply sum_le_sum
  intro q hq
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast Nat.pos_of_mem_divisors hq) (neg_nonpos.mpr hs)

lemma weightedDivisorCount_lower (m M : ℕ) (hm : m ≤ M) {s : ℝ} (hs : 0 ≤ s) :
    (M : ℝ)^(-s)*weightedDivisorCount m 0 ≤ weightedDivisorCount m s := by
  simp only [weightedDivisorCount,neg_zero,Real.rpow_zero,mul_sum,mul_one]
  apply sum_le_sum
  intro q hq
  have hqM : q ≤ M := (Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hq).2)
    (Nat.dvd_of_mem_divisors hq)).trans hm
  exact Real.rpow_le_rpow_of_nonpos
    (by exact_mod_cast Nat.pos_of_mem_divisors hq) (by exact_mod_cast hqM)
    (neg_nonpos.mpr hs)

lemma weightedDivisorSum_subcritical_bounds (f : ℤ[X]) :
    ∀ᶠ N : ℕ in atTop, ∀ s : ℝ, 0 ≤ s →
      exp (-((f.natDegree+1 : ℕ) : ℝ)*(s*log N))*weightedDivisorSum f 0 N ≤
        weightedDivisorSum f s N ∧
      weightedDivisorSum f s N ≤ weightedDivisorSum f 0 N := by
  obtain ⟨B,hB⟩ := naturalValue_polynomial_upper f
  filter_upwards [eventually_ge_atTop (max B 1)] with N hN
  intro s hs
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow : (((N^(f.natDegree+1) : ℕ) : ℝ))^(-s) =
      exp (-((f.natDegree+1 : ℕ) : ℝ)*(s*log N)) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
      Real.rpow_def_of_pos hN0]
    congr 1
    ring
  constructor
  · rw [← hpow,weightedDivisorSum,weightedDivisorSum,mul_sum]
    apply sum_le_sum
    intro n hn
    exact weightedDivisorCount_lower _ _ (hB N hN n (mem_Ioc.mp hn).2) hs
  · apply sum_le_sum
    intro n hn
    exact weightedDivisorCount_le_zero _ hs

/-- Below the critical scale, regularization does not change the normalized sum.
Consequently, convergence in this regime is as strong as unweighted convergence. -/
lemma weightedDivisorSum_subcritical_difference_limit {f : ℤ[X]}
    (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) {s : ℕ → ℝ}
    (hs : ∀ᶠ N in atTop, 0 ≤ s N)
    (hscale : Tendsto (fun N : ℕ => s N*log N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (weightedDivisorSum f 0 N-weightedDivisorSum f (s N) N)/
      ((N : ℝ)*log N)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := polynomial_divisor_sum_upper_nat hdeg hirr
  let e : ℕ → ℝ := fun N => exp (-((f.natDegree+1 : ℕ) : ℝ)*(s N*log N))
  have he : Tendsto e atTop (𝓝 1) := by
    have hex : Tendsto (fun N : ℕ => -((f.natDegree+1 : ℕ) : ℝ)*(s N*log N))
        atTop (𝓝 0) := by simpa only [mul_zero] using hscale.const_mul (-((f.natDegree+1 : ℕ) : ℝ))
    simpa only [Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp hex
  apply squeeze_zero_norm' (a := fun N => C*(1-e N))
  · filter_upwards [hs,hbound,weightedDivisorSum_subcritical_bounds f,
      eventually_gt_atTop (1 : ℕ)] with N hsN hN hb hN1
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlog : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
    have hden : 0 < (N : ℝ)*log N := mul_pos hNr hlog
    obtain ⟨hl,hu⟩ := hb (s N) hsN
    have heN : e N ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (mul_nonneg hsN hlog.le)
    have hU : weightedDivisorSum f 0 N ≤ C*(N : ℝ)*log N := by
      simpa only [weightedDivisorSum,weightedDivisorCount_zero] using hN
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sub_nonneg.mpr hu) hden.le)]
    apply (div_le_iff₀ hden).mpr
    calc
      weightedDivisorSum f 0 N-weightedDivisorSum f (s N) N ≤
          (1-e N)*weightedDivisorSum f 0 N := by dsimp only [e]; nlinarith [hl]
      _ ≤ (1-e N)*(C*(N : ℝ)*log N) :=
        mul_le_mul_of_nonneg_left hU (sub_nonneg.mpr heN)
      _ = _ := by ring
  · have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [sub_self,mul_zero] using (h1.sub he).const_mul C

lemma weightedDivisorSum_subcritical_limit_iff {f : ℤ[X]}
    (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) {s : ℕ → ℝ}
    (hs : ∀ᶠ N in atTop, 0 ≤ s N)
    (hscale : Tendsto (fun N : ℕ => s N*log N) atTop (𝓝 0)) (c : ℝ) :
    Tendsto (fun N : ℕ => weightedDivisorSum f (s N) N/((N : ℝ)*log N)) atTop (𝓝 c) ↔
    Tendsto (fun N : ℕ => weightedDivisorSum f 0 N/((N : ℝ)*log N)) atTop (𝓝 c) := by
  have he := weightedDivisorSum_subcritical_difference_limit hdeg hirr hs hscale
  constructor
  · intro h
    have hh := h.add he
    simp only [add_zero] at hh
    convert hh using 1
    ext N
    ring
  · intro h
    have hh := h.sub he
    simp only [sub_zero] at hh
    convert hh using 1
    ext N
    ring

lemma weightedDivisorSum_zero_eq (f : ℤ[X]) (N : ℕ) :
    weightedDivisorSum f 0 N + (σ 0 (naturalValue f 0) : ℝ) = Erdos975Sum f (N : ℝ) := by
  have h := sum_Ioc_add_eq_sum_Icc
    (f := fun n : ℕ => (σ 0 (naturalValue f n) : ℝ)) (Nat.zero_le N)
  simpa only [weightedDivisorSum,weightedDivisorCount_zero,Erdos975Sum,
    Nat.floor_natCast,show (0 : ℕ) = ⊥ from rfl,Icc_bot,naturalValue] using h

lemma weightedDivisorSum_zero_limit_iff (f : ℤ[X]) (c : ℝ) :
    Tendsto (fun N : ℕ => weightedDivisorSum f 0 N/((N : ℝ)*log N)) atTop (𝓝 c) ↔
    Tendsto (fun x : ℝ => Erdos975Sum f x/(x*log x)) atTop (𝓝 c) := by
  rw [real_limit_iff_nat_limit]
  have hden : Tendsto (fun N : ℕ => (N : ℝ)*log N) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have he : Tendsto (fun N : ℕ => (σ 0 (naturalValue f 0) : ℝ)/((N : ℝ)*log N))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hden
  constructor
  · intro h
    have hh := h.add he
    simp only [add_zero] at hh
    convert hh using 1
    ext N
    rw [← add_div,weightedDivisorSum_zero_eq]
  · intro h
    have hh := h.sub he
    simp only [sub_zero] at hh
    convert hh using 1
    ext N
    rw [← sub_div,← weightedDivisorSum_zero_eq]
    ring

lemma weightedDivisorSum_subcritical_erdos_limit_iff {f : ℤ[X]}
    (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) {s : ℕ → ℝ}
    (hs : ∀ᶠ N in atTop, 0 ≤ s N)
    (hscale : Tendsto (fun N : ℕ => s N*log N) atTop (𝓝 0)) (c : ℝ) :
    Tendsto (fun N : ℕ => weightedDivisorSum f (s N) N/((N : ℝ)*log N)) atTop (𝓝 c) ↔
    Tendsto (fun x : ℝ => Erdos975Sum f x/(x*log x)) atTop (𝓝 c) :=
  (weightedDivisorSum_subcritical_limit_iff hdeg hirr hs hscale c).trans
    (weightedDivisorSum_zero_limit_iff f c)

end GeneralDivisors


/- Ordinary means for divisors supported on a fixed finite set of primes.
No uniformity as that set grows is asserted. -/

open Finset Real Filter Polynomial
open scoped Topology ArithmeticFunction.sigma

namespace GeneralDivisors
open Sieve

lemma positiveDivisibleCount_polynomial_bound (f : ℤ[X]) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, 0 < q →
      (positiveDivisibleCount f q N : ℝ)/N ≤
        3*(polynomialRootCount f q : ℝ)/(q : ℝ)^(((f.natDegree+1 : ℕ) : ℝ)⁻¹) := by
  obtain ⟨B,hB⟩ := naturalValue_polynomial_upper f
  filter_upwards [eventually_ge_atTop (max B 1)] with N hN q hq
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  let D : ℕ := f.natDegree+1
  have hD : (0 : ℝ) < D := by dsimp [D]; positivity
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by dsimp [D]; omega)
  have hδ : (D : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD1
  by_cases hc : positiveDivisibleCount f q N = 0
  · simp only [hc,Nat.cast_zero,zero_div]
    positivity
  have hqN : q ≤ N^D := by
    obtain ⟨n,hn⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
    obtain ⟨hn,hdiv⟩ := mem_filter.mp hn
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hdiv).2)
      (Nat.dvd_of_mem_divisors hdiv)).trans (hB N hN n (mem_Ioc.mp hn).2)
  have hpowN : (q : ℝ)^((D : ℝ)⁻¹) ≤ N := by
    have hh := Real.rpow_le_rpow hqr.le (show (q : ℝ) ≤ (N : ℝ)^D by exact_mod_cast hqN)
      (inv_nonneg.mpr hD.le)
    rw [← Real.rpow_natCast_mul hNr.le, mul_inv_cancel₀ hD.ne',Real.rpow_one] at hh
    exact hh
  have hpowq : (q : ℝ)^((D : ℝ)⁻¹) ≤ q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ q by exact_mod_cast hq) hδ
  have hpow0 : 0 < (q : ℝ)^((D : ℝ)⁻¹) := Real.rpow_pos_of_pos hqr _
  have hcount : (positiveDivisibleCount f q N : ℝ)/N ≤
      (polynomialRootCount f q : ℝ)/q+2*(polynomialRootCount f q : ℝ)/N := by
    have h0 : (positiveDivisibleCount f q N : ℝ) ≤ divisibleValueCount f q N := by
      exact_mod_cast positiveDivisibleCount_le f q N
    have he := (abs_le.mp (polynomial_root_count_error f hq N)).2
    apply (div_le_iff₀ hNr).mpr
    calc
      _ ≤ (N : ℝ)/q*polynomialRootCount f q+2*polynomialRootCount f q := by linarith
      _ = _ := by field_simp
  calc
    _ ≤ (polynomialRootCount f q : ℝ)/q+2*(polynomialRootCount f q : ℝ)/N := hcount
    _ ≤ (polynomialRootCount f q : ℝ)/(q : ℝ)^((D : ℝ)⁻¹)+
        2*(polynomialRootCount f q : ℝ)/(q : ℝ)^((D : ℝ)⁻¹) := by
      exact add_le_add (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpow0 hpowq)
        (div_le_div_of_nonneg_left (by positivity) hpow0 hpowN)
    _ = _ := by dsimp [D]; ring

lemma smooth_root_series_hasSum {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) {δ : ℝ} (hδ : 0 < δ) (M : ℕ) :
    HasSum (fun q : M.smoothNumbers => (polynomialRootCount f q : ℝ)/(q : ℝ)^δ)
      (∏ p ∈ M.primesBelow, ∑' k : ℕ, (polynomialRootCount f (p^k) : ℝ)/(p^k : ℕ)^δ) := by
  let v : ℕ → ℝ := fun q => rootFunction f q/(q : ℝ)^δ
  have hv0 (q : ℕ) : 0 ≤ v q := by
    exact div_nonneg (rootFunction_nonneg f q) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  have hv1 : v 1 = 1 := by simp [v,(rootFunction_multiplicative f).1]
  have hvmul {m n : ℕ} (hmn : m.Coprime n) : v (m*n) = v m*v n := by
    simp only [v,(rootFunction_multiplicative f).map_mul_of_coprime hmn,Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  have hpp (p k : ℕ) (hp : p.Prime) : v (p^k) =
      (polynomialRootCount f (p^k) : ℝ)*((p : ℝ)^(-δ))^k := by
    dsimp only [v]
    rw [rootFunction_apply f (pow_ne_zero _ hp.ne_zero),Nat.cast_pow,
      natPow_rpow_comm _ (Nat.cast_nonneg p),div_eq_mul_inv,← inv_pow,
      ← Real.rpow_neg (Nat.cast_nonneg p)]
  obtain ⟨R,hR,hRbound⟩ := root_prime_powers_uniform hdeg hirr
  have hlocal {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => ‖v (p^k)‖) := by
    have hpr : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hq : (p : ℝ)^(-δ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hpr (neg_neg_of_pos hδ)
    have hgeom : Summable (fun k : ℕ => R*((p : ℝ)^(-δ))^k) :=
      (summable_geometric_of_lt_one (Real.rpow_nonneg (Nat.cast_nonneg p) _) hq).mul_left R
    apply hgeom.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro k
    rw [Real.norm_eq_abs,abs_of_nonneg (hv0 _),hpp p k hp]
    exact mul_le_mul_of_nonneg_right (hRbound p hp k) (by positivity)
  have hh := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hv1 (fun {_ _} => hvmul) hlocal M).2
  have hEq : (fun q : M.smoothNumbers => v q) =
      (fun q : M.smoothNumbers => (polynomialRootCount f q : ℝ)/(q : ℝ)^δ) := by
    funext q
    dsimp only [v]
    rw [rootFunction_apply f (Nat.ne_zero_of_mem_smoothNumbers q.property)]
  rw [hEq] at hh
  convert hh using 1
  apply prod_congr rfl
  intro p hp
  apply tsum_congr
  intro k
  dsimp only [v]
  rw [rootFunction_apply f (pow_ne_zero _ (Nat.prime_of_mem_primesBelow hp).ne_zero)]

lemma smooth_positiveDivisibleCount_mean {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) (M : ℕ) :
    Tendsto (fun N : ℕ => ∑' q : M.smoothNumbers, (positiveDivisibleCount f q N : ℝ)/N)
      atTop (𝓝 (∑' q : M.smoothNumbers, (polynomialRootCount f q : ℝ)/(q : ℝ))) := by
  have hδ : 0 < (((f.natDegree+1 : ℕ) : ℝ)⁻¹) := by positivity
  have hs := (smooth_root_series_hasSum hdeg hirr hδ M).summable.mul_left 3
  apply tendsto_tsum_of_dominated_convergence hs
  · intro q
    exact positiveDivisibleCount_limit hpos (Nat.pos_of_ne_zero
      (Nat.ne_zero_of_mem_smoothNumbers q.property))
  · filter_upwards [positiveDivisibleCount_polynomial_bound f] with N hN q
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    simpa only [mul_div_assoc] using hN q (Nat.pos_of_ne_zero
      (Nat.ne_zero_of_mem_smoothNumbers q.property))

noncomputable def smoothDivisorCount (m M : ℕ) : ℕ :=
  {q ∈ m.divisors | q ∈ M.smoothNumbers}.card

noncomputable def smoothDivisorSum (f : ℤ[X]) (M N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, (smoothDivisorCount (naturalValue f n) M : ℝ)

lemma smoothDivisorSum_eq_tsum (f : ℤ[X]) (M N : ℕ) :
    smoothDivisorSum f M N = ∑' q : M.smoothNumbers, (positiveDivisibleCount f q N : ℝ) := by
  classical
  let Q : Finset ℕ := ((Ioc 0 N).biUnion (fun n => (naturalValue f n).divisors)).filter
    (· ∈ M.smoothNumbers)
  have hQ (q : ℕ) : q ∈ Q ↔ q ∈ M.smoothNumbers ∧
      ∃ n ∈ Ioc 0 N, q ∈ (naturalValue f n).divisors := by
    simp only [Q,mem_filter,mem_biUnion,and_comm]
  have hzero (q : M.smoothNumbers) (hq : q ∉ Q.subtype (· ∈ M.smoothNumbers)) :
      (positiveDivisibleCount f q N : ℝ) = 0 := by
    have hqQ : (q : ℕ) ∉ Q := by simpa only [mem_subtype] using hq
    have hempty : {n ∈ Ioc 0 N | (q : ℕ) ∈ (naturalValue f n).divisors} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨hn,hd⟩ := mem_filter.mp hn
      exact hqQ ((hQ q).mpr ⟨q.property,n,hn,hd⟩)
    simp only [positiveDivisibleCount,hempty,card_empty,Nat.cast_zero]
  rw [tsum_eq_sum hzero,sum_subtype_of_mem (fun q : ℕ => (positiveDivisibleCount f q N : ℝ))
    (fun q hq => ((hQ q).mp hq).1)]
  simp only [positiveDivisibleCount,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  rw [sum_boole]
  apply congrArg (fun S : Finset ℕ => (S.card : ℝ))
  ext q
  simp only [mem_filter,hQ]
  constructor
  · rintro ⟨hd,hs⟩
    exact ⟨⟨hs,n,hn,hd⟩,hd⟩
  · rintro ⟨⟨hs,_⟩,hd⟩
    exact ⟨hd,hs⟩

lemma smoothDivisorSum_mean {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) (M : ℕ) :
    Tendsto (fun N : ℕ => smoothDivisorSum f M N/N) atTop
      (𝓝 (∑' q : M.smoothNumbers, (polynomialRootCount f q : ℝ)/(q : ℝ))) := by
  simpa only [smoothDivisorSum_eq_tsum,tsum_div_const] using
    smooth_positiveDivisibleCount_mean hdeg hirr hpos M

lemma smoothDivisorSum_euler_mean {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) (M : ℕ) :
    Tendsto (fun N : ℕ => smoothDivisorSum f M N/N) atTop
      (𝓝 (∏ p ∈ M.primesBelow, ∑' k : ℕ, (polynomialRootCount f (p^k) : ℝ)/(p^k : ℕ))) := by
  have he := (smooth_root_series_hasSum hdeg hirr (by norm_num : (0 : ℝ) < 1) M).tsum_eq
  simp only [Real.rpow_one] at he
  rw [← he]
  exact smoothDivisorSum_mean hdeg hirr hpos M

/-- Divisors built from any fixed finite set of primes are negligible on the
normalization in the original conjecture. This is not uniform in M. -/
lemma smoothDivisorSum_log_limit {f : ℤ[X]} (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) (M : ℕ) :
    Tendsto (fun N : ℕ => smoothDivisorSum f M N/((N : ℝ)*log N)) atTop (𝓝 0) := by
  simpa only [div_div] using (smoothDivisorSum_mean hdeg hirr hpos M).div_atTop
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))

end GeneralDivisors

/--
For an irreducible polynomial $f \in \mathbb{Z}[x]$ with $f(n) \ge 1$ for sufficiently large $n$,
does there exists a constant $c = c(f) > 0$ such that
$\sum_{n \le x} \tau(f(n)) \approx c \cdot x \log x$?

Note that it is unclear whether the polynomial should have integer coefficients or merely be
integer-valued. We assume the former. -/
theorem erdos_975 : 
    ∀ f : ℤ[X], f.natDegree ≠ 0 → Irreducible f → (∀ᶠ n in atTop, 1 ≤ f.eval n) →
    ∃ c > (0 : ℝ), Tendsto (fun x ↦ Erdos975Sum f x / (x * log x)) atTop (𝓝 c) := by
  intro f hdeg hirr hpos
  by_cases hd : f.natDegree = 1
  · exact erdos_975_degree_one f hd hirr hpos
  · by_cases hquad : f.natDegree = 2
    · exact erdos_975_degree_two f hquad hirr hpos
    · have hdegree : 3 ≤ f.natDegree := by omega
      obtain ⟨a, ha, hmean⟩ := GeneralDivisors.polynomialRootCount_mean_positive f hdeg hirr
      apply (GeneralDivisors.higher_degree_positive_limit_iff_large_limit
        hdegree hpos ha hmean).mpr
      sorry

end Erdos975
