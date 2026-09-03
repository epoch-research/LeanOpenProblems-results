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

lemma tendsto_erdos975Sum_iff_nat (f : ℤ[X]) (c : ℝ) :
    Tendsto (fun x ↦ Erdos975Sum f x / (x * log x)) atTop (𝓝 c) ↔
    Tendsto (fun n : ℕ ↦ Erdos975Sum f n / ((n : ℝ) * log n)) atTop (𝓝 c) := by
  constructor
  · intro h
    exact h.comp tendsto_natCast_atTop_atTop
  · intro h
    have hf := Asymptotics.isEquivalent_nat_floor (R := ℝ)
    have hd := hf.mul (hf.log tendsto_id)
    have he := (Asymptotics.IsEquivalent.refl (u := Erdos975Sum f) (l := atTop)).div hd
    apply he.tendsto_nhds_iff.mp
    simpa only [Function.comp_def, Pi.div_apply, Pi.mul_apply, Erdos975Sum,
      Nat.floor_natCast] using h.comp (tendsto_nat_floor_atTop (α := ℝ))

def polynomialRootResidues (f : ℤ[X]) (d : ℕ) : Finset ℕ :=
  (Finset.range d).filter (fun r : ℕ ↦ (d : ℤ) ∣ f.eval (r : ℤ))

lemma dvd_eval_mod_iff (f : ℤ[X]) (d n : ℕ) :
    (d : ℤ) ∣ f.eval (n : ℤ) ↔ (d : ℤ) ∣ f.eval ((n % d : ℕ) : ℤ) := by
  have harg : (d : ℤ) ∣ (n : ℤ) - ((n % d : ℕ) : ℤ) := by
    simpa only [Int.natCast_emod] using (Int.mod_modEq (n : ℤ) (d : ℤ)).dvd
  exact dvd_iff_dvd_of_dvd_sub
    (harg.trans (Polynomial.sub_dvd_eval_sub (n : ℤ) ((n % d : ℕ) : ℤ) f))

lemma polynomial_root_count (f : ℤ[X]) (d N : ℕ) (hd : 0 < d) :
    ((Finset.range N).filter (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ))).card =
      N / d * (polynomialRootResidues f d).card +
        ((polynomialRootResidues f d).filter (fun r ↦ r < N % d)).card := by
  have hmap : Set.MapsTo (fun n ↦ n % d)
      ((Finset.range N).filter (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ)))
      (polynomialRootResidues f d) := by
    intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range,
      polynomialRootResidues] at hn ⊢
    exact ⟨Nat.mod_lt _ hd, (dvd_eval_mod_iff f d n).mp hn.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    ∑ r ∈ polynomialRootResidues f d,
        (((Finset.range N).filter (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ))).filter
          (fun n ↦ n % d = r)).card =
      ∑ r ∈ polynomialRootResidues f d,
        ((Finset.range N).filter (fun n ↦ n ≡ r [MOD d])).card := by
      apply Finset.sum_congr rfl
      intro r hr
      have hr' := Finset.mem_filter.mp hr
      have hrd : r < d := Finset.mem_range.mp hr'.1
      congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Nat.ModEq,
        Nat.mod_eq_of_lt hrd]
      constructor
      · exact fun h ↦ ⟨h.1.1, h.2⟩
      · rintro ⟨hn, hmod⟩
        exact ⟨⟨hn, (dvd_eval_mod_iff f d n).mpr (hmod.symm ▸ hr'.2)⟩, hmod⟩
    _ = ∑ r ∈ polynomialRootResidues f d,
        (N / d + if r < N % d then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card N hd,
        Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)]
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.sum_filter, Nat.cast_id, mul_one]
      rw [Nat.mul_comm]

lemma polynomial_root_count_error (f : ℤ[X]) (d N : ℕ) (hd : 0 < d) :
    |(((Finset.range N).filter (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ))).card : ℝ) -
      (N : ℝ) / d * (polynomialRootResidues f d).card| ≤
        (polynomialRootResidues f d).card := by
  rw [polynomial_root_count f d N hd, Nat.cast_add, Nat.cast_mul, abs_le]
  have hq : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
  have hq' : (N : ℝ) / d - 1 ≤ ((N / d : ℕ) : ℝ) := by
    simpa only [Nat.floor_div_eq_div] using (Nat.sub_one_lt_floor ((N : ℝ) / d)).le
  have hr : (((polynomialRootResidues f d).filter (fun r ↦ r < N % d)).card : ℝ) ≤
      (polynomialRootResidues f d).card := by
    exact_mod_cast Finset.card_filter_le (polynomialRootResidues f d) _
  have hρ : (0 : ℝ) ≤ (polynomialRootResidues f d).card := by positivity
  have hr0 : (0 : ℝ) ≤ ((polynomialRootResidues f d).filter (fun r ↦ r < N % d)).card := by
    positivity
  constructor <;> nlinarith

lemma truncated_divisor_count_error (f : ℤ[X]) (D N : ℕ) :
    |(∑ d ∈ Finset.Icc 1 D,
        (((Finset.range N).filter (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ))).card : ℝ)) -
      (N : ℝ) * ∑ d ∈ Finset.Icc 1 D, (polynomialRootResidues f d).card / (d : ℝ)| ≤
        ∑ d ∈ Finset.Icc 1 D, ((polynomialRootResidues f d).card : ℝ) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    |∑ d ∈ Finset.Icc 1 D,
        ((((Finset.range N).filter (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ))).card : ℝ) -
          (N : ℝ) * ((polynomialRootResidues f d).card / d))| ≤
      ∑ d ∈ Finset.Icc 1 D,
        |(((Finset.range N).filter (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ))).card : ℝ) -
          (N : ℝ) * ((polynomialRootResidues f d).card / d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      have hd' : 0 < d := (Finset.mem_Icc.mp hd).1
      simpa only [div_mul_eq_mul_div, mul_div_assoc] using polynomial_root_count_error f d N hd'

lemma sigma_zero_hyperbola (m : ℕ) :
    σ 0 m + (m.divisors.filter (fun d ↦ d ^ 2 = m)).card =
      2 * (m.divisors.filter (fun d ↦ d ≤ m.sqrt)).card := by
  let L := m.divisors.filter (fun d ↦ d ≤ m / d)
  let U := m.divisors.filter (fun d ↦ m / d ≤ d)
  have hcard : U.card = L.card := by
    simp only [U, L, Finset.card_eq_sum_ones, Finset.sum_filter]
    calc
      ∑ d ∈ m.divisors, (if m / d ≤ d then 1 else 0) =
          ∑ d ∈ m.divisors, (if m / d ≤ m / (m / d) then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) (Nat.ne_zero_of_mem_divisors hd)]
      _ = _ := Nat.sum_div_divisors m (fun d ↦ if d ≤ m / d then 1 else 0)
  have hunion : L ∪ U = m.divisors := by
    ext d
    simp only [L, U, Finset.mem_union, Finset.mem_filter]
    have := le_total d (m / d)
    tauto
  have hinter : L ∩ U = m.divisors.filter (fun d ↦ d ^ 2 = m) := by
    ext d
    simp only [L, U, Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hd, hle⟩, _, hge⟩
      have hmul := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      refine ⟨hd, ?_⟩
      nlinarith
    · rintro ⟨hd, hs⟩
      have hmul := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      have hp := Nat.pos_of_mem_divisors hd
      have heq : d = m / d := by nlinarith
      exact ⟨⟨hd, heq.le⟩, hd, heq.ge⟩
  have hsmall : L = m.divisors.filter (fun d ↦ d ≤ m.sqrt) := by
    ext d
    simp only [L, Finset.mem_filter]
    constructor
    · rintro ⟨hd, hle⟩
      refine ⟨hd, Nat.le_sqrt.mpr ?_⟩
      exact (Nat.le_div_iff_mul_le (Nat.pos_of_mem_divisors hd)).mp hle
    · rintro ⟨hd, hle⟩
      refine ⟨hd, (Nat.le_div_iff_mul_le (Nat.pos_of_mem_divisors hd)).mpr ?_⟩
      exact Nat.le_sqrt.mp hle
  have hc := Finset.card_union_add_card_inter L U
  rw [hunion, hinter, hcard, hsmall] at hc
  simpa only [ArithmeticFunction.sigma_zero_apply, two_mul] using hc

lemma card_square_divisors_le_one (m : ℕ) :
    (m.divisors.filter (fun d ↦ d ^ 2 = m)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  nlinarith

noncomputable def Erdos975SmallDivisorSum (f : ℤ[X]) (x : ℝ) : ℝ :=
  ∑ n ≤ ⌊x⌋₊, (((⌊f.eval (n : ℤ)⌋₊).divisors.filter
    (fun d ↦ d ≤ (⌊f.eval (n : ℤ)⌋₊).sqrt)).card : ℝ)

noncomputable def Erdos975SquareCorrection (f : ℤ[X]) (x : ℝ) : ℝ :=
  ∑ n ≤ ⌊x⌋₊, (((⌊f.eval (n : ℤ)⌋₊).divisors.filter
    (fun d ↦ d ^ 2 = ⌊f.eval (n : ℤ)⌋₊)).card : ℝ)

lemma erdos975Sum_hyperbola (f : ℤ[X]) (x : ℝ) :
    Erdos975Sum f x + Erdos975SquareCorrection f x = 2 * Erdos975SmallDivisorSum f x := by
  simp only [Erdos975Sum, Erdos975SquareCorrection, Erdos975SmallDivisorSum,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact_mod_cast sigma_zero_hyperbola ⌊f.eval (n : ℤ)⌋₊

lemma squareCorrection_bounds (f : ℤ[X]) (x : ℝ) :
    0 ≤ Erdos975SquareCorrection f x ∧ Erdos975SquareCorrection f x ≤ ⌊x⌋₊ + 1 := by
  constructor
  · exact Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
  · calc
      Erdos975SquareCorrection f x ≤ ∑ n ∈ Finset.Iic ⌊x⌋₊, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        exact_mod_cast card_square_divisors_le_one ⌊f.eval (n : ℤ)⌋₊
      _ = _ := by simp

lemma tendsto_squareCorrection (f : ℤ[X]) :
    Tendsto (fun x ↦ Erdos975SquareCorrection f x / (x * log x)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (Real.tendsto_log_atTop.const_div_atTop 2)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_nonneg (squareCorrection_bounds f x).1
      (mul_nonneg (by linarith) (Real.log_pos hx).le)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have h0 : 0 < x := by linarith
    have hl : 0 < log x := Real.log_pos hx
    calc
      Erdos975SquareCorrection f x / (x * log x) ≤ (2 * x) / (x * log x) := by
        apply div_le_div_of_nonneg_right _ (mul_pos h0 hl).le
        have hc := (squareCorrection_bounds f x).2
        have hf := Nat.floor_le h0.le
        linarith
      _ = 2 / log x := by field_simp

lemma small_divisors_eq_filter_Icc (m D : ℕ) (hD : m.sqrt ≤ D) :
    m.divisors.filter (fun d ↦ d ≤ m.sqrt) =
      (Finset.Icc 1 D).filter (fun d ↦ d ∣ m ∧ d ^ 2 ≤ m ∧ m ≠ 0) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd, hm⟩, hs⟩
    have hp := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hm)
    exact ⟨⟨hp, hs.trans hD⟩, hd, Nat.le_sqrt'.mp hs, hm⟩
  · rintro ⟨_, hd, hs, hm⟩
    exact ⟨⟨hd, hm⟩, Nat.le_sqrt'.mpr hs⟩

lemma smallDivisorSum_swap (f : ℤ[X]) (N D : ℕ)
    (hD : ∀ n ≤ N, (⌊f.eval (n : ℤ)⌋₊).sqrt ≤ D) :
    Erdos975SmallDivisorSum f N =
      ∑ d ∈ Finset.Icc 1 D,
        (((Finset.Iic N).filter (fun n : ℕ ↦ d ∣ ⌊f.eval (n : ℤ)⌋₊ ∧
          d ^ 2 ≤ ⌊f.eval (n : ℤ)⌋₊ ∧ ⌊f.eval (n : ℤ)⌋₊ ≠ 0)).card : ℝ) := by
  simp only [Erdos975SmallDivisorSum, Nat.floor_natCast]
  calc
    ∑ n ∈ Finset.Iic N,
        (((⌊f.eval (n : ℤ)⌋₊).divisors.filter
          (fun d ↦ d ≤ (⌊f.eval (n : ℤ)⌋₊).sqrt)).card : ℝ) =
      ∑ n ∈ Finset.Iic N,
        (((Finset.Icc 1 D).filter (fun d ↦ d ∣ ⌊f.eval (n : ℤ)⌋₊ ∧
          d ^ 2 ≤ ⌊f.eval (n : ℤ)⌋₊ ∧ ⌊f.eval (n : ℤ)⌋₊ ≠ 0)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [small_divisors_eq_filter_Icc _ D (hD n (Finset.mem_Iic.mp hn))]
    _ = _ := by
      simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
      exact Finset.sum_comm

lemma small_divisor_floor_iff (z : ℤ) (d : ℕ) (hd : 0 < d) :
    (d ∣ ⌊z⌋₊ ∧ d ^ 2 ≤ ⌊z⌋₊ ∧ ⌊z⌋₊ ≠ 0) ↔ ((d : ℤ) ∣ z ∧ (d : ℤ) ^ 2 ≤ z) := by
  by_cases hz : 0 ≤ z
  · lift z to ℕ using hz
    simp only [Nat.floor_natCast, Int.natCast_dvd_natCast, ← Nat.cast_pow, Nat.cast_le]
    constructor
    · exact fun h ↦ ⟨h.1, h.2.1⟩
    · intro h
      refine ⟨h.1, h.2, ?_⟩
      have := pow_pos hd 2
      omega
  · have hz' : z < 0 := lt_of_not_ge hz
    rw [Nat.floor_of_nonpos hz'.le]
    constructor
    · intro h
      exact False.elim (h.2.2 rfl)
    · intro h
      have := sq_nonneg (d : ℤ)
      omega

lemma smallDivisorSum_swap_int (f : ℤ[X]) (N D : ℕ)
    (hD : ∀ n ≤ N, (⌊f.eval (n : ℤ)⌋₊).sqrt ≤ D) :
    Erdos975SmallDivisorSum f N =
      ∑ d ∈ Finset.Icc 1 D,
        (((Finset.Iic N).filter (fun n : ℕ ↦
          (d : ℤ) ∣ f.eval (n : ℤ) ∧ (d : ℤ) ^ 2 ≤ f.eval (n : ℤ))).card : ℝ) := by
  rw [smallDivisorSum_swap f N D hD]
  apply Finset.sum_congr rfl
  intro d hd
  congr 2
  apply Finset.filter_congr
  intro n hn
  exact small_divisor_floor_iff (f.eval (n : ℤ)) d (Finset.mem_Icc.mp hd).1

lemma periodic_zero_sum_range (u : ℕ → ℝ) (a : ℕ) (hu : Function.Periodic u a)
    (hzero : ∑ i ∈ Finset.range a, u i = 0) (N : ℕ) :
    ∑ i ∈ Finset.range N, u i = ∑ i ∈ Finset.range (N % a), u i := by
  have hblock : ∀ q : ℕ, ∑ i ∈ Finset.range (q * a), u i = 0 := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      have hshift : ∀ i, u (q * a + i) = u i := by
        intro i
        simpa only [Nat.cast_id, Nat.add_comm] using hu.nat_mul q i
      simp_rw [hshift]
      exact zero_add _ |>.trans hzero
  have hN : N / a * a + N % a = N := by
    simpa only [Nat.add_comm] using Nat.mod_add_div' N a
  calc
    ∑ i ∈ Finset.range N, u i =
        ∑ i ∈ Finset.range (N / a * a + N % a), u i := by rw [hN]
    _ = (∑ i ∈ Finset.range (N / a * a), u i) +
        ∑ i ∈ Finset.range (N % a), u (N / a * a + i) := Finset.sum_range_add ..
    _ = ∑ i ∈ Finset.range (N % a), u i := by
      rw [hblock, zero_add]
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [Nat.cast_id, Nat.add_comm] using hu.nat_mul (N / a) i

lemma periodic_zero_sum_bound (u : ℕ → ℝ) (a : ℕ) (ha : 0 < a)
    (hu : Function.Periodic u a) (hzero : ∑ i ∈ Finset.range a, u i = 0) (N : ℕ) :
    ‖∑ i ∈ Finset.range N, u i‖ ≤ ∑ i ∈ Finset.range a, ‖u i‖ := by
  rw [periodic_zero_sum_range u a hu hzero N]
  calc
    ‖∑ i ∈ Finset.range (N % a), u i‖ ≤
        ∑ i ∈ Finset.range (N % a), ‖u i‖ := norm_sum_le ..
    _ ≤ ∑ i ∈ Finset.range a, ‖u i‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.mod_lt N ha).le) (fun i _ _ ↦ norm_nonneg (u i))

lemma tendsto_harmonic_div_log :
    Tendsto (fun N : ℕ ↦ (harmonic N : ℝ) / log N) atTop (𝓝 1) := by
  have ht := (Real.tendsto_harmonic_sub_log.div_atTop
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).add_const 1
  simp only [zero_add, Function.comp_def] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  have hl : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  field_simp
  ring

lemma periodic_harmonic_limit (u : ℕ → ℝ) (a : ℕ) (ha : 0 < a)
    (hu : Function.Periodic u a) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N, u (n + 1) / (n + 1 : ℝ)) / log N)
      atTop (𝓝 ((∑ n ∈ Finset.range a, u (n + 1)) / a)) := by
  let c : ℝ := (∑ n ∈ Finset.range a, u (n + 1)) / a
  let z : ℕ → ℝ := fun n ↦ u (n + 1) - c
  have hzper : Function.Periodic z a := by
    intro n
    change u (n + a + 1) - c = u (n + 1) - c
    rw [show n + a + 1 = (n + 1) + a by omega, hu (n + 1)]
  have hzsum : ∑ n ∈ Finset.range a, z n = 0 := by
    simp only [z, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    dsimp [c]
    field_simp
    ring
  have hanti : Antitone (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) := by
    intro n m hnm
    apply inv_anti₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hlim : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hlim
      (periodic_zero_sum_bound z a ha hzper hzsum))
  have hL' : Tendsto (fun N : ℕ ↦
      (∑ n ∈ Finset.range N, u (n + 1) / (n + 1 : ℝ)) - c * harmonic N)
      atTop (𝓝 L) := by
    apply hL.congr
    intro N
    simp only [smul_eq_mul, z, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum,
      harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Nat.cast_add, Nat.cast_one,
      Rat.cast_add, Rat.cast_one]
    simp only [div_eq_mul_inv, mul_comm]
  have ht := (hL'.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).add
    (tendsto_harmonic_div_log.const_mul c)
  simp only [zero_add, mul_one, Function.comp_def] at ht
  apply ht.congr
  intro N
  ring

lemma sum_Icc_one_eq_sum_range_succ (g : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, g n) = ∑ n ∈ Finset.range N, g (n + 1) := by
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' g 0 N (c := 1)]
  simp only [Nat.zero_add, Finset.Ico_add_one_right_eq_Icc]

lemma coprime_harmonic_limit (a : ℕ) (ha : 0 < a) :
    ∃ c > (0 : ℝ), Tendsto
      (fun N : ℕ ↦ (∑ d ∈ Finset.Icc 1 N, if a.Coprime d then (1 : ℝ) / d else 0) / log N)
      atTop (𝓝 c) := by
  let u : ℕ → ℝ := fun d ↦ if a.Coprime d then 1 else 0
  let c : ℝ := (∑ n ∈ Finset.range a, u (n + 1)) / a
  have hu : Function.Periodic u a := by
    intro n
    simp only [u, Nat.coprime_add_self_right]
  have hc : 0 < c := by
    apply div_pos _ (Nat.cast_pos.mpr ha)
    apply Finset.sum_pos'
    · intro i hi
      dsimp [u]
      positivity
    · refine ⟨0, Finset.mem_range.mpr ha, ?_⟩
      simp [u]
  refine ⟨c, hc, ?_⟩
  apply (periodic_harmonic_limit u a ha hu).congr
  intro N
  rw [sum_Icc_one_eq_sum_range_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  dsimp [u]
  split_ifs <;> simp

lemma linear_root_card (a b d : ℕ) (hab : a.Coprime b) (hd : 0 < d) :
    ((Finset.range d).filter (fun r ↦ d ∣ a * r + b)).card =
      if a.Coprime d then 1 else 0 := by
  haveI : NeZero d := ⟨hd.ne'⟩
  by_cases had : a.Coprime d
  · rw [if_pos had]
    let r : ZMod d := -((a : ZMod d)⁻¹ * b)
    have hsol : (a : ZMod d) * r + b = 0 := by
      dsimp [r]
      rw [mul_neg, ← mul_assoc, ZMod.coe_mul_inv_eq_one a had]
      simp
    have heq : ∀ n : ℕ, d ∣ a * n + b ↔ (a : ZMod d) * n + b = 0 := by
      intro n
      rw [← Nat.cast_mul, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    have hset : (Finset.range d).filter (fun n ↦ d ∣ a * n + b) = {r.val} := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hn, hdiv⟩
        have hmul : (a : ZMod d) * n = (a : ZMod d) * r :=
          add_right_cancel ((heq n).mp hdiv |>.trans hsol.symm)
        have hnZ : (n : ZMod d) = r :=
          (ZMod.isUnit_iff_coprime a d |>.mpr had).mul_right_injective hmul
        have hmod : n ≡ r.val [MOD d] :=
          (ZMod.natCast_eq_natCast_iff n r.val d).mp (hnZ.trans (ZMod.natCast_zmod_val r).symm)
        exact hmod.eq_of_lt_of_lt hn (ZMod.val_lt r)
      · rintro rfl
        exact ⟨ZMod.val_lt r, (heq r.val).mpr (by simpa using hsol)⟩
    simp [hset]
  · rw [if_neg had]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have hdiv := (Finset.mem_filter.mp hr).2
    have hg : a.gcd d ∣ a * r + b := (Nat.gcd_dvd_right a d).trans hdiv
    have hgb : a.gcd d ∣ b :=
      (Nat.dvd_add_right (dvd_mul_of_dvd_left (Nat.gcd_dvd_left a d) r)).mp hg
    exact had (Nat.eq_one_of_dvd_coprimes hab (Nat.gcd_dvd_left a d) hgb)

lemma sigma_zero_fixed_hyperbola (m D : ℕ) (hD : m.sqrt ≤ D) :
    σ 0 m + (m.divisors.filter (fun d ↦ d ≤ D ∧ m / d ≤ D)).card =
      2 * (m.divisors.filter (fun d ↦ d ≤ D)).card := by
  let L := m.divisors.filter (fun d ↦ d ≤ D)
  let U := m.divisors.filter (fun d ↦ m / d ≤ D)
  have hcard : U.card = L.card := by
    simp only [U, L, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Nat.sum_div_divisors m (fun d ↦ if d ≤ D then 1 else 0)
  have hunion : L ∪ U = m.divisors := by
    ext d
    simp only [L, U, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hd
      have hm := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      rcases Nat.le_sqrt_of_eq_mul hm.symm with h | h
      · exact Or.inl ⟨hd, h.trans hD⟩
      · exact Or.inr ⟨hd, h.trans hD⟩
  have hinter : L ∩ U = m.divisors.filter (fun d ↦ d ≤ D ∧ m / d ≤ D) := by
    ext d
    simp only [L, U, Finset.mem_inter, Finset.mem_filter]
    tauto
  have hc := Finset.card_union_add_card_inter L U
  rw [hunion, hinter, hcard] at hc
  simpa only [ArithmeticFunction.sigma_zero_apply, L, two_mul] using hc

lemma card_divisors_both_le (m D : ℕ) :
    (m.divisors.filter (fun d ↦ d ≤ D ∧ m / d ≤ D)).card =
      (((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D)).filter (fun p : ℕ × ℕ ↦ p.1 * p.2 = m)).card := by
  have hset : (((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D)).filter
      (fun p : ℕ × ℕ ↦ p.1 * p.2 = m)) =
      m.divisorsAntidiagonal.filter (fun p ↦ p.1 ≤ D ∧ p.2 ≤ D) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Nat.mem_divisorsAntidiagonal]
    constructor
    · rintro ⟨⟨⟨h1, h1D⟩, ⟨h2, h2D⟩⟩, he⟩
      refine ⟨⟨he, ?_⟩, h1D, h2D⟩
      have hp1 : 0 < p.1 := by omega
      have hp2 : 0 < p.2 := by omega
      have := Nat.mul_pos hp1 hp2
      omega
    · rintro ⟨⟨he, hm⟩, h1D, h2D⟩
      have hprod : p.1 ≠ 0 ∧ p.2 ≠ 0 := mul_ne_zero_iff.mp (he ▸ hm)
      exact ⟨⟨⟨Nat.pos_of_ne_zero hprod.1, h1D⟩, ⟨Nat.pos_of_ne_zero hprod.2, h2D⟩⟩, he⟩
  rw [hset, ← Nat.map_div_right_divisors, Finset.filter_map, Finset.card_map]
  rfl

lemma sum_card_product_fibers_le (g : ℕ → ℕ) (hg : Function.Injective g)
    (s : Finset ℕ) (D : ℕ) :
    ∑ n ∈ s, ((((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D)).filter
      (fun p : ℕ × ℕ ↦ p.1 * p.2 = g n)).card) ≤ D ^ 2 := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    ∑ p ∈ (Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D),
        ∑ n ∈ s, (if p.1 * p.2 = g n then 1 else 0) ≤
      ∑ _p ∈ (Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D), 1 := by
      apply Finset.sum_le_sum
      intro p hp
      rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
      apply Finset.card_le_one.mpr
      intro n hn k hk
      apply hg
      exact (Finset.mem_filter.mp hn).2.symm.trans (Finset.mem_filter.mp hk).2
    _ = _ := by simp [pow_two]

lemma divisors_filter_le_eq (m D : ℕ) (hm : m ≠ 0) :
    m.divisors.filter (fun d ↦ d ≤ D) = (Finset.Icc 1 D).filter (fun d ↦ d ∣ m) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd, _⟩, hD⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hm), hD⟩, hd⟩
  · exact fun h ↦ ⟨⟨h.2, hm⟩, h.1.2⟩

lemma sum_sigma_fixed_hyperbola_bounds (g : ℕ → ℕ) (hg : Function.Injective g)
    (s : Finset ℕ) (D : ℕ) (hpos : ∀ n ∈ s, g n ≠ 0)
    (hD : ∀ n ∈ s, (g n).sqrt ≤ D) :
    (∑ n ∈ s, σ 0 (g n)) ≤
        2 * ∑ d ∈ Finset.Icc 1 D, (s.filter (fun n ↦ d ∣ g n)).card ∧
    2 * (∑ d ∈ Finset.Icc 1 D, (s.filter (fun n ↦ d ∣ g n)).card) ≤
        (∑ n ∈ s, σ 0 (g n)) + D ^ 2 := by
  have he : (∑ n ∈ s, σ 0 (g n)) +
      (∑ n ∈ s, ((g n).divisors.filter (fun d ↦ d ≤ D ∧ g n / d ≤ D)).card) =
      2 * ∑ d ∈ Finset.Icc 1 D, (s.filter (fun n ↦ d ∣ g n)).card := by
    rw [← Finset.sum_add_distrib]
    calc
      ∑ n ∈ s, (σ 0 (g n) + ((g n).divisors.filter (fun d ↦ d ≤ D ∧ g n / d ≤ D)).card) =
          ∑ n ∈ s, 2 * ((g n).divisors.filter (fun d ↦ d ≤ D)).card := by
        apply Finset.sum_congr rfl
        exact fun n hn ↦ sigma_zero_fixed_hyperbola (g n) D (hD n hn)
      _ = 2 * ∑ d ∈ Finset.Icc 1 D, (s.filter (fun n ↦ d ∣ g n)).card := by
        rw [← Finset.mul_sum]
        congr 1
        calc
          ∑ n ∈ s, ((g n).divisors.filter (fun d ↦ d ≤ D)).card =
              ∑ n ∈ s, ((Finset.Icc 1 D).filter (fun d ↦ d ∣ g n)).card := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [divisors_filter_le_eq _ D (hpos n hn)]
          _ = _ := by
            simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
            exact Finset.sum_comm
  have hb : (∑ n ∈ s, ((g n).divisors.filter (fun d ↦ d ≤ D ∧ g n / d ≤ D)).card) ≤ D ^ 2 := by
    simp only [card_divisors_both_le]
    exact sum_card_product_fibers_le g hg s D
  omega

noncomputable def linearPolynomial (a b : ℕ) : ℤ[X] := C (a : ℤ) * X + C (b : ℤ)

lemma eval_linearPolynomial (a b n : ℕ) :
    (linearPolynomial a b).eval (n : ℤ) = (a * n + b : ℕ) := by
  simp [linearPolynomial]

lemma root_card_linearPolynomial (a b d : ℕ) (hab : a.Coprime b) (hd : 0 < d) :
    (polynomialRootResidues (linearPolynomial a b) d).card = if a.Coprime d then 1 else 0 := by
  simp only [polynomialRootResidues, eval_linearPolynomial, Int.natCast_dvd_natCast]
  exact linear_root_card a b d hab hd

noncomputable def linearHarmonic (a D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, if a.Coprime d then (1 : ℝ) / d else 0

noncomputable def linearTruncatedSum (a b N D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D,
    (((Finset.Iic N).filter (fun n ↦ d ∣ a * n + b)).card : ℝ)

lemma linear_truncated_error (a b N D : ℕ) (hab : a.Coprime b) :
    |linearTruncatedSum a b N D - (N + 1 : ℝ) * linearHarmonic a D| ≤ D := by
  have hρ : (∑ d ∈ Finset.Icc 1 D,
      (polynomialRootResidues (linearPolynomial a b) d).card / (d : ℝ)) =
      linearHarmonic a D := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [root_card_linearPolynomial a b d hab (Finset.mem_Icc.mp hd).1]
    split_ifs <;> simp
  have hρb : (∑ d ∈ Finset.Icc 1 D,
      ((polynomialRootResidues (linearPolynomial a b) d).card : ℝ)) ≤ D := by
    calc
      _ ≤ ∑ _d ∈ Finset.Icc 1 D, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [root_card_linearPolynomial a b d hab (Finset.mem_Icc.mp hd).1]
        split_ifs <;> norm_num
      _ = _ := by simp
  have h := (truncated_divisor_count_error (linearPolynomial a b) D (N + 1)).trans hρb
  rw [hρ] at h
  have hI : Finset.range (N + 1) = Finset.Iic N := by
    ext n
    simp
  simp only [hI, eval_linearPolynomial, Int.natCast_dvd_natCast] at h
  simpa only [Nat.cast_add, Nat.cast_one, linearTruncatedSum] using h

lemma sum_linearPolynomial (a b N : ℕ) :
    Erdos975Sum (linearPolynomial a b) N =
      ∑ n ∈ Finset.Iic N, (σ 0 (a * n + b) : ℝ) := by
  simp only [Erdos975Sum, Nat.floor_natCast, eval_linearPolynomial]

lemma linear_divisor_approx (a b N : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    |Erdos975Sum (linearPolynomial a b) N -
      2 * (N + 1 : ℝ) * linearHarmonic a (a * N + b).sqrt| ≤ 3 * (a * N + b : ℕ) := by
  let D := (a * N + b).sqrt
  have hinj : Function.Injective (fun n ↦ a * n + b) := by
    intro n m h
    exact mul_left_cancel₀ ha.ne' (add_right_cancel h)
  have hpos : ∀ n ∈ Finset.Iic N, a * n + b ≠ 0 := by
    intro n hn
    omega
  have hD : ∀ n ∈ Finset.Iic N, (a * n + b).sqrt ≤ D := by
    intro n hn
    apply Nat.sqrt_le_sqrt
    exact Nat.add_le_add_right (Nat.mul_le_mul_left a (Finset.mem_Iic.mp hn)) b
  have hs := sum_sigma_fixed_hyperbola_bounds (fun n ↦ a * n + b) hinj (Finset.Iic N) D hpos hD
  have hs1 : Erdos975Sum (linearPolynomial a b) N ≤ 2 * linearTruncatedSum a b N D := by
    rw [sum_linearPolynomial]
    simp only [linearTruncatedSum]
    exact_mod_cast hs.1
  have hs2 : 2 * linearTruncatedSum a b N D ≤
      Erdos975Sum (linearPolynomial a b) N + (D : ℝ) ^ 2 := by
    rw [sum_linearPolynomial]
    simp only [linearTruncatedSum]
    exact_mod_cast hs.2
  have he := linear_truncated_error a b N D hab
  rw [abs_le] at he ⊢
  have hDsq : (D : ℝ) ^ 2 ≤ (a * N + b : ℕ) := by
    exact_mod_cast Nat.sqrt_le' (a * N + b)
  have hDle : (D : ℝ) ≤ (a * N + b : ℕ) := by
    exact_mod_cast Nat.sqrt_le_self (a * N + b)
  constructor <;> dsimp only [D] at * <;> nlinarith

lemma tendsto_linear_nat_value (a b : ℕ) (ha : 0 < a) :
    Tendsto (fun N : ℕ ↦ (a * N + b : ℕ) : ℕ → ℝ) atTop atTop := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have h : Tendsto (fun N : ℕ ↦ (a : ℝ) * N + b) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop haR).atTop_add tendsto_const_nhds
  simpa only [Nat.cast_add, Nat.cast_mul] using h

lemma tendsto_sqrt_linear_nat_value (a b : ℕ) (ha : 0 < a) :
    Tendsto (fun N : ℕ ↦ (a * N + b).sqrt) atTop atTop := by
  have h := (tendsto_nat_floor_atTop (α := ℝ)).comp
    (Real.tendsto_sqrt_atTop.comp (tendsto_linear_nat_value a b ha))
  simpa only [Function.comp_def, Real.nat_floor_real_sqrt_eq_nat_sqrt] using h

lemma tendsto_log_linear_nat_value (a b : ℕ) (ha : 0 < a) :
    Tendsto (fun N : ℕ ↦ log (a * N + b : ℕ) / log N) atTop (𝓝 1) := by
  have hN : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hq : Tendsto (fun N : ℕ ↦ (a * N + b : ℕ) / (N : ℝ)) atTop (𝓝 (a : ℝ)) := by
    have ht : Tendsto (fun N : ℕ ↦ (a : ℝ) + b / N) atTop (𝓝 ((a : ℝ) + 0)) :=
      tendsto_const_nhds.add (hN.const_div_atTop (b : ℝ))
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    push_cast
    field_simp
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have ht := ((hq.log haR.ne').div_atTop (Real.tendsto_log_atTop.comp hN)).add_const 1
  simp only [zero_add, Function.comp_def] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM0 : (0 : ℝ) < (a * N + b : ℕ) := by
    exact_mod_cast Nat.add_pos_left (Nat.mul_pos ha (by omega)) b
  have hl : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
  rw [Real.log_div hM0.ne' hN0.ne']
  field_simp
  ring

lemma tendsto_log_sqrt_linear_nat_value (a b : ℕ) (ha : 0 < a) :
    Tendsto (fun N : ℕ ↦ log ((a * N + b).sqrt : ℝ) / log N) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hM := tendsto_linear_nat_value a b ha
  have hs := Real.tendsto_sqrt_atTop.comp hM
  have he := Asymptotics.isEquivalent_nat_floor (R := ℝ) |>.comp_tendsto hs
  have he' := he.log hs
  have he'' := he'.div (Asymptotics.IsEquivalent.refl (u := fun N : ℕ ↦ log (N : ℝ)))
  simp only [Function.comp_def, Real.nat_floor_real_sqrt_eq_nat_sqrt] at he''
  apply he''.tendsto_nhds_iff.mpr
  apply ((tendsto_log_linear_nat_value a b ha).div_const 2).congr
  intro N
  change _ = log (Real.sqrt (a * N + b : ℕ)) / log (N : ℝ)
  rw [Real.log_sqrt (Nat.cast_nonneg _)]
  ring

lemma tendsto_linear_divisor_error (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    Tendsto (fun N : ℕ ↦
      (Erdos975Sum (linearPolynomial a b) N -
        2 * (N + 1 : ℝ) * linearHarmonic a (a * N + b).sqrt) / ((N : ℝ) * log N))
      atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop)
  apply squeeze_zero_norm' _ (hlog.const_div_atTop (3 * (a + b : ℕ)))
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hp : 0 < (N : ℝ) * log N := mul_pos hN0 hl
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hp]
  have hM : (a * N + b : ℕ) ≤ (a + b) * N := by
    have := Nat.le_mul_of_pos_right b (show 0 < N by omega)
    nlinarith
  calc
    _ ≤ (3 * (a * N + b : ℕ)) / ((N : ℝ) * log N) :=
      div_le_div_of_nonneg_right (linear_divisor_approx a b N ha hb hab) hp.le
    _ ≤ (3 * ((a + b : ℕ) * N)) / ((N : ℝ) * log N) := by
      apply div_le_div_of_nonneg_right _ hp.le
      have hM' : ((a * N + b : ℕ) : ℝ) ≤ ((a + b : ℕ) : ℝ) * N := by exact_mod_cast hM
      linarith
    _ = (3 * (a + b : ℕ)) / log N := by field_simp

lemma erdos975_linear_nat (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    ∃ c > (0 : ℝ),
      Tendsto (fun x ↦ Erdos975Sum (linearPolynomial a b) x / (x * log x)) atTop (𝓝 c) := by
  obtain ⟨c, hc, hH⟩ := coprime_harmonic_limit a ha
  change Tendsto (fun N : ℕ ↦ linearHarmonic a N / log N) atTop (𝓝 c) at hH
  have hD := tendsto_sqrt_linear_nat_value a b ha
  have hprod := (hH.comp hD).mul (tendsto_log_sqrt_linear_nat_value a b ha)
  have hH' : Tendsto (fun N : ℕ ↦ linearHarmonic a (a * N + b).sqrt / log N)
      atTop (𝓝 (c / 2)) := by
    have hc' : c * (1 / 2) = c / 2 := by ring
    rw [hc'] at hprod
    apply hprod.congr'
    filter_upwards [hD.eventually_gt_atTop 1] with N hDN
    have hl : 0 < log ((a * N + b).sqrt : ℝ) := Real.log_pos (by exact_mod_cast hDN)
    dsimp only [Function.comp_def]
    field_simp
  have hpref : Tendsto (fun N : ℕ ↦ (N + 1 : ℝ) / N) atTop (𝓝 1) := by
    have ht := (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop).const_div_atTop 1
    have ht' := ht.const_add 1
    norm_num only [add_zero] at ht'
    apply ht'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    field_simp
  have hmain : Tendsto (fun N : ℕ ↦
      (2 * (N + 1 : ℝ) * linearHarmonic a (a * N + b).sqrt) / ((N : ℝ) * log N))
      atTop (𝓝 c) := by
    have ht := (hpref.const_mul 2).mul hH'
    have hc' : 2 * 1 * (c / 2) = c := by ring
    rw [hc'] at ht
    apply ht.congr
    intro N
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  refine ⟨c, hc, (tendsto_erdos975Sum_iff_nat (linearPolynomial a b) c).mpr ?_⟩
  have ht := (tendsto_linear_divisor_error a b ha hb hab).add hmain
  simp only [zero_add] at ht
  apply ht.congr
  intro N
  ring

lemma erdos975Sum_nat_range (f : ℤ[X]) (N : ℕ) :
    Erdos975Sum f N = ∑ n ∈ Finset.range (N + 1), (σ 0 ⌊f.eval (n : ℤ)⌋₊ : ℝ) := by
  simp only [Erdos975Sum, Nat.floor_natCast]
  congr 1
  ext n
  simp

lemma erdos975Sum_shift_nat (f : ℤ[X]) (k N : ℕ) :
    Erdos975Sum f (N + k : ℕ) =
      Erdos975Sum (f.comp (X + C (k : ℤ))) N +
        ∑ n ∈ Finset.range k, (σ 0 ⌊f.eval (n : ℤ)⌋₊ : ℝ) := by
  simp only [erdos975Sum_nat_range, eval_comp, eval_add, eval_X, eval_C]
  have h := Finset.sum_range_add (fun n : ℕ ↦ (σ 0 ⌊f.eval (n : ℤ)⌋₊ : ℝ)) k (N + 1)
  simpa only [Nat.cast_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
    Int.add_comm, add_comm] using h

lemma erdos975_shift_iff (f : ℤ[X]) (k : ℕ) (c : ℝ) :
    Tendsto (fun x ↦ Erdos975Sum f x / (x * log x)) atTop (𝓝 c) ↔
    Tendsto (fun x ↦ Erdos975Sum (f.comp (X + C (k : ℤ))) x / (x * log x)) atTop (𝓝 c) := by
  rw [tendsto_erdos975Sum_iff_nat, tendsto_erdos975Sum_iff_nat]
  let P : ℝ := ∑ n ∈ Finset.range k, (σ 0 ⌊f.eval (n : ℤ)⌋₊ : ℝ)
  have hN : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlogN := Real.tendsto_log_atTop.comp hN
  have hquot : Tendsto (fun N : ℕ ↦ (N + k : ℕ) / (N : ℝ)) atTop (𝓝 1) := by
    have ht := (hN.const_div_atTop (k : ℝ)).const_add 1
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    push_cast
    field_simp
  have he : Asymptotics.IsEquivalent atTop
      (fun N : ℕ ↦ ((N + k : ℕ) : ℝ)) (fun N : ℕ ↦ (N : ℝ)) :=
    (Asymptotics.isEquivalent_iff_tendsto_one (hN.eventually_ne_atTop 0)).mpr hquot
  have hd := he.mul (he.log hN)
  have hr := (Asymptotics.IsEquivalent.refl (u := fun N : ℕ ↦ Erdos975Sum f (N + k : ℕ))).div hd
  have hz : Tendsto (fun N : ℕ ↦ P / ((N : ℝ) * log N)) atTop (𝓝 0) := by
    have ht := (hN.const_div_atTop P).div_atTop hlogN
    simpa only [Function.comp_def, div_div] using ht
  have heq : ∀ N : ℕ, Erdos975Sum f (N + k : ℕ) / ((N : ℝ) * log N) =
      Erdos975Sum (f.comp (X + C (k : ℤ))) N / ((N : ℝ) * log N) + P / ((N : ℝ) * log N) := by
    intro N
    rw [erdos975Sum_shift_nat, add_div]
  constructor
  · intro h
    have ht := hr.tendsto_nhds_iff.mp (h.comp (tendsto_add_atTop_nat k))
    have ht' := ht.sub hz
    simp only [sub_zero] at ht'
    apply ht'.congr
    intro N
    change Erdos975Sum f (N + k : ℕ) / ((N : ℝ) * log N) - P / ((N : ℝ) * log N) = _
    rw [heq]
    ring
  · intro h
    have ht := h.add hz
    simp only [add_zero] at ht
    have ht' : Tendsto (fun N : ℕ ↦ Erdos975Sum f (N + k : ℕ) / ((N : ℝ) * log N)) atTop (𝓝 c) :=
      ht.congr (fun N ↦ (heq N).symm)
    exact (tendsto_add_atTop_iff_nat k).mp (hr.tendsto_nhds_iff.mpr ht')

lemma linear_coprime_of_irreducible (a b : ℕ) (ha : 0 < a)
    (hirr : Irreducible (linearPolynomial a b)) : a.Coprime b := by
  have hdeg : (linearPolynomial a b).natDegree = 1 :=
    Polynomial.natDegree_eq_one.mpr ⟨(a : ℤ), by exact_mod_cast ha.ne', (b : ℤ), rfl⟩
  have hCdvd : C ((a.gcd b : ℕ) : ℤ) ∣ linearPolynomial a b := by
    change C ((a.gcd b : ℕ) : ℤ) ∣ C (a : ℤ) * X + C (b : ℤ)
    apply dvd_add
    · apply dvd_mul_of_dvd_left
      exact map_dvd C (show ((a.gcd b : ℕ) : ℤ) ∣ (a : ℤ) by exact_mod_cast Nat.gcd_dvd_left a b)
    · exact map_dvd C (show ((a.gcd b : ℕ) : ℤ) ∣ (b : ℤ) by exact_mod_cast Nat.gcd_dvd_right a b)
  have hu := hirr.isPrimitive (by omega) ((a.gcd b : ℕ) : ℤ) hCdvd
  simpa only [Int.natAbs_natCast] using Int.isUnit_iff_natAbs_eq.mp hu

lemma linear_slope_pos (a b : ℤ) (ha : a ≠ 0)
    (hpos : ∀ᶠ n in atTop, 1 ≤ a * n + b) : 0 < a := by
  by_contra h
  have ha' : a ≤ -1 := by omega
  obtain ⟨n, hn, hn1, hnb⟩ :=
    (hpos.and ((eventually_ge_atTop (1 : ℤ)).and (eventually_ge_atTop (b + 1)))).exists
  have hmul := mul_le_mul_of_nonneg_right ha' (show 0 ≤ n by omega)
  linarith

lemma erdos975_degree_one (f : ℤ[X]) (hdeg : f.natDegree = 1) (hirr : Irreducible f)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    ∃ c > (0 : ℝ), Tendsto (fun x ↦ Erdos975Sum f x / (x * log x)) atTop (𝓝 c) := by
  obtain ⟨a, ha, b, rfl⟩ := Polynomial.natDegree_eq_one.mp hdeg
  have hpos' : ∀ᶠ n : ℤ in atTop, 1 ≤ a * n + b := by
    simpa only [eval_add, eval_mul, eval_C, eval_X] using hpos
  have haP := linear_slope_pos a b ha hpos'
  lift a to ℕ using haP.le
  have haNat : 0 < a := by exact_mod_cast haP
  have hposNat : ∀ᶠ k : ℕ in atTop, 1 ≤ (a : ℤ) * k + b :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ ↦ (k : ℤ)) atTop atTop).eventually hpos'
  obtain ⟨k, hk⟩ := hposNat.exists
  let B := ((a : ℤ) * k + b).toNat
  have hB : (B : ℤ) = (a : ℤ) * k + b := Int.toNat_of_nonneg (by omega)
  have hBP : 0 < B := by
    have h : (0 : ℤ) < (B : ℤ) := by rw [hB]; omega
    exact_mod_cast h
  have hshift : (C (a : ℤ) * X + C b).comp (X + C (k : ℤ)) = linearPolynomial a B := by
    simp only [linearPolynomial, add_comp, mul_comp, C_comp, X_comp, hB, map_add, map_mul]
    ring
  have hirshift : Irreducible ((C (a : ℤ) * X + C b).comp (X + C (k : ℤ))) := by
    simpa only [Polynomial.coe_taylorEquiv, Polynomial.taylor_apply] using
      (Irreducible.map (Polynomial.taylorEquiv (k : ℤ)) hirr)
  rw [hshift] at hirshift
  have hab := linear_coprime_of_irreducible a B haNat hirshift
  obtain ⟨c, hc, hlim⟩ := erdos975_linear_nat a B haNat hBP hab
  refine ⟨c, hc, (erdos975_shift_iff (C (a : ℤ) * X + C b) k c).mpr ?_⟩
  simpa only [hshift] using hlim

abbrev ModularRoot (f : ℤ[X]) (d : ℕ) :=
  {x : ZMod d // f.eval₂ (Int.castRingHom (ZMod d)) x = 0}

lemma eval_mod_natCast (f : ℤ[X]) (d n : ℕ) :
    f.eval₂ (Int.castRingHom (ZMod d)) (n : ZMod d) = ((f.eval (n : ℤ) : ℤ) : ZMod d) := by
  simpa only [Int.coe_castRingHom, Int.cast_natCast] using
    Polynomial.eval₂_at_apply (p := f) (Int.castRingHom (ZMod d)) (n : ℤ)

lemma dvd_eval_iff_eval_mod (f : ℤ[X]) (d n : ℕ) :
    (d : ℤ) ∣ f.eval (n : ℤ) ↔ f.eval₂ (Int.castRingHom (ZMod d)) (n : ZMod d) = 0 := by
  rw [eval_mod_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]

noncomputable def polynomialRootResiduesEquiv (f : ℤ[X]) (d : ℕ) [NeZero d] :
    ↥(polynomialRootResidues f d) ≃ ModularRoot f d where
  toFun r := ⟨(r.val : ZMod d),
    (dvd_eval_iff_eval_mod f d r.val).mp (Finset.mem_filter.mp r.property).2⟩
  invFun x := ⟨x.val.val, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (ZMod.val_lt x.val),
      (dvd_eval_iff_eval_mod f d x.val.val).mpr (by simpa using x.property)⟩⟩
  left_inv r := Subtype.ext (ZMod.val_natCast_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp r.property).1))
  right_inv x := Subtype.ext (ZMod.natCast_zmod_val x.val)

lemma rootResidues_card_eq_modularRoot (f : ℤ[X]) (d : ℕ) [NeZero d] :
    (polynomialRootResidues f d).card = Nat.card (ModularRoot f d) := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    Nat.card_congr (polynomialRootResiduesEquiv f d)

lemma hom_eval₂_int {R S : Type*} [Ring R] [Ring S] (g : R →+* S) (f : ℤ[X]) (x : R) :
    g (f.eval₂ (Int.castRingHom R) x) = f.eval₂ (Int.castRingHom S) (g x) := by
  rw [Polynomial.hom_eval₂, RingHom.ext_int (g.comp (Int.castRingHom R)) (Int.castRingHom S)]

noncomputable def modularRootMulEquiv (f : ℤ[X]) (m n : ℕ) (hmn : m.Coprime n) :
    ModularRoot f (m * n) ≃ ModularRoot f m × ModularRoot f n := by
  let e := ZMod.chineseRemainder hmn
  refine (Equiv.subtypeEquiv e.toEquiv ?_).trans Equiv.subtypeProdEquivProd
  intro x
  change f.eval₂ (Int.castRingHom (ZMod (m * n))) x = 0 ↔
    f.eval₂ (Int.castRingHom (ZMod m)) (e x).1 = 0 ∧
    f.eval₂ (Int.castRingHom (ZMod n)) (e x).2 = 0
  rw [← e.map_eq_zero_iff, Prod.ext_iff]
  have h1 := hom_eval₂_int ((RingHom.fst (ZMod m) (ZMod n)).comp e.toRingHom) f x
  have h2 := hom_eval₂_int ((RingHom.snd (ZMod m) (ZMod n)).comp e.toRingHom) f x
  change (e (f.eval₂ (Int.castRingHom (ZMod (m * n))) x)).1 =
    f.eval₂ (Int.castRingHom (ZMod m)) (e x).1 at h1
  change (e (f.eval₂ (Int.castRingHom (ZMod (m * n))) x)).2 =
    f.eval₂ (Int.castRingHom (ZMod n)) (e x).2 at h2
  rw [h1, h2]
  rfl

lemma rootResidues_card_mul (f : ℤ[X]) (m n : ℕ) [NeZero m] [NeZero n] (hmn : m.Coprime n) :
    (polynomialRootResidues f (m * n)).card =
      (polynomialRootResidues f m).card * (polynomialRootResidues f n).card := by
  rw [rootResidues_card_eq_modularRoot, rootResidues_card_eq_modularRoot,
    rootResidues_card_eq_modularRoot]
  simpa only [Nat.card_prod] using Nat.card_congr (modularRootMulEquiv f m n hmn)

noncomputable def polynomialRootCount (f : ℤ[X]) : ArithmeticFunction ℕ where
  toFun d := (polynomialRootResidues f d).card
  map_zero' := by simp [polynomialRootResidues]

lemma polynomialRootCount_multiplicative (f : ℤ[X]) : (polynomialRootCount f).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [polynomialRootCount, polynomialRootResidues]
  · intro m n hm hn hmn
    haveI : NeZero m := ⟨hm⟩
    haveI : NeZero n := ⟨hn⟩
    exact rootResidues_card_mul f m n hmn

noncomputable def harmonicWeightSum (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, u d / d

lemma sum_le_harmonic_split (u : ℕ → ℝ) (hu : ∀ d, 0 ≤ u d)
    (N M : ℕ) (hMN : M ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, u d) ≤
      M * harmonicWeightSum u M + N * (harmonicWeightSum u N - harmonicWeightSum u M) := by
  have hsub : Finset.Icc 1 M ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc le_rfl hMN
  have hs := Finset.sum_sdiff hsub (f := fun d ↦ u d / (d : ℝ))
  have hsr := Finset.sum_sdiff hsub (f := u)
  dsimp [harmonicWeightSum]
  rw [← hsr]
  have hm : ∑ d ∈ Finset.Icc 1 M, u d ≤ M * ∑ d ∈ Finset.Icc 1 M, u d / d := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hdM : (d : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hd).2
    calc
      u d = (d : ℝ) * (u d / d) := by field_simp
      _ ≤ M * (u d / d) := mul_le_mul_of_nonneg_right hdM (div_nonneg (hu d) hd0.le)
  have hn : ∑ d ∈ Finset.Icc 1 N \ Finset.Icc 1 M, u d ≤
      N * ∑ d ∈ Finset.Icc 1 N \ Finset.Icc 1 M, u d / d := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hdN := Finset.mem_Icc.mp (Finset.mem_sdiff.mp hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hdN.1
    have hdN' : (d : ℝ) ≤ N := by exact_mod_cast hdN.2
    calc
      u d = (d : ℝ) * (u d / d) := by field_simp
      _ ≤ N * (u d / d) := mul_le_mul_of_nonneg_right hdN' (div_nonneg (hu d) hd0.le)
  nlinarith

lemma tendsto_log_nat_floor_scaled_div_log (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ ↦ log (⌊a * N⌋₊ : ℝ) / log N) atTop (𝓝 1) := by
  have hN : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hM := hN.const_mul_atTop ha
  have he := (Asymptotics.isEquivalent_nat_floor (R := ℝ)).comp_tendsto hM
  have he' := (he.log hM).div (Asymptotics.IsEquivalent.refl (u := fun N : ℕ ↦ log (N : ℝ)))
  apply he'.tendsto_nhds_iff.mpr
  have hl := (Real.tendsto_log_atTop.comp hN).const_div_atTop (log a)
  have hl' := hl.add_const 1
  simp only [zero_add] at hl'
  apply hl'.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN1)).ne'
  simp only [Function.comp_def, Pi.div_apply]
  rw [Real.log_mul ha.ne' hN0.ne', add_div, div_self hlog]

lemma tendsto_harmonic_scaled (u : ℕ → ℝ) (c : ℝ)
    (h : Tendsto (fun N : ℕ ↦ harmonicWeightSum u N / log N) atTop (𝓝 c))
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ ↦ harmonicWeightSum u ⌊a * N⌋₊ / log N) atTop (𝓝 c) := by
  have hM := tendsto_nat_floor_mul_atTop a ha
  have ht := (h.comp hM).mul (tendsto_log_nat_floor_scaled_div_log a ha)
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [hM.eventually_gt_atTop 1] with N hMN
  have hl : log (⌊a * N⌋₊ : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hMN)).ne'
  dsimp only [Function.comp_def]
  field_simp

lemma tendsto_sum_div_mul_log_of_harmonic (u : ℕ → ℝ) (hu : ∀ d, 0 ≤ u d) (c : ℝ)
    (h : Tendsto (fun N : ℕ ↦ harmonicWeightSum u N / log N) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ ↦ (∑ d ∈ Finset.Icc 1 N, u d) / ((N : ℝ) * log N))
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 ((|c| + 1) / ε))
  have hk1 : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hk0 : (0 : ℝ) < k := lt_trans zero_lt_one hk1
  have hkε : |c| + 1 < ε * k := by
    have := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hk)
    linarith
  let a : ℝ := 1 / k
  have ha : 0 < a := one_div_pos.mpr hk0
  have ha1 : a ≤ 1 := (div_le_one hk0).mpr hk1.le
  have hcε : a * c < ε := by
    dsimp [a]
    rw [one_div_mul_eq_div, div_lt_iff₀ hk0]
    linarith [le_abs_self c]
  have hB : Tendsto (fun N : ℕ ↦ harmonicWeightSum u N / log N +
      (a - 1) * (harmonicWeightSum u ⌊a * N⌋₊ / log N)) atTop (𝓝 (a * c)) := by
    have ht := h.add ((tendsto_harmonic_scaled u c h a ha).const_mul (a - 1))
    have he : c + (a - 1) * c = a * c := by ring
    simpa only [he] using ht
  have hbound : ∀ᶠ N : ℕ in atTop,
      (∑ d ∈ Finset.Icc 1 N, u d) / ((N : ℝ) * log N) ≤
      harmonicWeightSum u N / log N +
      (a - 1) * (harmonicWeightSum u ⌊a * N⌋₊ / log N) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hl : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
    have hM : (⌊a * N⌋₊ : ℝ) ≤ a * N := Nat.floor_le (by positivity)
    have hMN : ⌊a * N⌋₊ ≤ N := by
      exact_mod_cast hM.trans (mul_le_of_le_one_left hN0.le ha1)
    have hs := sum_le_harmonic_split u hu N ⌊a * N⌋₊ hMN
    have hH0 : 0 ≤ harmonicWeightSum u ⌊a * N⌋₊ := by
      exact Finset.sum_nonneg (fun d _ ↦ div_nonneg (hu d) (Nat.cast_nonneg d))
    apply (div_le_iff₀ (mul_pos hN0 hl)).mpr
    have he : (harmonicWeightSum u N / log N +
        (a - 1) * (harmonicWeightSum u ⌊a * N⌋₊ / log N)) * ((N : ℝ) * log N) =
        N * harmonicWeightSum u N + (a - 1) * N * harmonicWeightSum u ⌊a * N⌋₊ := by
      field_simp
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hM hH0]
  have hsmall := hB.eventually (gt_mem_nhds hcε)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp
    (hbound.and (hsmall.and (eventually_gt_atTop (1 : ℕ))))
  refine ⟨N0, fun N hN ↦ ?_⟩
  obtain ⟨hb, hlt, hN1⟩ := hN0 N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg]
  · exact hb.trans_lt hlt
  · apply div_nonneg (Finset.sum_nonneg (fun d _ ↦ hu d))
    exact mul_nonneg (Nat.cast_nonneg N) (Real.log_nonneg (by exact_mod_cast hN1.le))

open scoped ArithmeticFunction.Moebius

lemma sum_multiples_weighted (v : ℕ → ℝ) (q N : ℕ) (hq : 0 < q) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n ↦ q ∣ n), v n) =
      ∑ j ∈ Finset.Icc 1 (N / q), v (q * j) := by
  symm
  apply Finset.sum_nbij (fun j ↦ q * j)
  · intro j hj
    obtain ⟨hj1, hjN⟩ := Finset.mem_Icc.mp hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith, ?_⟩, dvd_mul_right _ _⟩
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hq).mp hjN
  · intro i hi j hj hij
    exact Nat.eq_of_mul_eq_mul_left hq hij
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hqn⟩ := hn
    refine ⟨n / q, Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hnN⟩, Nat.mul_div_cancel' hqn⟩
    have hqle := Nat.le_of_dvd hn1 hqn
    exact (Nat.le_div_iff_mul_le hq).mpr (by simpa using hqle)
  · intro j hj; rfl

lemma harmonicWeightSum_convolution (g h : ArithmeticFunction ℝ) (N : ℕ) :
    harmonicWeightSum (g * h : ArithmeticFunction ℝ) N =
      ∑ a ∈ Finset.Icc 1 N, g a / a * harmonicWeightSum h (N / a) := by
  unfold harmonicWeightSum
  calc
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Icc 1 N,
        if a ∣ n then g a * h (n / a) / n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
      have hdiv : n.divisors = (Finset.Icc 1 N).filter (fun a ↦ a ∣ n) := by
        ext a
        simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨ha, _⟩
          exact ⟨⟨Nat.pos_of_dvd_of_pos ha hn1, (Nat.le_of_dvd hn1 ha).trans hnN⟩, ha⟩
        · exact fun ha ↦ ⟨ha.2, by omega⟩
      rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b ↦ g a * h b),
        Finset.sum_div, hdiv, Finset.sum_filter]
    _ = ∑ a ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        if a ∣ n then g a * h (n / a) / n else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha0 : 0 < a := (Finset.mem_Icc.mp ha).1
      rw [← Finset.sum_filter, sum_multiples_weighted _ a N ha0, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [Nat.mul_div_cancel_left b ha0, Nat.cast_mul]
      ring

noncomputable def polynomialTruncatedSum (f : ℤ[X]) (N D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D,
    (((Finset.Iic N).filter (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ))).card : ℝ)

lemma polynomialTruncatedSum_error (f : ℤ[X]) (N D : ℕ) :
    |polynomialTruncatedSum f N D - (N + 1 : ℝ) *
      harmonicWeightSum (fun d ↦ (polynomialRootResidues f d).card) D| ≤
      ∑ d ∈ Finset.Icc 1 D, ((polynomialRootResidues f d).card : ℝ) := by
  have hI : Finset.range (N + 1) = Finset.Iic N := by ext n; simp
  simpa only [hI, Nat.cast_add, Nat.cast_one] using truncated_divisor_count_error f D (N + 1)

lemma smallDivisorSum_truncated_bounds (f : ℤ[X]) (N D : ℕ)
    (hlower : ∀ n ≤ N, (n : ℤ) ^ 2 ≤ f.eval (n : ℤ))
    (hD : ∀ n ≤ N, (⌊f.eval (n : ℤ)⌋₊).sqrt ≤ D) :
    Erdos975SmallDivisorSum f N ≤ polynomialTruncatedSum f N D ∧
    polynomialTruncatedSum f N D ≤ Erdos975SmallDivisorSum f N +
      ∑ d ∈ Finset.Icc 1 D, ((polynomialRootResidues f d).card : ℝ) := by
  have hp : ∀ d ∈ Finset.Icc 1 D,
      ((Finset.Iic N).filter (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ) ∧
        (d : ℤ) ^ 2 ≤ f.eval (n : ℤ))).card ≤
        ((Finset.Iic N).filter (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ))).card ∧
      ((Finset.Iic N).filter (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ))).card ≤
        ((Finset.Iic N).filter (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ) ∧
          (d : ℤ) ^ 2 ≤ f.eval (n : ℤ))).card + (polynomialRootResidues f d).card := by
    intro d hd
    let S := (Finset.Iic N).filter (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ))
    let good := S.filter (fun n : ℕ ↦ (d : ℤ) ^ 2 ≤ f.eval (n : ℤ))
    let bad := S.filter (fun n : ℕ ↦ ¬(d : ℤ) ^ 2 ≤ f.eval (n : ℤ))
    have hcount : good.card + bad.card = S.card := Finset.card_filter_add_card_filter_not _
    have hbad : bad ⊆ polynomialRootResidues f d := by
      intro n hn
      obtain ⟨hnS, hnB⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnN, hdiv⟩ := Finset.mem_filter.mp hnS
      have hnN' : n ≤ N := Finset.mem_Iic.mp hnN
      have hnd : n < d := by
        by_contra h
        have hdn : (d : ℤ) ≤ n := by exact_mod_cast (show d ≤ n by omega)
        have hsq : (d : ℤ) ^ 2 ≤ (n : ℤ) ^ 2 := by gcongr
        exact hnB (hsq.trans (hlower n hnN'))
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnd, hdiv⟩
    have hb := Finset.card_le_card hbad
    have hg := Finset.card_filter_le S (fun n : ℕ ↦ (d : ℤ) ^ 2 ≤ f.eval (n : ℤ))
    have hgood : good = (Finset.Iic N).filter (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ) ∧
        (d : ℤ) ^ 2 ≤ f.eval (n : ℤ)) := Finset.filter_filter ..
    rw [← hgood]
    change good.card ≤ S.card ∧ S.card ≤ good.card + (polynomialRootResidues f d).card
    omega
  rw [smallDivisorSum_swap_int f N D hD]
  constructor
  · exact Finset.sum_le_sum (fun d hd ↦ by exact_mod_cast (hp d hd).1)
  · rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun d hd ↦ by exact_mod_cast (hp d hd).2)

lemma smallDivisorSum_truncated_error (f : ℤ[X]) (N D : ℕ)
    (hlower : ∀ n ≤ N, (n : ℤ) ^ 2 ≤ f.eval (n : ℤ))
    (hD : ∀ n ≤ N, (⌊f.eval (n : ℤ)⌋₊).sqrt ≤ D) :
    |Erdos975SmallDivisorSum f N - (N + 1 : ℝ) *
      harmonicWeightSum (fun d ↦ (polynomialRootResidues f d).card) D| ≤
      2 * ∑ d ∈ Finset.Icc 1 D, ((polynomialRootResidues f d).card : ℝ) := by
  have hb := smallDivisorSum_truncated_bounds f N D hlower hD
  have he := polynomialTruncatedSum_error f N D
  rw [abs_le] at he ⊢
  have hR : 0 ≤ ∑ d ∈ Finset.Icc 1 D, ((polynomialRootResidues f d).card : ℝ) := by positivity
  constructor <;> linarith

noncomputable def quadraticPolynomial (a b c : ℕ) : ℤ[X] :=
  C (a : ℤ) * X ^ 2 + C (b : ℤ) * X + C (c : ℤ)

lemma eval_quadraticPolynomial (a b c n : ℕ) :
    (quadraticPolynomial a b c).eval (n : ℤ) = ((a * n ^ 2 + b * n + c : ℕ) : ℤ) := by
  simp [quadraticPolynomial]

lemma quadraticPolynomial_lower (a b c n : ℕ) (ha : 0 < a) :
    (n : ℤ) ^ 2 ≤ (quadraticPolynomial a b c).eval (n : ℤ) := by
  rw [eval_quadraticPolynomial, ← Nat.cast_pow, Nat.cast_le]
  have h := Nat.le_mul_of_pos_left (n ^ 2) ha
  omega

lemma quadraticPolynomial_sqrt_bound (a b c N n : ℕ) (ha : 0 < a) (hN : 0 < N) (hn : n ≤ N) :
    (⌊(quadraticPolynomial a b c).eval (n : ℤ)⌋₊).sqrt ≤ (a + b + c) * N := by
  rw [eval_quadraticPolynomial, Nat.floor_natCast]
  have hn2 : n ^ 2 ≤ N ^ 2 := by gcongr
  have hN2 : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) N
  have hC : 1 ≤ a + b + c := by omega
  have hb : b * n ≤ b * N ^ 2 := Nat.mul_le_mul_left b (hn.trans hN2)
  have hc : c ≤ c * N ^ 2 := Nat.le_mul_of_pos_right c (pow_pos hN 2)
  have hval : a * n ^ 2 + b * n + c ≤ (a + b + c) * N ^ 2 := by
    nlinarith [Nat.mul_le_mul_left a hn2]
  have hval' : a * n ^ 2 + b * n + c ≤ ((a + b + c) * N) ^ 2 := by
    have h := Nat.mul_le_mul_left (N ^ 2) (Nat.le_self_pow (n := 2) (by norm_num) (a + b + c))
    nlinarith
  exact (Nat.sqrt_le_sqrt hval').trans (by simp [Nat.sqrt_eq'])

lemma tendsto_root_sum_scaled (u : ℕ → ℝ) (hu : ∀ d, 0 ≤ u d) (c : ℝ)
    (h : Tendsto (fun N : ℕ ↦ harmonicWeightSum u N / log N) atTop (𝓝 c))
    (C : ℕ) (hC : 0 < C) :
    Tendsto (fun N : ℕ ↦ (∑ d ∈ Finset.Icc 1 (C * N), u d) / ((N : ℝ) * log N))
      atTop (𝓝 0) := by
  have hD : Tendsto (fun N : ℕ ↦ C * N) atTop atTop :=
    tendsto_atTop_mono (fun N ↦ Nat.le_mul_of_pos_left N hC) tendsto_id
  have hR := (tendsto_sum_div_mul_log_of_harmonic u hu c h).comp hD
  have hlog := tendsto_log_linear_nat_value C 0 hC
  simp only [Nat.add_zero] at hlog
  have ht := hR.mul (hlog.const_mul (C : ℝ))
  simp only [zero_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ), hD.eventually_gt_atTop 1] with N hN hDN
  have hlogD : log (C * N : ℕ) ≠ 0 := (Real.log_pos (by exact_mod_cast hDN)).ne'
  have hC0 : (C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hC.ne'
  dsimp only [Function.comp_def]
  push_cast at hlogD ⊢
  field_simp

lemma erdos975_quadratic_nat_of_harmonic (a b c : ℕ) (ha : 0 < a) (κ : ℝ)
    (h : Tendsto (fun N : ℕ ↦
      harmonicWeightSum (fun d ↦ (polynomialRootResidues (quadraticPolynomial a b c) d).card) N /
        log N) atTop (𝓝 κ)) :
    Tendsto (fun x ↦ Erdos975Sum (quadraticPolynomial a b c) x / (x * log x)) atTop (𝓝 (2 * κ)) := by
  let f := quadraticPolynomial a b c
  let C := a + b + c
  let u : ℕ → ℝ := fun d ↦ (polynomialRootResidues f d).card
  have hC : 0 < C := by dsimp [C]; omega
  have hR := tendsto_root_sum_scaled u (fun _ ↦ Nat.cast_nonneg _) κ h C hC
  have hH : Tendsto (fun N : ℕ ↦ harmonicWeightSum u (C * N) / log N) atTop (𝓝 κ) := by
    have ht := tendsto_harmonic_scaled u κ h (C : ℝ) (Nat.cast_pos.mpr hC)
    simpa only [← Nat.cast_mul, Nat.floor_natCast] using ht
  have hErr : Tendsto (fun N : ℕ ↦
      (Erdos975SmallDivisorSum f N - (N + 1 : ℝ) * harmonicWeightSum u (C * N)) /
        ((N : ℝ) * log N)) atTop (𝓝 0) := by
    have hb := hR.const_mul 2
    simp only [mul_zero] at hb
    apply squeeze_zero_norm' _ hb
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    have hN0 : 0 < N := by omega
    have hden : 0 < (N : ℝ) * log N := mul_pos (Nat.cast_pos.mpr hN0)
      (Real.log_pos (by exact_mod_cast hN))
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
    have he := smallDivisorSum_truncated_error f N (C * N)
      (fun n _ ↦ quadraticPolynomial_lower a b c n ha)
      (fun n hn ↦ quadraticPolynomial_sqrt_bound a b c N n ha hN0 hn)
    exact (div_le_div_of_nonneg_right he hden.le).trans_eq (by ring)
  have hNreal : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hq : Tendsto (fun N : ℕ ↦ (N + 1 : ℝ) / N) atTop (𝓝 1) := by
    have ht := (hNreal.const_div_atTop (1 : ℝ)).const_add 1
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    field_simp
  have hsmall : Tendsto (fun N : ℕ ↦ Erdos975SmallDivisorSum f N / ((N : ℝ) * log N))
      atTop (𝓝 κ) := by
    have ht := hErr.add (hq.mul hH)
    simp only [one_mul, zero_add] at ht
    apply ht.congr
    intro N
    ring
  have ht := (hsmall.const_mul 2).sub ((tendsto_squareCorrection f).comp hNreal)
  simp only [sub_zero] at ht
  apply (tendsto_erdos975Sum_iff_nat f _).mpr
  apply ht.congr
  intro N
  have he := erdos975Sum_hyperbola f (N : ℝ)
  dsimp only [Function.comp_def]
  rw [← mul_div_assoc, ← sub_div]
  congr 1
  linarith

noncomputable def modularRootShiftEquiv (f : ℤ[X]) (d : ℕ) (k : ℤ) :
    ModularRoot (f.comp (X + C k)) d ≃ ModularRoot f d := by
  apply Equiv.subtypeEquiv (Equiv.addRight (k : ZMod d))
  intro x
  simp only [eval₂_comp, eval₂_add, eval₂_X, eval₂_C, Int.coe_castRingHom]
  rfl

lemma rootResidues_card_shift (f : ℤ[X]) (d : ℕ) (k : ℤ) :
    (polynomialRootResidues (f.comp (X + C k)) d).card = (polynomialRootResidues f d).card := by
  by_cases hd : d = 0
  · simp [hd, polynomialRootResidues]
  · haveI : NeZero d := ⟨hd⟩
    rw [rootResidues_card_eq_modularRoot, rootResidues_card_eq_modularRoot]
    exact Nat.card_congr (modularRootShiftEquiv f d k)

lemma quadratic_slope_pos (a b c : ℤ) (ha : a ≠ 0)
    (hpos : ∀ᶠ n in atTop, 1 ≤ a * n ^ 2 + b * n + c) : 0 < a := by
  by_contra h
  have ha' : a ≤ -1 := by omega
  obtain ⟨n, hnpos, hn1, hnb, hnc⟩ :=
    (hpos.and ((eventually_ge_atTop (1 : ℤ)).and
      ((eventually_ge_atTop (b + 1)).and (eventually_ge_atTop (c + 1))))).exists
  have hn0 : 0 ≤ n := by omega
  have haineq := mul_le_mul_of_nonneg_right ha' (sq_nonneg n)
  have hbineq := mul_le_mul_of_nonneg_right hnb hn0
  nlinarith

lemma quadratic_natDegree_eq_two (f : ℤ[X]) (hdeg : f.natDegree = 2) :
    ∃ a b c : ℤ, a ≠ 0 ∧ f = C a * X ^ 2 + C b * X + C c := by
  refine ⟨f.coeff 2, f.coeff 1, f.coeff 0, ?_, ?_⟩
  · rw [← hdeg, coeff_natDegree]
    apply leadingCoeff_ne_zero.mpr
    intro hf
    simp [hf] at hdeg
  · have he := f.as_sum_range_C_mul_X_pow
    rw [hdeg] at he
    norm_num [Finset.sum_range_succ] at he
    conv_lhs => rw [he]
    simp only [← Polynomial.C_eq_intCast, Int.cast_id]
    ring

lemma quadratic_shift_to_nat (f : ℤ[X]) (hdeg : f.natDegree = 2)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    ∃ k a b c : ℕ, 0 < a ∧ f.comp (X + C (k : ℤ)) = quadraticPolynomial a b c := by
  obtain ⟨a, b, c, ha, hf⟩ := quadratic_natDegree_eq_two f hdeg
  have hpos' : ∀ᶠ n : ℤ in atTop, 1 ≤ a * n ^ 2 + b * n + c := by
    simpa only [hf, eval_add, eval_mul, eval_pow, eval_C, eval_X] using hpos
  have haP := quadratic_slope_pos a b c ha hpos'
  lift a to ℕ using haP.le
  have haNat : 0 < a := by exact_mod_cast haP
  have hposNat : ∀ᶠ k : ℕ in atTop, 1 ≤ (a : ℤ) * k ^ 2 + b * k + c :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ ↦ (k : ℤ)) atTop atTop).eventually hpos'
  obtain ⟨k, hkpos, hkb⟩ := (hposNat.and (eventually_ge_atTop (-b).toNat)).exists
  have hkb' : -b ≤ (k : ℤ) := (Int.self_le_toNat (-b)).trans (by exact_mod_cast hkb)
  have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
  have ha1 : (1 : ℤ) ≤ a := by exact_mod_cast haNat
  have hB : 0 ≤ b + 2 * (a : ℤ) * k := by
    have hm := mul_le_mul_of_nonneg_right ha1 hk0
    nlinarith
  let B := (b + 2 * (a : ℤ) * k).toNat
  let C₀ := ((a : ℤ) * k ^ 2 + b * k + c).toNat
  have hBcast : (B : ℤ) = b + 2 * (a : ℤ) * k := Int.toNat_of_nonneg hB
  have hCcast : (C₀ : ℤ) = (a : ℤ) * k ^ 2 + b * k + c := Int.toNat_of_nonneg (by omega)
  refine ⟨k, a, B, C₀, haNat, ?_⟩
  simp only [hf, quadraticPolynomial, add_comp, mul_comp, pow_comp, C_comp, X_comp,
    hBcast, hCcast, map_add, map_mul, map_pow, map_ofNat]
  ring

lemma erdos975_degree_two_of_harmonic (f : ℤ[X]) (hdeg : f.natDegree = 2)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) (κ : ℝ)
    (h : Tendsto (fun N : ℕ ↦ harmonicWeightSum (fun d ↦ (polynomialRootResidues f d).card) N /
      log N) atTop (𝓝 κ)) :
    Tendsto (fun x ↦ Erdos975Sum f x / (x * log x)) atTop (𝓝 (2 * κ)) := by
  obtain ⟨k, a, b, c, ha, hshift⟩ := quadratic_shift_to_nat f hdeg hpos
  have hH : Tendsto (fun N : ℕ ↦
      harmonicWeightSum (fun d ↦ (polynomialRootResidues (f.comp (X + C (k : ℤ))) d).card) N /
        log N) atTop (𝓝 κ) := by
    simpa only [rootResidues_card_shift] using h
  rw [hshift] at hH
  apply (erdos975_shift_iff f k (2 * κ)).mpr
  rw [hshift]
  exact erdos975_quadratic_nat_of_harmonic a b c ha κ hH

lemma harmonicWeightSum_nonneg (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (N : ℕ) :
    0 ≤ harmonicWeightSum u N := Finset.sum_nonneg fun d _ ↦ div_nonneg (hu d) (Nat.cast_nonneg d)

lemma harmonicWeightSum_mono (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) : Monotone (harmonicWeightSum u) := by
  intro M N hMN
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hMN)
    (fun d _ _ ↦ div_nonneg (hu d) (Nat.cast_nonneg d))

lemma tendsto_harmonicWeightSum_nat_div (u : ℕ → ℝ) (c : ℝ)
    (h : Tendsto (fun N : ℕ ↦ harmonicWeightSum u N / log N) atTop (𝓝 c))
    (q : ℕ) (hq : 0 < q) :
    Tendsto (fun N : ℕ ↦ harmonicWeightSum u (N / q) / log N) atTop (𝓝 c) := by
  have hD := Nat.tendsto_div_const_atTop hq.ne'
  have hl := tendsto_log_nat_floor_scaled_div_log (1 / q) (by positivity)
  simp only [one_div_mul_eq_div, Nat.floor_div_eq_div] at hl
  have ht := (h.comp hD).mul hl
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [hD.eventually_gt_atTop 1] with N hN
  have hlog : log ((N / q : ℕ) : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  dsimp only [Function.comp_def]
  field_simp

lemma tendsto_harmonicWeightSum_convolution (u v : ArithmeticFunction ℝ)
    (hu : ∀ n, 0 ≤ u n) (c : ℝ)
    (h : Tendsto (fun N : ℕ ↦ harmonicWeightSum u N / log N) atTop (𝓝 c))
    (hv : Summable (fun n : ℕ ↦ ‖v n / (n : ℝ)‖)) :
    Tendsto (fun N : ℕ ↦ harmonicWeightSum (v * u : ArithmeticFunction ℝ) N / log N)
      atTop (𝓝 ((∑' n : ℕ, v n / (n : ℝ)) * c)) := by
  let F : ℕ → ℕ → ℝ := fun N n ↦ v n / (n : ℝ) * (harmonicWeightSum u (N / n) / log N)
  have hb : Summable (fun n : ℕ ↦ ‖v n / (n : ℝ)‖ * (|c| + 1)) := hv.mul_right _
  have ht := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) hb
    (f := F) (g := fun n : ℕ ↦ v n / (n : ℝ) * c) ?_ ?_
  · rw [tsum_mul_right] at ht
    apply ht.congr
    intro N
    rw [tsum_eq_sum (s := Finset.Icc 1 N) ?_, harmonicWeightSum_convolution, Finset.sum_div]
    · apply Finset.sum_congr rfl
      intro n hn
      dsimp [F]
      ring
    · intro n hn
      by_cases hn0 : n = 0
      · simp [F, hn0]
      · have hnN : N < n := by simp only [Finset.mem_Icc] at hn; omega
        simp [F, Nat.div_eq_of_lt hnN, harmonicWeightSum]
  · intro n
    by_cases hn0 : n = 0
    · simp [F, hn0]
    · exact (tendsto_harmonicWeightSum_nat_div u c h n (Nat.pos_of_ne_zero hn0)).const_mul _
  · have hc : c < |c| + 1 := by linarith [le_abs_self c]
    filter_upwards [h.eventually (gt_mem_nhds hc), eventually_gt_atTop (1 : ℕ)] with N hNH hN1
    intro n
    have hl : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
    have h0 := div_nonneg (harmonicWeightSum_nonneg u hu (N / n)) hl.le
    have h1 : harmonicWeightSum u (N / n) / log N ≤ |c| + 1 :=
      (div_le_div_of_nonneg_right (harmonicWeightSum_mono u hu (Nat.div_le_self N n)) hl.le).trans hNH.le
    dsimp only [F]
    rw [norm_mul, Real.norm_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

lemma convolution_prime_pow (u v : ArithmeticFunction ℝ) (p k : ℕ) (hp : p.Prime) :
    (u * v) (p ^ k) = ∑ j ∈ Finset.range (k + 1), u (p ^ j) * v (p ^ (k - j)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b ↦ u a * v b),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.pow_div (by simpa using Finset.mem_range.mp hj) hp.pos]

open scoped Classical

noncomputable def polynomialInitialDivisorSum (f : ℤ[X]) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Iic N,
    (((Finset.Icc 1 n).filter (fun d : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ))).card : ℝ)

lemma polynomialInitialDivisorSum_swap (f : ℤ[X]) (N : ℕ) :
    polynomialInitialDivisorSum f N =
      ∑ d ∈ Finset.Icc 1 N,
        (((Finset.Iic N).filter (fun n : ℕ ↦ d ≤ n ∧ (d : ℤ) ∣ f.eval (n : ℤ))).card : ℝ) := by
  unfold polynomialInitialDivisorSum
  have hs : ∀ n ∈ Finset.Iic N,
      (Finset.Icc 1 n).filter (fun d : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ)) =
        (Finset.Icc 1 N).filter (fun d : ℕ ↦ d ≤ n ∧ (d : ℤ) ∣ f.eval (n : ℤ)) := by
    intro n hn
    have hnN := Finset.mem_Iic.mp hn
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  calc
    _ = ∑ n ∈ Finset.Iic N,
        (((Finset.Icc 1 N).filter (fun d : ℕ ↦ d ≤ n ∧ (d : ℤ) ∣ f.eval (n : ℤ))).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hs n hn]
    _ = _ := by
      simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
      exact Finset.sum_comm

lemma polynomialTruncatedSum_initial_identity (f : ℤ[X]) (N : ℕ) :
    polynomialTruncatedSum f N N = polynomialInitialDivisorSum f N +
      ∑ d ∈ Finset.Icc 1 N, ((polynomialRootResidues f d).card : ℝ) := by
  rw [polynomialInitialDivisorSum_swap, ← Finset.sum_add_distrib]
  unfold polynomialTruncatedSum
  apply Finset.sum_congr rfl
  intro d hd
  have hdN := (Finset.mem_Icc.mp hd).2
  let S := (Finset.Iic N).filter (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ))
  have hgood : S.filter (fun n ↦ d ≤ n) =
      (Finset.Iic N).filter (fun n : ℕ ↦ d ≤ n ∧ (d : ℤ) ∣ f.eval (n : ℤ)) := by
    ext n
    simp only [S, Finset.mem_filter]
    tauto
  have hbad : S.filter (fun n ↦ ¬d ≤ n) = polynomialRootResidues f d := by
    ext n
    simp only [S, polynomialRootResidues, Finset.mem_filter, Finset.mem_Iic, Finset.mem_range]
    omega
  have hc := Finset.card_filter_add_card_filter_not (s := S) (fun n ↦ d ≤ n)
  rw [hgood, hbad] at hc
  exact_mod_cast hc.symm

lemma polynomialInitialDivisorSum_error (f : ℤ[X]) (N : ℕ) :
    |polynomialInitialDivisorSum f N - (N + 1 : ℝ) *
      harmonicWeightSum (fun d ↦ (polynomialRootResidues f d).card) N| ≤
      2 * ∑ d ∈ Finset.Icc 1 N, ((polynomialRootResidues f d).card : ℝ) := by
  have he := polynomialTruncatedSum_error f N N
  rw [polynomialTruncatedSum_initial_identity, abs_le] at he
  have hR : 0 ≤ ∑ d ∈ Finset.Icc 1 N, ((polynomialRootResidues f d).card : ℝ) := by positivity
  rw [abs_le]
  constructor <;> linarith

lemma tendsto_polynomialInitialDivisorSum (f : ℤ[X]) (κ : ℝ)
    (h : Tendsto (fun N : ℕ ↦
      harmonicWeightSum (fun d ↦ (polynomialRootResidues f d).card) N / log N)
      atTop (𝓝 κ)) :
    Tendsto (fun N : ℕ ↦ polynomialInitialDivisorSum f N / ((N : ℝ) * log N))
      atTop (𝓝 κ) := by
  let u : ℕ → ℝ := fun d ↦ (polynomialRootResidues f d).card
  have hR := tendsto_sum_div_mul_log_of_harmonic u (fun _ ↦ Nat.cast_nonneg _) κ h
  have hErr : Tendsto (fun N : ℕ ↦
      (polynomialInitialDivisorSum f N - (N + 1 : ℝ) * harmonicWeightSum u N) /
        ((N : ℝ) * log N)) atTop (𝓝 0) := by
    have hb := hR.const_mul 2
    simp only [mul_zero] at hb
    apply squeeze_zero_norm' _ hb
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    have hden : 0 < (N : ℝ) * log N := mul_pos (by exact_mod_cast (show 0 < N by omega))
      (Real.log_pos (by exact_mod_cast hN))
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
    exact (div_le_div_of_nonneg_right (polynomialInitialDivisorSum_error f N) hden.le).trans_eq
      (by ring)
  have hNreal : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hq : Tendsto (fun N : ℕ ↦ (N + 1 : ℝ) / N) atTop (𝓝 1) := by
    have ht := (hNreal.const_div_atTop (1 : ℝ)).const_add 1
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    field_simp
  have ht := hErr.add (hq.mul h)
  simp only [one_mul, zero_add] at ht
  apply ht.congr
  intro N
  ring

noncomputable def Erdos975BalancedDivisorSum (f : ℤ[X]) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Iic N, (((⌊f.eval (n : ℤ)⌋₊).divisors.filter
    (fun d ↦ n < d ∧ d ≤ (⌊f.eval (n : ℤ)⌋₊).sqrt)).card : ℝ)

lemma balancedDivisorSum_nonneg (f : ℤ[X]) (N : ℕ) :
    0 ≤ Erdos975BalancedDivisorSum f N := by
  exact Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)

lemma small_divisors_initial_split (z : ℤ) (n : ℕ) (hz : (n : ℤ) ^ 2 ≤ z) :
    (⌊z⌋₊.divisors.filter (fun d ↦ d ≤ ⌊z⌋₊.sqrt)).card =
      ((Finset.Icc 1 n).filter (fun d : ℕ ↦ (d : ℤ) ∣ z)).card +
        (⌊z⌋₊.divisors.filter (fun d ↦ n < d ∧ d ≤ ⌊z⌋₊.sqrt)).card := by
  let S := ⌊z⌋₊.divisors.filter (fun d ↦ d ≤ ⌊z⌋₊.sqrt)
  have hgood : S.filter (fun d ↦ d ≤ n) =
      (Finset.Icc 1 n).filter (fun d : ℕ ↦ (d : ℤ) ∣ z) := by
    have hz0 : 0 ≤ z := (sq_nonneg _).trans hz
    lift z to ℕ using hz0
    ext d
    simp only [S, Nat.floor_natCast, Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc,
      Int.natCast_dvd_natCast]
    constructor
    · rintro ⟨⟨⟨hd, hz⟩, hs⟩, hdn⟩
      exact ⟨⟨Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hd, hz⟩), hdn⟩, hd⟩
    · rintro ⟨⟨hdpos, hdn⟩, hd⟩
      have hsq : n ^ 2 ≤ z := by exact_mod_cast hz
      have hd2 : d ^ 2 ≤ z := (Nat.pow_le_pow_left hdn 2).trans hsq
      have hzpos : 0 < z := lt_of_lt_of_le (pow_pos hdpos 2) hd2
      exact ⟨⟨⟨hd, hzpos.ne'⟩, Nat.le_sqrt'.mpr hd2⟩, hdn⟩
  have hbad : S.filter (fun d ↦ ¬d ≤ n) =
      ⌊z⌋₊.divisors.filter (fun d ↦ n < d ∧ d ≤ ⌊z⌋₊.sqrt) := by
    ext d
    simp only [S, Finset.mem_filter, not_le]
    tauto
  have hc := Finset.card_filter_add_card_filter_not (s := S) (fun d ↦ d ≤ n)
  rw [hgood, hbad] at hc
  exact hc.symm

lemma tendsto_sum_Iic_div_mul_log_of_eventually_zero (u : ℕ → ℝ)
    (hu : ∀ᶠ n in atTop, u n = 0) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Iic N, u n) / ((N : ℝ) * log N))
      atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp hu
  have he : ∀ᶠ N : ℕ in atTop, (∑ n ∈ Finset.Iic N, u n) = ∑ n ∈ Finset.range K, u n := by
    filter_upwards [eventually_ge_atTop K] with N hN
    symm
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_Iic.mpr (le_trans (Finset.mem_range.mp hn).le hN)
    · intro n hn hnK
      exact hK n (by simpa using hnK)
  have hN : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hden := hN.atTop_mul_atTop₀ (Real.tendsto_log_atTop.comp hN)
  apply (hden.const_div_atTop (∑ n ∈ Finset.range K, u n)).congr'
  filter_upwards [he] with N hN
  simp only [hN, Function.comp_apply]

lemma tendsto_smallDivisorSum_initial_error (f : ℤ[X])
    (hlower : ∀ᶠ n : ℕ in atTop, (n : ℤ) ^ 2 ≤ f.eval (n : ℤ)) :
    Tendsto (fun N : ℕ ↦
      (Erdos975SmallDivisorSum f N - polynomialInitialDivisorSum f N -
        Erdos975BalancedDivisorSum f N) / ((N : ℝ) * log N)) atTop (𝓝 0) := by
  let u : ℕ → ℝ := fun n ↦
    (((⌊f.eval (n : ℤ)⌋₊).divisors.filter (fun d ↦ d ≤ (⌊f.eval (n : ℤ)⌋₊).sqrt)).card : ℝ) -
    (((Finset.Icc 1 n).filter (fun d : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ))).card : ℝ) -
    (((⌊f.eval (n : ℤ)⌋₊).divisors.filter
      (fun d ↦ n < d ∧ d ≤ (⌊f.eval (n : ℤ)⌋₊).sqrt)).card : ℝ)
  have hu : ∀ᶠ n in atTop, u n = 0 := by
    filter_upwards [hlower] with n hn
    have he := small_divisors_initial_split (f.eval (n : ℤ)) n hn
    dsimp only [u]
    rw [he, Nat.cast_add]
    ring
  simpa only [u, Erdos975SmallDivisorSum, polynomialInitialDivisorSum, Erdos975BalancedDivisorSum,
    Nat.floor_natCast, Finset.sum_sub_distrib] using tendsto_sum_Iic_div_mul_log_of_eventually_zero u hu

lemma tendsto_erdos975Sum_iff_small_nat (f : ℤ[X]) (c : ℝ) :
    Tendsto (fun x ↦ Erdos975Sum f x / (x * log x)) atTop (𝓝 c) ↔
    Tendsto (fun N : ℕ ↦ Erdos975SmallDivisorSum f N / ((N : ℝ) * log N))
      atTop (𝓝 (c / 2)) := by
  rw [tendsto_erdos975Sum_iff_nat]
  have hs := (tendsto_squareCorrection f).comp tendsto_natCast_atTop_atTop
  constructor
  · intro h
    have ht := (h.add hs).div_const 2
    simp only [add_zero] at ht
    apply ht.congr
    intro N
    have he := erdos975Sum_hyperbola f (N : ℝ)
    dsimp only [Function.comp_def]
    rw [← add_div, he]
    ring
  · intro h
    have ht := (h.const_mul 2).sub hs
    have hc : 2 * (c / 2) - 0 = c := by ring
    rw [hc] at ht
    apply ht.congr
    intro N
    have he := congrArg (fun y : ℝ ↦ y / ((N : ℝ) * log N)) (erdos975Sum_hyperbola f N)
    simp only [add_div, mul_div_assoc] at he
    dsimp only [Function.comp_def]
    linarith

/-- Given the modular-root harmonic asymptotic, the remaining obstruction in degree at
least three is convergence of the contribution of divisors `n < d ≤ sqrt (f n)`. -/
lemma erdos975_iff_balanced_of_harmonic (f : ℤ[X]) (κ c : ℝ)
    (hlower : ∀ᶠ n : ℕ in atTop, (n : ℤ) ^ 2 ≤ f.eval (n : ℤ))
    (h : Tendsto (fun N : ℕ ↦
      harmonicWeightSum (fun d ↦ (polynomialRootResidues f d).card) N / log N)
      atTop (𝓝 κ)) :
    Tendsto (fun x ↦ Erdos975Sum f x / (x * log x)) atTop (𝓝 c) ↔
    Tendsto (fun N : ℕ ↦ Erdos975BalancedDivisorSum f N / ((N : ℝ) * log N))
      atTop (𝓝 (c / 2 - κ)) := by
  rw [tendsto_erdos975Sum_iff_small_nat]
  have hA := tendsto_polynomialInitialDivisorSum f κ h
  have hE := tendsto_smallDivisorSum_initial_error f hlower
  constructor
  · intro hS
    have ht := (hS.sub hA).sub hE
    simp only [sub_zero] at ht
    apply ht.congr
    intro N
    ring
  · intro hB
    have ht := (hA.add hB).add hE
    have hc : κ + (c / 2 - κ) + 0 = c / 2 := by ring
    rw [hc] at ht
    apply ht.congr
    intro N
    ring

lemma leadingCoeff_pos_of_eventually_positive (f : ℤ[X]) (hdeg : f.natDegree ≠ 0)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) : 0 < f.leadingCoeff := by
  let P : ℝ[X] := f.map (Int.castRingHom ℝ)
  have hPdeg : P.natDegree = f.natDegree := natDegree_map_eq_of_injective Int.cast_injective f
  have hPlead : P.leadingCoeff = (f.leadingCoeff : ℝ) :=
    leadingCoeff_map_of_injective Int.cast_injective f
  have heval : ∀ n : ℕ, P.eval (n : ℝ) = (↑(f.eval (n : ℤ)) : ℝ) := by
    intro n
    simpa only [P, eval_map, Int.coe_castRingHom, Int.cast_natCast] using
      (eval₂_at_apply (Int.castRingHom ℝ) (n : ℤ) (p := f))
  have hPdeg0 : 0 < P.degree := natDegree_pos_iff_degree_pos.mp (by omega)
  by_contra hneg
  have hlead : P.leadingCoeff ≤ 0 := by rw [hPlead]; exact_mod_cast (le_of_not_gt hneg)
  have hbot := (P.tendsto_atBot_of_leadingCoeff_nonpos hPdeg0 hlead).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hposN := (tendsto_natCast_atTop_atTop (R := ℤ)).eventually hpos
  obtain ⟨n, hnneg, hnpos⟩ := ((hbot.eventually_lt_atBot 0).and hposN).exists
  have hnneg' : (↑(f.eval (n : ℤ)) : ℝ) < 0 := by simpa only [Function.comp_def, heval] using hnneg
  have hnpos' : (1 : ℝ) ≤ ↑(f.eval (n : ℤ)) := by exact_mod_cast hnpos
  linarith

lemma eventually_eval_ge_square_of_degree_gt_two (f : ℤ[X]) (hdeg : 2 < f.natDegree)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    ∀ᶠ n : ℕ in atTop, (n : ℤ) ^ 2 ≤ f.eval (n : ℤ) := by
  let P : ℝ[X] := f.map (Int.castRingHom ℝ)
  have hPdeg : P.natDegree = f.natDegree := natDegree_map_eq_of_injective Int.cast_injective f
  have hPlead : P.leadingCoeff = (f.leadingCoeff : ℝ) :=
    leadingCoeff_map_of_injective Int.cast_injective f
  have heval : ∀ n : ℕ, P.eval (n : ℝ) = (↑(f.eval (n : ℤ)) : ℝ) := by
    intro n
    simpa only [P, eval_map, Int.coe_castRingHom, Int.cast_natCast] using
      (eval₂_at_apply (Int.castRingHom ℝ) (n : ℤ) (p := f))
  have hlead : 0 < P.leadingCoeff := by
    rw [hPlead]
    exact_mod_cast leadingCoeff_pos_of_eventually_positive f (by omega) hpos
  have hdegrees : (X ^ 2 : ℝ[X]).degree < P.degree := by
    apply degree_lt_degree
    simpa only [natDegree_X_pow, hPdeg] using hdeg
  have hQdeg : 0 < (P - X ^ 2).degree := by
    rw [degree_sub_eq_left_of_degree_lt hdegrees]
    apply natDegree_pos_iff_degree_pos.mp
    omega
  have hQlead : 0 ≤ (P - X ^ 2).leadingCoeff := by
    rw [leadingCoeff_sub_of_degree_lt hdegrees]
    exact hlead.le
  have ht := ((P - X ^ 2).tendsto_atTop_of_leadingCoeff_nonneg hQdeg hQlead).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [ht.eventually_ge_atTop 0] with n hn
  simp only [Function.comp_def, eval_sub, eval_pow, eval_X, heval, sub_nonneg] at hn
  exact_mod_cast hn

lemma erdos975_degree_gt_two_iff_balanced (f : ℤ[X]) (hdeg : 2 < f.natDegree)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) (κ c : ℝ)
    (h : Tendsto (fun N : ℕ ↦
      harmonicWeightSum (fun d ↦ (polynomialRootResidues f d).card) N / log N)
      atTop (𝓝 κ)) :
    Tendsto (fun x ↦ Erdos975Sum f x / (x * log x)) atTop (𝓝 c) ↔
    Tendsto (fun N : ℕ ↦ Erdos975BalancedDivisorSum f N / ((N : ℝ) * log N))
      atTop (𝓝 (c / 2 - κ)) :=
  erdos975_iff_balanced_of_harmonic f κ c
    (eventually_eval_ge_square_of_degree_gt_two f hdeg hpos) h

lemma erdos975_degree_gt_two_of_balanced_limit (f : ℤ[X]) (hdeg : 2 < f.natDegree)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) (κ : ℝ) (hκ : 0 < κ)
    (h : Tendsto (fun N : ℕ ↦
      harmonicWeightSum (fun d ↦ (polynomialRootResidues f d).card) N / log N)
      atTop (𝓝 κ))
    (hbalanced : ∃ β : ℝ,
      Tendsto (fun N : ℕ ↦ Erdos975BalancedDivisorSum f N / ((N : ℝ) * log N))
        atTop (𝓝 β)) :
    ∃ c > (0 : ℝ), Tendsto (fun x ↦ Erdos975Sum f x / (x * log x)) atTop (𝓝 c) := by
  obtain ⟨β, hβ⟩ := hbalanced
  have hnonneg : ∀ᶠ N : ℕ in atTop,
      0 ≤ Erdos975BalancedDivisorSum f N / ((N : ℝ) * log N) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact div_nonneg (balancedDivisorSum_nonneg f N)
      (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hN)))
  have hβ0 : 0 ≤ β := ge_of_tendsto hβ hnonneg
  refine ⟨2 * (κ + β), by linarith, ?_⟩
  apply (erdos975_degree_gt_two_iff_balanced f hdeg hpos κ _ h).mpr
  have he : 2 * (κ + β) / 2 - κ = β := by ring
  rwa [he]

lemma tendsto_logarithmic_average (u : ℕ → ℝ) (c : ℝ)
    (h : Tendsto u atTop (𝓝 c)) :
    Tendsto (fun N : ℕ ↦ (∑ k ∈ Finset.range N, u k / (k + 1 : ℝ)) / log N)
      atTop (𝓝 c) := by
  let w : ℕ → ℝ := fun k ↦ 1 / (k + 1 : ℝ)
  have hw : ∀ N, (∑ k ∈ Finset.range N, w k) = (harmonic N : ℝ) := by
    intro N
    simp [w, harmonic, Rat.cast_sum, Rat.cast_inv]
  have he : (fun k ↦ (u k - c) * w k) =o[atTop] w := by
    have hzero := (Asymptotics.isLittleO_one_iff ℝ).mpr (tendsto_sub_nhds_zero_iff.mpr h)
    simpa only [one_mul] using hzero.mul_isBigO (Asymptotics.isBigO_refl w atTop)
  have hes := he.sum_range (fun k ↦ by dsimp [w]; positivity)
    Real.tendsto_sum_range_one_div_nat_succ_atTop
  have heh := hes.tendsto_div_nhds_zero
  simp only [hw] at heh
  have he0 := heh.mul tendsto_harmonic_div_log
  simp only [zero_mul] at he0
  have hErr : Tendsto (fun N : ℕ ↦ (∑ k ∈ Finset.range N, (u k - c) * w k) / log N)
      atTop (𝓝 0) := by
    apply he0.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hH : (harmonic N : ℝ) ≠ 0 := by
      have hp : 0 < harmonic N := harmonic_pos hN.ne'
      exact_mod_cast hp.ne'
    field_simp
  have ht := hErr.add (tendsto_harmonic_div_log.const_mul c)
  simp only [mul_one, zero_add] at ht
  apply ht.congr
  intro N
  rw [← hw]
  simp only [w, div_eq_mul_inv, one_mul, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

lemma harmonicWeightSum_partial_summation (u : ℕ → ℝ) (N : ℕ) :
    harmonicWeightSum u N =
      (∑ n ∈ Finset.Icc 1 N, u n) / (N + 1 : ℝ) +
        ∑ k ∈ Finset.range N, (∑ n ∈ Finset.Icc 1 (k + 1), u n) /
          ((k + 1 : ℝ) * (k + 2 : ℝ)) := by
  induction N with
  | zero => simp [harmonicWeightSum]
  | succ N ih =>
    rw [harmonicWeightSum, Finset.sum_Icc_succ_top (by omega), ← harmonicWeightSum, ih,
      Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega)]
    push_cast
    have hN1 : (N + 1 : ℝ) ≠ 0 := by positivity
    have hN2 : (N + 2 : ℝ) ≠ 0 := by positivity
    field_simp
    ring

lemma tendsto_nat_div_succ :
    Tendsto (fun N : ℕ ↦ (N : ℝ) / (N + 1)) atTop (𝓝 1) := by
  have hN : Tendsto (fun N : ℕ ↦ (N : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have ht := (hN.const_div_atTop (1 : ℝ)).const_sub 1
  simp only [sub_zero] at ht
  apply ht.congr
  intro N
  have hN1 : (N + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma tendsto_harmonicWeightSum_of_sum_div (u : ℕ → ℝ) (c : ℝ)
    (h : Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 N, u n) / (N : ℝ)) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ ↦ harmonicWeightSum u N / log N) atTop (𝓝 c) := by
  let A : ℕ → ℝ := fun N ↦ ∑ n ∈ Finset.Icc 1 N, u n
  have hA : Tendsto (fun N : ℕ ↦ A N / (N + 1 : ℝ)) atTop (𝓝 c) := by
    have ht := h.mul tendsto_nat_div_succ
    simp only [mul_one] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    dsimp [A]
    field_simp
  have hAl : Tendsto (fun k : ℕ ↦ A (k + 1) / (k + 2 : ℝ)) atTop (𝓝 c) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
      using hA.comp (tendsto_add_atTop_nat 1)
  have hmean := tendsto_logarithmic_average _ c hAl
  have hB := hA.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have ht := hB.add hmean
  simp only [zero_add] at ht
  apply ht.congr
  intro N
  rw [harmonicWeightSum_partial_summation, add_div]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only [A]
  rw [div_div, mul_comm]

open scoped NumberField

lemma ideal_count_sum_div_limit (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun N : ℕ ↦
      (∑ n ∈ Finset.Icc 1 N, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ)) / N)
      atTop (𝓝 (NumberField.dedekindZeta_residue K)) := by
  refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
    tendsto_natCast_atTop_atTop).congr fun N ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr 1
  norm_cast
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 N = Finset.Ioc 0 N from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (N.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOf_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

lemma ideal_count_harmonic_limit (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun N : ℕ ↦ harmonicWeightSum
      (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ)) N / log N)
      atTop (𝓝 (NumberField.dedekindZeta_residue K)) :=
  tendsto_harmonicWeightSum_of_sum_div _ _ (ideal_count_sum_div_limit K)

noncomputable def monicLinearFactorEquivRoot {F : Type*} [Field F] [DecidableEq F]
    (f : F[X]) (hf : f ≠ 0) :
    {q : (UniqueFactorizationMonoid.normalizedFactors f).toFinset // (q : F[X]).natDegree = 1} ≃
      {x : F // f.eval x = 0} where
  toFun q := ⟨-q.val.val.coeff 0, by
    have hq := (Polynomial.mem_normalizedFactors_iff (p := q.val.val) hf).mp
      (by simpa only [Multiset.mem_toFinset] using q.val.property)
    have he : q.val.val = X - C (-q.val.val.coeff 0) := by
      simpa using hq.2.1.eq_X_add_C q.property
    exact dvd_iff_isRoot.mp (he ▸ hq.2.2)⟩
  invFun x := ⟨⟨X - C x.val, by
    simpa only [Multiset.mem_toFinset] using (Polynomial.mem_normalizedFactors_iff hf).mpr
      ⟨irreducible_X_sub_C x.val, monic_X_sub_C x.val, dvd_iff_isRoot.mpr x.property⟩⟩,
    natDegree_X_sub_C x.val⟩
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    have hq := (Polynomial.mem_normalizedFactors_iff (p := q.val.val) hf).mp
      (by simpa only [Multiset.mem_toFinset] using q.val.property)
    simpa using (hq.2.1.eq_X_add_C q.property).symm
  right_inv x := by
    apply Subtype.ext
    simp

noncomputable def idealNormPrimeEquivPrimeOverDegreeOne
    (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    {I : Ideal (𝓞 K) // Ideal.absNorm I = p} ≃
      {P : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) //
        (Ideal.span {(p : ℤ)}).inertiaDeg (P : Ideal (𝓞 K)) = 1} where
  toFun I := by
    have hnormprime : (Ideal.absNorm I.val).Prime := by rwa [I.property]
    have hprime : I.val.IsPrime := Ideal.isPrime_of_irreducible_absNorm
      ((Nat.irreducible_iff_nat_prime _).mpr hnormprime)
    have hlies : I.val.LiesOver (Ideal.span {(p : ℤ)}) := by
      apply Ideal.LiesOver.mk
      simpa only [I.property, Ideal.under_def] using Ideal.span_singleton_absNorm hnormprime
    let P : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := ⟨I.val, hprime, hlies⟩
    refine ⟨P, ?_⟩
    haveI := hlies
    have he := Ideal.absNorm_eq_pow_inertiaDeg' I.val hp
    apply Nat.pow_right_injective hp.two_le
    simpa only [pow_one, I.property] using he.symm
  invFun P := ⟨P.val.val, by
    rw [Ideal.absNorm_eq_pow_inertiaDeg' _ hp, P.property, pow_one]⟩
  left_inv I := by rfl
  right_inv P := by rfl

lemma rootResidues_minpoly_prime_eq_ideal_count
    (K : Type*) [Field K] [NumberField K] (θ : 𝓞 K) (p : ℕ) [Fact p.Prime]
    (hp : ¬p ∣ RingOfIntegers.exponent θ) :
    (polynomialRootResidues (minpoly ℤ θ) p).card =
      Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p} := by
  let E := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp
  have hdegree : ∀ P : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
      (Ideal.span {(p : ℤ)}).inertiaDeg (P : Ideal (𝓞 K)) = 1 ↔
        ((E P : RingOfIntegers.monicFactorsMod θ p) : (ZMod p)[X]).natDegree = 1 := by
    intro P
    have he := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
      hp (E P).property
    change (Ideal.span {(p : ℤ)}).inertiaDeg (E.symm (E P) : Ideal (𝓞 K)) =
      ((E P : RingOfIntegers.monicFactorsMod θ p) : (ZMod p)[X]).natDegree at he
    rw [Equiv.symm_apply_apply] at he
    rw [he]
  let E' : {P : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) //
      (Ideal.span {(p : ℤ)}).inertiaDeg (P : Ideal (𝓞 K)) = 1} ≃
      {q : RingOfIntegers.monicFactorsMod θ p // (q : (ZMod p)[X]).natDegree = 1} :=
    E.subtypeEquiv hdegree
  let f : (ZMod p)[X] := (minpoly ℤ θ).map (Int.castRingHom (ZMod p))
  have hf : f ≠ 0 := map_monic_ne_zero (minpoly.monic θ.isIntegral)
  rw [rootResidues_card_eq_modularRoot]
  calc
    Nat.card (ModularRoot (minpoly ℤ θ) p) = Nat.card {x : ZMod p // f.eval x = 0} := by
      simp only [f, ModularRoot, eval_map]
    _ = Nat.card {q : (UniqueFactorizationMonoid.normalizedFactors f).toFinset //
        (q : (ZMod p)[X]).natDegree = 1} := (Nat.card_congr (monicLinearFactorEquivRoot f hf)).symm
    _ = Nat.card {P : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) //
        (Ideal.span {(p : ℤ)}).inertiaDeg (P : Ideal (𝓞 K)) = 1} := (Nat.card_congr E').symm
    _ = _ := (Nat.card_congr (idealNormPrimeEquivPrimeOverDegreeOne K p (Fact.out : p.Prime))).symm

lemma ideal_sup_product_of_coprime {R : Type*} [CommRing R] (I A B : Ideal R)
    (hAB : A ⊔ B = ⊤) (hprod : A * B ≤ I) : (I ⊔ A) * (I ⊔ B) = I := by
  apply le_antisymm
  · rw [Ideal.mul_sup, Ideal.sup_mul, Ideal.sup_mul]
    exact sup_le (sup_le Ideal.mul_le_right Ideal.mul_le_left)
      (sup_le Ideal.mul_le_right hprod)
  · calc
      I = I * (A ⊔ B) := by rw [hAB, Ideal.mul_top]
      _ = I * A ⊔ I * B := Ideal.mul_sup _ _ _
      _ ≤ (I ⊔ A) * (I ⊔ B) := by
        apply sup_le
        · rw [mul_comm I A]
          exact Ideal.mul_mono le_sup_right le_sup_left
        · exact Ideal.mul_mono le_sup_left le_sup_right

lemma ideal_absNorm_span_nat (K : Type*) [Field K] [NumberField K] (a : ℕ) :
    Ideal.absNorm (Ideal.span {(a : 𝓞 K)}) = a ^ Module.finrank ℤ (𝓞 K) := by
  rw [Ideal.absNorm_span_singleton]
  have he := Algebra.norm_algebraMap_of_basis (Module.Free.chooseBasis ℤ (𝓞 K)) (a : ℤ)
  rw [← Module.finrank_eq_card_basis (Module.Free.chooseBasis ℤ (𝓞 K))] at he
  simpa only [map_natCast, Int.natAbs_pow, Int.natAbs_natCast] using congrArg Int.natAbs he

lemma ideal_eq_of_le_of_norm_eq (K : Type*) [Field K] [NumberField K]
    (I J : Ideal (𝓞 K)) (hIJ : I ≤ J) (h : Ideal.absNorm I = Ideal.absNorm J)
    (hJ : Ideal.absNorm J ≠ 0) : I = J := by
  obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.mpr hIJ
  have hn : Ideal.absNorm L = 1 := by
    have he : Ideal.absNorm J * Ideal.absNorm L = Ideal.absNorm J * 1 := by
      rw [← map_mul, ← hL, h, mul_one]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hJ) he
  rw [Ideal.absNorm_eq_one_iff] at hn
  rw [hL, hn, Ideal.mul_top]

lemma ideal_absNorm_sup_span_of_coprime (K : Type*) [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hI : Ideal.absNorm I = a * b) :
    Ideal.absNorm (I ⊔ Ideal.span {(a : 𝓞 K)}) = a ∧
      Ideal.absNorm (I ⊔ Ideal.span {(b : 𝓞 K)}) = b := by
  let A : Ideal (𝓞 K) := Ideal.span {(a : 𝓞 K)}
  let B : Ideal (𝓞 K) := Ideal.span {(b : 𝓞 K)}
  have hAB : A ⊔ B = ⊤ := by
    apply Ideal.isCoprime_iff_sup_eq.mp
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    simpa only [map_natCast] using hab.isCoprime.map (Int.castRingHom (𝓞 K))
  have hprod : A * B ≤ I := by
    change Ideal.span {(a : 𝓞 K)} * Ideal.span {(b : 𝓞 K)} ≤ I
    rw [Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul, ← hI]
    exact Ideal.span_singleton_absNorm_le I
  have he := congrArg Ideal.absNorm (ideal_sup_product_of_coprime I A B hAB hprod)
  rw [map_mul, hI] at he
  have hA : Ideal.absNorm (I ⊔ A) ∣ a ^ Module.finrank ℤ (𝓞 K) := by
    rw [← ideal_absNorm_span_nat K a]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have hB : Ideal.absNorm (I ⊔ B) ∣ b ^ Module.finrank ℤ (𝓞 K) := by
    rw [← ideal_absNorm_span_nat K b]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have hAa : Ideal.absNorm (I ⊔ A) ∣ a :=
    (Nat.Coprime.of_dvd_left hA (hab.pow_left _)).dvd_of_dvd_mul_right
      (he ▸ dvd_mul_right _ _)
  have hBb : Ideal.absNorm (I ⊔ B) ∣ b :=
    (Nat.Coprime.of_dvd_left hB (hab.symm.pow_left _)).dvd_of_dvd_mul_left
      (he ▸ dvd_mul_left _ _)
  have hAp : 0 < Ideal.absNorm (I ⊔ A) := by
    have hm : 0 < Ideal.absNorm (I ⊔ A) * Ideal.absNorm (I ⊔ B) := he.symm ▸ Nat.mul_pos ha hb
    exact Nat.pos_of_mul_pos_right hm
  have hBp : 0 < Ideal.absNorm (I ⊔ B) := by
    have hm : 0 < Ideal.absNorm (I ⊔ A) * Ideal.absNorm (I ⊔ B) := he.symm ▸ Nat.mul_pos ha hb
    exact Nat.pos_of_mul_pos_left hm
  have hAle := Nat.le_of_dvd ha hAa
  have hBle := Nat.le_of_dvd hb hBb
  constructor <;> change _ = _ <;> nlinarith

noncomputable def idealNormMulEquiv (K : Type*) [Field K] [NumberField K]
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    {I : Ideal (𝓞 K) // Ideal.absNorm I = a * b} ≃
      {I : Ideal (𝓞 K) // Ideal.absNorm I = a} × {I : Ideal (𝓞 K) // Ideal.absNorm I = b} where
  toFun I :=
    ⟨⟨I.val ⊔ Ideal.span {(a : 𝓞 K)},
        (ideal_absNorm_sup_span_of_coprime K I.val a b ha hb hab I.property).1⟩,
      ⟨I.val ⊔ Ideal.span {(b : 𝓞 K)},
        (ideal_absNorm_sup_span_of_coprime K I.val a b ha hb hab I.property).2⟩⟩
  invFun J := ⟨J.1.val * J.2.val, by rw [map_mul, J.1.property, J.2.property]⟩
  left_inv I := by
    apply Subtype.ext
    apply ideal_sup_product_of_coprime
    · apply Ideal.isCoprime_iff_sup_eq.mp
      apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
      simpa only [map_natCast] using hab.isCoprime.map (Int.castRingHom (𝓞 K))
    · rw [Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul]
      simpa only [I.property] using Ideal.span_singleton_absNorm_le I.val
  right_inv J := by
    apply Prod.ext
    · apply Subtype.ext
      apply ideal_eq_of_le_of_norm_eq K
      · apply sup_le Ideal.mul_le_right
        simpa only [J.1.property] using Ideal.span_singleton_absNorm_le J.1.val
      · rw [J.1.property]
        apply (ideal_absNorm_sup_span_of_coprime K _ a b ha hb hab ?_).1
        rw [map_mul, J.1.property, J.2.property]
      · rw [J.1.property]
        exact ha.ne'
    · apply Subtype.ext
      apply ideal_eq_of_le_of_norm_eq K
      · apply sup_le Ideal.mul_le_left
        simpa only [J.2.property] using Ideal.span_singleton_absNorm_le J.2.val
      · rw [J.2.property]
        apply (ideal_absNorm_sup_span_of_coprime K _ a b ha hb hab ?_).2
        rw [map_mul, J.1.property, J.2.property]
      · rw [J.2.property]
        exact hb.ne'

lemma ideal_count_mul (K : Type*) [Field K] [NumberField K]
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = a * b} =
      Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = a} *
        Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = b} := by
  rw [Nat.card_congr (idealNormMulEquiv K a b ha hb hab), Nat.card_prod]

noncomputable def idealNormCount (K : Type*) [Field K] [NumberField K] : ArithmeticFunction ℕ where
  toFun n := if n = 0 then 0 else Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  map_zero' := by simp

lemma idealNormCount_apply (K : Type*) [Field K] [NumberField K] (n : ℕ) (hn : n ≠ 0) :
    idealNormCount K n = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := by
  simp [idealNormCount, hn]

lemma idealNormCount_multiplicative (K : Type*) [Field K] [NumberField K] :
    (idealNormCount K).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [idealNormCount, Ideal.absNorm_eq_one_iff]
  · intro a b ha hb hab
    rw [idealNormCount_apply K _ (Nat.mul_ne_zero ha hb), idealNormCount_apply K _ ha,
      idealNormCount_apply K _ hb]
    exact ideal_count_mul K a b (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) hab

lemma idealNormCount_harmonic_limit (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun N : ℕ ↦ harmonicWeightSum (idealNormCount K : ArithmeticFunction ℝ) N / log N)
      atTop (𝓝 (NumberField.dedekindZeta_residue K)) := by
  apply (ideal_count_harmonic_limit K).congr
  intro N
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [ArithmeticFunction.natCoe_apply,
    idealNormCount_apply K n (by have := (Finset.mem_Icc.mp hn).1; omega)]

lemma root_harmonic_limit_of_ideal_convolution (f : ℤ[X])
    (K : Type*) [Field K] [NumberField K] (v : ArithmeticFunction ℝ)
    (heq : (polynomialRootCount f : ArithmeticFunction ℝ) =
      v * (idealNormCount K : ArithmeticFunction ℝ))
    (hv : Summable (fun n : ℕ ↦ ‖v n / (n : ℝ)‖)) :
    Tendsto (fun N : ℕ ↦
      harmonicWeightSum (fun d ↦ (polynomialRootResidues f d).card) N / log N)
      atTop (𝓝 ((∑' n : ℕ, v n / (n : ℝ)) * NumberField.dedekindZeta_residue K)) := by
  have ht := tendsto_harmonicWeightSum_convolution (idealNormCount K : ArithmeticFunction ℝ) v
    (fun _ ↦ Nat.cast_nonneg _) _ (idealNormCount_harmonic_limit K) hv
  rw [← heq] at ht
  exact ht

lemma polynomial_root_map_bijective_of_square_zero
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Surjective φ)
    (hker : ∀ x : R, φ x = 0 → x ^ 2 = 0) (f : R[X])
    (hsimple : ∀ x : R, φ (f.eval x) = 0 → IsUnit (f.derivative.eval x)) :
    Function.Bijective (fun x : {x : R // f.eval x = 0} ↦
      (⟨φ x.val, by rw [eval_map, eval₂_at_apply, x.property, map_zero]⟩ :
        {y : S // (f.map φ).eval y = 0})) := by
  constructor
  · intro x y hxy
    have hφxy : φ x.val = φ y.val := congrArg Subtype.val hxy
    have hδ : (y.val - x.val) ^ 2 = 0 := hker _ (by rw [map_sub, hφxy, sub_self])
    have he := f.eval_add_of_sq_eq_zero x.val (y.val - x.val) hδ
    rw [add_sub_cancel, x.property, y.property, zero_add] at he
    have hu := hsimple x.val (by rw [x.property, map_zero])
    have hd : y.val - x.val = 0 := (hu.mul_right_eq_zero.mp he.symm)
    exact Subtype.ext (sub_eq_zero.mp hd).symm
  · intro y
    obtain ⟨a, ha⟩ := hφ y.val
    have hfa : φ (f.eval a) = 0 := by
      rw [← eval₂_at_apply, ← eval_map, ha]
      exact y.property
    obtain ⟨u, hu⟩ := hsimple a hfa
    let δ : R := -(f.eval a) * ↑u⁻¹
    have hφδ : φ δ = 0 := by simp [δ, hfa]
    have hroot : f.eval (a + δ) = 0 := by
      rw [f.eval_add_of_sq_eq_zero a δ (hker δ hφδ), ← hu]
      dsimp [δ]
      rw [mul_left_comm, Units.mul_inv, mul_one]
      ring
    refine ⟨⟨a + δ, hroot⟩, ?_⟩
    apply Subtype.ext
    simp only [map_add, hφδ, add_zero, ha]

lemma eval_int_map_naturality {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : ℤ[X]) (x : R) :
    φ ((f.map (Int.castRingHom R)).eval x) =
      (f.map (Int.castRingHom S)).eval (φ x) := by
  rw [← eval₂_at_apply, ← eval_map, Polynomial.map_map,
    RingHom.ext_int (φ.comp (Int.castRingHom R)) (Int.castRingHom S)]

lemma zmod_castHom_prime_pow_kernel_sq (p k : ℕ) (hp : p ≠ 0) (hk : 0 < k)
    (x : ZMod (p ^ (k + 1)))
    (hx : ZMod.castHom (pow_dvd_pow p (by omega : k ≤ k + 1)) (ZMod (p ^ k)) x = 0) :
    x ^ 2 = 0 := by
  haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp⟩
  have hx' : (x.val : ZMod (p ^ k)) = 0 := by
    rw [← ZMod.natCast_zmod_val x] at hx
    simpa only [map_natCast] using hx
  have hdiv := (ZMod.natCast_eq_zero_iff _ _).mp hx'
  rw [← ZMod.natCast_zmod_val x, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  have hpow : p ^ (k + 1) ∣ (p ^ k) ^ 2 := by
    rw [← pow_mul]
    exact pow_dvd_pow p (by omega)
  exact hpow.trans (pow_dvd_pow_of_dvd hdiv 2)

lemma zmod_prime_pow_isUnit_of_mod_prime_ne_zero (p e : ℕ) (hp : p.Prime)
    (he : e ≠ 0) (x : ZMod (p ^ e))
    (hx : ZMod.castHom (dvd_pow_self p he) (ZMod p) x ≠ 0) : IsUnit x := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hx' : (x.val : ZMod p) ≠ 0 := by
    rw [← ZMod.natCast_zmod_val x] at hx
    simpa only [map_natCast] using hx
  have hd : ¬p ∣ x.val := fun h ↦ hx' ((ZMod.natCast_eq_zero_iff _ _).mpr h)
  have hc : x.val.Coprime (p ^ e) := ((hp.coprime_iff_not_dvd.mpr hd).symm).pow_right e
  simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime x.val (p ^ e)).mpr hc

lemma rootResidues_prime_pow_succ_of_simple (f : ℤ[X]) (p k : ℕ) [Fact p.Prime]
    (hk : 0 < k)
    (hsimple : ∀ x : ZMod p, f.eval₂ (Int.castRingHom (ZMod p)) x = 0 →
      f.derivative.eval₂ (Int.castRingHom (ZMod p)) x ≠ 0) :
    (polynomialRootResidues f (p ^ (k + 1))).card =
      (polynomialRootResidues f (p ^ k)).card := by
  let R := ZMod (p ^ (k + 1))
  let S := ZMod (p ^ k)
  let φ : R →+* S := ZMod.castHom (pow_dvd_pow p (by omega : k ≤ k + 1)) S
  let ψ : S →+* ZMod p := ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)
  let τ : R →+* ZMod p := ZMod.castHom (dvd_pow_self p (by omega : k + 1 ≠ 0)) (ZMod p)
  let F : R[X] := f.map (Int.castRingHom R)
  have hcomp : ψ.comp φ = τ := Subsingleton.elim _ _
  have hφsimple : ∀ x : R, φ (F.eval x) = 0 → IsUnit (F.derivative.eval x) := by
    intro x hx
    have hroot : (f.map (Int.castRingHom (ZMod p))).eval (τ x) = 0 := by
      rw [← eval_int_map_naturality τ f x, ← hcomp, RingHom.comp_apply, hx, map_zero]
    have hder : τ (F.derivative.eval x) ≠ 0 := by
      change τ ((f.map (Int.castRingHom R)).derivative.eval x) ≠ 0
      rw [derivative_map, eval_int_map_naturality, eval_map]
      exact hsimple (τ x) (by simpa only [eval_map] using hroot)
    exact zmod_prime_pow_isUnit_of_mod_prime_ne_zero p (k + 1) Fact.out (by omega) _ hder
  have hbij := polynomial_root_map_bijective_of_square_zero φ (ZMod.castHom_surjective _)
    (zmod_castHom_prime_pow_kernel_sq p k (Fact.out : p.Prime).ne_zero hk) F hφsimple
  have hcard := Nat.card_congr (Equiv.ofBijective _ hbij)
  have hmap : F.map φ = f.map (Int.castRingHom S) := by
    dsimp only [F]
    rw [Polynomial.map_map, RingHom.ext_int (φ.comp (Int.castRingHom R)) (Int.castRingHom S)]
  rw [hmap] at hcard
  haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [rootResidues_card_eq_modularRoot, rootResidues_card_eq_modularRoot]
  simpa only [F, ModularRoot, eval_map] using hcard

lemma rootResidues_prime_pow_of_simple (f : ℤ[X]) (p k : ℕ) [Fact p.Prime]
    (hsimple : ∀ x : ZMod p, f.eval₂ (Int.castRingHom (ZMod p)) x = 0 →
      f.derivative.eval₂ (Int.castRingHom (ZMod p)) x ≠ 0) :
    (polynomialRootResidues f (p ^ (k + 1))).card = (polynomialRootResidues f p).card := by
  induction k with
  | zero => simp only [zero_add, pow_one]
  | succ k ih =>
    rw [rootResidues_prime_pow_succ_of_simple f p (k + 1) (by omega) hsimple]
    exact ih

lemma resultant_derivative_ne_zero_of_irreducible (f : ℤ[X])
    (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) : f.resultant f.derivative ≠ 0 := by
  have hirrQ : Irreducible (f.map (Int.castRingHom ℚ)) :=
    ((hirr.isPrimitive hdeg).irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hirr
  have hsep : IsCoprime (f.map (Int.castRingHom ℚ))
      (f.map (Int.castRingHom ℚ)).derivative := hirrQ.separable
  have hres := Polynomial.resultant_ne_zero _ _ hsep
  rw [derivative_map] at hres
  simp only [natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective] at hres
  rw [resultant_map_map] at hres
  intro hz
  exact hres (by rw [hz, map_zero])

lemma simple_roots_of_not_dvd_resultant (f : ℤ[X]) (hdeg : f.natDegree ≠ 0)
    (p : ℕ) (hp : ¬(p : ℤ) ∣ f.resultant f.derivative) :
    ∀ x : ZMod p, f.eval₂ (Int.castRingHom (ZMod p)) x = 0 →
      f.derivative.eval₂ (Int.castRingHom (ZMod p)) x ≠ 0 := by
  obtain ⟨a, b, _, _, hab⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f f.derivative le_rfl le_rfl (Or.inl hdeg)
  intro x hx hd
  have he := congrArg (fun g : ℤ[X] ↦ g.eval₂ (Int.castRingHom (ZMod p)) x) hab
  simp only [eval₂_add, eval₂_mul, eval₂_C, Int.coe_castRingHom, hx, hd,
    zero_mul, zero_add] at he
  exact hp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he.symm)

lemma rootResidues_prime_pow_of_not_dvd_resultant (f : ℤ[X]) (hdeg : f.natDegree ≠ 0)
    (p k : ℕ) [Fact p.Prime] (hp : ¬(p : ℤ) ∣ f.resultant f.derivative) :
    (polynomialRootResidues f (p ^ (k + 1))).card = (polynomialRootResidues f p).card :=
  rootResidues_prime_pow_of_simple f p k (simple_roots_of_not_dvd_resultant f hdeg p hp)

lemma rootResidues_prime_le_natDegree_of_simple (f : ℤ[X]) (p : ℕ) [Fact p.Prime]
    (hsimple : ∀ x : ZMod p, f.eval₂ (Int.castRingHom (ZMod p)) x = 0 →
      f.derivative.eval₂ (Int.castRingHom (ZMod p)) x ≠ 0) :
    (polynomialRootResidues f p).card ≤ f.natDegree := by
  let F : (ZMod p)[X] := f.map (Int.castRingHom (ZMod p))
  have hF : F ≠ 0 := by
    intro hf
    have hx : f.eval₂ (Int.castRingHom (ZMod p)) 0 = 0 := by
      rw [← eval_map]
      change F.eval 0 = 0
      rw [hf]
      simp
    have hd := hsimple 0 hx
    apply hd
    rw [← eval_map, ← derivative_map]
    change F.derivative.eval 0 = 0
    rw [hf]
    simp
  let e : ModularRoot f p ≃ F.roots.toFinset := Equiv.subtypeEquivRight (fun x ↦ by
    simp only [Multiset.mem_toFinset, mem_roots hF, IsRoot.def,
      F, eval_map])
  rw [rootResidues_card_eq_modularRoot, Nat.card_congr e, Nat.card_eq_fintype_card,
    Fintype.card_coe]
  exact (Multiset.toFinset_card_le _).trans (F.card_roots'.trans (natDegree_map_le ..))

noncomputable def dirichletAtom (m : ℕ) : ArithmeticFunction ℝ where
  toFun n := if n = m ∧ n ≠ 0 then 1 else 0
  map_zero' := by simp

lemma dirichletAtom_mul_apply (m : ℕ) (u : ArithmeticFunction ℝ) (n : ℕ) (hn : n ≠ 0) :
    (dirichletAtom m * u) n = if m ∣ n then u (n / m) else 0 := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b ↦ dirichletAtom m a * u b)]
  have he : ∀ d ∈ n.divisors, dirichletAtom m d * u (n / d) =
      if m = d then u (n / d) else 0 := by
    intro d hd
    have hd0 := (Nat.pos_of_mem_divisors hd).ne'
    change (if d = m ∧ d ≠ 0 then 1 else 0) * u (n / d) = _
    by_cases hdm : d = m
    · rw [if_pos ⟨hdm, hd0⟩, if_pos hdm.symm, one_mul]
    · rw [if_neg (fun h ↦ hdm h.1), if_neg (Ne.symm hdm), zero_mul]
  rw [Finset.sum_congr rfl he, Finset.sum_ite_eq]
  by_cases hmn : m ∣ n
  · rw [if_pos (Nat.mem_divisors.mpr ⟨hmn, hn⟩), if_pos hmn]
  · rw [if_neg (fun h ↦ hmn (Nat.mem_divisors.mp h).1), if_neg hmn]

lemma dirichletAtom_one : dirichletAtom 1 = 1 := by
  ext n
  by_cases hn : n = 1
  · simp [dirichletAtom, hn]
  · simp [dirichletAtom, hn]

noncomputable def idealAvoidingFiber (K : Type*) [Field K] [NumberField K]
    (s : Finset (Ideal (𝓞 K))) (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOf_absNorm_eq n).toFinset.filter (fun I ↦ ∀ P ∈ s, ¬P ∣ I)

lemma mem_idealAvoidingFiber (K : Type*) [Field K] [NumberField K]
    (s : Finset (Ideal (𝓞 K))) (n : ℕ) (I : Ideal (𝓞 K)) :
    I ∈ idealAvoidingFiber K s n ↔ Ideal.absNorm I = n ∧ ∀ P ∈ s, ¬P ∣ I := by
  simp [idealAvoidingFiber]

noncomputable def idealAvoidCount (K : Type*) [Field K] [NumberField K]
    (s : Finset (Ideal (𝓞 K))) : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else (idealAvoidingFiber K s n).card
  map_zero' := by simp

lemma idealAvoidCount_apply (K : Type*) [Field K] [NumberField K]
    (s : Finset (Ideal (𝓞 K))) (n : ℕ) (hn : n ≠ 0) :
    idealAvoidCount K s n = ((idealAvoidingFiber K s n).card : ℝ) := by
  simp [idealAvoidCount, hn]

lemma idealAvoidCount_empty (K : Type*) [Field K] [NumberField K] :
    idealAvoidCount K ∅ = (idealNormCount K : ArithmeticFunction ℝ) := by
  ext n
  by_cases hn : n = 0
  · simp [hn]
  rw [idealAvoidCount_apply K _ n hn, ArithmeticFunction.natCoe_apply, idealNormCount_apply K n hn]
  congr 1
  simp only [idealAvoidingFiber, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
    Finset.filter_true_of_mem]
  change _ = Nat.card ↥{I : Ideal (𝓞 K) | Ideal.absNorm I = n}
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ (Ideal.finite_setOf_absNorm_eq n)]

lemma idealAvoidingFiber_divisible_card (K : Type*) [Field K] [NumberField K]
    (s : Finset (Ideal (𝓞 K))) (P : Ideal (𝓞 K)) (hP : Prime P) (hPs : P ∉ s)
    (hs : ∀ Q ∈ s, Prime Q) (n : ℕ) (hdiv : Ideal.absNorm P ∣ n) :
    ((idealAvoidingFiber K s n).filter (fun I ↦ P ∣ I)).card =
      (idealAvoidingFiber K s (n / Ideal.absNorm P)).card := by
  have hNP : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hP.ne_zero
  symm
  apply Finset.card_nbij (fun J ↦ P * J)
  · intro J hJ
    obtain ⟨hJn, hJs⟩ := (mem_idealAvoidingFiber K _ _ _).mp hJ
    refine Finset.mem_filter.mpr ⟨(mem_idealAvoidingFiber K _ _ _).mpr ⟨?_, ?_⟩,
      dvd_mul_right _ _⟩
    · rw [map_mul, hJn, Nat.mul_div_cancel' hdiv]
    · intro Q hQs hQ
      rcases (hs Q hQs).dvd_mul.mp hQ with hQP | hQJ
      · have hQP' : Q = P := associated_iff_eq.mp (((hs Q hQs).dvd_prime_iff_associated hP).mp hQP)
        exact hPs (hQP' ▸ hQs)
      · exact hJs Q hQs hQJ
  · intro I hI J hJ he
    exact mul_left_cancel₀ hP.ne_zero he
  · intro I hI
    obtain ⟨hI, Pdiv⟩ := Finset.mem_filter.mp hI
    obtain ⟨hIn, hIs⟩ := (mem_idealAvoidingFiber K _ _ _).mp hI
    obtain ⟨J, hJ⟩ := Pdiv
    refine ⟨J, (mem_idealAvoidingFiber K _ _ _).mpr ⟨?_, ?_⟩, hJ.symm⟩
    · apply Nat.eq_div_of_mul_eq_right hNP
      rw [← map_mul, ← hJ, hIn]
    · intro Q hQs hQJ
      apply hIs Q hQs
      rw [hJ]
      exact dvd_mul_of_dvd_right hQJ P

lemma idealAvoidCount_insert (K : Type*) [Field K] [NumberField K]
    (s : Finset (Ideal (𝓞 K))) (P : Ideal (𝓞 K)) (hP : Prime P) (hPs : P ∉ s)
    (hs : ∀ Q ∈ s, Prime Q) :
    idealAvoidCount K (insert P s) = (1 - dirichletAtom (Ideal.absNorm P)) * idealAvoidCount K s := by
  ext n
  by_cases hn : n = 0
  · simp [hn]
  rw [sub_mul, one_mul, ZeroHom.sub_apply, dirichletAtom_mul_apply _ _ n hn,
    idealAvoidCount_apply K _ n hn, idealAvoidCount_apply K _ n hn]
  have hset : (idealAvoidingFiber K s n).filter (fun I ↦ ¬P ∣ I) =
      idealAvoidingFiber K (insert P s) n := by
    ext I
    simp only [Finset.mem_filter, mem_idealAvoidingFiber, Finset.mem_insert,
      forall_eq_or_imp]
    tauto
  have hc := Finset.card_filter_add_card_filter_not (s := idealAvoidingFiber K s n) (fun I ↦ P ∣ I)
  rw [hset] at hc
  by_cases hdiv : Ideal.absNorm P ∣ n
  · rw [if_pos hdiv]
    have hquot : n / Ideal.absNorm P ≠ 0 := by
      exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv)
        (Nat.pos_of_dvd_of_pos hdiv (Nat.pos_of_ne_zero hn))).ne'
    rw [idealAvoidCount_apply K _ _ hquot]
    rw [idealAvoidingFiber_divisible_card K s P hP hPs hs n hdiv] at hc
    have hcR : ((idealAvoidingFiber K s (n / Ideal.absNorm P)).card : ℝ) +
        (idealAvoidingFiber K (insert P s) n).card = (idealAvoidingFiber K s n).card := by
      exact_mod_cast hc
    linarith
  · rw [if_neg hdiv, sub_zero]
    have hempty : ((idealAvoidingFiber K s n).filter (fun I ↦ P ∣ I)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hI
      obtain ⟨hI, hPI⟩ := Finset.mem_filter.mp hI
      have hIn := ((mem_idealAvoidingFiber K _ _ _).mp hI).1
      exact hdiv (hIn ▸ map_dvd Ideal.absNorm hPI)
    rw [hempty, Finset.card_empty, zero_add] at hc
    exact_mod_cast hc

lemma idealAvoidCount_eq_product (K : Type*) [Field K] [NumberField K]
    (s : Finset (Ideal (𝓞 K))) (hs : ∀ P ∈ s, Prime P) :
    idealAvoidCount K s =
      (∏ P ∈ s, (1 - dirichletAtom (Ideal.absNorm P))) * (idealNormCount K : ArithmeticFunction ℝ) := by
  induction s using Finset.induction with
  | empty => simp [idealAvoidCount_empty]
  | @insert P s hPs ih =>
    have hP : Prime P := hs P (Finset.mem_insert_self _ _)
    have hs' : ∀ Q ∈ s, Prime Q := fun Q hQ ↦ hs Q (Finset.mem_insert_of_mem hQ)
    rw [idealAvoidCount_insert K s P hP hPs hs', ih hs', Finset.prod_insert hPs, mul_assoc]

noncomputable def rationalPrimeIdeals (K : Type*) [Field K] [NumberField K] (p : ℕ) :
    Finset (Ideal (𝓞 K)) := _root_.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)

lemma mem_rationalPrimeIdeals (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 K)) : P ∈ rationalPrimeIdeals K p ↔
      P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) := by
  haveI := Int.ideal_span_isMaximal_of_prime p
  exact _root_.mem_primesOverFinset_iff
    (by simp [(Fact.out : p.Prime).ne_zero]) (𝓞 K)

lemma prime_of_mem_rationalPrimeIdeals (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 K)) (hP : P ∈ rationalPrimeIdeals K p) : Prime P := by
  obtain ⟨hprime, hlies⟩ := (mem_rationalPrimeIdeals K p P).mp hP
  haveI := hlies
  exact Ideal.prime_of_isPrime
    (Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)})
      (by simp [(Fact.out : p.Prime).ne_zero]) P) hprime

lemma norm_of_mem_rationalPrimeIdeals (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 K)) (hP : P ∈ rationalPrimeIdeals K p) :
    Ideal.absNorm P = p ^ (Ideal.span {(p : ℤ)}).inertiaDeg P := by
  haveI := ((mem_rationalPrimeIdeals K p P).mp hP).2
  exact Ideal.absNorm_eq_pow_inertiaDeg' P Fact.out

lemma prime_ideal_liesOver_of_mem_nat (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 K)) (hP : P.IsPrime) (hpP : (p : 𝓞 K) ∈ P) :
    P.LiesOver (Ideal.span {(p : ℤ)}) := by
  refine ⟨(Int.ideal_span_isMaximal_of_prime p).eq_of_le
    (Ideal.comap_ne_top _ hP.ne_top) ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
  simpa only [map_natCast] using hpP

lemma idealAvoidCount_prime_pow_succ (K : Type*) [Field K] [NumberField K]
    (p k : ℕ) [Fact p.Prime] : idealAvoidCount K (rationalPrimeIdeals K p) (p ^ (k + 1)) = 0 := by
  have hp : p.Prime := Fact.out
  rw [idealAvoidCount_apply K _ _ (pow_ne_zero _ hp.ne_zero)]
  have hempty : idealAvoidingFiber K (rationalPrimeIdeals K p) (p ^ (k + 1)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro I hI
    obtain ⟨hIn, havoid⟩ := (mem_idealAvoidingFiber K _ _ _).mp hI
    have hI0 : I ≠ 0 := by
      intro h
      rw [h, map_zero] at hIn
      exact (pow_ne_zero _ hp.ne_zero) hIn.symm
    have hIunit : ¬IsUnit I := by
      intro h
      have h1 : Ideal.absNorm I = 1 := by rw [Ideal.isUnit_iff.mp h, Ideal.absNorm_top]
      exact (Nat.one_lt_pow (by omega : k + 1 ≠ 0) hp.one_lt).ne' (hIn ▸ h1)
    obtain ⟨P, hPirr, hPI⟩ := WfDvdMonoid.exists_irreducible_factor hIunit hI0
    have hP : Prime P := (UniqueFactorizationMonoid.irreducible_iff_prime).mp hPirr
    have hPprime := Ideal.isPrime_of_prime hP
    have hpP : (p : 𝓞 K) ∈ P := by
      apply hPprime.mem_of_pow_mem (k + 1)
      have hN := Ideal.absNorm_mem I
      rw [hIn, Nat.cast_pow] at hN
      exact (Ideal.dvd_iff_le.mp hPI) hN
    have hPs : P ∈ rationalPrimeIdeals K p := (mem_rationalPrimeIdeals K p P).mpr
      ⟨hPprime, prime_ideal_liesOver_of_mem_nat K p P hPprime hpP⟩
    exact havoid P hPs hPI
  rw [hempty, Finset.card_empty, Nat.cast_zero]

lemma idealAvoidCount_one (K : Type*) [Field K] [NumberField K]
    (s : Finset (Ideal (𝓞 K))) (hs : ∀ P ∈ s, Prime P) : idealAvoidCount K s 1 = 1 := by
  rw [idealAvoidCount_apply K s 1 one_ne_zero]
  have hset : idealAvoidingFiber K s 1 = {⊤} := by
    ext I
    rw [mem_idealAvoidingFiber, Finset.mem_singleton, Ideal.absNorm_eq_one_iff]
    constructor
    · exact fun h ↦ h.1
    · intro hI
      refine ⟨hI, ?_⟩
      intro P hP hPI
      apply (hs P hP).not_unit
      apply isUnit_of_dvd_one
      simpa only [hI, Ideal.one_eq_top] using hPI
  rw [hset, Finset.card_singleton, Nat.cast_one]

noncomputable def idealLocalInverse (K : Type*) [Field K] [NumberField K] (p : ℕ) :
    ArithmeticFunction ℝ :=
  ∏ P ∈ rationalPrimeIdeals K p, (1 - dirichletAtom (Ideal.absNorm P))

lemma idealLocalInverse_mul_idealNormCount (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :
    idealLocalInverse K p * (idealNormCount K : ArithmeticFunction ℝ) =
      idealAvoidCount K (rationalPrimeIdeals K p) :=
  (idealAvoidCount_eq_product K _ (prime_of_mem_rationalPrimeIdeals K p)).symm

lemma idealLocalInverse_prime_pow (K : Type*) [Field K] [NumberField K]
    (p k : ℕ) [Fact p.Prime] :
    (idealLocalInverse K p * (idealNormCount K : ArithmeticFunction ℝ)) (p ^ k) =
      if k = 0 then 1 else 0 := by
  rw [idealLocalInverse_mul_idealNormCount]
  cases k with
  | zero =>
    rw [pow_zero, if_pos rfl]
    exact idealAvoidCount_one K _ (prime_of_mem_rationalPrimeIdeals K p)
  | succ k => rw [idealAvoidCount_prime_pow_succ]; simp

lemma dirichletAtom_zero : dirichletAtom 0 = 0 := by
  ext n
  simp [dirichletAtom]

lemma dirichletAtom_mul (m n : ℕ) : dirichletAtom m * dirichletAtom n = dirichletAtom (m * n) := by
  by_cases hm : m = 0
  · simp [hm, dirichletAtom_zero]
  by_cases hn : n = 0
  · simp [hn, dirichletAtom_zero]
  ext k
  by_cases hk : k = 0
  · simp [hk]
  rw [dirichletAtom_mul_apply m _ k hk]
  by_cases hd : m ∣ k
  · rw [if_pos hd]
    have hq : k / m ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hd)
      (Nat.pos_of_ne_zero hm)).ne'
    have he : k / m = n ↔ k = m * n := by
      constructor
      · intro h
        rw [← h, Nat.mul_div_cancel' hd]
      · intro h
        rw [h, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm)]
    simp [dirichletAtom, he, hq, hk]
  · rw [if_neg hd]
    have he : k ≠ m * n := by intro h; exact hd (h ▸ dvd_mul_right _ _)
    simp [dirichletAtom, he]

lemma dirichletAtom_prod {ι : Type*} (s : Finset ι) (m : ι → ℕ) :
    ∏ i ∈ s, dirichletAtom (m i) = dirichletAtom (∏ i ∈ s, m i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [dirichletAtom_one]
  | @insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, ih, dirichletAtom_mul]

lemma signed_dirichletAtom_apply (r : ℕ) (a n : ℕ) :
    (((-1 : ArithmeticFunction ℝ) ^ r) * dirichletAtom a : ArithmeticFunction ℝ) n =
      (-1 : ℝ) ^ r * dirichletAtom a n := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', mul_assoc]
    have he : (-1 : ArithmeticFunction ℝ) * ((-1 : ArithmeticFunction ℝ) ^ r * dirichletAtom a) =
        -((-1 : ArithmeticFunction ℝ) ^ r * dirichletAtom a) := by ring
    rw [he]
    change -(((-1 : ArithmeticFunction ℝ) ^ r * dirichletAtom a : ArithmeticFunction ℝ) n) = _
    rw [ih, pow_succ']
    ring

def arithmeticEvaluation (n : ℕ) : ArithmeticFunction ℝ →+ ℝ where
  toFun u := u n
  map_zero' := rfl
  map_add' _ _ := rfl

lemma arithmeticFunction_sum_apply {ι : Type*} (s : Finset ι) (u : ι → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ s, u i) n = ∑ i ∈ s, u i n :=
  map_sum (arithmeticEvaluation n) u s

lemma finite_local_inverse_powerset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m : ι → ℕ) (n : ℕ) :
    (∏ i ∈ s, (1 - dirichletAtom (m i)) : ArithmeticFunction ℝ) n =
      ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card * dirichletAtom (∏ i ∈ t, m i) n := by
  rw [Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one, dirichletAtom_prod]
  rw [arithmeticFunction_sum_apply]
  apply Finset.sum_congr rfl
  intro t ht
  exact signed_dirichletAtom_apply _ _ _

lemma rationalPrimeIdeals_inertia_pos (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 K)) (hP : P ∈ rationalPrimeIdeals K p) :
    0 < (Ideal.span {(p : ℤ)}).inertiaDeg P := by
  haveI := Int.ideal_span_isMaximal_of_prime p
  haveI := ((mem_rationalPrimeIdeals K p P).mp hP).2
  exact Ideal.inertiaDeg_pos _ _

lemma rationalPrimeIdeals_inertia_sum_le (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :
    ∑ P ∈ rationalPrimeIdeals K p, (Ideal.span {(p : ℤ)}).inertiaDeg P ≤ Module.finrank ℚ K := by
  haveI := Int.ideal_span_isMaximal_of_prime p
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simp [(Fact.out : p.Prime).ne_zero]
  rw [← Ideal.sum_ramification_inertia (𝓞 K) ℚ K hp0]
  apply Finset.sum_le_sum
  intro P hP
  haveI := ((mem_rationalPrimeIdeals K p P).mp hP).2
  haveI := ((mem_rationalPrimeIdeals K p P).mp hP).1
  exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero
    (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0))

lemma rationalPrimeIdeals_card_le (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : (rationalPrimeIdeals K p).card ≤ Module.finrank ℚ K := by
  calc
    (rationalPrimeIdeals K p).card = ∑ P ∈ rationalPrimeIdeals K p, 1 := by simp
    _ ≤ ∑ P ∈ rationalPrimeIdeals K p, (Ideal.span {(p : ℤ)}).inertiaDeg P :=
      Finset.sum_le_sum (fun P hP ↦ rationalPrimeIdeals_inertia_pos K p P hP)
    _ ≤ _ := rationalPrimeIdeals_inertia_sum_le K p

lemma idealLocalInverse_powerset (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    idealLocalInverse K p n = ∑ t ∈ (rationalPrimeIdeals K p).powerset,
      (-1 : ℝ) ^ t.card * dirichletAtom
        (p ^ (∑ P ∈ t, (Ideal.span {(p : ℤ)}).inertiaDeg P)) n := by
  rw [idealLocalInverse, finite_local_inverse_powerset]
  apply Finset.sum_congr rfl
  intro t ht
  have hsub := Finset.mem_powerset.mp ht
  have he : (∏ P ∈ t, Ideal.absNorm P) = p ^ (∑ P ∈ t, (Ideal.span {(p : ℤ)}).inertiaDeg P) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl (fun P hP ↦ norm_of_mem_rationalPrimeIdeals K p P (hsub hP))
  rw [he]

lemma idealLocalInverse_prime_pow_eq_zero (K : Type*) [Field K] [NumberField K]
    (p k : ℕ) [Fact p.Prime] (hk : Module.finrank ℚ K < k) : idealLocalInverse K p (p ^ k) = 0 := by
  rw [idealLocalInverse_powerset]
  apply Finset.sum_eq_zero
  intro t ht
  have hsub := Finset.mem_powerset.mp ht
  have hsum : (∑ P ∈ t, (Ideal.span {(p : ℤ)}).inertiaDeg P) ≤ Module.finrank ℚ K :=
    (Finset.sum_le_sum_of_subset hsub).trans (rationalPrimeIdeals_inertia_sum_le K p)
  have he : p ^ k ≠ p ^ (∑ P ∈ t, (Ideal.span {(p : ℤ)}).inertiaDeg P) := by
    intro h
    have := (Nat.pow_right_injective (Fact.out : p.Prime).two_le) h
    omega
  simp [dirichletAtom, he]

lemma rationalPrimeIdeals_nonempty (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : (rationalPrimeIdeals K p).Nonempty := by
  haveI := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨P⟩ := (inferInstance : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)))
  exact ⟨P.val, (mem_rationalPrimeIdeals K p P.val).mpr P.property⟩

lemma sum_dirichletAtom_prime_pow (p d e : ℕ) (hp : p.Prime) (he : e ≤ d) :
    ∑ j ∈ Finset.range (d + 1), dirichletAtom (p ^ e) (p ^ j) = (1 : ℝ) := by
  have hterm : ∀ j : ℕ, dirichletAtom (p ^ e) (p ^ j) = if e = j then 1 else 0 := by
    intro j
    have hz := pow_ne_zero j hp.ne_zero
    have hpow : p ^ j = p ^ e ↔ e = j :=
      (Nat.pow_right_injective hp.two_le).eq_iff.trans eq_comm
    simp [dirichletAtom, hpow, hp.ne_zero]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (by omega))]

lemma idealLocalInverse_sum_eq_zero (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :
    ∑ j ∈ Finset.range (Module.finrank ℚ K + 1), idealLocalInverse K p (p ^ j) = (0 : ℝ) := by
  simp_rw [idealLocalInverse_powerset]
  rw [Finset.sum_comm]
  have hterm : ∀ t ∈ (rationalPrimeIdeals K p).powerset,
      ∑ j ∈ Finset.range (Module.finrank ℚ K + 1), (-1 : ℝ) ^ t.card *
        dirichletAtom (p ^ (∑ P ∈ t, (Ideal.span {(p : ℤ)}).inertiaDeg P)) (p ^ j) =
          (-1 : ℝ) ^ t.card := by
    intro t ht
    rw [← Finset.mul_sum, sum_dirichletAtom_prime_pow p _ _ Fact.out ?_, mul_one]
    exact (Finset.sum_le_sum_of_subset (Finset.mem_powerset.mp ht)).trans
      (rationalPrimeIdeals_inertia_sum_le K p)
  rw [Finset.sum_congr rfl hterm]
  have he := Finset.prod_sub (fun _ : Ideal (𝓞 K) ↦ (1 : ℝ)) (fun _ ↦ (1 : ℝ))
    (rationalPrimeIdeals K p)
  simp only [sub_self, Finset.prod_const_one, mul_one] at he
  rw [← he]
  exact Finset.prod_eq_zero (rationalPrimeIdeals_nonempty K p).choose_spec rfl

lemma idealLocalInverse_sum_abs_le (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :
    ∑ j ∈ Finset.range (Module.finrank ℚ K + 1), |idealLocalInverse K p (p ^ j)| ≤
      (2 : ℝ) ^ Module.finrank ℚ K := by
  have hbound : ∀ n, |idealLocalInverse K p n| ≤
      ∑ t ∈ (rationalPrimeIdeals K p).powerset,
        dirichletAtom (p ^ (∑ P ∈ t, (Ideal.span {(p : ℤ)}).inertiaDeg P)) n := by
    intro n
    rw [idealLocalInverse_powerset]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro t ht
    simp only [dirichletAtom, ArithmeticFunction.coe_mk]
    split_ifs <;> simp
  calc
    _ ≤ ∑ j ∈ Finset.range (Module.finrank ℚ K + 1),
        ∑ t ∈ (rationalPrimeIdeals K p).powerset,
          dirichletAtom (p ^ (∑ P ∈ t, (Ideal.span {(p : ℤ)}).inertiaDeg P)) (p ^ j) :=
      Finset.sum_le_sum (fun j _ ↦ hbound (p ^ j))
    _ = ∑ t ∈ (rationalPrimeIdeals K p).powerset, (1 : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      exact sum_dirichletAtom_prime_pow p _ _ Fact.out
        ((Finset.sum_le_sum_of_subset (Finset.mem_powerset.mp ht)).trans
          (rationalPrimeIdeals_inertia_sum_le K p))
    _ = (2 : ℝ) ^ (rationalPrimeIdeals K p).card := by simp
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (rationalPrimeIdeals_card_le K p)

lemma idealLocalInverse_apply_one (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : idealLocalInverse K p 1 = 1 := by
  have he := idealLocalInverse_prime_pow K p 0
  rw [pow_zero, ArithmeticFunction.mul_apply_one,
    (idealNormCount_multiplicative K).natCast.map_one, mul_one, if_pos rfl] at he
  exact he

lemma idealLocalInverse_apply_prime (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :
    idealLocalInverse K p p = -(idealNormCount K p : ℝ) := by
  have he := idealLocalInverse_prime_pow K p 1
  rw [convolution_prime_pow _ _ p 1 Fact.out] at he
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, Nat.sub_zero,
    Nat.sub_self, zero_add, if_neg Nat.one_ne_zero] at he
  rw [idealLocalInverse_apply_one, (idealNormCount_multiplicative K).natCast.map_one,
    one_mul, mul_one] at he
  simp only [ite_false, ArithmeticFunction.natCoe_apply] at he
  linarith

lemma idealLocalCorrection_apply_one (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (u : ArithmeticFunction ℝ) (hu : u 1 = 1) :
    (idealLocalInverse K p * u) 1 = 1 := by
  rw [ArithmeticFunction.mul_apply_one, idealLocalInverse_apply_one, hu, mul_one]

lemma idealLocalCorrection_apply_prime (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (u : ArithmeticFunction ℝ) (hu : u 1 = 1)
    (hup : u p = idealNormCount K p) : (idealLocalInverse K p * u) p = 0 := by
  have he := convolution_prime_pow (idealLocalInverse K p) u p 1 (Fact.out : p.Prime)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, Nat.sub_zero,
    Nat.sub_self, zero_add] at he
  rw [he, idealLocalInverse_apply_one, idealLocalInverse_apply_prime, hu, hup]
  ring

lemma idealLocalCorrection_prime_pow_eq_zero (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (u : ArithmeticFunction ℝ) (r : ℝ)
    (hu : ∀ j : ℕ, u (p ^ (j + 1)) = r) (k : ℕ) (hk : Module.finrank ℚ K < k) :
    (idealLocalInverse K p * u) (p ^ k) = 0 := by
  rw [convolution_prime_pow _ _ p k Fact.out]
  have htrunc : (∑ j ∈ Finset.range (k + 1), idealLocalInverse K p (p ^ j) * u (p ^ (k - j))) =
      ∑ j ∈ Finset.range (Module.finrank ℚ K + 1), idealLocalInverse K p (p ^ j) * u (p ^ (k - j)) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hjD
    rw [idealLocalInverse_prime_pow_eq_zero K p j (by simpa using hjD), zero_mul]
  rw [htrunc]
  have hterm : ∀ j ∈ Finset.range (Module.finrank ℚ K + 1),
      idealLocalInverse K p (p ^ j) * u (p ^ (k - j)) = idealLocalInverse K p (p ^ j) * r := by
    intro j hj
    have hjk : 0 < k - j := by have := Finset.mem_range.mp hj; omega
    rw [show k - j = (k - j - 1) + 1 by omega, hu]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, idealLocalInverse_sum_eq_zero, zero_mul]

lemma idealLocalCorrection_abs_le (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (u : ArithmeticFunction ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ j : ℕ, |u (p ^ j)| ≤ B) (k : ℕ) :
    |(idealLocalInverse K p * u) (p ^ k)| ≤ (2 : ℝ) ^ Module.finrank ℚ K * B := by
  rw [convolution_prime_pow _ _ p k Fact.out]
  calc
    _ ≤ ∑ j ∈ Finset.range (k + 1), |idealLocalInverse K p (p ^ j)| * B := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hu _) (abs_nonneg _)
    _ = (∑ j ∈ Finset.range (k + 1), |idealLocalInverse K p (p ^ j)|) * B :=
      (Finset.sum_mul ..).symm
    _ ≤ (2 : ℝ) ^ Module.finrank ℚ K * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      calc
        _ ≤ ∑ j ∈ Finset.range (Module.finrank ℚ K + 1), |idealLocalInverse K p (p ^ j)| := by
          by_cases hk : k ≤ Module.finrank ℚ K
          · exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_mono (by omega)) (fun _ _ _ ↦ abs_nonneg _)
          · apply le_of_eq
            symm
            apply Finset.sum_subset (Finset.range_mono (by omega))
            intro j hj hjD
            rw [idealLocalInverse_prime_pow_eq_zero K p j (by simpa using hjD), abs_zero]
        _ ≤ _ := idealLocalInverse_sum_abs_le K p

noncomputable def multiplicativeExtension (w : ℕ → ℕ → ℝ) : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else n.factorization.prod w
  map_zero' := by simp

lemma multiplicativeExtension_multiplicative (w : ℕ → ℕ → ℝ) :
    (multiplicativeExtension w).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [multiplicativeExtension]
  · intro m n hm hn hmn
    simp only [multiplicativeExtension, ArithmeticFunction.coe_mk,
      if_neg hm, if_neg hn, if_neg (Nat.mul_ne_zero hm hn), Nat.factorization_mul hm hn]
    exact Finsupp.prod_add_index_of_disjoint (by simpa using hmn.disjoint_primeFactors) w

lemma multiplicativeExtension_prime_pow (w : ℕ → ℕ → ℝ) (p k : ℕ) (hp : p.Prime)
    (hw : w p 0 = 1) : multiplicativeExtension w (p ^ k) = w p k := by
  cases k with
  | zero => simp [multiplicativeExtension, hw]
  | succ k =>
    simp [multiplicativeExtension, hp.ne_zero, Nat.factorization_pow,
      hp.factorization, Finsupp.prod, Nat.support_factorization, Finsupp.smul_single,
      Nat.primeFactors_pow p (by omega : k + 1 ≠ 0), hp.primeFactors]

noncomputable def idealCorrection (K : Type*) [Field K] [NumberField K]
    (u : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  multiplicativeExtension (fun p k ↦ (idealLocalInverse K p * u) (p ^ k))

lemma idealCorrection_multiplicative (K : Type*) [Field K] [NumberField K]
    (u : ArithmeticFunction ℝ) : (idealCorrection K u).IsMultiplicative :=
  multiplicativeExtension_multiplicative _

lemma idealCorrection_prime_pow (K : Type*) [Field K] [NumberField K]
    (u : ArithmeticFunction ℝ) (hu : u.IsMultiplicative) (p k : ℕ) [Fact p.Prime] :
    idealCorrection K u (p ^ k) = (idealLocalInverse K p * u) (p ^ k) := by
  apply multiplicativeExtension_prime_pow _ p k Fact.out
  rw [pow_zero, idealLocalCorrection_apply_one K p u hu.map_one]

lemma convolution_prime_pow_congr_left (u v w : ArithmeticFunction ℝ)
    (p k : ℕ) (hp : p.Prime) (h : ∀ j, u (p ^ j) = v (p ^ j)) :
    (u * w) (p ^ k) = (v * w) (p ^ k) := by
  rw [convolution_prime_pow _ _ p k hp, convolution_prime_pow _ _ p k hp]
  apply Finset.sum_congr rfl
  intro j hj
  rw [h]

lemma mul_idealLocalInverse_local_identity (K : Type*) [Field K] [NumberField K]
    (u : ArithmeticFunction ℝ) (p k : ℕ) [Fact p.Prime] :
    (u * (idealLocalInverse K p * (idealNormCount K : ArithmeticFunction ℝ))) (p ^ k) = u (p ^ k) := by
  rw [convolution_prime_pow _ _ p k Fact.out]
  rw [Finset.sum_eq_single k]
  · rw [Nat.sub_self, idealLocalInverse_prime_pow, if_pos rfl, mul_one]
  · intro j hj hjk
    have hkj : k - j ≠ 0 := by have := Finset.mem_range.mp hj; omega
    rw [idealLocalInverse_prime_pow, if_neg hkj, mul_zero]
  · simp

lemma idealCorrection_mul_idealNormCount (K : Type*) [Field K] [NumberField K]
    (u : ArithmeticFunction ℝ) (hu : u.IsMultiplicative) :
    idealCorrection K u * (idealNormCount K : ArithmeticFunction ℝ) = u := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((idealCorrection_multiplicative K u).mul (idealNormCount_multiplicative K).natCast) _ hu).mpr
  intro p k hp
  haveI : Fact p.Prime := ⟨hp⟩
  rw [convolution_prime_pow_congr_left _ (idealLocalInverse K p * u) _ p k hp
    (fun j ↦ idealCorrection_prime_pow K u hu p j)]
  have he : (idealLocalInverse K p * u) * (idealNormCount K : ArithmeticFunction ℝ) =
      u * (idealLocalInverse K p * (idealNormCount K : ArithmeticFunction ℝ)) := by ring
  rw [he, mul_idealLocalInverse_local_identity]

lemma rootCount_idealCorrection_identity (f : ℤ[X])
    (K : Type*) [Field K] [NumberField K] :
    (polynomialRootCount f : ArithmeticFunction ℝ) =
      idealCorrection K (polynomialRootCount f : ArithmeticFunction ℝ) *
        (idealNormCount K : ArithmeticFunction ℝ) :=
  (idealCorrection_mul_idealNormCount K _ (polynomialRootCount_multiplicative f).natCast).symm

lemma root_harmonic_limit_of_idealCorrection_summable (f : ℤ[X])
    (K : Type*) [Field K] [NumberField K]
    (hv : Summable (fun n : ℕ ↦
      ‖idealCorrection K (polynomialRootCount f : ArithmeticFunction ℝ) n / (n : ℝ)‖)) :
    Tendsto (fun N : ℕ ↦ harmonicWeightSum (fun d ↦ (polynomialRootResidues f d).card) N / log N)
      atTop (𝓝 ((∑' n : ℕ, idealCorrection K (polynomialRootCount f : ArithmeticFunction ℝ) n /
        (n : ℝ)) * NumberField.dedekindZeta_residue K)) :=
  root_harmonic_limit_of_ideal_convolution f K _ (rootCount_idealCorrection_identity f K) hv

lemma summable_of_multiplicative_local_bound (f : ℕ → ℝ)
    (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hf : ∀ n, 0 ≤ f n)
    (hmul : ∀ m n, m.Coprime n → f (m * n) = f m * f n)
    (C : ℕ → ℝ) (hC : Summable C) (hCpos : ∀ n, 0 ≤ C n)
    (hlocal : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ ↦ f (p ^ k)))
    (hbound : ∀ p : ℕ, p.Prime → (∑' k : ℕ, f (p ^ k)) ≤ 1 + C p) : Summable f := by
  apply summable_of_sum_range_le hf (c := Real.exp (∑' p, C p))
  intro N
  have hlocalnorm : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ ↦ ‖f (p ^ k)‖) := by
    intro p hp
    exact (hlocal p hp).norm
  have hS := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hf1
    (fun {m n} hmn ↦ hmul m n hmn) hlocalnorm (Finset.range N)
  have hInd : Summable ((Nat.factoredNumbers (Finset.range N)).indicator f) :=
    summable_subtype_iff_indicator.mp hS.1.of_norm
  have hsum : (∑ i ∈ Finset.range N, f i) =
      ∑ i ∈ Finset.range N, (Nat.factoredNumbers (Finset.range N)).indicator f i := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hi0 : i = 0
    · simp [hi0, hf0, Set.indicator]
    · have hmem := Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hi0) (Finset.mem_range.mp hi)
      rw [Nat.smoothNumbers_eq_factoredNumbers] at hmem
      exact (Set.indicator_of_mem hmem f).symm
  rw [hsum]
  calc
    _ ≤ ∑' i : ℕ, (Nat.factoredNumbers (Finset.range N)).indicator f i :=
      hInd.sum_le_tsum _ (fun i _ ↦ Set.indicator_nonneg (fun i _ ↦ hf i) i)
    _ = ∑' i : Nat.factoredNumbers (Finset.range N), f i := (tsum_subtype _ _).symm
    _ = ∏ p ∈ (Finset.range N).filter Nat.Prime, ∑' k : ℕ, f (p ^ k) := hS.2.tsum_eq
    _ ≤ ∏ p ∈ (Finset.range N).filter Nat.Prime, (1 + C p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact tsum_nonneg (fun k ↦ hf _)
      · intro p hp
        exact hbound p (Finset.mem_filter.mp hp).2
    _ ≤ ∏ p ∈ (Finset.range N).filter Nat.Prime, Real.exp (C p) := by
      apply Finset.prod_le_prod
      · intro p hp
        linarith [hCpos p]
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp (C p)
    _ = Real.exp (∑ p ∈ (Finset.range N).filter Nat.Prime, C p) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (hC.sum_le_tsum _ (fun p _ ↦ hCpos p))

lemma summable_weighted_multiplicative_of_local_bound (u : ArithmeticFunction ℝ)
    (hu : u.IsMultiplicative) (C : ℕ → ℝ) (hC : Summable C) (hCpos : ∀ n, 0 ≤ C n)
    (hlocal : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ ↦ |u (p ^ k) / (p : ℝ) ^ k|))
    (hbound : ∀ p : ℕ, p.Prime → (∑' k : ℕ, |u (p ^ k) / (p : ℝ) ^ k|) ≤ 1 + C p) :
    Summable (fun n : ℕ ↦ ‖u n / (n : ℝ)‖) := by
  simp only [Real.norm_eq_abs]
  apply summable_of_multiplicative_local_bound (fun n ↦ |u n / (n : ℝ)|)
    (by simp) (by dsimp only; rw [hu.map_one]; norm_num) (fun _ ↦ abs_nonneg _) ?_ C hC hCpos
  · simpa only [Nat.cast_pow] using hlocal
  · simpa only [Nat.cast_pow] using hbound
  · intro m n hmn
    dsimp only
    rw [hu.map_mul_of_coprime hmn, Nat.cast_mul, mul_div_mul_comm, abs_mul]

lemma convolution_prime_pow_weighted (u v : ArithmeticFunction ℝ) (p k : ℕ) (hp : p.Prime) :
    (u * v) (p ^ k) / (p : ℝ) ^ k =
      ∑ j ∈ Finset.range (k + 1), (u (p ^ j) / (p : ℝ) ^ j) *
        (v (p ^ (k - j)) / (p : ℝ) ^ (k - j)) := by
  rw [convolution_prime_pow _ _ p k hp, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [div_mul_div_comm, ← pow_add, Nat.add_sub_of_le (by simpa using Finset.mem_range.mp hj)]

lemma idealLocalInverse_weighted_summable (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :
    Summable (fun k : ℕ ↦ ‖idealLocalInverse K p (p ^ k) / (p : ℝ) ^ k‖) := by
  apply summable_of_ne_finset_zero (s := Finset.range (Module.finrank ℚ K + 1))
  intro k hk
  rw [idealLocalInverse_prime_pow_eq_zero K p k (by simpa using hk), zero_div, norm_zero]

lemma idealCorrection_local_summable (K : Type*) [Field K] [NumberField K]
    (u : ArithmeticFunction ℝ) (hu : u.IsMultiplicative) (p : ℕ) [Fact p.Prime]
    (hlocal : Summable (fun k : ℕ ↦ ‖u (p ^ k) / (p : ℝ) ^ k‖)) :
    Summable (fun k : ℕ ↦ ‖idealCorrection K u (p ^ k) / (p : ℝ) ^ k‖) := by
  have hs := summable_norm_sum_mul_range_of_summable_norm
    (idealLocalInverse_weighted_summable K p) hlocal
  apply hs.congr
  intro k
  rw [idealCorrection_prime_pow K u hu p k, convolution_prime_pow_weighted _ _ p k Fact.out]

lemma idealCorrection_local_good_summable (K : Type*) [Field K] [NumberField K]
    (u : ArithmeticFunction ℝ) (hu : u.IsMultiplicative) (p : ℕ) [Fact p.Prime]
    (r : ℝ) (hr : ∀ j : ℕ, u (p ^ (j + 1)) = r) :
    Summable (fun k : ℕ ↦ ‖idealCorrection K u (p ^ k) / (p : ℝ) ^ k‖) := by
  apply summable_of_ne_finset_zero (s := Finset.range (Module.finrank ℚ K + 1))
  intro k hk
  rw [idealCorrection_prime_pow K u hu p k,
    idealLocalCorrection_prime_pow_eq_zero K p u r hr k (by simpa using hk), zero_div, norm_zero]

lemma idealCorrection_local_good_bound (K : Type*) [Field K] [NumberField K]
    (u : ArithmeticFunction ℝ) (hu : u.IsMultiplicative) (p : ℕ) [Fact p.Prime]
    (r B : ℝ) (hB : 0 ≤ B) (hup : u p = idealNormCount K p)
    (hr : ∀ j : ℕ, u (p ^ (j + 1)) = r) (huB : ∀ j : ℕ, |u (p ^ j)| ≤ B) :
    (∑' k : ℕ, ‖idealCorrection K u (p ^ k) / (p : ℝ) ^ k‖) ≤
      1 + (Module.finrank ℚ K : ℝ) * ((2 : ℝ) ^ Module.finrank ℚ K * B) / (p : ℝ) ^ 2 := by
  have hs := idealCorrection_local_good_summable K u hu p r hr
  rw [hs.tsum_eq_zero_add]
  have h1 : idealCorrection K u 1 = 1 := (idealCorrection_multiplicative K u).map_one
  simp only [pow_zero, h1, div_one, norm_one]
  apply add_le_add le_rfl
  rw [tsum_eq_sum (s := Finset.range (Module.finrank ℚ K)) ?_]
  · calc
      _ ≤ ∑ _k ∈ Finset.range (Module.finrank ℚ K),
          ((2 : ℝ) ^ Module.finrank ℚ K * B) / (p : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        rw [idealCorrection_prime_pow K u hu p (k + 1)]
        by_cases hk0 : k = 0
        · subst k
          rw [zero_add, pow_one, idealLocalCorrection_apply_prime K p u hu.map_one hup,
            zero_div, norm_zero]
          positivity
        · have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
          have hden : 0 < (p : ℝ) ^ 2 := by positivity
          have hpows : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ (k + 1) :=
            pow_le_pow_right₀ hpR (by omega)
          have hdenabs : |(p : ℝ) ^ (k + 1)| = (p : ℝ) ^ (k + 1) := abs_of_nonneg (by positivity)
          rw [Real.norm_eq_abs, abs_div, hdenabs]
          calc
            _ ≤ ((2 : ℝ) ^ Module.finrank ℚ K * B) / (p : ℝ) ^ (k + 1) :=
              div_le_div_of_nonneg_right (idealLocalCorrection_abs_le K p u B hB huB (k + 1))
                (by positivity)
            _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hden hpows
      _ = _ := by simp; ring
  · intro k hk
    rw [idealCorrection_prime_pow K u hu p (k + 1),
      idealLocalCorrection_prime_pow_eq_zero K p u r hr (k + 1) (by simpa using hk),
      zero_div, norm_zero]

lemma idealCorrection_summable_of_finite_good_primes (K : Type*) [Field K] [NumberField K]
    (u : ArithmeticFunction ℝ) (hu : u.IsMultiplicative) (s : Finset ℕ)
    (B : ℝ) (hB : 0 ≤ B)
    (hlocal : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ ↦ ‖u (p ^ k) / (p : ℝ) ^ k‖))
    (hgood : ∀ p : ℕ, p.Prime → p ∉ s →
      u p = idealNormCount K p ∧ (∀ j : ℕ, u (p ^ (j + 1)) = u p) ∧
        ∀ j : ℕ, |u (p ^ j)| ≤ B) :
    Summable (fun n : ℕ ↦ ‖idealCorrection K u n / (n : ℝ)‖) := by
  let A : ℝ := (Module.finrank ℚ K : ℝ) * ((2 : ℝ) ^ Module.finrank ℚ K * B)
  let C : ℕ → ℝ := fun n ↦ if n ∈ s then
    ∑' k : ℕ, ‖idealCorrection K u (n ^ k) / (n : ℝ) ^ k‖ else A / (n : ℝ) ^ 2
  have hCpos : ∀ n, 0 ≤ C n := by
    intro n
    dsimp [C, A]
    split_ifs
    · exact tsum_nonneg (fun _ ↦ abs_nonneg _)
    · positivity
  have hbase : Summable (fun n : ℕ ↦ A / (n : ℝ) ^ 2) := by
    simpa only [div_eq_mul_inv] using
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))).mul_left A
  have hC : Summable C := hbase.congr_cofinite ?_
  · apply summable_weighted_multiplicative_of_local_bound (idealCorrection K u)
      (idealCorrection_multiplicative K u) C hC hCpos
    · intro p hp
      haveI : Fact p.Prime := ⟨hp⟩
      simpa only [Real.norm_eq_abs] using idealCorrection_local_summable K u hu p (hlocal p hp)
    · intro p hp
      haveI : Fact p.Prime := ⟨hp⟩
      by_cases hps : p ∈ s
      · simp only [C, if_pos hps, Real.norm_eq_abs]
        linarith
      · obtain ⟨hup, hr, hbound⟩ := hgood p hp hps
        simpa only [C, if_neg hps, A, Real.norm_eq_abs] using
          idealCorrection_local_good_bound K u hu p (u p) B hB hup hr hbound
  · filter_upwards [s.finite_toSet.compl_mem_cofinite] with n hn
    exact (if_neg hn).symm

lemma rootCorrection_summable_of_prime_agreement (f : ℤ[X]) (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) (K : Type*) [Field K] [NumberField K] (s : Finset ℕ)
    (hagree : ∀ p : ℕ, p.Prime → p ∉ s →
      (polynomialRootResidues f p).card = idealNormCount K p)
    (hlocal : ∀ p : ℕ, p.Prime → Summable
      (fun k : ℕ ↦ (polynomialRootResidues f (p ^ k)).card / (p : ℝ) ^ k)) :
    Summable (fun n : ℕ ↦ ‖idealCorrection K (polynomialRootCount f : ArithmeticFunction ℝ) n /
      (n : ℝ)‖) := by
  let D := (f.resultant f.derivative).natAbs
  have hD0 : D ≠ 0 := Int.natAbs_ne_zero.mpr (resultant_derivative_ne_zero_of_irreducible f hdeg hirr)
  apply idealCorrection_summable_of_finite_good_primes K
    (polynomialRootCount f : ArithmeticFunction ℝ) (polynomialRootCount_multiplicative f).natCast
    (s ∪ D.primeFactors) (f.natDegree + 1 : ℝ) (by positivity)
  · intro p hp
    simpa only [ArithmeticFunction.natCoe_apply, polynomialRootCount, ArithmeticFunction.coe_mk]
      using (hlocal p hp).norm
  · intro p hp hps
    haveI : Fact p.Prime := ⟨hp⟩
    have hps' : p ∉ s := fun h ↦ hps (Finset.mem_union_left _ h)
    have hnotdiv : ¬p ∣ D := fun h ↦ hps
      (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hD0⟩))
    have hres : ¬(p : ℤ) ∣ f.resultant f.derivative := by
      intro h
      exact hnotdiv (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr h)
    refine ⟨?_, ?_, ?_⟩
    · change ((polynomialRootResidues f p).card : ℝ) = (idealNormCount K p : ℝ)
      exact_mod_cast hagree p hp hps' 
    · intro j
      change ((polynomialRootResidues f (p ^ (j + 1))).card : ℝ) = (polynomialRootResidues f p).card
      exact_mod_cast rootResidues_prime_pow_of_not_dvd_resultant f hdeg p j hres
    · intro j
      rw [ArithmeticFunction.natCoe_apply, abs_of_nonneg (Nat.cast_nonneg _)]
      cases j with
      | zero => simp [pow_zero, (polynomialRootCount_multiplicative f).map_one]
      | succ j =>
        change ((polynomialRootResidues f (p ^ (j + 1))).card : ℝ) ≤ _
        rw [rootResidues_prime_pow_of_not_dvd_resultant f hdeg p j hres]
        have hb := rootResidues_prime_le_natDegree_of_simple f p
          (simple_roots_of_not_dvd_resultant f hdeg p hres)
        have hbR : ((polynomialRootResidues f p).card : ℝ) ≤ f.natDegree := by exact_mod_cast hb
        linarith

lemma eval_sub_factor_derivative {R : Type*} [CommRing R] (f : R[X]) (x y : R) :
    ∃ q : R, f.eval x - f.eval y = (x-y) * (f.derivative.eval y + (x-y)*q) := by
  obtain ⟨g, hg⟩ := X_sub_C_dvd_sub_C_eval (p := f) (a := y)
  have hder := congrArg (fun F : R[X] ↦ F.derivative.eval y) hg
  simp only [derivative_sub, derivative_C, sub_zero, derivative_mul, derivative_X,
    eval_add, eval_mul, one_mul, eval_sub, eval_X, eval_C, sub_self,
    zero_mul, add_zero] at hder
  obtain ⟨q, hq⟩ := sub_dvd_eval_sub x y g
  refine ⟨q, ?_⟩
  have he := congrArg (fun F : R[X] ↦ F.eval x) hg
  simp only [eval_sub, eval_C, eval_mul, eval_X] at he
  rw [he, hder]
  congr 1
  linear_combination hq

lemma prime_pow_dvd_left_of_bounded_right {R : Type*} [CommRing R] [IsDomain R]
    (p : R) (hp : Prime p) (k e : ℕ) (a b : R)
    (hab : p ^ (k + e) ∣ a * b) (hb : ¬p ^ e ∣ b) : p ^ k ∣ a := by
  induction e generalizing b with
  | zero => exact (hb (by simp)).elim
  | succ e ih =>
    by_cases hd : p ∣ b
    · obtain ⟨c, rfl⟩ := hd
      apply ih c
      · apply (mul_dvd_mul_iff_left hp.ne_zero).mp
        simpa only [Nat.add_succ, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hab
      · intro h
        exact hb (by simpa only [pow_succ, mul_comm] using mul_dvd_mul_left p h)
    · exact (pow_dvd_pow p (by omega : k ≤ k + (e + 1))).trans
        (hp.pow_dvd_of_dvd_mul_right _ hd hab)

lemma root_derivative_not_dvd (f : ℤ[X]) (hdeg : f.natDegree ≠ 0)
    (m : ℤ) (hm : ¬m ∣ f.resultant f.derivative) (x : ℤ) (hx : m ∣ f.eval x) :
    ¬m ∣ f.derivative.eval x := by
  obtain ⟨a, b, _, _, hab⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f f.derivative le_rfl le_rfl (Or.inl hdeg)
  intro hd
  apply hm
  have he := congrArg (fun g : ℤ[X] ↦ g.eval x) hab
  simp only [eval_add, eval_mul, eval_C] at he
  rw [← he]
  exact dvd_add (dvd_mul_of_dvd_left hx _) (dvd_mul_of_dvd_left hd _)

lemma root_difference_dvd_of_congruent (f : ℤ[X]) (hdeg : f.natDegree ≠ 0)
    (p : ℕ) (hp : p.Prime) (e k : ℕ) (hek : e ≤ k)
    (hres : ¬(p : ℤ) ^ e ∣ f.resultant f.derivative)
    (x y : ℤ) (hx : (p : ℤ) ^ k ∣ f.eval x) (hy : (p : ℤ) ^ k ∣ f.eval y)
    (hxy : (p : ℤ) ^ e ∣ x - y) : (p : ℤ) ^ (k-e) ∣ x - y := by
  have hd := root_derivative_not_dvd f hdeg ((p : ℤ) ^ e) hres y
    ((pow_dvd_pow (p : ℤ) hek).trans hy)
  obtain ⟨q, hq⟩ := eval_sub_factor_derivative f x y
  apply prime_pow_dvd_left_of_bounded_right (p : ℤ) (Nat.prime_iff_prime_int.mp hp)
    (k-e) e (x-y) (f.derivative.eval y + (x-y)*q)
  · rw [Nat.sub_add_cancel hek, ← hq]
    exact dvd_sub hx hy
  · intro h
    apply hd
    exact (dvd_add_left (dvd_mul_of_dvd_left hxy q)).mp h

lemma rootResidues_prime_pow_card_bound (f : ℤ[X]) (hdeg : f.natDegree ≠ 0)
    (p : ℕ) (hp : p.Prime) (e : ℕ)
    (hres : ¬(p : ℤ) ^ e ∣ f.resultant f.derivative) (k : ℕ) :
    (polynomialRootResidues f (p ^ k)).card ≤ p ^ (2*e) := by
  by_cases hek : e ≤ k
  · let φ : ℕ → ℕ × ℕ := fun x ↦ (x % p^e, x / p^(k-e))
    have hcard := Finset.card_le_card_of_injOn φ
      (s := polynomialRootResidues f (p^k))
      (t := (Finset.range (p^e)) ×ˢ (Finset.range (p^e)))
    have heq : p^e * p^(k-e) = p^k := by rw [← pow_add, Nat.add_sub_of_le hek]
    have hmaps : Set.MapsTo φ (polynomialRootResidues f (p^k))
        (↑((Finset.range (p^e)) ×ˢ (Finset.range (p^e))) : Set (ℕ × ℕ)) := by
      intro x hx
      obtain ⟨hx, _⟩ := (Finset.mem_filter.mp (show x ∈ (Finset.range (p^k)).filter _ from hx))
      change (x % p^e, x / p^(k-e)) ∈ (Finset.range (p^e)) ×ˢ (Finset.range (p^e))
      simp only [Finset.mem_product, Finset.mem_range]
      refine ⟨Nat.mod_lt _ (pow_pos hp.pos _), ?_⟩
      apply (Nat.div_lt_iff_lt_mul (pow_pos hp.pos _)).mpr
      rw [heq]
      exact Finset.mem_range.mp hx
    have hinj : (↑(polynomialRootResidues f (p^k)) : Set ℕ).InjOn φ := by
      intro x hx y hy hxy
      obtain ⟨hxlt, hx⟩ := (Finset.mem_filter.mp (show x ∈ (Finset.range (p^k)).filter _ from hx))
      obtain ⟨hylt, hy⟩ := (Finset.mem_filter.mp (show y ∈ (Finset.range (p^k)).filter _ from hy))
      have hlo : x % p^e = y % p^e := congrArg Prod.fst hxy
      have hhi : x / p^(k-e) = y / p^(k-e) := congrArg Prod.snd hxy
      have hd : (p : ℤ)^(k-e) ∣ (x : ℤ) - y :=
        root_difference_dvd_of_congruent f hdeg p hp e k hek hres x y
          (by simpa only [Nat.cast_pow] using hx)
          (by simpa only [Nat.cast_pow] using hy)
          (by simpa only [Nat.cast_pow] using (Nat.modEq_iff_dvd.mp hlo.symm))
      have hemod : y % p^(k-e) = x % p^(k-e) :=
        Nat.modEq_iff_dvd.mpr (by simpa only [Nat.cast_pow] using hd)
      have hxdiv := Nat.mod_add_div x (p^(k-e))
      have hydiv := Nat.mod_add_div y (p^(k-e))
      rw [← hhi, hemod] at hydiv
      omega
    simpa only [Finset.card_product, Finset.card_range, ← pow_add,
      ← two_mul] using hcard hmaps hinj
  · have hsub : polynomialRootResidues f (p^k) ⊆ Finset.range (p^k) :=
      Finset.filter_subset _ _
    exact (Finset.card_le_card hsub).trans (by
      rw [Finset.card_range]
      exact Nat.pow_le_pow_right hp.pos (by omega))

lemma exists_bound_prime_pow_rootResidues_of_resultant_ne_zero (f : ℤ[X])
    (hdeg : f.natDegree ≠ 0) (hres : f.resultant f.derivative ≠ 0)
    (p : ℕ) (hp : p.Prime) :
    ∃ B : ℕ, ∀ k : ℕ, (polynomialRootResidues f (p^k)).card ≤ B := by
  let e := (f.resultant f.derivative).natAbs
  have he : ¬(p : ℤ)^e ∣ f.resultant f.derivative := by
    intro h
    have hd : p^e ∣ e := by
      simpa only [Int.natAbs_pow, Int.natAbs_natCast, e] using Int.natAbs_dvd_natAbs.mpr h
    exact (Nat.lt_pow_self hp.one_lt).not_ge
      (Nat.le_of_dvd (Int.natAbs_pos.mpr hres) hd)
  exact ⟨p^(2*e), rootResidues_prime_pow_card_bound f hdeg p hp e he⟩

lemma rootResidues_prime_pow_weighted_summable_of_resultant_ne_zero (f : ℤ[X])
    (hdeg : f.natDegree ≠ 0) (hres : f.resultant f.derivative ≠ 0)
    (p : ℕ) (hp : p.Prime) :
    Summable (fun k : ℕ ↦ (polynomialRootResidues f (p^k)).card / (p:ℝ)^k) := by
  obtain ⟨B, hB⟩ := exists_bound_prime_pow_rootResidues_of_resultant_ne_zero f hdeg hres p hp
  have hgeom : Summable (fun k : ℕ ↦ (B:ℝ) / (p:ℝ)^k) := by
    simp_rw [div_eq_mul_inv, ← inv_pow]
    exact (summable_geometric_of_lt_one (r := (p:ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt))).mul_left (B:ℝ)
  apply Summable.of_nonneg_of_le (fun _ ↦ by positivity) _ hgeom
  intro k
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hB k

lemma rootResidues_prime_pow_weighted_summable (f : ℤ[X]) (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) (p : ℕ) (hp : p.Prime) :
    Summable (fun k : ℕ ↦ (polynomialRootResidues f (p^k)).card / (p:ℝ)^k) :=
  rootResidues_prime_pow_weighted_summable_of_resultant_ne_zero f hdeg
    (resultant_derivative_ne_zero_of_irreducible f hdeg hirr) p hp

lemma rootCorrection_summable (f : ℤ[X]) (hdeg : f.natDegree ≠ 0)
    (hirr : Irreducible f) (K : Type*) [Field K] [NumberField K] (s : Finset ℕ)
    (hagree : ∀ p : ℕ, p.Prime → p ∉ s →
      (polynomialRootResidues f p).card = idealNormCount K p) :
    Summable (fun n : ℕ ↦ ‖idealCorrection K (polynomialRootCount f : ArithmeticFunction ℝ) n /
      (n : ℝ)‖) :=
  rootCorrection_summable_of_prime_agreement f hdeg hirr K s hagree
    (rootResidues_prime_pow_weighted_summable f hdeg hirr)

lemma weighted_atom_prime_pow (p : ℕ) (hp : p.Prime) (e k : ℕ) :
    dirichletAtom (p^e) (p^k) / (p:ℝ)^k =
      if k = e then ((p:ℝ)^e)⁻¹ else 0 := by
  have hpow : p^k = p^e ↔ k = e := (Nat.pow_right_injective hp.two_le).eq_iff
  by_cases hk : k = e
  · simp [dirichletAtom, hk, hp.ne_zero, div_eq_mul_inv]
  · simp [dirichletAtom, hpow, hk]

lemma idealLocalInverse_weighted_tsum (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :
    (∑' k : ℕ, idealLocalInverse K p (p^k) / (p:ℝ)^k) =
      ∏ P ∈ rationalPrimeIdeals K p, (1 - (Ideal.absNorm P : ℝ)⁻¹) := by
  classical
  let e := fun P : Ideal (𝓞 K) ↦ (Ideal.span {(p:ℤ)}).inertiaDeg P
  have hs : ∀ t ∈ (rationalPrimeIdeals K p).powerset,
      Summable (fun k : ℕ ↦ (-1:ℝ)^t.card * dirichletAtom (p^(∑ P ∈ t, e P)) (p^k) /
        (p:ℝ)^k) := by
    intro t ht
    simp_rw [mul_div_assoc, weighted_atom_prime_pow p Fact.out]
    exact (hasSum_ite_eq (∑ P ∈ t, e P) ((p:ℝ)^(∑ P ∈ t, e P))⁻¹).summable.mul_left _
  simp_rw [idealLocalInverse_powerset, Finset.sum_div]
  rw [Summable.tsum_finsetSum hs]
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Finset.prod_const_one, mul_one]
  have he : (∏ P ∈ t, (Ideal.absNorm P : ℝ)⁻¹) = ((p:ℝ)^(∑ P ∈ t, e P))⁻¹ := by
    rw [Finset.prod_inv_distrib]
    congr 1
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro P hP
    exact_mod_cast norm_of_mem_rationalPrimeIdeals K p P ((Finset.mem_powerset.mp ht) hP)
  rw [he]
  simp_rw [mul_div_assoc, weighted_atom_prime_pow p Fact.out]
  rw [tsum_mul_left, tsum_ite_eq]

lemma idealLocalInverse_weighted_tsum_pos (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :
    0 < ∑' k : ℕ, idealLocalInverse K p (p^k) / (p:ℝ)^k := by
  rw [idealLocalInverse_weighted_tsum]
  apply Finset.prod_pos
  intro P hP
  apply sub_pos.mpr
  apply inv_lt_one_of_one_lt₀
  rw [norm_of_mem_rationalPrimeIdeals K p P hP, Nat.cast_pow]
  exact one_lt_pow₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    (rationalPrimeIdeals_inertia_pos K p P hP).ne'

lemma convolution_prime_pow_weighted_tsum (u v : ArithmeticFunction ℝ)
    (p : ℕ) (hp : p.Prime)
    (hu : Summable (fun k : ℕ ↦ ‖u (p^k) / (p:ℝ)^k‖))
    (hv : Summable (fun k : ℕ ↦ ‖v (p^k) / (p:ℝ)^k‖)) :
    (∑' k : ℕ, (u*v) (p^k) / (p:ℝ)^k) =
      (∑' k : ℕ, u (p^k) / (p:ℝ)^k) * (∑' k : ℕ, v (p^k) / (p:ℝ)^k) := by
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hu hv]
  apply tsum_congr
  intro k
  exact convolution_prime_pow_weighted u v p k hp

lemma idealCorrection_local_tsum_pos (K : Type*) [Field K] [NumberField K]
    (u : ArithmeticFunction ℝ) (hu : u.IsMultiplicative) (hu0 : ∀ n, 0 ≤ u n)
    (p : ℕ) [Fact p.Prime]
    (hs : Summable (fun k : ℕ ↦ ‖u (p^k) / (p:ℝ)^k‖)) :
    0 < ∑' k : ℕ, idealCorrection K u (p^k) / (p:ℝ)^k := by
  simp_rw [idealCorrection_prime_pow K u hu p]
  rw [convolution_prime_pow_weighted_tsum _ _ p Fact.out
    (idealLocalInverse_weighted_summable K p) hs]
  apply mul_pos (idealLocalInverse_weighted_tsum_pos K p)
  have h1 := hs.of_norm.le_tsum 0 (fun k _ ↦ div_nonneg (hu0 _) (by positivity))
  simp only [pow_zero, hu.map_one, div_one] at h1
  exact zero_lt_one.trans_le h1

lemma prime_power_pair_injective :
    Function.Injective (fun z : Nat.Primes × ℕ ↦ (z.1 : ℕ) ^ (z.2 + 1)) := by
  intro x y h
  obtain ⟨hp, hk⟩ := x.1.property.pow_inj y.1.property h
  exact Prod.ext (Subtype.ext hp) hk

lemma tsum_pos_of_multiplicative_local_pos (f : ℕ → ℝ)
    (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hmul : ∀ {m n}, m.Coprime n → f (m*n) = f m * f n)
    (hs : Summable (fun n ↦ ‖f n‖))
    (hlocal : ∀ p : Nat.Primes, 0 < ∑' k : ℕ, f ((p:ℕ)^k)) :
    0 < ∑' n : ℕ, f n := by
  let F : Nat.Primes → ℝ := fun p ↦ ∑' k : ℕ, f ((p:ℕ)^k)
  let C : Nat.Primes → ℝ := fun p ↦ ∑' k : ℕ, f ((p:ℕ)^(k+1))
  have hprime : Summable (fun z : Nat.Primes × ℕ ↦ ‖f ((z.1:ℕ)^(z.2+1))‖) :=
    hs.comp_injective prime_power_pair_injective
  have hC : Summable (fun p ↦ ‖C p‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun p ↦
      norm_tsum_le_tsum_norm (hprime.prod_factor p)) hprime.prod
  have hFC : F = fun p ↦ 1 + C p := by
    funext p
    have hsp := hs.comp_injective (Nat.pow_right_injective p.property.two_le)
    have he := hsp.of_norm.tsum_eq_zero_add
    simpa only [pow_zero, hf1, F, C] using he
  have hnz : (∏' p : Nat.Primes, F p) ≠ 0 := by
    rw [hFC]
    apply tprod_one_add_ne_zero_of_summable _ hC
    intro p
    rw [← congrFun hFC p]
    exact (hlocal p).ne'
  have he := EulerProduct.eulerProduct_hasProd hf1 hmul hs hf0
  have hnonneg : 0 ≤ ∑' n : ℕ, f n := by
    apply ge_of_tendsto he
    exact Filter.Eventually.of_forall (fun s : Finset Nat.Primes ↦
      Finset.prod_nonneg (fun p _ ↦ (hlocal p).le))
  exact lt_of_le_of_ne hnonneg (by rw [← he.tprod_eq]; exact hnz.symm)

lemma idealCorrection_tsum_pos (K : Type*) [Field K] [NumberField K]
    (u : ArithmeticFunction ℝ) (hu : u.IsMultiplicative) (hu0 : ∀ n, 0 ≤ u n)
    (hlocal : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ ↦ ‖u (p^k) / (p:ℝ)^k‖))
    (hs : Summable (fun n : ℕ ↦ ‖idealCorrection K u n / (n:ℝ)‖)) :
    0 < ∑' n : ℕ, idealCorrection K u n / (n:ℝ) := by
  refine tsum_pos_of_multiplicative_local_pos
    (fun n ↦ idealCorrection K u n / (n:ℝ)) (by simp)
    (by simp [(idealCorrection_multiplicative K u).map_one]) ?_ hs ?_
  · intro m n hmn
    dsimp only
    rw [(idealCorrection_multiplicative K u).map_mul_of_coprime hmn, Nat.cast_mul,
      div_mul_div_comm]
  · intro p
    haveI : Fact (p:ℕ).Prime := ⟨p.property⟩
    simpa only [Nat.cast_pow] using idealCorrection_local_tsum_pos K u hu hu0 p
      (hlocal p p.property)

lemma root_harmonic_positive_limit_of_prime_agreement (f : ℤ[X])
    (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f)
    (K : Type*) [Field K] [NumberField K] (s : Finset ℕ)
    (hagree : ∀ p : ℕ, p.Prime → p ∉ s →
      (polynomialRootResidues f p).card = idealNormCount K p) :
    ∃ c > (0:ℝ), Tendsto
      (fun N : ℕ ↦ harmonicWeightSum (fun d ↦ (polynomialRootResidues f d).card) N / log N)
      atTop (𝓝 c) := by
  have hs := rootCorrection_summable f hdeg hirr K s hagree
  refine ⟨_, mul_pos ?_ (NumberField.dedekindZeta_residue_pos K),
    root_harmonic_limit_of_idealCorrection_summable f K hs⟩
  apply idealCorrection_tsum_pos K _ (polynomialRootCount_multiplicative f).natCast
    (fun _ ↦ Nat.cast_nonneg _) _ hs
  intro p hp
  simpa only [ArithmeticFunction.natCoe_apply, polynomialRootCount, ArithmeticFunction.coe_mk]
    using (rootResidues_prime_pow_weighted_summable f hdeg hirr p hp).norm

lemma ringOfIntegers_exponent_ne_zero (K : Type*) [Field K] [NumberField K]
    (θ : 𝓞 K) (htop : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    RingOfIntegers.exponent θ ≠ 0 := by
  let B := PowerBasis.ofAdjoinEqTop θ.isIntegral_coe.tower_top htop
  have hB : B.gen = (θ : K) := rfl
  have hdiscint : IsIntegral ℤ (Algebra.discr ℚ B.basis) :=
    Algebra.discr_isIntegral ℚ (fun i ↦ by
      rw [B.basis_eq_pow i, hB]
      exact θ.isIntegral_coe.pow _)
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdiscint
  have hd0 : d ≠ 0 := by
    intro hz
    exact Algebra.discr_not_zero_of_basis ℚ B.basis (by simpa [hz] using hd.symm)
  have hcond : (d : 𝓞 K) ∈ conductor ℤ θ := by
    rw [mem_conductor_iff]
    intro z
    have hz := Algebra.discr_mul_isIntegral_mem_adjoin ℚ
      (show IsIntegral ℤ B.gen from θ.isIntegral_coe) z.isIntegral_coe
    rw [hB, ← hd, algebraMap_smul, Algebra.smul_def] at hz
    have himage : Algebra.adjoin ℤ {(θ : K)} =
        (Algebra.adjoin ℤ {θ}).map (IsScalarTower.toAlgHom ℤ (𝓞 K) K) := by
      rw [AlgHom.map_adjoin, Set.image_singleton]
      rfl
    rw [himage] at hz
    obtain ⟨y, hy, he⟩ := hz
    have hyz : y = (d : 𝓞 K) * z := by
      apply NumberField.RingOfIntegers.ext
      simpa using he
    rwa [hyz] at hy
  intro hz
  have hbot : Ideal.under ℤ (conductor ℤ θ) = ⊥ := Ideal.absNorm_eq_zero_iff.mp hz
  have hdmem : d ∈ Ideal.under ℤ (conductor ℤ θ) := hcond
  rw [hbot, Ideal.mem_bot] at hdmem
  exact hd0 hdmem

lemma integralNormalization_minpoly_of_primitive_root (f : ℤ[X])
    (hdeg : f.natDegree ≠ 0) (K : Type*) [Field K] [NumberField K]
    (α : K) (hroot : f.aeval α = 0) (htop : Algebra.adjoin ℚ {α} = ⊤)
    (hdim : Module.finrank ℚ K = f.natDegree) :
    ∃ θ : 𝓞 K, minpoly ℤ θ = f.integralNormalization ∧
      Algebra.adjoin ℚ {(θ : K)} = ⊤ := by
  have hf : f ≠ 0 := by intro h; simp [h] at hdeg
  have hlc : (f.leadingCoeff : K) ≠ 0 := by
    exact_mod_cast leadingCoeff_ne_zero.mpr hf
  let z : K := (f.leadingCoeff : K) * α
  have hz : f.integralNormalization.aeval z = 0 := by
    exact integralNormalization_aeval_eq_zero hroot (fun x hx ↦ (FaithfulSMul.algebraMap_injective ℤ K) (hx.trans (map_zero _).symm))
  have hint : IsIntegral ℤ z := ⟨f.integralNormalization, monic_integralNormalization hf, hz⟩
  let θ : 𝓞 K := ⟨z, hint⟩
  have hztop : Algebra.adjoin ℚ {z} = ⊤ := by
    apply top_unique
    rw [← htop]
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    have hzmem : z ∈ Algebra.adjoin ℚ {z} := Algebra.subset_adjoin (Set.mem_singleton _)
    have hm := (Algebra.adjoin ℚ {z}).smul_mem hzmem ((f.leadingCoeff : ℚ)⁻¹)
    simpa only [Algebra.smul_def, map_inv₀, map_intCast, z, inv_mul_cancel_left₀ hlc] using hm
  let B := PowerBasis.ofAdjoinEqTop hint.tower_top hztop
  have hmin_deg : (minpoly ℤ θ).natDegree = f.natDegree := by
    have he := minpoly.isIntegrallyClosed_eq_field_fractions ℚ K θ.isIntegral
    have hd := congrArg Polynomial.natDegree he
    rw [(minpoly.monic θ.isIntegral).natDegree_map] at hd
    rw [← hd]
    change (minpoly ℚ B.gen).natDegree = _
    rw [B.natDegree_minpoly, ← B.finrank, hdim]
  refine ⟨θ, ?_, hztop⟩
  apply (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic θ.isIntegral)
    (monic_integralNormalization hf) ?_ ?_).symm
  · apply minpoly.isIntegrallyClosed_dvd θ.isIntegral
    apply (FaithfulSMul.algebraMap_injective (𝓞 K) K)
    rw [map_zero, ← aeval_algebraMap_apply]
    exact hz
  · simp only [natDegree_integralNormalization, hmin_deg, le_refl]

lemma rootResidues_integralNormalization_prime (f : ℤ[X]) (hdeg : f.natDegree ≠ 0)
    (p : ℕ) [Fact p.Prime] (hp : ¬(p:ℤ) ∣ f.leadingCoeff) :
    (polynomialRootResidues f p).card =
      (polynomialRootResidues f.integralNormalization p).card := by
  have ha : (f.leadingCoeff : ZMod p) ≠ 0 :=
    fun h ↦ hp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  let e : ModularRoot f p ≃ ModularRoot f.integralNormalization p :=
    Equiv.subtypeEquiv (Equiv.mulLeft₀ (f.leadingCoeff : ZMod p) ha) (fun x ↦ by
      change f.eval₂ (Int.castRingHom (ZMod p)) x = 0 ↔
        f.integralNormalization.eval₂ (Int.castRingHom (ZMod p))
          ((f.leadingCoeff : ZMod p) * x) = 0
      have he := integralNormalization_eval₂_leadingCoeff_mul (p := f) (by omega)
        (Int.castRingHom (ZMod p)) x
      simp only [Int.coe_castRingHom] at he
      rw [he]
      simp only [mul_eq_zero, pow_ne_zero _ ha, false_or])
  rw [rootResidues_card_eq_modularRoot, rootResidues_card_eq_modularRoot]
  exact Nat.card_congr e

lemma exists_numberField_prime_root_agreement (f : ℤ[X])
    (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (s : Finset ℕ),
      ∀ p : ℕ, p.Prime → p ∉ s →
        (polynomialRootResidues f p).card = idealNormCount K p := by
  classical
  let F : ℚ[X] := f.map (Int.castRingHom ℚ)
  have hirrQ : Irreducible F :=
    ((hirr.isPrimitive hdeg).irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hirr
  letI : Fact (Irreducible F) := ⟨hirrQ⟩
  let K := AdjoinRoot F
  let α : K := AdjoinRoot.root F
  have hroot : f.aeval α = 0 := by
    rw [← aeval_map_algebraMap ℚ]
    exact (AdjoinRoot.aeval_eq F).trans AdjoinRoot.mk_self
  have htop : Algebra.adjoin ℚ {α} = ⊤ := AdjoinRoot.adjoinRoot_eq_top
  have hdim : Module.finrank ℚ K = f.natDegree := by
    rw [(AdjoinRoot.powerBasis hirrQ.ne_zero).finrank]
    exact natDegree_map_eq_of_injective Int.cast_injective f
  obtain ⟨θ, hmin, hθ⟩ :=
    integralNormalization_minpoly_of_primitive_root f hdeg K α hroot htop hdim
  have hexp := ringOfIntegers_exponent_ne_zero K θ hθ
  have hlc : f.leadingCoeff.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (leadingCoeff_ne_zero.mpr hirr.ne_zero)
  refine ⟨K, inferInstance, inferInstance,
    f.leadingCoeff.natAbs.primeFactors ∪ (RingOfIntegers.exponent θ).primeFactors, ?_⟩
  intro p hp hps
  haveI : Fact p.Prime := ⟨hp⟩
  have hplc : ¬(p:ℤ) ∣ f.leadingCoeff := by
    intro h
    apply hps
    apply Finset.mem_union_left
    apply Nat.mem_primeFactors.mpr
    exact ⟨hp, by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr h, hlc⟩
  have hpexp : ¬p ∣ RingOfIntegers.exponent θ := by
    intro h
    exact hps (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hexp⟩))
  rw [rootResidues_integralNormalization_prime f hdeg p hplc, ← hmin,
    rootResidues_minpoly_prime_eq_ideal_count K θ p hpexp, idealNormCount_apply K p hp.ne_zero]

lemma polynomialRootCount_positive_harmonic_limit (f : ℤ[X])
    (hdeg : f.natDegree ≠ 0) (hirr : Irreducible f) :
    ∃ c > (0:ℝ), Tendsto
      (fun N : ℕ ↦ harmonicWeightSum (fun d ↦ (polynomialRootResidues f d).card) N / log N)
      atTop (𝓝 c) := by
  obtain ⟨K, hK, hNF, s, hagree⟩ := exists_numberField_prime_root_agreement f hdeg hirr
  letI := hK
  letI := hNF
  exact root_harmonic_positive_limit_of_prime_agreement f hdeg hirr K s hagree

lemma erdos975_degree_two (f : ℤ[X]) (hdeg : f.natDegree = 2) (hirr : Irreducible f)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    ∃ c > (0:ℝ), Tendsto (fun x ↦ Erdos975Sum f x / (x * log x)) atTop (𝓝 c) := by
  obtain ⟨κ, hκ, hH⟩ := polynomialRootCount_positive_harmonic_limit f (by omega) hirr
  exact ⟨2 * κ, mul_pos (by norm_num) hκ, erdos975_degree_two_of_harmonic f hdeg hpos κ hH⟩

lemma erdos975_degree_le_two (f : ℤ[X]) (hdeg : f.natDegree ≠ 0)
    (hle : f.natDegree ≤ 2) (hirr : Irreducible f)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    ∃ c > (0:ℝ), Tendsto (fun x ↦ Erdos975Sum f x / (x * log x)) atTop (𝓝 c) := by
  by_cases h1 : f.natDegree = 1
  · exact erdos975_degree_one f h1 hirr hpos
  · exact erdos975_degree_two f (by omega) hirr hpos

lemma erdos975_degree_gt_two_iff_balanced_converges (f : ℤ[X]) (hdeg : 2 < f.natDegree)
    (hirr : Irreducible f) (hpos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    (∃ c > (0:ℝ), Tendsto (fun x ↦ Erdos975Sum f x / (x * log x)) atTop (𝓝 c)) ↔
    (∃ β : ℝ, Tendsto
      (fun N : ℕ ↦ Erdos975BalancedDivisorSum f N / ((N:ℝ) * log N)) atTop (𝓝 β)) := by
  obtain ⟨κ, hκ, hH⟩ := polynomialRootCount_positive_harmonic_limit f (by omega) hirr
  constructor
  · rintro ⟨c, _, hc⟩
    exact ⟨c/2-κ, (erdos975_degree_gt_two_iff_balanced f hdeg hpos κ c hH).mp hc⟩
  · exact erdos975_degree_gt_two_of_balanced_limit f hdeg hpos κ hκ hH


/- Conjecture. -/

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
  by_cases hle : f.natDegree ≤ 2
  · exact erdos975_degree_le_two f hdeg hle hirr hpos
  · apply (erdos975_degree_gt_two_iff_balanced_converges f (by omega) hirr hpos).mpr
    sorry

end Erdos975
