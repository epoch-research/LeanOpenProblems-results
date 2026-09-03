import FormalConjecturesUtil

/-!
Finite Fourier estimates for the analytic route to Erdős 972.
These estimates concern exponential sums, not simultaneous primality.
-/
namespace Erdos972ExponentialSum

open Finset Complex
open scoped ComplexConjugate

lemma character_orthogonality (q : ℕ) [NeZero q] (t : ZMod q) :
    (∑ m : ZMod q, ZMod.stdAddChar (t * m)) =
      if t = 0 then (q : ℂ) else 0 := by
  classical
  split_ifs with h
  · simp [h, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q h)

lemma conjugate_character {q : ℕ} [NeZero q] (t : ZMod q) :
    conj (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  rw [ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj,
    ← AddChar.map_neg_eq_inv]
  rfl

noncomputable def finiteFourier {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (m : ZMod q) : ℂ :=
  ∑ n : ZMod q, f n * ZMod.stdAddChar (m * n)

/-- Parseval's identity, with the unnormalized finite Fourier transform. -/
theorem finiteFourier_energy {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ m : ZMod q, ‖finiteFourier f m‖ ^ 2) =
      (q : ℝ) * ∑ n : ZMod q, ‖f n‖ ^ 2 := by
  classical
  have hc :
      (∑ m : ZMod q, finiteFourier f m * conj (finiteFourier f m)) =
        (q : ℂ) * ∑ n : ZMod q, f n * conj (f n) := by
    calc
      _ = ∑ m : ZMod q, ∑ n : ZMod q, ∑ k : ZMod q,
          (f n * conj (f k)) * ZMod.stdAddChar ((n - k) * m) := by
        apply sum_congr rfl
        intro m _
        simp only [finiteFourier, map_sum, map_mul, sum_mul, mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro n _
        apply sum_congr rfl
        intro k _
        rw [conjugate_character]
        have he : (n - k) * m = m * n + -(m * k) := by ring
        rw [he, AddChar.map_add_eq_mul]
        ring
      _ = ∑ n : ZMod q, ∑ k : ZMod q,
          (f n * conj (f k)) * ∑ m : ZMod q,
            ZMod.stdAddChar ((n - k) * m) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro n _
        rw [sum_comm]
        apply sum_congr rfl
        intro k _
        rw [mul_sum]
      _ = _ := by
        simp only [character_orthogonality, sub_eq_zero, mul_ite, mul_zero]
        simp [← mul_sum, mul_comm]
  apply Complex.ofReal_injective
  push_cast
  simpa only [← Complex.mul_conj'] using hc

/-- The finite Fourier kernel has squared operator norm `q`. -/
theorem rational_bilinear_bound {q : ℕ} [NeZero q]
    (a b : ZMod q → ℂ) :
    ‖∑ m : ZMod q, ∑ n : ZMod q,
        a m * b n * ZMod.stdAddChar (m * n)‖ ^ 2 ≤
      (q : ℝ) * (∑ m : ZMod q, ‖a m‖ ^ 2) *
        ∑ n : ZMod q, ‖b n‖ ^ 2 := by
  have he : (∑ m : ZMod q, ∑ n : ZMod q,
      a m * b n * ZMod.stdAddChar (m * n)) =
        ∑ m : ZMod q, a m * finiteFourier b m := by
    simp only [finiteFourier, mul_sum, mul_assoc]
  rw [he]
  have ht : ‖∑ m : ZMod q, a m * finiteFourier b m‖ ≤
      ∑ m : ZMod q, ‖a m‖ * ‖finiteFourier b m‖ := by
    simpa only [norm_mul] using norm_sum_le (univ : Finset (ZMod q))
      (fun m => a m * finiteFourier b m)
  calc
    _ ≤ (∑ m : ZMod q, ‖a m‖ * ‖finiteFourier b m‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ht 2
    _ ≤ (∑ m : ZMod q, ‖a m‖ ^ 2) *
        ∑ m : ZMod q, ‖finiteFourier b m‖ ^ 2 :=
      sum_mul_sq_le_sq_mul_sq univ _ _
    _ = _ := by rw [finiteFourier_energy]; ring

/-- Multiplication of the frequency by a unit preserves the Fourier energy. -/
theorem finiteFourier_energy_unit {q : ℕ} [NeZero q]
    (u : (ZMod q)ˣ) (f : ZMod q → ℂ) :
    (∑ m : ZMod q, ‖finiteFourier f ((u : ZMod q) * m)‖ ^ 2) =
      (q : ℝ) * ∑ n : ZMod q, ‖f n‖ ^ 2 := by
  rw [show (∑ m : ZMod q, ‖finiteFourier f ((u : ZMod q) * m)‖ ^ 2) =
      ∑ m : ZMod q, ‖finiteFourier f m‖ ^ 2 from
        Equiv.sum_comp u.mulLeft (fun m => ‖finiteFourier f m‖ ^ 2)]
  exact finiteFourier_energy f

/-- The same bilinear bound with any unit numerator. -/
theorem rational_bilinear_bound_unit {q : ℕ} [NeZero q]
    (u : (ZMod q)ˣ) (a b : ZMod q → ℂ) :
    ‖∑ m : ZMod q, ∑ n : ZMod q,
        a m * b n * ZMod.stdAddChar ((u : ZMod q) * m * n)‖ ^ 2 ≤
      (q : ℝ) * (∑ m : ZMod q, ‖a m‖ ^ 2) *
        ∑ n : ZMod q, ‖b n‖ ^ 2 := by
  have he : (∑ m : ZMod q, ∑ n : ZMod q,
      a m * b n * ZMod.stdAddChar ((u : ZMod q) * m * n)) =
        ∑ m : ZMod q, a m * finiteFourier b ((u : ZMod q) * m) := by
    simp only [finiteFourier, mul_sum, mul_assoc]
  rw [he]
  have ht : ‖∑ m : ZMod q, a m * finiteFourier b ((u : ZMod q) * m)‖ ≤
      ∑ m : ZMod q, ‖a m‖ * ‖finiteFourier b ((u : ZMod q) * m)‖ := by
    simpa only [norm_mul] using norm_sum_le (univ : Finset (ZMod q))
      (fun m => a m * finiteFourier b ((u : ZMod q) * m))
  calc
    _ ≤ (∑ m : ZMod q, ‖a m‖ * ‖finiteFourier b ((u : ZMod q) * m)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ht 2
    _ ≤ (∑ m : ZMod q, ‖a m‖ ^ 2) *
        ∑ m : ZMod q, ‖finiteFourier b ((u : ZMod q) * m)‖ ^ 2 :=
      sum_mul_sq_le_sq_mul_sq univ _ _
    _ = _ := by rw [finiteFourier_energy_unit]; ring

/-- Truncated rational bilinear sums with coefficients bounded by one. -/
theorem rational_bilinear_bound_finset {q : ℕ} [NeZero q]
    (u : (ZMod q)ˣ) (s t : Finset (ZMod q)) (a b : ZMod q → ℂ)
    (ha : ∀ m ∈ s, ‖a m‖ ≤ 1) (hb : ∀ n ∈ t, ‖b n‖ ≤ 1) :
    ‖∑ m ∈ s, ∑ n ∈ t,
        a m * b n * ZMod.stdAddChar ((u : ZMod q) * m * n)‖ ^ 2 ≤
      (q : ℝ) * s.card * t.card := by
  classical
  let a₀ : ZMod q → ℂ := fun m => if m ∈ s then a m else 0
  let b₀ : ZMod q → ℂ := fun n => if n ∈ t then b n else 0
  have h := rational_bilinear_bound_unit u a₀ b₀
  simp only [a₀, b₀, ite_mul, mul_ite, zero_mul, mul_zero,
    sum_ite_irrel, sum_const_zero, sum_ite_mem, apply_ite norm, norm_zero,
    ite_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), univ_inter] at h
  have haE : (∑ m ∈ s, ‖a m‖ ^ 2) ≤ (s.card : ℝ) := by
    calc
      _ ≤ ∑ _m ∈ s, (1 : ℝ) := by
        apply sum_le_sum
        intro m hm
        exact (pow_le_pow_left₀ (norm_nonneg _) (ha m hm) 2).trans_eq (by norm_num)
      _ = _ := by simp
  have hbE : (∑ n ∈ t, ‖b n‖ ^ 2) ≤ (t.card : ℝ) := by
    calc
      _ ≤ ∑ _n ∈ t, (1 : ℝ) := by
        apply sum_le_sum
        intro n hn
        exact (pow_le_pow_left₀ (norm_nonneg _) (hb n hn) 2).trans_eq (by norm_num)
      _ = _ := by simp
  apply h.trans
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left haE (Nat.cast_nonneg q)) hbE
    (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)

/-- A separable exponential perturbation costs at most `exp ‖z‖`.
Expanding the exponential into powers keeps the two coefficient sequences
separate, so the finite Fourier bound applies to every term. -/
theorem perturbed_rational_bilinear_bound {q : ℕ} [NeZero q]
    (u : (ZMod q)ˣ) (s t : Finset (ZMod q))
    (a b x y : ZMod q → ℂ) (z : ℂ)
    (ha : ∀ m ∈ s, ‖a m‖ ≤ 1) (hb : ∀ n ∈ t, ‖b n‖ ≤ 1)
    (hx : ∀ m ∈ s, ‖x m‖ ≤ 1) (hy : ∀ n ∈ t, ‖y n‖ ≤ 1) :
    ‖∑ m ∈ s, ∑ n ∈ t,
        a m * b n * ZMod.stdAddChar ((u : ZMod q) * m * n) *
          Complex.exp (z * x m * y n)‖ ≤
      Real.exp ‖z‖ * Real.sqrt ((q : ℝ) * s.card * t.card) := by
  classical
  let B : ℝ := Real.sqrt ((q : ℝ) * s.card * t.card)
  let T : ℕ → ℂ := fun k => ∑ m ∈ s, ∑ n ∈ t,
    (a m * b n * ZMod.stdAddChar ((u : ZMod q) * m * n)) *
      ((z * x m * y n) ^ k / (k.factorial : ℂ))
  have hsum : HasSum T
      (∑ m ∈ s, ∑ n ∈ t,
        a m * b n * ZMod.stdAddChar ((u : ZMod q) * m * n) *
          Complex.exp (z * x m * y n)) := by
    apply hasSum_sum
    intro m hm
    apply hasSum_sum
    intro n hn
    simpa only [Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp (z * x m * y n)).mul_left
        (a m * b n * ZMod.stdAddChar ((u : ZMod q) * m * n))
  have hterm (k : ℕ) : T k = (z ^ k / (k.factorial : ℂ)) *
      ∑ m ∈ s, ∑ n ∈ t,
        (a m * x m ^ k) * (b n * y n ^ k) *
          ZMod.stdAddChar ((u : ZMod q) * m * n) := by
    dsimp [T]
    rw [mul_sum]
    apply sum_congr rfl
    intro m hm
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    simp only [mul_pow]
    ring
  have hbound (k : ℕ) : ‖T k‖ ≤ (‖z‖ ^ k / (k.factorial : ℝ)) * B := by
    rw [hterm, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.le_sqrt_of_sq_le
    apply rational_bilinear_bound_finset u s t
    · intro m hm
      rw [norm_mul, norm_pow]
      calc
        _ ≤ 1 * 1 ^ k := mul_le_mul (ha m hm)
          (pow_le_pow_left₀ (norm_nonneg _) (hx m hm) k)
          (pow_nonneg (norm_nonneg _) _) (by norm_num)
        _ = 1 := by simp
    · intro n hn
      rw [norm_mul, norm_pow]
      calc
        _ ≤ 1 * 1 ^ k := mul_le_mul (hb n hn)
          (pow_le_pow_left₀ (norm_nonneg _) (hy n hn) k)
          (pow_nonneg (norm_nonneg _) _) (by norm_num)
        _ = 1 := by simp
  have hmajorant : HasSum (fun k : ℕ => (‖z‖ ^ k / (k.factorial : ℝ)) * B)
      (Real.exp ‖z‖ * B) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ‖z‖).mul_right B
  exact hsum.norm_le_of_bounded hmajorant hbound

noncomputable def phase (θ : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi : ℝ) * Complex.I * (θ : ℂ))

lemma rational_phase {q : ℕ} [NeZero q] (a : ℕ) (ha : a.Coprime q)
    (m n : ZMod q) :
    ZMod.stdAddChar ((ZMod.unitOfCoprime a ha : ZMod q) * m * n) =
      phase ((a : ℝ) / q * m.val * n.val) := by
  have he : ((a * m.val * n.val : ℕ) : ZMod q) =
      (ZMod.unitOfCoprime a ha : ZMod q) * m * n := by
    simp only [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.coe_unitOfCoprime]
  rw [← he, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  unfold phase
  congr 1
  push_cast
  ring

/-- A bilinear estimate at a rational approximation scale.
The indices are residues represented in `[0,q)`, so the coordinate product is at
most `q²`. A `1/q²` perturbation therefore changes the Fourier bound by only a
constant factor. -/
theorem near_rational_bilinear_bound {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ)
    (hθ : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (s t : Finset (ZMod q)) (c d : ZMod q → ℂ)
    (hc : ∀ m ∈ s, ‖c m‖ ≤ 1) (hd : ∀ n ∈ t, ‖d n‖ ≤ 1) :
    ‖∑ m ∈ s, ∑ n ∈ t, c m * d n * phase (θ * m.val * n.val)‖ ≤
      Real.exp (2 * Real.pi) * Real.sqrt ((q : ℝ) * s.card * t.card) := by
  classical
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime a haq
  let x : ZMod q → ℂ := fun m => (m.val : ℂ) / q
  let z : ℂ := (2 * Real.pi : ℝ) * Complex.I *
    ((θ - (a : ℝ) / q : ℝ) : ℂ) * (q : ℂ) ^ 2
  have hx (m : ZMod q) : ‖x m‖ ≤ 1 := by
    dsimp [x]
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    apply (div_le_one hq).mpr
    exact Nat.cast_le.mpr (Nat.le_of_lt m.val_lt)
  have hδ : |θ - (a : ℝ) / q| * (q : ℝ) ^ 2 ≤ 1 :=
    (le_div_iff₀ (sq_pos_of_pos hq)).mp hθ
  have hz : ‖z‖ ≤ 2 * Real.pi := by
    have hp : 0 ≤ 2 * Real.pi := by positivity
    dsimp [z]
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, Complex.norm_natCast, abs_of_nonneg (le_of_lt Real.pi_pos),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_one]
    nlinarith [Real.pi_pos]
  have hphase (m n : ZMod q) :
      phase (θ * m.val * n.val) =
        ZMod.stdAddChar ((u : ZMod q) * m * n) * Complex.exp (z * x m * x n) := by
    change phase (θ * m.val * n.val) =
      ZMod.stdAddChar ((ZMod.unitOfCoprime a haq : ZMod q) * m * n) *
        Complex.exp (z * x m * x n)
    rw [rational_phase a haq m n]
    unfold phase
    rw [← Complex.exp_add]
    congr 1
    dsimp [z, x]
    push_cast
    field_simp
    ring
  have he :
      (∑ m ∈ s, ∑ n ∈ t, c m * d n * phase (θ * m.val * n.val)) =
        ∑ m ∈ s, ∑ n ∈ t,
          c m * d n * ZMod.stdAddChar ((u : ZMod q) * m * n) *
            Complex.exp (z * x m * x n) := by
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro n hn
    rw [hphase]
    ring
  rw [he]
  apply (perturbed_rational_bilinear_bound u s t c d x x z hc hd
    (fun m _ => hx m) (fun n _ => hx n)).trans
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hz) (Real.sqrt_nonneg _)

/-- Sum coefficients having the same image under a residue map. -/
noncomputable def fiberSum {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (ρ : ι → κ)
    (a : ι → ℂ) (r : κ) : ℂ :=
  ∑ m ∈ s.filter (fun m => ρ m = r), a m

lemma norm_sum_sq_le_card_mul_energy {ι : Type*} (s : Finset ι) (a : ι → ℂ) :
    ‖∑ m ∈ s, a m‖ ^ 2 ≤ (s.card : ℝ) * ∑ m ∈ s, ‖a m‖ ^ 2 := by
  have h₁ := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s a) 2
  have h₂ := sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun m => ‖a m‖)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at h₂
  exact h₁.trans h₂

/-- Aggregating coefficients modulo a finite set increases their squared energy
by at most the largest fiber cardinality. -/
lemma fiberSum_energy {ι κ : Type*} [Fintype κ] [DecidableEq κ] (s : Finset ι) (ρ : ι → κ)
    (a : ι → ℂ) (K : ℕ)
    (hK : ∀ r, (s.filter (fun m => ρ m = r)).card ≤ K) :
    (∑ r : κ, ‖fiberSum s ρ a r‖ ^ 2) ≤ (K : ℝ) * ∑ m ∈ s, ‖a m‖ ^ 2 := by
  classical
  calc
    _ ≤ ∑ r : κ, ((s.filter (fun m => ρ m = r)).card : ℝ) *
        ∑ m ∈ s.filter (fun m => ρ m = r), ‖a m‖ ^ 2 := by
      exact sum_le_sum (fun r _ => norm_sum_sq_le_card_mul_energy _ _)
    _ ≤ ∑ r : κ, (K : ℝ) * ∑ m ∈ s.filter (fun m => ρ m = r), ‖a m‖ ^ 2 := by
      apply sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hK r))
        (sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by rw [← mul_sum, sum_fiberwise]

lemma bilinear_fiberSum {ι κ : Type*} {q : ℕ} [NeZero q]
    (u : (ZMod q)ˣ) (s : Finset ι) (t : Finset κ)
    (ρ : ι → ZMod q) (σ : κ → ZMod q) (a : ι → ℂ) (b : κ → ℂ) :
    (∑ r : ZMod q, ∑ v : ZMod q,
        fiberSum s ρ a r * fiberSum t σ b v *
          ZMod.stdAddChar ((u : ZMod q) * r * v)) =
      ∑ m ∈ s, ∑ n ∈ t, a m * b n *
        ZMod.stdAddChar ((u : ZMod q) * ρ m * σ n) := by
  classical
  calc
    _ = ∑ r : ZMod q, ∑ v : ZMod q,
        ∑ m ∈ s.filter (fun m => ρ m = r),
          ∑ n ∈ t.filter (fun n => σ n = v),
            a m * b n * ZMod.stdAddChar ((u : ZMod q) * ρ m * σ n) := by
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro v _
      simp only [fiberSum, sum_mul, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro m hm
      apply sum_congr rfl
      intro n hn
      rw [(mem_filter.mp hm).2, (mem_filter.mp hn).2]
    _ = ∑ r : ZMod q, ∑ m ∈ s.filter (fun m => ρ m = r),
        ∑ v : ZMod q, ∑ n ∈ t.filter (fun n => σ n = v),
          a m * b n * ZMod.stdAddChar ((u : ZMod q) * ρ m * σ n) := by
      apply sum_congr rfl
      intro r _
      rw [sum_comm]
    _ = ∑ r : ZMod q, ∑ m ∈ s.filter (fun m => ρ m = r),
        ∑ n ∈ t, a m * b n * ZMod.stdAddChar ((u : ZMod q) * ρ m * σ n) := by
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro m hm
      rw [sum_fiberwise]
    _ = _ := sum_fiberwise _ _ _

/-- A rational bilinear estimate for arbitrary index sets, with their residue
multiplicities made explicit. The coefficient energies need not be bounded. -/
theorem rational_bilinear_bound_fibers {ι κ : Type*} {q : ℕ} [NeZero q]
    (u : (ZMod q)ˣ) (s : Finset ι) (t : Finset κ)
    (ρ : ι → ZMod q) (σ : κ → ZMod q) (a : ι → ℂ) (b : κ → ℂ)
    (K L : ℕ) (hK : ∀ r, (s.filter (fun m => ρ m = r)).card ≤ K)
    (hL : ∀ v, (t.filter (fun n => σ n = v)).card ≤ L) :
    ‖∑ m ∈ s, ∑ n ∈ t, a m * b n *
        ZMod.stdAddChar ((u : ZMod q) * ρ m * σ n)‖ ^ 2 ≤
      (q : ℝ) * ((K : ℝ) * ∑ m ∈ s, ‖a m‖ ^ 2) *
        ((L : ℝ) * ∑ n ∈ t, ‖b n‖ ^ 2) := by
  classical
  have h := rational_bilinear_bound_unit u (fiberSum s ρ a) (fiberSum t σ b)
  rw [bilinear_fiberSum] at h
  apply h.trans
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (fiberSum_energy s ρ a K hK) (Nat.cast_nonneg q))
    (fiberSum_energy t σ b L hL) (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)

lemma energy_le_card {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (ha : ∀ m ∈ s, ‖a m‖ ≤ 1) : (∑ m ∈ s, ‖a m‖ ^ 2) ≤ (s.card : ℝ) := by
  calc
    _ ≤ ∑ _m ∈ s, (1 : ℝ) := by
      apply sum_le_sum
      intro m hm
      exact (pow_le_pow_left₀ (norm_nonneg _) (ha m hm) 2).trans_eq (by norm_num)
    _ = _ := by simp

/-- The bounded-coefficient form of the multiplicity estimate. -/
theorem rational_bilinear_bound_fibers_bounded {ι κ : Type*} {q : ℕ} [NeZero q]
    (u : (ZMod q)ˣ) (s : Finset ι) (t : Finset κ)
    (ρ : ι → ZMod q) (σ : κ → ZMod q) (a : ι → ℂ) (b : κ → ℂ)
    (K L : ℕ) (hK : ∀ r, (s.filter (fun m => ρ m = r)).card ≤ K)
    (hL : ∀ v, (t.filter (fun n => σ n = v)).card ≤ L)
    (ha : ∀ m ∈ s, ‖a m‖ ≤ 1) (hb : ∀ n ∈ t, ‖b n‖ ≤ 1) :
    ‖∑ m ∈ s, ∑ n ∈ t, a m * b n *
        ZMod.stdAddChar ((u : ZMod q) * ρ m * σ n)‖ ^ 2 ≤
      (q : ℝ) * ((K : ℝ) * s.card) * ((L : ℝ) * t.card) := by
  apply (rational_bilinear_bound_fibers u s t ρ σ a b K L hK hL).trans
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (energy_le_card s a ha) (Nat.cast_nonneg K))
      (Nat.cast_nonneg q))
    (mul_le_mul_of_nonneg_left (energy_le_card t b hb) (Nat.cast_nonneg L))
    (by positivity) (by positivity)

/-- In a natural interval, a residue class contains at most `M/q + 1` indices. -/
lemma card_natCast_fiber_le {q : ℕ} [NeZero q] (s : Finset ℕ) (M : ℕ)
    (hs : ∀ m ∈ s, m ≤ M) (r : ZMod q) :
    (s.filter (fun m : ℕ => (m : ZMod q) = r)).card ≤ M / q + 1 := by
  classical
  have h := card_le_card_of_injOn (s := s.filter (fun m : ℕ => (m : ZMod q) = r))
    (t := range (M / q + 1)) (fun m : ℕ => m / q) ?_ ?_
  · simpa only [card_range] using h
  · intro m hm
    apply mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (hs m (mem_filter.mp hm).1))
  · intro m hm n hn he
    have hr : (m : ZMod q) = (n : ZMod q) :=
      (mem_filter.mp hm).2.trans (mem_filter.mp hn).2.symm
    have hr' : m % q = n % q := by
      simpa only [ZMod.val_natCast] using congrArg ZMod.val hr
    have hm' := Nat.div_add_mod m q
    have hn' := Nat.div_add_mod n q
    change m / q = n / q at he
    rw [he, hr'] at hm'
    exact hm'.symm.trans hn'

lemma rational_phase_nat {q : ℕ} [NeZero q] (a : ℕ) (ha : a.Coprime q)
    (m n : ℕ) :
    ZMod.stdAddChar ((ZMod.unitOfCoprime a ha : ZMod q) * (m : ZMod q) * (n : ZMod q)) =
      phase ((a : ℝ) / q * m * n) := by
  have he : ((a * m * n : ℕ) : ZMod q) =
      (ZMod.unitOfCoprime a ha : ZMod q) * (m : ZMod q) * (n : ZMod q) := by
    simp only [Nat.cast_mul, ZMod.coe_unitOfCoprime]
  rw [← he, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  unfold phase
  congr 1
  push_cast
  ring

/-- A rational bilinear estimate on arbitrary finite subsets of natural intervals. -/
theorem rational_bilinear_bound_nat {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (s t : Finset ℕ) (M N : ℕ)
    (hs : ∀ m ∈ s, m ≤ M) (ht : ∀ n ∈ t, n ≤ N)
    (c d : ℕ → ℂ) (hc : ∀ m ∈ s, ‖c m‖ ≤ 1) (hd : ∀ n ∈ t, ‖d n‖ ≤ 1) :
    ‖∑ m ∈ s, ∑ n ∈ t, c m * d n * phase ((a : ℝ) / q * m * n)‖ ^ 2 ≤
      (q : ℝ) * ((M / q + 1 : ℕ) * (s.card : ℝ)) *
        ((N / q + 1 : ℕ) * (t.card : ℝ)) := by
  have h := rational_bilinear_bound_fibers_bounded (ZMod.unitOfCoprime a haq) s t
    (fun m : ℕ => (m : ZMod q)) (fun n : ℕ => (n : ZMod q)) c d
    (M / q + 1) (N / q + 1) (card_natCast_fiber_le s M hs)
    (card_natCast_fiber_le t N ht) hc hd
  simpa only [rational_phase_nat] using h

/-- The exponential perturbation bound with explicit residue multiplicities. -/
theorem perturbed_rational_bilinear_bound_fibers {ι κ : Type*} {q : ℕ} [NeZero q]
    (u : (ZMod q)ˣ) (s : Finset ι) (t : Finset κ)
    (ρ : ι → ZMod q) (σ : κ → ZMod q)
    (a x : ι → ℂ) (b y : κ → ℂ) (z : ℂ)
    (K L : ℕ) (hK : ∀ r, (s.filter (fun m => ρ m = r)).card ≤ K)
    (hL : ∀ v, (t.filter (fun n => σ n = v)).card ≤ L)
    (ha : ∀ m ∈ s, ‖a m‖ ≤ 1) (hb : ∀ n ∈ t, ‖b n‖ ≤ 1)
    (hx : ∀ m ∈ s, ‖x m‖ ≤ 1) (hy : ∀ n ∈ t, ‖y n‖ ≤ 1) :
    ‖∑ m ∈ s, ∑ n ∈ t,
        a m * b n * ZMod.stdAddChar ((u : ZMod q) * ρ m * σ n) *
          Complex.exp (z * x m * y n)‖ ≤
      Real.exp ‖z‖ * Real.sqrt ((q : ℝ) * ((K : ℝ) * s.card) * ((L : ℝ) * t.card)) := by
  classical
  let B : ℝ := Real.sqrt ((q : ℝ) * ((K : ℝ) * s.card) * ((L : ℝ) * t.card))
  let T : ℕ → ℂ := fun k => ∑ m ∈ s, ∑ n ∈ t,
    (a m * b n * ZMod.stdAddChar ((u : ZMod q) * ρ m * σ n)) *
      ((z * x m * y n) ^ k / (k.factorial : ℂ))
  have hsum : HasSum T
      (∑ m ∈ s, ∑ n ∈ t,
        a m * b n * ZMod.stdAddChar ((u : ZMod q) * ρ m * σ n) *
          Complex.exp (z * x m * y n)) := by
    apply hasSum_sum
    intro m hm
    apply hasSum_sum
    intro n hn
    simpa only [Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp (z * x m * y n)).mul_left
        (a m * b n * ZMod.stdAddChar ((u : ZMod q) * ρ m * σ n))
  have hterm (k : ℕ) : T k = (z ^ k / (k.factorial : ℂ)) *
      ∑ m ∈ s, ∑ n ∈ t,
        (a m * x m ^ k) * (b n * y n ^ k) *
          ZMod.stdAddChar ((u : ZMod q) * ρ m * σ n) := by
    dsimp [T]
    rw [mul_sum]
    apply sum_congr rfl
    intro m hm
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    simp only [mul_pow]
    ring
  have hbound (k : ℕ) : ‖T k‖ ≤ (‖z‖ ^ k / (k.factorial : ℝ)) * B := by
    rw [hterm, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.le_sqrt_of_sq_le
    apply rational_bilinear_bound_fibers_bounded u s t ρ σ _ _ K L hK hL
    · intro m hm
      rw [norm_mul, norm_pow]
      calc
        _ ≤ 1 * 1 ^ k := mul_le_mul (ha m hm)
          (pow_le_pow_left₀ (norm_nonneg _) (hx m hm) k)
          (pow_nonneg (norm_nonneg _) _) (by norm_num)
        _ = 1 := by simp
    · intro n hn
      rw [norm_mul, norm_pow]
      calc
        _ ≤ 1 * 1 ^ k := mul_le_mul (hb n hn)
          (pow_le_pow_left₀ (norm_nonneg _) (hy n hn) k)
          (pow_nonneg (norm_nonneg _) _) (by norm_num)
        _ = 1 := by simp
  have hmajorant : HasSum (fun k : ℕ => (‖z‖ ^ k / (k.factorial : ℝ)) * B)
      (Real.exp ‖z‖ * B) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ‖z‖).mul_right B
  exact hsum.norm_le_of_bounded hmajorant hbound

/-- The natural-index bilinear estimate at any scale on which the total
rational-approximation error is at most one. -/
theorem near_rational_bilinear_bound_nat_of_error {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ) (s t : Finset ℕ) (M N : ℕ)
    (hM : 0 < M) (hN : 0 < N)
    (herror : |θ - (a : ℝ) / q| * M * N ≤ 1)
    (hs : ∀ m ∈ s, m ≤ M) (ht : ∀ n ∈ t, n ≤ N)
    (c d : ℕ → ℂ) (hc : ∀ m ∈ s, ‖c m‖ ≤ 1) (hd : ∀ n ∈ t, ‖d n‖ ≤ 1) :
    ‖∑ m ∈ s, ∑ n ∈ t, c m * d n * phase (θ * m * n)‖ ≤
      Real.exp (2 * Real.pi) *
        Real.sqrt ((q : ℝ) * ((M / q + 1 : ℕ) * (s.card : ℝ)) *
          ((N / q + 1 : ℕ) * (t.card : ℝ))) := by
  classical
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime a haq
  let x : ℕ → ℂ := fun m => (m : ℂ) / M
  let y : ℕ → ℂ := fun n => (n : ℂ) / N
  let z : ℂ := (2 * Real.pi : ℝ) * Complex.I *
    ((θ - (a : ℝ) / q : ℝ) : ℂ) * (M : ℂ) * (N : ℂ)
  have hx (m : ℕ) (hm : m ∈ s) : ‖x m‖ ≤ 1 := by
    dsimp [x]
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    exact (div_le_one hMR).mpr (Nat.cast_le.mpr (hs m hm))
  have hy (n : ℕ) (hn : n ∈ t) : ‖y n‖ ≤ 1 := by
    dsimp [y]
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    exact (div_le_one hNR).mpr (Nat.cast_le.mpr (ht n hn))
  have hz : ‖z‖ ≤ 2 * Real.pi := by
    dsimp [z]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, Complex.norm_natCast, abs_of_nonneg (le_of_lt Real.pi_pos),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_one]
    calc
      _ = (2 * Real.pi) * (|θ - (a : ℝ) / q| * M * N) := by ring
      _ ≤ (2 * Real.pi) * 1 := mul_le_mul_of_nonneg_left herror (by positivity)
      _ = _ := by ring
  have hphase (m n : ℕ) :
      phase (θ * m * n) =
        ZMod.stdAddChar ((u : ZMod q) * (m : ZMod q) * (n : ZMod q)) *
          Complex.exp (z * x m * y n) := by
    change phase (θ * m * n) =
      ZMod.stdAddChar ((ZMod.unitOfCoprime a haq : ZMod q) *
        (m : ZMod q) * (n : ZMod q)) * Complex.exp (z * x m * y n)
    rw [rational_phase_nat]
    unfold phase
    rw [← Complex.exp_add]
    congr 1
    dsimp [z, x, y]
    push_cast
    field_simp [hMC, hNC]
    ring
  have he :
      (∑ m ∈ s, ∑ n ∈ t, c m * d n * phase (θ * m * n)) =
        ∑ m ∈ s, ∑ n ∈ t,
          c m * d n * ZMod.stdAddChar ((u : ZMod q) * (m : ZMod q) * (n : ZMod q)) *
            Complex.exp (z * x m * y n) := by
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro n hn
    rw [hphase]
    ring
  rw [he]
  apply (perturbed_rational_bilinear_bound_fibers u s t
    (fun m : ℕ => (m : ZMod q)) (fun n : ℕ => (n : ZMod q))
    c x d y z (M / q + 1) (N / q + 1)
    (card_natCast_fiber_le s M hs) (card_natCast_fiber_le t N ht)
    hc hd hx hy).trans
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hz) (Real.sqrt_nonneg _)

/-- A `1/q²` rational approximation supplies the natural-index bilinear estimate
throughout rectangles whose coordinate product is at most `q²`. -/
theorem near_rational_bilinear_bound_nat {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ)
    (hθ : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (s t : Finset ℕ) (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hMN : (M : ℝ) * N ≤ (q : ℝ) ^ 2)
    (hs : ∀ m ∈ s, m ≤ M) (ht : ∀ n ∈ t, n ≤ N)
    (c d : ℕ → ℂ) (hc : ∀ m ∈ s, ‖c m‖ ≤ 1) (hd : ∀ n ∈ t, ‖d n‖ ≤ 1) :
    ‖∑ m ∈ s, ∑ n ∈ t, c m * d n * phase (θ * m * n)‖ ≤
      Real.exp (2 * Real.pi) *
        Real.sqrt ((q : ℝ) * ((M / q + 1 : ℕ) * (s.card : ℝ)) *
          ((N / q + 1 : ℕ) * (t.card : ℝ))) := by
  apply near_rational_bilinear_bound_nat_of_error a haq θ s t M N hM hN _ hs ht c d hc hd
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hδ : |θ - (a : ℝ) / q| * (q : ℝ) ^ 2 ≤ 1 :=
    (le_div_iff₀ (sq_pos_of_pos hq)).mp hθ
  calc
    _ = |θ - (a : ℝ) / q| * ((M : ℝ) * N) := by ring
    _ ≤ |θ - (a : ℝ) / q| * (q : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hMN (abs_nonneg _)
    _ ≤ 1 := hδ

@[simp] lemma norm_phase (θ : ℝ) : ‖phase θ‖ = 1 := by
  unfold phase
  rw [Complex.norm_exp]
  simp

lemma phase_add (θ φ : ℝ) : phase (θ + φ) = phase θ * phase φ := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma phase_nat_mul (θ : ℝ) (n : ℕ) : phase (θ * n) = phase θ ^ n := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma norm_phase_sub_one (θ : ℝ) :
    ‖phase θ - 1‖ = 2 * |Real.sin (Real.pi * θ)| := by
  have he : (2 * Real.pi : ℝ) * Complex.I * (θ : ℂ) =
      Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ) := by push_cast; ring
  rw [phase, he, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * θ) / 2 = Real.pi * θ by ring]
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

lemma four_mul_le_norm_phase_sub_one {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 1 / 2) :
    4 * θ ≤ ‖phase θ - 1‖ := by
  have hs := Real.mul_le_sin
    (show 0 ≤ Real.pi * θ by positivity)
    (show Real.pi * θ ≤ Real.pi / 2 by nlinarith [Real.pi_pos])
  have he : (2 / Real.pi) * (Real.pi * θ) = 2 * θ := by
    field_simp [Real.pi_ne_zero]
  rw [he] at hs
  rw [norm_phase_sub_one]
  nlinarith [le_abs_self (Real.sin (Real.pi * θ))]

lemma norm_phase_sub_one_lower {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    4 * min θ (1 - θ) ≤ ‖phase θ - 1‖ := by
  by_cases hθ2 : θ ≤ 1 / 2
  · rw [min_eq_left (by linarith)]
    exact four_mul_le_norm_phase_sub_one hθ0 hθ2
  · rw [min_eq_right (by linarith)]
    have h := four_mul_le_norm_phase_sub_one
      (show 0 ≤ 1 - θ by linarith) (show 1 - θ ≤ 1 / 2 by linarith)
    rw [norm_phase_sub_one, show Real.pi * (1 - θ) = Real.pi - Real.pi * θ by ring,
      Real.sin_pi_sub, ← norm_phase_sub_one] at h
    exact h

lemma geom_sum_norm_mul_le_two {z : ℂ} (hz : ‖z‖ = 1) (K : ℕ) :
    ‖∑ j ∈ range K, z ^ j‖ * ‖z - 1‖ ≤ 2 := by
  rw [← norm_mul, geom_sum_mul]
  calc
    _ ≤ ‖z ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz, norm_one, one_pow]; norm_num

lemma stdAddChar_eq_phase_val {q : ℕ} [NeZero q] (k : ZMod q) :
    ZMod.stdAddChar k = phase ((k.val : ℝ) / q) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, phase]
  congr 1
  push_cast
  ring

/-- Distance of a residue to zero, measured using its standard natural representative. -/
def residueDistance {q : ℕ} [NeZero q] (k : ZMod q) : ℕ := min k.val (q - k.val)

lemma residueDistance_pos {q : ℕ} [NeZero q] {k : ZMod q} (hk : k ≠ 0) :
    0 < residueDistance k := by
  apply lt_min
  · have hv : k.val ≠ 0 := by simpa using hk
    omega
  · have := k.val_lt
    omega

lemma stdAddChar_sub_one_lower {q : ℕ} [NeZero q] (k : ZMod q) :
    4 * (residueDistance k : ℝ) / q ≤ ‖ZMod.stdAddChar k - 1‖ := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hv : (k.val : ℝ) ≤ q := Nat.cast_le.mpr k.val_lt.le
  have hl := norm_phase_sub_one_lower
    (show (0 : ℝ) ≤ (k.val : ℝ) / q by positivity)
    ((div_le_one hq).mpr hv)
  have hmin₁ : (residueDistance k : ℝ) ≤ k.val :=
    Nat.cast_le.mpr (min_le_left _ _)
  have hmin₂ : (residueDistance k : ℝ) ≤ (q : ℝ) - k.val := by
    have h := Nat.cast_le (α := ℝ).mpr (min_le_right k.val (q - k.val))
    rw [Nat.cast_sub k.val_lt.le] at h
    exact h
  have hd : (residueDistance k : ℝ) / q ≤
      min ((k.val : ℝ) / q) (1 - (k.val : ℝ) / q) := by
    apply le_min
    · exact div_le_div_of_nonneg_right hmin₁ hq.le
    · apply (div_le_iff₀ hq).mpr
      have he : (1 - (k.val : ℝ) / q) * q = (q : ℝ) - k.val := by field_simp
      rwa [he]
  rw [stdAddChar_eq_phase_val, mul_div_assoc]
  exact (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 4)).trans hl

lemma stdAddChar_nat_mul_eq_pow {q : ℕ} [NeZero q] (k : ZMod q) (j : ℕ) :
    ZMod.stdAddChar (k * (j : ZMod q)) = ZMod.stdAddChar k ^ j := by
  rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

/-- A uniform geometric-sum bound for nonzero finite Fourier frequencies. -/
theorem stdAddChar_prefix_bound {q : ℕ} [NeZero q] (k : ZMod q) (hk : k ≠ 0)
    (K : ℕ) :
    ‖∑ j ∈ range K, ZMod.stdAddChar (k * (j : ZMod q))‖ ≤
      (q : ℝ) / (2 * residueDistance k) := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hd : (0 : ℝ) < residueDistance k := Nat.cast_pos.mpr (residueDistance_pos hk)
  simp_rw [stdAddChar_nat_mul_eq_pow]
  have hg := geom_sum_norm_mul_le_two (AddChar.norm_apply (ZMod.stdAddChar (N := q)) k) K
  have hl := mul_le_mul_of_nonneg_left (stdAddChar_sub_one_lower k)
    (norm_nonneg (∑ j ∈ range K, ZMod.stdAddChar k ^ j))
  have h := hl.trans hg
  rw [← mul_div_assoc] at h
  have h' := (div_le_iff₀ hq).mp h
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * residueDistance k)).mpr
  nlinarith

/-- Fourier coefficients of a prefix of natural representatives modulo `q`. -/
noncomputable def prefixCoeff {q : ℕ} [NeZero q] (K : ℕ) (k : ZMod q) : ℂ :=
  (∑ j ∈ range K, ZMod.stdAddChar (k * (j : ZMod q))) / (q : ℂ)

/-- Fourier inversion for a possibly empty initial segment of `ZMod q`. -/
theorem prefixCoeff_inversion {q : ℕ} [NeZero q] (K : ℕ) (hK : K ≤ q) (n : ZMod q) :
    (∑ k : ZMod q, prefixCoeff K k * ZMod.stdAddChar (-(k * n))) =
      if n.val < K then 1 else 0 := by
  classical
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hsum :
      (∑ k : ZMod q, (∑ j ∈ range K, ZMod.stdAddChar (k * (j : ZMod q))) *
        ZMod.stdAddChar (-(k * n))) = if n.val < K then (q : ℂ) else 0 := by
    calc
      _ = ∑ j ∈ range K, ∑ k : ZMod q,
          ZMod.stdAddChar (((j : ZMod q) - n) * k) := by
        simp only [sum_mul]
        rw [sum_comm]
        apply sum_congr rfl
        intro j hj
        apply sum_congr rfl
        intro k hk
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      _ = ∑ j ∈ range K, if j = n.val then (q : ℂ) else 0 := by
        apply sum_congr rfl
        intro j hj
        rw [character_orthogonality]
        have hjq : j < q := (mem_range.mp hj).trans_le hK
        have he : ((j : ZMod q) - n = 0) ↔ j = n.val := by
          rw [sub_eq_zero]
          constructor
          · intro h
            simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hjq] using congrArg ZMod.val h
          · intro h
            apply ZMod.val_injective q
            simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hjq] using h
        simp only [he]
      _ = _ := by simp only [sum_ite_eq', mem_range]
  calc
    _ = (∑ k : ZMod q, (∑ j ∈ range K, ZMod.stdAddChar (k * (j : ZMod q))) *
        ZMod.stdAddChar (-(k * n))) / (q : ℂ) := by
      rw [sum_div]
      apply sum_congr rfl
      intro k hk
      dsimp [prefixCoeff]
      ring
    _ = _ := by rw [hsum]; split_ifs <;> simp [hqC]

noncomputable def prefixMajorant {q : ℕ} [NeZero q] (k : ZMod q) : ℝ :=
  if k = 0 then 1 else 1 / (2 * residueDistance k)

lemma prefixMajorant_pos {q : ℕ} [NeZero q] (k : ZMod q) : 0 < prefixMajorant k := by
  unfold prefixMajorant
  split_ifs with h
  · norm_num
  · have := residueDistance_pos h
    positivity

lemma norm_prefixCoeff_le {q : ℕ} [NeZero q] (K : ℕ) (hK : K ≤ q) (k : ZMod q) :
    ‖prefixCoeff K k‖ ≤ prefixMajorant k := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  by_cases hk : k = 0
  · subst k
    simp only [prefixCoeff, zero_mul, AddChar.map_zero_eq_one, sum_const,
      nsmul_eq_mul, mul_one, prefixMajorant, norm_div,
      Complex.norm_natCast, card_range]
    exact (div_le_one hq).mpr (Nat.cast_le.mpr hK)
  · unfold prefixCoeff
    rw [norm_div, Complex.norm_natCast, prefixMajorant, if_neg hk]
    calc
      _ ≤ ((q : ℝ) / (2 * residueDistance k)) / q :=
        div_le_div_of_nonneg_right (stdAddChar_prefix_bound k hk K) hq.le
      _ = _ := by field_simp

lemma sum_reciprocal_val_le_harmonic {q : ℕ} [NeZero q] :
    (∑ k : ZMod q, (1 : ℝ) / k.val) ≤ (harmonic q : ℝ) := by
  classical
  have he : (∑ k : ZMod q, (1 : ℝ) / k.val) =
      ∑ j ∈ range q, (1 : ℝ) / j := by
    apply sum_bij (fun k _ => k.val)
    · intro k hk
      exact mem_range.mpr k.val_lt
    · intro k hk l hl he
      exact ZMod.val_injective q he
    · intro j hj
      refine ⟨(j : ZMod q), mem_univ _, ?_⟩
      exact (ZMod.val_natCast q j).trans (Nat.mod_eq_of_lt (mem_range.mp hj))
    · intro k hk
      rfl
  rw [he]
  calc
    _ ≤ ∑ j ∈ range (q + 1), (1 : ℝ) / j := by
      apply sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_succ q))
      intro j hj hnj
      positivity
    _ = (harmonic q : ℝ) := by
      rw [sum_range_succ']
      simp only [Nat.cast_zero, div_zero, add_zero]
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

/-- The completion coefficients have logarithmic total mass. -/
theorem sum_prefixMajorant_le {q : ℕ} [NeZero q] :
    (∑ k : ZMod q, prefixMajorant k) ≤ 2 + Real.log q := by
  classical
  have hpoint (k : ZMod q) : prefixMajorant k ≤
      (if k = 0 then 1 else 0) + ((1 : ℝ) / k.val + 1 / (-k).val) / 2 := by
    by_cases hk : k = 0
    · subst k
      simp [prefixMajorant]
    · letI : NeZero k := ⟨hk⟩
      have hv : 0 < k.val := by
        have hv0 : k.val ≠ 0 := by simpa using hk
        exact Nat.pos_of_ne_zero hv0
      have hw : 0 < q - k.val := by have := k.val_lt; omega
      rw [prefixMajorant, if_neg hk, if_neg hk, zero_add,
        ZMod.val_neg_of_ne_zero, residueDistance]
      by_cases hle : k.val ≤ q - k.val
      · rw [min_eq_left hle]
        have h₀ : (0 : ℝ) ≤ 1 / (q - k.val : ℕ) := by positivity
        have he : (1 : ℝ) / (2 * k.val) = (1 / k.val) / 2 := by ring
        rw [he]
        linarith
      · rw [min_eq_right (le_of_not_ge hle)]
        have h₀ : (0 : ℝ) ≤ 1 / k.val := by positivity
        have he : (1 : ℝ) / (2 * (q - k.val : ℕ)) = (1 / (q - k.val : ℕ)) / 2 := by ring
        rw [he]
        linarith
  have hneg : (∑ k : ZMod q, (1 : ℝ) / (-k).val) =
      ∑ k : ZMod q, (1 : ℝ) / k.val := by
    exact Equiv.sum_comp (Equiv.neg (ZMod q)) (fun k => (1 : ℝ) / k.val)
  have h := sum_le_sum (s := univ) (fun k _ => hpoint k)
  simp only [sum_add_distrib, sum_ite_eq', mem_univ, if_true] at h
  rw [← sum_div, sum_add_distrib, hneg] at h
  have hh := sum_reciprocal_val_le_harmonic (q := q)
  have hl := harmonic_le_one_add_log q
  linarith

/-- Fourier completion of row-dependent prefixes. Any bilinear estimate stable
under bounded coefficient changes loses only `2 + log H` when the rows are cut
at varying points. -/
theorem bilinear_prefix_completion {ι κ : Type*} {H : ℕ} [NeZero H]
    (s : Finset ι) (t : Finset κ) (ν : κ → ZMod H) (F : ι → ℕ)
    (hF : ∀ m ∈ s, F m ≤ H) (A : ι → κ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hrect : ∀ a : ι → ℂ, ∀ b : κ → ℂ,
      (∀ m ∈ s, ‖a m‖ ≤ 1) → (∀ n ∈ t, ‖b n‖ ≤ 1) →
      ‖∑ m ∈ s, ∑ n ∈ t, a m * b n * A m n‖ ≤ B) :
    ‖∑ m ∈ s, ∑ n ∈ t, if (ν n).val < F m then A m n else 0‖ ≤
      (2 + Real.log H) * B := by
  classical
  let T : ZMod H → ℂ := fun k => ∑ m ∈ s, ∑ n ∈ t,
    prefixCoeff (F m) k * ZMod.stdAddChar (-(k * ν n)) * A m n
  have he : (∑ m ∈ s, ∑ n ∈ t, if (ν n).val < F m then A m n else 0) =
      ∑ k : ZMod H, T k := by
    calc
      _ = ∑ m ∈ s, ∑ n ∈ t,
          (∑ k : ZMod H, prefixCoeff (F m) k * ZMod.stdAddChar (-(k * ν n))) *
            A m n := by
        apply sum_congr rfl
        intro m hm
        apply sum_congr rfl
        intro n hn
        rw [prefixCoeff_inversion _ (hF m hm)]
        split_ifs <;> simp
      _ = ∑ m ∈ s, ∑ k : ZMod H, ∑ n ∈ t,
          prefixCoeff (F m) k * ZMod.stdAddChar (-(k * ν n)) * A m n := by
        apply sum_congr rfl
        intro m hm
        simp only [sum_mul]
        rw [sum_comm]
      _ = _ := by rw [sum_comm]
  have hT (k : ZMod H) : ‖T k‖ ≤ prefixMajorant k * B := by
    let w : ℝ := prefixMajorant k
    have hw : 0 < w := prefixMajorant_pos k
    have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
    let a : ι → ℂ := fun m => prefixCoeff (F m) k / (w : ℂ)
    let b : κ → ℂ := fun n => ZMod.stdAddChar (-(k * ν n))
    have ha : ∀ m ∈ s, ‖a m‖ ≤ 1 := by
      intro m hm
      dsimp [a]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
      exact (div_le_one hw).mpr (norm_prefixCoeff_le (F m) (hF m hm) k)
    have hb : ∀ n ∈ t, ‖b n‖ ≤ 1 := by
      intro n hn
      exact (AddChar.norm_apply _ _).le
    have hfactor : T k = (w : ℂ) * ∑ m ∈ s, ∑ n ∈ t, a m * b n * A m n := by
      dsimp [T]
      rw [mul_sum]
      apply sum_congr rfl
      intro m hm
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      dsimp [a, b]
      field_simp
    rw [hfactor, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
    exact mul_le_mul_of_nonneg_left (hrect a b ha hb) hw.le
  rw [he]
  calc
    _ ≤ ∑ k : ZMod H, ‖T k‖ := norm_sum_le _ _
    _ ≤ ∑ k : ZMod H, prefixMajorant k * B := sum_le_sum (fun k _ => hT k)
    _ = (∑ k : ZMod H, prefixMajorant k) * B := (sum_mul ..).symm
    _ ≤ (2 + Real.log H) * B := mul_le_mul_of_nonneg_right sum_prefixMajorant_le hB

/-- A hyperbola-truncated bilinear phase sum. This is the form needed for the
large-variable term in Vaughan's identity. -/
theorem near_rational_hyperbola_bound {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ) (s t : Finset ℕ) (M N X : ℕ)
    (hM : 0 < M) (hN : 0 < N)
    (herror : |θ - (a : ℝ) / q| * M * N ≤ 1)
    (hs : ∀ m ∈ s, 0 < m ∧ m ≤ M) (ht : ∀ n ∈ t, n ≤ N)
    (c d : ℕ → ℂ) (hc : ∀ m ∈ s, ‖c m‖ ≤ 1) (hd : ∀ n ∈ t, ‖d n‖ ≤ 1) :
    ‖∑ m ∈ s, ∑ n ∈ t.filter (fun n => m * n ≤ X),
        c m * d n * phase (θ * m * n)‖ ≤
      (2 + Real.log (N + 1)) * (Real.exp (2 * Real.pi) *
        Real.sqrt ((q : ℝ) * ((M / q + 1 : ℕ) * (s.card : ℝ)) *
          ((N / q + 1 : ℕ) * (t.card : ℝ)))) := by
  classical
  let H : ℕ := N + 1
  letI : NeZero H := ⟨by dsimp [H]; omega⟩
  let ν : ℕ → ZMod H := fun n => (n : ZMod H)
  let F : ℕ → ℕ := fun m => min (X / m + 1) H
  let A : ℕ → ℕ → ℂ := fun m n => c m * d n * phase (θ * m * n)
  let B : ℝ := Real.exp (2 * Real.pi) *
    Real.sqrt ((q : ℝ) * ((M / q + 1 : ℕ) * (s.card : ℝ)) *
      ((N / q + 1 : ℕ) * (t.card : ℝ)))
  have hrect : ∀ f g : ℕ → ℂ,
      (∀ m ∈ s, ‖f m‖ ≤ 1) → (∀ n ∈ t, ‖g n‖ ≤ 1) →
      ‖∑ m ∈ s, ∑ n ∈ t, f m * g n * A m n‖ ≤ B := by
    intro f g hf hg
    have hfg := near_rational_bilinear_bound_nat_of_error a haq θ s t M N hM hN
      herror (fun m hm => (hs m hm).2) ht
      (fun m => f m * c m) (fun n => g n * d n) ?_ ?_
    · convert hfg using 1
      congr 1
      apply sum_congr rfl
      intro m hm
      apply sum_congr rfl
      intro n hn
      dsimp [A]
      ring
    · intro m hm
      rw [norm_mul]
      simpa using mul_le_mul (hf m hm) (hc m hm) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    · intro n hn
      rw [norm_mul]
      simpa using mul_le_mul (hg n hn) (hd n hn) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h := bilinear_prefix_completion s t ν F
    (fun m hm => min_le_right _ _) A B (by positivity) hrect
  have hcut (m : ℕ) (hm : m ∈ s) (n : ℕ) (hn : n ∈ t) :
      (ν n).val < F m ↔ m * n ≤ X := by
    have hnH : n < H := by dsimp [H]; exact Nat.lt_succ_of_le (ht n hn)
    dsimp [ν, F]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hnH, lt_min_iff]
    simp only [hnH, and_true, Nat.lt_succ_iff]
    rw [Nat.le_div_iff_mul_le (hs m hm).1, Nat.mul_comm n m]
  have he :
      (∑ m ∈ s, ∑ n ∈ t.filter (fun n => m * n ≤ X), A m n) =
        ∑ m ∈ s, ∑ n ∈ t, if (ν n).val < F m then A m n else 0 := by
    apply sum_congr rfl
    intro m hm
    rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    simp only [hcut m hm n hn]
  rw [← he] at h
  simpa only [A, B, H, Nat.cast_add, Nat.cast_one] using h

lemma norm_phase_sub_one_le (θ : ℝ) :
    ‖phase θ - 1‖ ≤ 2 * Real.pi * |θ| := by
  rw [norm_phase_sub_one]
  calc
    _ ≤ 2 * |Real.pi * θ| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = _ := by rw [abs_mul, abs_of_pos Real.pi_pos]; ring

lemma norm_phase_sub_le (θ φ : ℝ) :
    ‖phase θ - phase φ‖ ≤ 2 * Real.pi * |θ - φ| := by
  have he : phase θ - phase φ = phase φ * (phase (θ - φ) - 1) := by
    rw [mul_sub, ← phase_add, mul_one]
    congr 1
    congr 1
    ring
  rw [he, norm_mul, norm_phase, one_mul]
  exact norm_phase_sub_one_le _

lemma unit_natCast_ne_zero {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) {m : ℕ}
    (hm0 : 0 < m) (hmq : m < q) : (u : ZMod q) * (m : ZMod q) ≠ 0 := by
  intro h
  have hz : (m : ZMod q) = 0 := u.mul_right_eq_zero.mp h
  have hv := congrArg ZMod.val hz
  simp only [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt hmq] at hv
  omega

/-- Small rational frequencies cannot be destroyed by a `1/q²` perturbation. -/
lemma near_rational_small_frequency_lower {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ)
    (hθ : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    {m R : ℕ} (hm0 : 0 < m) (hmR : m ≤ R) (hR : 8 * R ≤ q) :
    2 * (residueDistance ((ZMod.unitOfCoprime a haq : ZMod q) * (m : ZMod q)) : ℝ) / q ≤
      ‖phase (θ * m) - 1‖ := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hmq : m < q := by omega
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime a haq
  let k : ZMod q := (u : ZMod q) * (m : ZMod q)
  have hk : k ≠ 0 := unit_natCast_ne_zero u hm0 hmq
  have hd : (1 : ℝ) ≤ residueDistance k := by exact_mod_cast residueDistance_pos hk
  have hchar : ZMod.stdAddChar k = phase ((a : ℝ) / q * m) := by
    simpa only [Nat.cast_one, mul_one] using rational_phase_nat a haq m 1
  have hδq : |θ - (a : ℝ) / q| * (q : ℝ) ^ 2 ≤ 1 :=
    (le_div_iff₀ (sq_pos_of_pos hq)).mp hθ
  have hδ : |θ - (a : ℝ) / q| * q ≤ 1 / q := by
    apply (le_div_iff₀ hq).mpr
    nlinarith
  have hscale : 2 * Real.pi * m ≤ (q : ℝ) := by
    have hmR' : (m : ℝ) ≤ R := Nat.cast_le.mpr hmR
    have hR' : (8 : ℝ) * R ≤ q := by exact_mod_cast hR
    have hp := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (Nat.cast_nonneg m)
    nlinarith
  have hdist : ‖phase (θ * m) - ZMod.stdAddChar k‖ ≤ (residueDistance k : ℝ) / q := by
    rw [hchar]
    calc
      _ ≤ 2 * Real.pi * |θ * m - (a : ℝ) / q * m| := norm_phase_sub_le _ _
      _ = |θ - (a : ℝ) / q| * (2 * Real.pi * m) := by
        rw [← sub_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ m from Nat.cast_nonneg m)]
        ring
      _ ≤ |θ - (a : ℝ) / q| * q := mul_le_mul_of_nonneg_left hscale (abs_nonneg _)
      _ ≤ 1 / q := hδ
      _ ≤ (residueDistance k : ℝ) / q := div_le_div_of_nonneg_right hd hq.le
  have hb := stdAddChar_sub_one_lower k
  have ht := norm_sub_le_norm_sub_add_norm_sub (ZMod.stdAddChar k) (phase (θ * m)) 1
  rw [norm_sub_rev (ZMod.stdAddChar k) (phase (θ * m))] at ht
  change 2 * (residueDistance k : ℝ) / q ≤ _
  rw [mul_div_assoc] at hb ⊢
  have hpos : 0 ≤ (residueDistance k : ℝ) / q := by positivity
  linarith

/-- Each small outer index has a geometric-sum bound independent of the length
of its inner prefix. -/
theorem near_rational_small_prefix_bound {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ)
    (hθ : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    {m R : ℕ} (hm0 : 0 < m) (hmR : m ≤ R) (hR : 8 * R ≤ q) (K : ℕ) :
    ‖∑ n ∈ range K, phase (θ * m * n)‖ ≤
      (q : ℝ) / residueDistance ((ZMod.unitOfCoprime a haq : ZMod q) * (m : ZMod q)) := by
  let k : ZMod q := (ZMod.unitOfCoprime a haq : ZMod q) * (m : ZMod q)
  have hk : k ≠ 0 := unit_natCast_ne_zero _ hm0 (by omega)
  have hd : (0 : ℝ) < residueDistance k := Nat.cast_pos.mpr (residueDistance_pos hk)
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have he : (∑ n ∈ range K, phase (θ * m * n)) =
      ∑ n ∈ range K, phase (θ * m) ^ n := by
    exact sum_congr rfl (fun n hn => phase_nat_mul (θ * m) n)
  rw [he]
  have hg := geom_sum_norm_mul_le_two (norm_phase (θ * m)) K
  have hl := mul_le_mul_of_nonneg_left
    (near_rational_small_frequency_lower a haq θ hθ hm0 hmR hR)
    (norm_nonneg (∑ n ∈ range K, phase (θ * m) ^ n))
  have h := hl.trans hg
  rw [← mul_div_assoc] at h
  have h' := (div_le_iff₀ hq).mp h
  apply (le_div_iff₀ hd).mpr
  nlinarith

lemma sum_comp_le_fiber_bound {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (s : Finset ι) (ρ : ι → κ) (f : κ → ℝ) (hf : ∀ r, 0 ≤ f r)
    (K : ℕ) (hK : ∀ r, (s.filter (fun m => ρ m = r)).card ≤ K) :
    (∑ m ∈ s, f (ρ m)) ≤ (K : ℝ) * ∑ r : κ, f r := by
  classical
  rw [← sum_fiberwise_of_maps_to' (s := s) (t := univ) (g := ρ)
    (fun m hm => mem_univ _) f]
  calc
    _ = ∑ r : κ, ((s.filter (fun m => ρ m = r)).card : ℝ) * f r := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ ∑ r : κ, (K : ℝ) * f r := by
      exact sum_le_sum (fun r _ => mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hK r)) (hf r))
    _ = _ := (mul_sum ..).symm

/-- The complete Type-I bound for bounded outer coefficients and arbitrary
inner prefix lengths, at a small outer-index scale. -/
theorem near_rational_typeI_bound {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ)
    (hθ : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (s : Finset ℕ) (R : ℕ) (hs : ∀ m ∈ s, 0 < m ∧ m ≤ R)
    (hR : 8 * R ≤ q) (K : ℕ → ℕ) (c : ℕ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hc : ∀ m ∈ s, ‖c m‖ ≤ C) :
    ‖∑ m ∈ s, c m * ∑ n ∈ range (K m), phase (θ * m * n)‖ ≤
      2 * C * q * (2 + Real.log q) := by
  classical
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime a haq
  have hRlt : R < q := by have := Nat.pos_of_ne_zero (NeZero.ne q); omega
  have hfiber (r : ZMod q) :
      (s.filter (fun m : ℕ => (m : ZMod q) = r)).card ≤ 1 := by
    simpa only [Nat.div_eq_of_lt hRlt, zero_add] using
      card_natCast_fiber_le s R (fun m hm => (hs m hm).2) r
  have hsum : (∑ m ∈ s, prefixMajorant ((u : ZMod q) * (m : ZMod q))) ≤
      ∑ r : ZMod q, prefixMajorant r := by
    have h := sum_comp_le_fiber_bound s (fun m : ℕ => (m : ZMod q))
      (fun r => prefixMajorant ((u : ZMod q) * r))
      (fun r => (prefixMajorant_pos _).le) 1 hfiber
    simp only [Nat.cast_one, one_mul] at h
    exact h.trans_eq (Equiv.sum_comp u.mulLeft prefixMajorant)
  have hpoint (m : ℕ) (hm : m ∈ s) :
      ‖∑ n ∈ range (K m), phase (θ * m * n)‖ ≤
        2 * (q : ℝ) * prefixMajorant ((u : ZMod q) * (m : ZMod q)) := by
    have hk := unit_natCast_ne_zero u (hs m hm).1 ((hs m hm).2.trans_lt hRlt)
    apply (near_rational_small_prefix_bound a haq θ hθ (hs m hm).1 (hs m hm).2 hR (K m)).trans_eq
    change (q : ℝ) / residueDistance ((u : ZMod q) * (m : ZMod q)) = _
    rw [prefixMajorant, if_neg hk]
    field_simp
  calc
    _ ≤ ∑ m ∈ s, ‖c m‖ * ‖∑ n ∈ range (K m), phase (θ * m * n)‖ := by
      simpa only [norm_mul] using norm_sum_le s
        (fun m => c m * ∑ n ∈ range (K m), phase (θ * m * n))
    _ ≤ ∑ m ∈ s, C * (2 * (q : ℝ) * prefixMajorant ((u : ZMod q) * (m : ZMod q))) := by
      exact sum_le_sum (fun m hm => mul_le_mul (hc m hm) (hpoint m hm)
        (norm_nonneg _) hC)
    _ = (2 * C * q) * ∑ m ∈ s, prefixMajorant ((u : ZMod q) * (m : ZMod q)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro m hm
      ring
    _ ≤ (2 * C * q) * (2 + Real.log q) :=
      mul_le_mul_of_nonneg_left (hsum.trans sum_prefixMajorant_le) (by positivity)

lemma norm_monotone_weighted_prefix {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (w : ℕ → ℝ) (hw : Monotone w) (hw0 : 0 ≤ w 0)
    (z : ℕ → E) (K : ℕ) (B : ℝ)
    (hB : ∀ j ≤ K, ‖∑ n ∈ range j, z n‖ ≤ B) :
    ‖∑ n ∈ range K, w n • z n‖ ≤ 2 * w (K - 1) * B := by
  have hB0 : 0 ≤ B := by simpa using hB 0 (Nat.zero_le K)
  have hwK : 0 ≤ w (K - 1) := hw0.trans (hw (Nat.zero_le _))
  rw [sum_range_by_parts]
  calc
    _ ≤ ‖w (K - 1) • ∑ n ∈ range K, z n‖ +
        ‖∑ i ∈ range (K - 1), (w (i + 1) - w i) • ∑ n ∈ range (i + 1), z n‖ :=
      norm_sub_le _ _
    _ ≤ w (K - 1) * B + ∑ i ∈ range (K - 1), (w (i + 1) - w i) * B := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hwK]
        exact mul_le_mul_of_nonneg_left (hB K le_rfl) hwK
      · apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro i hi
        have hd : 0 ≤ w (i + 1) - w i := sub_nonneg.mpr (hw (Nat.le_succ _))
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_left (hB (i + 1) (by have := mem_range.mp hi; omega)) hd
    _ = (2 * w (K - 1) - w 0) * B := by
      rw [← sum_mul, sum_range_sub]
      ring
    _ ≤ _ := by nlinarith

lemma monotone_log_natCast : Monotone (fun n : ℕ => Real.log n) := by
  intro m n hmn
  by_cases hm : m = 0
  · simpa [hm] using Real.log_natCast_nonneg n
  · exact Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))
      (Nat.cast_le.mpr hmn)

lemma norm_log_weighted_prefix {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (z : ℕ → E) (K : ℕ) (B : ℝ)
    (hB : ∀ j ≤ K, ‖∑ n ∈ range j, z n‖ ≤ B) :
    ‖∑ n ∈ range K, Real.log n • z n‖ ≤ 2 * Real.log K * B := by
  have hB0 : 0 ≤ B := by simpa using hB 0 (Nat.zero_le K)
  apply (norm_monotone_weighted_prefix (fun n => Real.log n)
    monotone_log_natCast (by simp) z K B hB).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (monotone_log_natCast (Nat.sub_le K 1)) (by norm_num)) hB0

/-- Truncating a prefix by a second prefix takes the minimum of the lengths. -/
lemma sum_range_ite_lt {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (j k : ℕ) :
    (∑ n ∈ range j, if n < k then f n else 0) = ∑ n ∈ range (min j k), f n := by
  classical
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter, mem_range, lt_min_iff]

/-- A uniform bound for all row-prefix cutoffs also controls a common monotone
weight in the inner variable, at the standard partial-summation cost. -/
lemma norm_monotone_weighted_rows {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (s : Finset ι) (A : ι → ℕ → E) (K : ι → ℕ)
    (L : ℕ) (hK : ∀ m ∈ s, K m ≤ L)
    (w : ℕ → ℝ) (hw : Monotone w) (hw0 : 0 ≤ w 0) (B : ℝ)
    (hB : ∀ F : ι → ℕ, (∀ m ∈ s, F m ≤ K m) →
      ‖∑ m ∈ s, ∑ n ∈ range (F m), A m n‖ ≤ B) :
    ‖∑ m ∈ s, ∑ n ∈ range (K m), w n • A m n‖ ≤ 2 * w L * B := by
  classical
  let z : ℕ → E := fun n => ∑ m ∈ s, if n < K m then A m n else 0
  have hz (j : ℕ) :
      (∑ n ∈ range j, z n) = ∑ m ∈ s, ∑ n ∈ range (min j (K m)), A m n := by
    dsimp only [z]
    rw [sum_comm]
    apply sum_congr rfl
    intro m hm
    exact sum_range_ite_lt _ _ _
  have hzb (j : ℕ) : ‖∑ n ∈ range j, z n‖ ≤ B := by
    rw [hz]
    exact hB (fun m => min j (K m)) (fun m hm => min_le_right _ _)
  have hB0 : 0 ≤ B := by simpa using hzb 0
  have he : (∑ n ∈ range L, w n • z n) =
      ∑ m ∈ s, ∑ n ∈ range (K m), w n • A m n := by
    dsimp only [z]
    simp_rw [smul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro m hm
    simp_rw [smul_ite, smul_zero]
    rw [sum_range_ite_lt, min_eq_right (hK m hm)]
  rw [← he]
  apply (norm_monotone_weighted_prefix w hw hw0 z L B
    (fun j hj => hzb j)).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hw (Nat.sub_le L 1)) (by norm_num)) hB0


/-- The logarithmically weighted Type-I estimate. The logarithm at zero is zero,
so that the zero index has no contribution. -/
theorem near_rational_typeI_log_bound {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ)
    (hθ : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (s : Finset ℕ) (R : ℕ) (hs : ∀ m ∈ s, 0 < m ∧ m ≤ R)
    (hR : 8 * R ≤ q) (K : ℕ → ℕ) (L : ℕ)
    (hK : ∀ m ∈ s, K m ≤ L) (c : ℕ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hc : ∀ m ∈ s, ‖c m‖ ≤ C) :
    ‖∑ m ∈ s, c m * ∑ n ∈ range (K m),
        (Real.log n : ℂ) * phase (θ * m * n)‖ ≤
      4 * C * Real.log L * q * (2 + Real.log q) := by
  have h := norm_monotone_weighted_rows s
    (fun m n => c m * phase (θ * m * n)) K L hK
    (fun n => Real.log n) monotone_log_natCast (by simp)
    (2 * C * q * (2 + Real.log q)) (by
      intro F hF
      simpa only [← mul_sum] using
        near_rational_typeI_bound a haq θ hθ s R hs hR F c C hC hc)
  have he : (∑ m ∈ s, ∑ n ∈ range (K m),
      Real.log n • (c m * phase (θ * m * n))) =
      ∑ m ∈ s, c m * ∑ n ∈ range (K m),
        (Real.log n : ℂ) * phase (θ * m * n) := by
    simp only [Complex.real_smul, mul_sum]
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro n hn
    ring
  rw [he] at h
  convert h using 1; ring

lemma sum_Ioc_zero_eq_sum_range_succ {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (K : ℕ) :
    (∑ n ∈ Ioc 0 K, f n) = ∑ n ∈ range K, f (n + 1) := by
  simpa only [Nat.Ico_zero_eq_range, Ico_add_one_add_one_eq_Ioc] using
    (sum_Ico_add' f 0 K 1).symm

/-- Excluding zero from the inner prefixes does not enlarge the Type-I bound:
the shift is absorbed into an outer coefficient of unit modulus. -/
theorem near_rational_typeI_positive_bound {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ)
    (hθ : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (s : Finset ℕ) (R : ℕ) (hs : ∀ m ∈ s, 0 < m ∧ m ≤ R)
    (hR : 8 * R ≤ q) (K : ℕ → ℕ) (c : ℕ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hc : ∀ m ∈ s, ‖c m‖ ≤ C) :
    ‖∑ m ∈ s, c m * ∑ n ∈ Ioc 0 (K m), phase (θ * m * n)‖ ≤
      2 * C * q * (2 + Real.log q) := by
  have hphase (m n : ℕ) :
      phase (θ * m * (n + 1 : ℕ)) = phase (θ * m) * phase (θ * m * n) := by
    push_cast
    rw [show θ * m * ((n : ℝ) + 1) = θ * m + θ * m * n by ring, phase_add]
  have he : (∑ m ∈ s, c m * ∑ n ∈ Ioc 0 (K m), phase (θ * m * n)) =
      ∑ m ∈ s, (c m * phase (θ * m)) *
        ∑ n ∈ range (K m), phase (θ * m * n) := by
    simp_rw [sum_Ioc_zero_eq_sum_range_succ, hphase, ← mul_sum, mul_assoc]
  rw [he]
  apply near_rational_typeI_bound a haq θ hθ s R hs hR K
    (fun m => c m * phase (θ * m)) C hC
  intro m hm
  simpa only [norm_mul, norm_phase, mul_one] using hc m hm

lemma sum_Ioc_zero_eq_sum_range_of_zero {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (hf : f 0 = 0) (K : ℕ) :
    (∑ n ∈ Ioc 0 K, f n) = ∑ n ∈ range (K + 1), f n := by
  rw [sum_range_succ', hf, add_zero, sum_Ioc_zero_eq_sum_range_succ]

/-- The logarithmically weighted estimate in positive-index form. -/
theorem near_rational_typeI_positive_log_bound {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ)
    (hθ : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (s : Finset ℕ) (R : ℕ) (hs : ∀ m ∈ s, 0 < m ∧ m ≤ R)
    (hR : 8 * R ≤ q) (K : ℕ → ℕ) (L : ℕ)
    (hK : ∀ m ∈ s, K m ≤ L) (c : ℕ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hc : ∀ m ∈ s, ‖c m‖ ≤ C) :
    ‖∑ m ∈ s, c m * ∑ n ∈ Ioc 0 (K m),
        (Real.log n : ℂ) * phase (θ * m * n)‖ ≤
      4 * C * Real.log (L + 1) * q * (2 + Real.log q) := by
  have he (m : ℕ) :
      (∑ n ∈ Ioc 0 (K m), (Real.log n : ℂ) * phase (θ * m * n)) =
        ∑ n ∈ range (K m + 1), (Real.log n : ℂ) * phase (θ * m * n) := by
    exact sum_Ioc_zero_eq_sum_range_of_zero _ (by simp) _
  simp_rw [he]
  simpa only [Nat.cast_add, Nat.cast_one] using
    near_rational_typeI_log_bound a haq θ hθ s R hs hR
      (fun m => K m + 1) (L + 1) (fun m hm => Nat.add_le_add_right (hK m hm) 1)
      c C hC hc

/-- Multiplication by coefficients bounded by one cannot increase energy. -/
lemma energy_mul_mask_le {ι : Type*} (s : Finset ι) (a x : ι → ℂ)
    (hx : ∀ m ∈ s, ‖x m‖ ≤ 1) :
    (∑ m ∈ s, ‖a m * x m‖ ^ 2) ≤ ∑ m ∈ s, ‖a m‖ ^ 2 := by
  apply sum_le_sum
  intro m hm
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hx m hm) (norm_nonneg (a m))

/-- Exponential perturbation of the rational energy estimate. -/
theorem perturbed_rational_bilinear_energy_bound_fibers {ι κ : Type*} {q : ℕ} [NeZero q]
    (u : (ZMod q)ˣ) (s : Finset ι) (t : Finset κ)
    (ρ : ι → ZMod q) (σ : κ → ZMod q)
    (a x : ι → ℂ) (b y : κ → ℂ) (z : ℂ)
    (K L : ℕ) (hK : ∀ r, (s.filter (fun m => ρ m = r)).card ≤ K)
    (hL : ∀ v, (t.filter (fun n => σ n = v)).card ≤ L)
    (hx : ∀ m ∈ s, ‖x m‖ ≤ 1) (hy : ∀ n ∈ t, ‖y n‖ ≤ 1) :
    ‖∑ m ∈ s, ∑ n ∈ t,
        a m * b n * ZMod.stdAddChar ((u : ZMod q) * ρ m * σ n) *
          Complex.exp (z * x m * y n)‖ ≤
      Real.exp ‖z‖ * Real.sqrt ((q : ℝ) * ((K : ℝ) * ∑ m ∈ s, ‖a m‖ ^ 2) * ((L : ℝ) * ∑ n ∈ t, ‖b n‖ ^ 2)) := by
  classical
  let B : ℝ := Real.sqrt ((q : ℝ) * ((K : ℝ) * ∑ m ∈ s, ‖a m‖ ^ 2) * ((L : ℝ) * ∑ n ∈ t, ‖b n‖ ^ 2))
  let T : ℕ → ℂ := fun k => ∑ m ∈ s, ∑ n ∈ t,
    (a m * b n * ZMod.stdAddChar ((u : ZMod q) * ρ m * σ n)) *
      ((z * x m * y n) ^ k / (k.factorial : ℂ))
  have hsum : HasSum T
      (∑ m ∈ s, ∑ n ∈ t,
        a m * b n * ZMod.stdAddChar ((u : ZMod q) * ρ m * σ n) *
          Complex.exp (z * x m * y n)) := by
    apply hasSum_sum
    intro m hm
    apply hasSum_sum
    intro n hn
    simpa only [Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp (z * x m * y n)).mul_left
        (a m * b n * ZMod.stdAddChar ((u : ZMod q) * ρ m * σ n))
  have hterm (k : ℕ) : T k = (z ^ k / (k.factorial : ℂ)) *
      ∑ m ∈ s, ∑ n ∈ t,
        (a m * x m ^ k) * (b n * y n ^ k) *
          ZMod.stdAddChar ((u : ZMod q) * ρ m * σ n) := by
    dsimp [T]
    rw [mul_sum]
    apply sum_congr rfl
    intro m hm
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    simp only [mul_pow]
    ring
  have hbound (k : ℕ) : ‖T k‖ ≤ (‖z‖ ^ k / (k.factorial : ℝ)) * B := by
    rw [hterm, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.le_sqrt_of_sq_le
    apply (rational_bilinear_bound_fibers u s t ρ σ _ _ K L hK hL).trans
    have hxa : (∑ m ∈ s, ‖a m * x m ^ k‖ ^ 2) ≤ ∑ m ∈ s, ‖a m‖ ^ 2 := by
      apply energy_mul_mask_le
      intro m hm
      simpa only [norm_pow, one_pow] using
        pow_le_pow_left₀ (norm_nonneg _) (hx m hm) k
    have hyb : (∑ n ∈ t, ‖b n * y n ^ k‖ ^ 2) ≤ ∑ n ∈ t, ‖b n‖ ^ 2 := by
      apply energy_mul_mask_le
      intro n hn
      simpa only [norm_pow, one_pow] using
        pow_le_pow_left₀ (norm_nonneg _) (hy n hn) k
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hxa (Nat.cast_nonneg K)) (Nat.cast_nonneg q))
      (mul_le_mul_of_nonneg_left hyb (Nat.cast_nonneg L)) (by positivity) (by positivity)
  have hmajorant : HasSum (fun k : ℕ => (‖z‖ ^ k / (k.factorial : ℝ)) * B)
      (Real.exp ‖z‖ * B) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ‖z‖).mul_right B
  exact hsum.norm_le_of_bounded hmajorant hbound


/-- Natural-index form with arbitrary coefficient energies. -/
theorem near_rational_bilinear_energy_bound_nat {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ) (s t : Finset ℕ) (M N : ℕ)
    (hM : 0 < M) (hN : 0 < N)
    (herror : |θ - (a : ℝ) / q| * M * N ≤ 1)
    (hs : ∀ m ∈ s, m ≤ M) (ht : ∀ n ∈ t, n ≤ N)
    (c d : ℕ → ℂ) :
    ‖∑ m ∈ s, ∑ n ∈ t, c m * d n * phase (θ * m * n)‖ ≤
      Real.exp (2 * Real.pi) *
        Real.sqrt ((q : ℝ) * ((M / q + 1 : ℕ) * (∑ m ∈ s, ‖c m‖ ^ 2)) *
          ((N / q + 1 : ℕ) * (∑ n ∈ t, ‖d n‖ ^ 2))) := by
  classical
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime a haq
  let x : ℕ → ℂ := fun m => (m : ℂ) / M
  let y : ℕ → ℂ := fun n => (n : ℂ) / N
  let z : ℂ := (2 * Real.pi : ℝ) * Complex.I *
    ((θ - (a : ℝ) / q : ℝ) : ℂ) * (M : ℂ) * (N : ℂ)
  have hx (m : ℕ) (hm : m ∈ s) : ‖x m‖ ≤ 1 := by
    dsimp [x]
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    exact (div_le_one hMR).mpr (Nat.cast_le.mpr (hs m hm))
  have hy (n : ℕ) (hn : n ∈ t) : ‖y n‖ ≤ 1 := by
    dsimp [y]
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    exact (div_le_one hNR).mpr (Nat.cast_le.mpr (ht n hn))
  have hz : ‖z‖ ≤ 2 * Real.pi := by
    dsimp [z]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, Complex.norm_natCast, abs_of_nonneg (le_of_lt Real.pi_pos),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_one]
    calc
      _ = (2 * Real.pi) * (|θ - (a : ℝ) / q| * M * N) := by ring
      _ ≤ (2 * Real.pi) * 1 := mul_le_mul_of_nonneg_left herror (by positivity)
      _ = _ := by ring
  have hphase (m n : ℕ) :
      phase (θ * m * n) =
        ZMod.stdAddChar ((u : ZMod q) * (m : ZMod q) * (n : ZMod q)) *
          Complex.exp (z * x m * y n) := by
    change phase (θ * m * n) =
      ZMod.stdAddChar ((ZMod.unitOfCoprime a haq : ZMod q) *
        (m : ZMod q) * (n : ZMod q)) * Complex.exp (z * x m * y n)
    rw [rational_phase_nat]
    unfold phase
    rw [← Complex.exp_add]
    congr 1
    dsimp [z, x, y]
    push_cast
    field_simp [hMC, hNC]
    ring
  have he :
      (∑ m ∈ s, ∑ n ∈ t, c m * d n * phase (θ * m * n)) =
        ∑ m ∈ s, ∑ n ∈ t,
          c m * d n * ZMod.stdAddChar ((u : ZMod q) * (m : ZMod q) * (n : ZMod q)) *
            Complex.exp (z * x m * y n) := by
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro n hn
    rw [hphase]
    ring
  rw [he]
  apply (perturbed_rational_bilinear_energy_bound_fibers u s t
    (fun m : ℕ => (m : ZMod q)) (fun n : ℕ => (n : ZMod q))
    c x d y z (M / q + 1) (N / q + 1)
    (card_natCast_fiber_le s M hs) (card_natCast_fiber_le t N ht)
    hx hy).trans
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hz) (Real.sqrt_nonneg _)


/-- Hyperbolic truncation with arbitrary coefficient energies. -/
theorem near_rational_hyperbola_energy_bound {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ) (s t : Finset ℕ) (M N X : ℕ)
    (hM : 0 < M) (hN : 0 < N)
    (herror : |θ - (a : ℝ) / q| * M * N ≤ 1)
    (hs : ∀ m ∈ s, 0 < m ∧ m ≤ M) (ht : ∀ n ∈ t, n ≤ N)
    (c d : ℕ → ℂ) :
    ‖∑ m ∈ s, ∑ n ∈ t.filter (fun n => m * n ≤ X),
        c m * d n * phase (θ * m * n)‖ ≤
      (2 + Real.log (N + 1)) * (Real.exp (2 * Real.pi) *
        Real.sqrt ((q : ℝ) * ((M / q + 1 : ℕ) * (∑ m ∈ s, ‖c m‖ ^ 2)) *
          ((N / q + 1 : ℕ) * (∑ n ∈ t, ‖d n‖ ^ 2)))) := by
  classical
  let H : ℕ := N + 1
  letI : NeZero H := ⟨by dsimp [H]; omega⟩
  let ν : ℕ → ZMod H := fun n => (n : ZMod H)
  let F : ℕ → ℕ := fun m => min (X / m + 1) H
  let A : ℕ → ℕ → ℂ := fun m n => c m * d n * phase (θ * m * n)
  let B : ℝ := Real.exp (2 * Real.pi) *
    Real.sqrt ((q : ℝ) * ((M / q + 1 : ℕ) * (∑ m ∈ s, ‖c m‖ ^ 2)) *
      ((N / q + 1 : ℕ) * (∑ n ∈ t, ‖d n‖ ^ 2)))
  have hrect : ∀ f g : ℕ → ℂ,
      (∀ m ∈ s, ‖f m‖ ≤ 1) → (∀ n ∈ t, ‖g n‖ ≤ 1) →
      ‖∑ m ∈ s, ∑ n ∈ t, f m * g n * A m n‖ ≤ B := by
    intro f g hf hg
    have hfg := near_rational_bilinear_energy_bound_nat a haq θ s t M N hM hN
      herror (fun m hm => (hs m hm).2) ht
      (fun m => f m * c m) (fun n => g n * d n)
    have hcE : (∑ m ∈ s, ‖f m * c m‖ ^ 2) ≤ ∑ m ∈ s, ‖c m‖ ^ 2 := by
      simpa only [mul_comm] using energy_mul_mask_le s c f hf
    have hdE : (∑ n ∈ t, ‖g n * d n‖ ^ 2) ≤ ∑ n ∈ t, ‖d n‖ ^ 2 := by
      simpa only [mul_comm] using energy_mul_mask_le t d g hg
    have hb : Real.exp (2 * Real.pi) *
        Real.sqrt ((q : ℝ) * ((M / q + 1 : ℕ) * ∑ m ∈ s, ‖f m * c m‖ ^ 2) *
          ((N / q + 1 : ℕ) * ∑ n ∈ t, ‖g n * d n‖ ^ 2)) ≤ B := by
      apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt _) (by positivity)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hcE (Nat.cast_nonneg _)) (Nat.cast_nonneg q))
        (mul_le_mul_of_nonneg_left hdE (Nat.cast_nonneg _)) (by positivity) (by positivity)
    convert hfg.trans hb using 1
    congr 1
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro n hn
    dsimp [A]
    ring
  have h := bilinear_prefix_completion s t ν F
    (fun m hm => min_le_right _ _) A B (by positivity) hrect
  have hcut (m : ℕ) (hm : m ∈ s) (n : ℕ) (hn : n ∈ t) :
      (ν n).val < F m ↔ m * n ≤ X := by
    have hnH : n < H := by dsimp [H]; exact Nat.lt_succ_of_le (ht n hn)
    dsimp [ν, F]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hnH, lt_min_iff]
    simp only [hnH, and_true, Nat.lt_succ_iff]
    rw [Nat.le_div_iff_mul_le (hs m hm).1, Nat.mul_comm n m]
  have he :
      (∑ m ∈ s, ∑ n ∈ t.filter (fun n => m * n ≤ X), A m n) =
        ∑ m ∈ s, ∑ n ∈ t, if (ν n).val < F m then A m n else 0 := by
    apply sum_congr rfl
    intro m hm
    rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    simp only [hcut m hm n hn]
  rw [← he] at h
  simpa only [A, B, H, Nat.cast_add, Nat.cast_one] using h


#print axioms near_rational_hyperbola_energy_bound

#print axioms near_rational_bilinear_energy_bound_nat
#print axioms perturbed_rational_bilinear_energy_bound_fibers

#print axioms near_rational_typeI_positive_bound
#print axioms near_rational_typeI_positive_log_bound

#print axioms near_rational_typeI_log_bound
#print axioms norm_monotone_weighted_rows

#print axioms near_rational_typeI_bound

#print axioms bilinear_prefix_completion
#print axioms near_rational_hyperbola_bound

#print axioms prefixCoeff_inversion
#print axioms sum_prefixMajorant_le

#print axioms stdAddChar_prefix_bound

#print axioms near_rational_bilinear_bound_nat

#print axioms rational_bilinear_bound_nat
#print axioms perturbed_rational_bilinear_bound_fibers

#print axioms rational_bilinear_bound_fibers
#print axioms rational_bilinear_bound_fibers_bounded

#print axioms near_rational_bilinear_bound
#print axioms perturbed_rational_bilinear_bound
#print axioms finiteFourier_energy
#print axioms rational_bilinear_bound
#print axioms rational_bilinear_bound_unit
#print axioms rational_bilinear_bound_finset

end Erdos972ExponentialSum
