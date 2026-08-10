import FormalConjectures.Util.ProblemImports

open Finset

/--
A048153: $a(n) = \sum_{k=1}^n (k^2 \bmod n)$.
This sequence is defined in Lean as the sum of $k^2 \bmod n$ for $k \in \{0, 1, \dots, n-1\}$.
-/
def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)


/-! # Section from Dev/Basic.lean -/

section

open Complex Finset

namespace OEIS48153

/-! ## The function `E x = exp (2 π I x)` and basic properties -/

noncomputable def E (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

lemma E_add (x y : ℝ) : E (x + y) = E x * E y := by
  simp only [E, ofReal_add]
  rw [← Complex.exp_add]
  ring_nf

lemma E_intCast (n : ℤ) : E n = 1 := by
  have : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ)
      = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [E, this, Complex.exp_int_mul_two_pi_mul_I]

lemma E_natCast (n : ℕ) : E n = 1 := by
  simpa using E_intCast n

lemma E_zero : E 0 = 1 := by simpa using E_natCast 0

lemma E_add_int (x : ℝ) (n : ℤ) : E (x + n) = E x := by
  rw [E_add, E_intCast, mul_one]

lemma E_add_nat (x : ℝ) (n : ℕ) : E (x + n) = E x := by
  rw [E_add, E_natCast, mul_one]

lemma E_eq_exp_mul_I (x : ℝ) : E x = Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I) := by
  rw [E]
  congr 1
  push_cast
  ring

lemma E_re (x : ℝ) : (E x).re = Real.cos (2 * Real.pi * x) := by
  rw [E_eq_exp_mul_I, Complex.exp_ofReal_mul_I_re]

lemma E_im (x : ℝ) : (E x).im = Real.sin (2 * Real.pi * x) := by
  rw [E_eq_exp_mul_I, Complex.exp_ofReal_mul_I_im]

lemma E_mul_I_im (x : ℝ) : (Complex.I * E x).im = Real.cos (2 * Real.pi * x) := by
  simp [Complex.mul_im, E_re, E_im]

lemma nat_div_real_split (a n : ℕ) (hn : (n : ℝ) ≠ 0) :
    (a : ℝ) / n = ((a % n : ℕ) : ℝ) / n + ((a / n : ℕ) : ℝ) := by
  have h1 : ((a % n : ℕ) : ℝ) + ((a / n : ℕ) : ℝ) * (n : ℝ) = (a : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.mod_add_div' a n)
  field_simp
  linarith [h1]

/-- If `a ≡ b (mod n)` then `E (a / n) = E (b / n)`. -/
lemma E_div_congr {n a b : ℕ} (h : a % n = b % n) :
    E ((a : ℝ) / n) = E ((b : ℝ) / n) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [nat_div_real_split a n hn', nat_div_real_split b n hn', E_add_nat, E_add_nat, h]

/-! ## Sums of periodic functions over `range` -/

lemma sum_range_mul_of_periodic {M : Type*} [AddCommMonoid M] (f : ℕ → M) (d : ℕ)
    (hf : ∀ k, f (k + d) = f k) (c : ℕ) :
    ∑ k ∈ range (c * d), f k = c • (∑ k ∈ range d, f k) := by
  have hshift : ∀ (j : ℕ) (k : ℕ), f (j * d + k) = f k := by
    intro j
    induction j with
    | zero => intro k; simp
    | succ j ihj =>
      intro k
      have : (j + 1) * d + k = (j * d + k) + d := by ring
      rw [this, hf, ihj]
  induction c with
  | zero => simp
  | succ c ih =>
    have h1 : (c + 1) * d = c * d + d := by ring
    rw [h1, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl fun k _ => hshift c k

/-! ## Quadratic Gauss sums -/

/-- The quadratic Gauss sum `∑_{k=0}^{q-1} exp(2 π i m k² / q)`. -/
noncomputable def gq (m q : ℕ) : ℂ := ∑ k ∈ range q, E ((m * k ^ 2 : ℕ) / q)

lemma gq_term_periodic (m q : ℕ) (k : ℕ) :
    E (((m * (k + q) ^ 2 : ℕ) : ℝ) / q) = E (((m * k ^ 2 : ℕ) : ℝ) / q) := by
  refine E_div_congr ?_
  have : m * (k + q) ^ 2 = m * k ^ 2 + (m * (2 * k) + m * q) * q := by ring
  simp [this, Nat.add_mul_mod_self_right]

/-- If `q ∣ n` then the Gauss-type sum over `range n` collapses. -/
lemma sum_range_E_dvd (m q n : ℕ) (h : q ∣ n) :
    ∑ k ∈ range n, E (((m * k ^ 2 : ℕ) : ℝ) / q) = (n / q : ℕ) • gq m q := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    obtain rfl : n = 0 := Nat.eq_zero_of_zero_dvd h
    simp [gq]
  obtain ⟨c, rfl⟩ := h
  rw [Nat.mul_div_cancel_left c hq, mul_comm q c]
  exact sum_range_mul_of_periodic _ q (gq_term_periodic m q) c

/-- `gq` depends only on `m` mod `q`. -/
lemma gq_congr {m m' q : ℕ} (h : m % q = m' % q) : gq m q = gq m' q := by
  refine Finset.sum_congr rfl fun k _ => ?_
  refine E_div_congr ?_
  exact (Nat.ModEq.mul_right (k ^ 2) h)

/-! ## Sums over `ZMod q` -/

lemma sum_zmod_eq_sum_range {M : Type*} [AddCommMonoid M] (q : ℕ) [NeZero q] (f : ℕ → M) :
    ∑ a : ZMod q, f a.val = ∑ k ∈ range q, f k := by
  refine Finset.sum_nbij' (fun a => a.val) (fun k => (k : ZMod q)) ?_ ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro k _
    exact Finset.mem_univ _
  · intro a _
    simp [ZMod.natCast_val, ZMod.cast_id]
  · intro k hk
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hk)
  · intro a _
    rfl

lemma gq_eq_sum_zmod (m q : ℕ) [NeZero q] :
    gq m q = ∑ a : ZMod q, E (((m * a.val ^ 2 : ℕ) : ℝ) / q) := by
  rw [gq, ← sum_zmod_eq_sum_range q (fun k => E (((m * k ^ 2 : ℕ) : ℝ) / q))]

end OEIS48153

end

/-! # Section from Dev/Theta.lean -/

section

open Complex Finset Filter Topology Real

namespace OEIS48153

/-! ## Tail bound for the two-variable Jacobi theta function at real `z` -/

lemma jacobiTheta₂_term_zero (z τ : ℂ) : jacobiTheta₂_term 0 z τ = 1 := by
  simp [jacobiTheta₂_term]

lemma norm_theta2_sub_one_le {x : ℝ} {τ : ℂ} (hτ : 0 < τ.im) :
    ‖jacobiTheta₂ x τ - 1‖ ≤ 2 * rexp (-Real.pi * τ.im) / (1 - rexp (-Real.pi * τ.im)) := by
  set u : ℝ := rexp (-Real.pi * τ.im) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have hu1 : u < 1 := by
    rw [hu, Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) hτ
  set f : ℤ → ℂ := fun n => jacobiTheta₂_term n (x : ℂ) τ with hf
  have hnorm : ∀ n : ℤ, ‖f n‖ = rexp (-Real.pi * n ^ 2 * τ.im) := by
    intro n
    rw [hf]
    rw [norm_jacobiTheta₂_term n (x : ℂ) τ]
    norm_num [Complex.ofReal_im]
  have habs : ∀ n : ℤ, (n.natAbs : ℝ) ≤ (n : ℝ) ^ 2 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hn
      have h2 : ((n.natAbs : ℝ)) = |(n : ℝ)| := by
        simp [Nat.cast_natAbs]
      rw [h2]
      nlinarith [abs_nonneg (n : ℝ), sq_abs (n : ℝ)]
  have hbound : ∀ n : ℤ, ‖f n‖ ≤ u ^ n.natAbs := by
    intro n
    rw [hnorm n, hu, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (habs n) (mul_pos Real.pi_pos hτ).le]
  have hgeom : Summable (fun n : ℕ => u ^ (n + 1)) := by
    simpa [pow_succ'] using (summable_geometric_of_lt_one hu0.le hu1).mul_left u
  have h0 : Summable (fun n : ℕ => f n) :=
    Summable.of_norm_bounded (g := fun n : ℕ => u ^ n)
      (summable_geometric_of_lt_one hu0.le hu1) (fun n => by simpa using hbound n)
  have h1 : Summable (fun n : ℕ => ‖f (n + 1)‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hgeom
    simpa using hbound (n + 1)
  have hboundneg : ∀ n : ℕ, ‖f (-((n : ℤ) + 1))‖ ≤ u ^ (n + 1) := by
    intro n
    have hb := hbound (-((n : ℤ) + 1))
    have hAbs : ((-((n : ℤ) + 1)).natAbs) = n + 1 := by
      rw [Int.natAbs_neg]
      exact_mod_cast Int.natAbs_natCast (n + 1)
    rwa [hAbs] at hb
  have h2 : Summable (fun n : ℕ => ‖f (-(n + 1))‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hgeom
    exact hboundneg n
  have key : HasSum f ((∑' n : ℕ, f n) + ∑' n : ℕ, f (-(n + 1))) :=
    HasSum.of_nat_of_neg_add_one h0.hasSum (h2.of_norm).hasSum
  have hΘ : jacobiTheta₂ (x : ℂ) τ = (∑' n : ℕ, f n) + ∑' n : ℕ, f (-(n + 1)) :=
    (hasSum_jacobiTheta₂_term (x : ℂ) hτ).unique key
  have hsplit : (∑' n : ℕ, f n) = f 0 + ∑' n : ℕ, f (n + 1) := h0.tsum_eq_zero_add
  have hf0 : f 0 = 1 := jacobiTheta₂_term_zero _ _
  have hgeomsum : (∑' n : ℕ, u ^ (n + 1)) = u * (1 - u)⁻¹ := by
    simp_rw [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_lt_one hu0.le hu1]
  have hA : ‖∑' n : ℕ, f (n + 1)‖ ≤ u * (1 - u)⁻¹ := by
    calc ‖∑' n : ℕ, f (n + 1)‖ ≤ ∑' n : ℕ, ‖f (n + 1)‖ := norm_tsum_le_tsum_norm h1
    _ ≤ ∑' n : ℕ, u ^ (n + 1) := h1.tsum_le_tsum (fun n => by simpa using hbound (n + 1)) hgeom
    _ = u * (1 - u)⁻¹ := hgeomsum
  have hB : ‖∑' n : ℕ, f (-(n + 1))‖ ≤ u * (1 - u)⁻¹ := by
    calc ‖∑' n : ℕ, f (-(n + 1))‖ ≤ ∑' n : ℕ, ‖f (-(n + 1))‖ := norm_tsum_le_tsum_norm h2
    _ ≤ ∑' n : ℕ, u ^ (n + 1) := h2.tsum_le_tsum (fun n => hboundneg n) hgeom
    _ = u * (1 - u)⁻¹ := hgeomsum
  have : jacobiTheta₂ (x : ℂ) τ - 1 = (∑' n : ℕ, f (n + 1)) + ∑' n : ℕ, f (-(n + 1)) := by
    rw [hΘ, hsplit, hf0]; ring
  rw [this]
  calc ‖(∑' n : ℕ, f (n + 1)) + ∑' n : ℕ, f (-(n + 1))‖
      ≤ ‖∑' n : ℕ, f (n + 1)‖ + ‖∑' n : ℕ, f (-(n + 1))‖ := norm_add_le _ _
  _ ≤ u * (1 - u)⁻¹ + u * (1 - u)⁻¹ := add_le_add hA hB
  _ = 2 * u / (1 - u) := by ring

/-- Convenient form: if `1 ≤ im τ` then `‖jacobiTheta₂ x τ - 1‖ ≤ 4 exp(-π im τ)`. -/
lemma norm_theta2_sub_one_le' {x : ℝ} {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta₂ x τ - 1‖ ≤ 4 * rexp (-Real.pi * τ.im) := by
  have hτ0 : 0 < τ.im := lt_of_lt_of_le one_pos hτ
  refine (norm_theta2_sub_one_le hτ0).trans ?_
  set u : ℝ := rexp (-Real.pi * τ.im) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have husmall : u ≤ rexp (-1) := by
    rw [hu, Real.exp_le_exp]
    nlinarith [Real.pi_gt_three]
  have h12 : rexp (-1) ≤ 1/2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hu12 : u ≤ 1/2 := husmall.trans h12
  rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - u)]
  nlinarith [hu0.le]

/-! ## Splitting the theta series into residue classes mod `M` -/

lemma theta_split (M : ℕ) (hM : 0 < M) (c : ℝ) (u u' : ℤ)
    (hc2 : (M : ℝ) ^ 2 * c = 2 * u) (hc1 : (M : ℝ) * c = u') {w : ℂ} (hw : 0 < w.im) :
    jacobiTheta₂ 0 ((c : ℂ) + w) =
      ∑ r ∈ range M, cexp ((π : ℂ) * I * r ^ 2 * c) * cexp ((π : ℂ) * I * r ^ 2 * w) *
        jacobiTheta₂ ((M : ℂ) * r * w) ((M : ℂ) ^ 2 * w) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have him : 0 < ((c : ℂ) + w).im := by simpa using hw
  have him2 : 0 < ((M : ℂ) ^ 2 * w).im := by
    have : ((M : ℂ) ^ 2 * w).im = (M : ℝ) ^ 2 * w.im := by
      simp [Complex.mul_im]
      norm_cast
      ring
    rw [this]
    positivity
  set F : ℤ → ℂ := fun n => cexp ((π : ℂ) * I * n ^ 2 * ((c : ℂ) + w)) with hF
  have HF : HasSum F (jacobiTheta₂ 0 ((c : ℂ) + w)) := by
    have := hasSum_jacobiTheta₂_term 0 him
    refine this.congr_fun fun n => ?_
    simp [jacobiTheta₂_term, hF]
  -- reindex over (Fin M) × ℤ  via (r, m) ↦ m * M + r
  set e : Fin M × ℤ ≃ ℤ :=
    (Equiv.prodComm (Fin M) ℤ).trans (Int.divModEquiv M).symm with he
  have HF2 : HasSum (F ∘ e) (jacobiTheta₂ 0 ((c : ℂ) + w)) := (e.hasSum_iff).mpr HF
  -- fiberwise sums
  have hc2' : ((M : ℂ)) ^ 2 * (c : ℂ) = 2 * (u : ℂ) := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hc2
    push_cast at this ⊢
    exact this
  have hc1' : ((M : ℂ)) * (c : ℂ) = (u' : ℂ) := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hc1
    push_cast at this ⊢
    exact this
  have hfiber : ∀ r : Fin M,
      HasSum (fun m : ℤ => F (e (r, m)))
        (cexp ((π : ℂ) * I * (r : ℕ) ^ 2 * c) * cexp ((π : ℂ) * I * (r : ℕ) ^ 2 * w) *
          jacobiTheta₂ ((M : ℂ) * (r : ℕ) * w) ((M : ℂ) ^ 2 * w)) := by
    intro r
    have hterm := hasSum_jacobiTheta₂_term ((M : ℂ) * (r : ℕ) * w) him2
    have := hterm.mul_left
      (cexp ((π : ℂ) * I * (r : ℕ) ^ 2 * c) * cexp ((π : ℂ) * I * (r : ℕ) ^ 2 * w))
    refine this.congr_fun fun m => ?_
    show F (e (r, m)) = cexp ((π : ℂ) * I * (r : ℕ) ^ 2 * c) * cexp ((π : ℂ) * I * (r : ℕ) ^ 2 * w) *
        jacobiTheta₂_term m ((M : ℂ) * (r : ℕ) * w) ((M : ℂ) ^ 2 * w)
    symm
    have heval : e (r, m) = m * M + (r : ℤ) := rfl
    simp only [heval, jacobiTheta₂_term, hF]
    have harg : (π : ℂ) * I * ((m * M + (r : ℤ) : ℤ) : ℂ) ^ 2 * ((c : ℂ) + w) =
        ((π : ℂ) * I * (r : ℕ) ^ 2 * c + (π : ℂ) * I * (r : ℕ) ^ 2 * w +
          (2 * (π : ℂ) * I * m * ((M : ℂ) * (r : ℕ) * w) + (π : ℂ) * I * m ^ 2 * ((M : ℂ) ^ 2 * w)))
        + ((m ^ 2 * u + m * (r : ℤ) * u' : ℤ) : ℂ) * (2 * (π : ℂ) * I) := by
      have hrr : ((r : ℤ) : ℂ) = ((r : ℕ) : ℂ) := by push_cast; rfl
      push_cast
      linear_combination ((π : ℂ) * I * (m : ℂ) ^ 2) * hc2' +
        (2 * (π : ℂ) * I * (m : ℂ) * ((r : ℕ) : ℂ)) * hc1'
    conv_rhs => rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [← Complex.exp_add, ← Complex.exp_add]
  have Hg : HasSum
      (fun r : Fin M => cexp ((π : ℂ) * I * (r : ℕ) ^ 2 * c) * cexp ((π : ℂ) * I * (r : ℕ) ^ 2 * w) *
        jacobiTheta₂ ((M : ℂ) * (r : ℕ) * w) ((M : ℂ) ^ 2 * w))
      (jacobiTheta₂ 0 ((c : ℂ) + w)) :=
    HF2.prod_fiberwise hfiber
  have := (hasSum_fintype (fun r : Fin M =>
      cexp ((π : ℂ) * I * (r : ℕ) ^ 2 * c) * cexp ((π : ℂ) * I * (r : ℕ) ^ 2 * w) *
        jacobiTheta₂ ((M : ℂ) * (r : ℕ) * w) ((M : ℂ) ^ 2 * w))).unique Hg
  rw [← this, ← Fin.sum_univ_eq_sum_range (fun r : ℕ =>
      cexp ((π : ℂ) * I * r ^ 2 * c) * cexp ((π : ℂ) * I * r ^ 2 * w) *
        jacobiTheta₂ ((M : ℂ) * r * w) ((M : ℂ) ^ 2 * w)) M]

/-- Functional-equation form of each term in `theta_split`. -/
lemma theta_term_fe (M : ℕ) (hM : 0 < M) (r : ℕ) {w : ℂ} (hw : 0 < w.im) :
    cexp ((π : ℂ) * I * r ^ 2 * w) * jacobiTheta₂ ((M : ℂ) * r * w) ((M : ℂ) ^ 2 * w) =
      (1 / ((-I * ((M : ℂ) ^ 2 * w)) ^ (1 / 2 : ℂ))) *
        jacobiTheta₂ (((r : ℝ) / M : ℝ) : ℂ) (-1 / ((M : ℂ) ^ 2 * w)) := by
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have h1 := jacobiTheta₂_functional_equation ((M : ℂ) * r * w) ((M : ℂ) ^ 2 * w)
  rw [h1]
  have h2 : ((M : ℂ) * r * w) / ((M : ℂ) ^ 2 * w) = (((r : ℝ) / M : ℝ) : ℂ) := by
    push_cast
    field_simp
  have h3 : cexp ((π : ℂ) * I * r ^ 2 * w) * cexp (-(π : ℂ) * I * ((M : ℂ) * r * w) ^ 2 /
      ((M : ℂ) ^ 2 * w)) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    field_simp
    ring
  rw [h2]
  calc cexp ((π : ℂ) * I * r ^ 2 * w) *
        (1 / (-I * ((M : ℂ) ^ 2 * w)) ^ (1 / 2 : ℂ) *
          cexp (-(π : ℂ) * I * ((M : ℂ) * r * w) ^ 2 / ((M : ℂ) ^ 2 * w)) *
          jacobiTheta₂ (((r : ℝ) / M : ℝ) : ℂ) (-1 / ((M : ℂ) ^ 2 * w)))
      = (cexp ((π : ℂ) * I * r ^ 2 * w) * cexp (-(π : ℂ) * I * ((M : ℂ) * r * w) ^ 2 /
          ((M : ℂ) ^ 2 * w))) * (1 / (-I * ((M : ℂ) ^ 2 * w)) ^ (1 / 2 : ℂ) *
          jacobiTheta₂ (((r : ℝ) / M : ℝ) : ℂ) (-1 / ((M : ℂ) ^ 2 * w))) := by ring
  _ = (1 / ((-I * ((M : ℂ) ^ 2 * w)) ^ (1 / 2 : ℂ))) *
        jacobiTheta₂ (((r : ℝ) / M : ℝ) : ℂ) (-1 / ((M : ℂ) ^ 2 * w)) := by
      rw [h3, one_mul]

/-- Combined split + functional equation. -/
lemma theta_split_fe (M : ℕ) (hM : 0 < M) (c : ℝ) (u u' : ℤ)
    (hc2 : (M : ℝ) ^ 2 * c = 2 * u) (hc1 : (M : ℝ) * c = u') {w : ℂ} (hw : 0 < w.im) :
    jacobiTheta₂ 0 ((c : ℂ) + w) =
      (1 / ((-I * ((M : ℂ) ^ 2 * w)) ^ (1 / 2 : ℂ))) *
        ∑ r ∈ range M, cexp ((π : ℂ) * I * r ^ 2 * c) *
          jacobiTheta₂ (((r : ℝ) / M : ℝ) : ℂ) (-1 / ((M : ℂ) ^ 2 * w)) := by
  rw [theta_split M hM c u u' hc2 hc1 hw, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [mul_assoc, theta_term_fe M hM r hw]
  ring

/-! ## The limit of theta terms as `im τ → ∞` -/

lemma tendsto_theta2_one {α : Type*} {l : Filter α} {τ : α → ℂ} (x : ℝ)
    (hτ : Tendsto (fun a => (τ a).im) l atTop) :
    Tendsto (fun a => jacobiTheta₂ (x : ℂ) (τ a)) l (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ᶠ a in l, ‖jacobiTheta₂ (x : ℂ) (τ a) - 1‖ ≤ 4 * rexp (-π * (τ a).im) := by
    filter_upwards [hτ.eventually_ge_atTop 1] with a ha
    exact norm_theta2_sub_one_le' ha
  have hexp : Tendsto (fun a => 4 * rexp (-π * (τ a).im)) l (𝓝 0) := by
    have h1 : Tendsto (fun a => -π * (τ a).im) l atBot :=
      hτ.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos)
    have h2 : Tendsto (fun a => rexp (-π * (τ a).im)) l (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h1
    simpa using h2.const_mul 4
  exact squeeze_zero' (Eventually.of_forall fun a => norm_nonneg _) hbound hexp

lemma tendsto_sum_theta2 {α : Type*} {l : Filter α} {τ : α → ℂ} (M : ℕ) (φ : ℕ → ℂ) (x : ℕ → ℝ)
    (hτ : Tendsto (fun a => (τ a).im) l atTop) :
    Tendsto (fun a => ∑ r ∈ range M, φ r * jacobiTheta₂ ((x r : ℝ) : ℂ) (τ a)) l
      (𝓝 (∑ r ∈ range M, φ r)) := by
  have : ∀ r ∈ range M, Tendsto (fun a => φ r * jacobiTheta₂ ((x r : ℝ) : ℂ) (τ a)) l
      (𝓝 (φ r * 1)) := fun r _ => (tendsto_theta2_one (x r) hτ).const_mul (φ r)
  have h := tendsto_finset_sum (range M) this
  simpa using h

/-! ## cpow helper lemmas -/

lemma cpow_half_ofReal_pos_mul {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ≠ 0) :
    ((t : ℂ) * z) ^ (1 / 2 : ℂ) = (Real.sqrt t : ℂ) * z ^ (1 / 2 : ℂ) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have htz : (t : ℂ) * z ≠ 0 := mul_ne_zero htC hz
  rw [Complex.cpow_def_of_ne_zero htz, Complex.cpow_def_of_ne_zero hz,
    Complex.log_ofReal_mul ht hz, add_mul, Complex.exp_add]
  congr 1
  have : (Real.log t : ℂ) * (1 / 2 : ℂ) = ((Real.log t * (1 / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_exp]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]

lemma cpow_half_ofReal_nonneg (x : ℝ) (hx : 0 ≤ x) :
    ((x : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt x : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hx,
    Real.sqrt_eq_rpow]

lemma neg_I_cpow_half : (-I) ^ (1 / 2 : ℂ) = (Real.sqrt 2 / 2 : ℝ) * (1 - I) := by
  have hne : (-I : ℂ) ≠ 0 := by simp
  have hlog : Complex.log (-I) = -(π : ℂ) / 2 * I := by
    rw [← Complex.exp_neg_pi_div_two_mul_I, Complex.log_exp]
    · simp
      nlinarith [Real.pi_pos]
    · simp
      nlinarith [Real.pi_pos]
  rw [Complex.cpow_def_of_ne_zero hne, hlog]
  have harg : (-(π : ℂ) / 2 * I) * (1 / 2 : ℂ) = ((-(π / 4) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast
  ring

/-! ## Assembly: the exact value of the quadratic Gauss sum -/

lemma theta_fe_zero (τ : ℂ) :
    jacobiTheta₂ 0 τ = (1 / ((-I * τ) ^ (1 / 2 : ℂ))) * jacobiTheta₂ 0 (-1 / τ) := by
  have h := jacobiTheta₂_functional_equation 0 τ
  simpa using h

section GaussValue

variable {N : ℕ}

/-- The path `τ(t) = 2/N + it` approaching the rational point `2/N`. -/
private noncomputable def tf (N : ℕ) (t : ℝ) : ℂ := ((2 / (N : ℝ) : ℝ) : ℂ) + I * t

private noncomputable def wf (N : ℕ) (t : ℝ) : ℂ := I * N * t / (2 * tf N t)

private noncomputable def S1f (N : ℕ) (t : ℝ) : ℂ :=
  ∑ r ∈ range N, cexp ((π : ℂ) * I * r ^ 2 * ((2 / (N : ℝ) : ℝ) : ℂ)) *
    jacobiTheta₂ ((((r : ℝ) / N : ℝ)) : ℂ) (-1 / ((N : ℂ) ^ 2 * (I * t)))

private noncomputable def S2f (N : ℕ) (t : ℝ) : ℂ :=
  ∑ r ∈ range 2, cexp ((π : ℂ) * I * r ^ 2 * ((-(N : ℝ) / 2 : ℝ) : ℂ)) *
    jacobiTheta₂ ((((r : ℝ) / 2 : ℝ)) : ℂ) (-1 / ((2 : ℂ) ^ 2 * wf N t))

private lemma tf_im (t : ℝ) : (tf N t).im = t := by simp [tf]

private lemma tf_ne {t : ℝ} (ht : 0 < t) : tf N t ≠ 0 := by
  intro h
  have h2 : (0 : ℂ).im = t := h ▸ tf_im (N := N) t
  simp at h2
  exact ht.ne' h2.symm

private lemma step1 (hN : 0 < N) {t : ℝ} (ht : 0 < t) :
    jacobiTheta₂ 0 (tf N t) = (1 / (((N : ℝ) * Real.sqrt t : ℝ) : ℂ)) * S1f N t := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hw : 0 < (I * (t : ℂ)).im := by simpa using ht
  have h1 := theta_split_fe N hN (2 / (N : ℝ)) (N : ℤ) (2 : ℤ)
    (by push_cast; field_simp) (by push_cast; field_simp) hw
  simp only [tf, S1f]
  rw [h1]
  have hpre : -I * ((N : ℂ) ^ 2 * (I * t)) = (((N : ℝ) ^ 2 * t : ℝ) : ℂ) := by
    push_cast
    linear_combination (-(N : ℂ) ^ 2 * (t : ℂ)) * Complex.I_sq
  rw [hpre, cpow_half_ofReal_nonneg _ (by positivity)]
  have hsq : Real.sqrt ((N : ℝ) ^ 2 * t) = N * Real.sqrt t := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hNR.le]
  rw [hsq]

private lemma sigma_eq (hN : 0 < N) {t : ℝ} (ht : 0 < t) :
    -1 / tf N t = ((-(N : ℝ) / 2 : ℝ) : ℂ) + wf N t := by
  have hτ : tf N t ≠ 0 := tf_ne ht
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hτ' : 2 / (N : ℂ) + I * t ≠ 0 := by
    have he : tf N t = 2 / (N : ℂ) + I * t := by simp only [tf]; push_cast; ring
    rwa [he] at hτ
  have h2N : (2 : ℂ) + (N : ℂ) * I * (t : ℂ) ≠ 0 := by
    intro h
    apply hτ'
    have he2 : (2 : ℂ) / (N : ℂ) + I * (t : ℂ) = ((2 : ℂ) + (N : ℂ) * I * (t : ℂ)) / (N : ℂ) := by
      field_simp
    rw [he2, h, zero_div]
  rw [div_eq_iff hτ]
  simp only [tf, wf] at *
  push_cast
  field_simp [h2N]
  ring_nf

private lemma wf_im_pos (hN : 0 < N) {t : ℝ} (ht : 0 < t) : 0 < (wf N t).im := by
  have h1 : wf N t = -1 / tf N t + (((N : ℝ) / 2 : ℝ) : ℂ) := by
    rw [sigma_eq hN ht]; push_cast; ring
  have h2 : (wf N t).im = (-1 / tf N t).im := by rw [h1]; simp
  have h4 : 0 < Complex.normSq (tf N t) := Complex.normSq_pos.mpr (tf_ne ht)
  rw [h2, neg_div, Complex.neg_im, one_div, Complex.inv_im, tf_im, neg_div, neg_neg]
  positivity

private lemma wf_ne (hN : 0 < N) {t : ℝ} (ht : 0 < t) : wf N t ≠ 0 := by
  intro h
  have h2 := wf_im_pos hN ht
  rw [h] at h2
  simp at h2

private lemma step3 (hN : 0 < N) {t : ℝ} (ht : 0 < t) :
    jacobiTheta₂ 0 (-1 / tf N t) =
      (1 / ((-I * ((2 : ℂ) ^ 2 * wf N t)) ^ (1 / 2 : ℂ))) * S2f N t := by
  have h1 := theta_split_fe 2 (by norm_num) (-(N : ℝ) / 2) (-(N : ℤ)) (-(N : ℤ))
    (by push_cast; ring) (by push_cast; ring) (wf_im_pos hN ht)
  rw [sigma_eq hN ht, h1]
  simp only [S2f, Nat.cast_ofNat]

private lemma tau1_eq (hN : 0 < N) {t : ℝ} (ht : 0 < t) :
    -1 / ((N : ℂ) ^ 2 * (I * t)) = I * ((((N : ℝ) ^ 2 * t)⁻¹ : ℝ) : ℂ) := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hden : (N : ℂ) ^ 2 * (I * t) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hNC) (mul_ne_zero I_ne_zero htC)
  rw [div_eq_iff hden]
  push_cast
  field_simp
  linear_combination -Complex.I_sq

private lemma tendsto_inv_sq_mul (hN : 0 < N) :
    Tendsto (fun t : ℝ => ((N : ℝ) ^ 2 * t)⁻¹) (𝓝[>] 0) atTop := by
  have hNR : (0 : ℝ) < ((N : ℝ) ^ 2)⁻¹ := by
    have : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    positivity
  have h1 : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
  have h2 := h1.const_mul_atTop hNR
  exact h2.congr fun t => (mul_inv _ _).symm

private lemma S1_lim (hN : 0 < N) :
    Tendsto (S1f N) (𝓝[>] 0) (𝓝 (gq 1 N)) := by
  have him : Tendsto (fun t : ℝ => (-1 / ((N : ℂ) ^ 2 * (I * (t : ℝ))) : ℂ).im)
      (𝓝[>] (0:ℝ)) atTop := by
    refine Tendsto.congr' ?_ (tendsto_inv_sq_mul hN)
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [tau1_eq hN ht, Complex.mul_im]
    simp only [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h := tendsto_sum_theta2 (l := 𝓝[>] (0:ℝ))
    (τ := fun t : ℝ => -1 / ((N : ℂ) ^ 2 * (I * (t : ℝ)))) N
    (fun r => cexp ((π : ℂ) * I * r ^ 2 * ((2 / (N : ℝ) : ℝ) : ℂ)))
    (fun r => (r : ℝ) / N) him
  have hgq : (∑ r ∈ range N, cexp ((π : ℂ) * I * r ^ 2 * ((2 / (N : ℝ) : ℝ) : ℂ))) = gq 1 N := by
    rw [gq]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [E]
    congr 1
    push_cast
    ring
  rw [hgq] at h
  exact h.congr fun t => by simp only [S1f]

private lemma tau2_eq (hN : 0 < N) {t : ℝ} (ht : 0 < t) :
    -1 / ((2 : ℂ) ^ 2 * wf N t) =
      ((-(1 / (2 * (N : ℝ))) : ℝ) : ℂ) + I * ((((N : ℝ) ^ 2 * t)⁻¹ : ℝ) : ℂ) := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hτ : tf N t ≠ 0 := tf_ne ht
  have h1 : (2 : ℂ) ^ 2 * wf N t = 2 * I * N * t / tf N t := by
    simp only [wf]
    field_simp
  have h2 : (2 : ℂ) * I * N * t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hNC) htC
  rw [h1, div_div_eq_mul_div, div_eq_iff h2]
  simp only [tf]
  push_cast
  field_simp
  linear_combination (-2 : ℂ) * Complex.I_sq

private lemma S2_lim (hN : 0 < N) :
    Tendsto (S2f N) (𝓝[>] 0) (𝓝 (1 + (-I) ^ N)) := by
  have him : Tendsto (fun t : ℝ => (-1 / ((2 : ℂ) ^ 2 * wf N t) : ℂ).im) (𝓝[>] (0:ℝ)) atTop := by
    refine Tendsto.congr' ?_ (tendsto_inv_sq_mul hN)
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [tau2_eq hN ht, Complex.add_im, Complex.mul_im]
    simp only [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h := tendsto_sum_theta2 (l := 𝓝[>] (0:ℝ))
    (τ := fun t : ℝ => -1 / ((2 : ℂ) ^ 2 * wf N t)) 2
    (fun r => cexp ((π : ℂ) * I * r ^ 2 * ((-(N : ℝ) / 2 : ℝ) : ℂ)))
    (fun r => (r : ℝ) / 2) him
  have hsum : (∑ r ∈ range 2, cexp ((π : ℂ) * I * (r : ℕ) ^ 2 * ((-(N : ℝ) / 2 : ℝ) : ℂ)))
      = 1 + (-I) ^ N := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : (π : ℂ) * I * (0 : ℕ) ^ 2 * ((-(N : ℝ) / 2 : ℝ) : ℂ) = 0 := by
      push_cast; ring
    have h1 : (π : ℂ) * I * (1 : ℕ) ^ 2 * ((-(N : ℝ) / 2 : ℝ) : ℂ)
        = (N : ℂ) * (-(π : ℂ) / 2 * I) := by
      push_cast; ring
    rw [h0, h1, Complex.exp_zero, Complex.exp_nat_mul, Complex.exp_neg_pi_div_two_mul_I]
  rw [hsum] at h
  exact h.congr fun t => by simp only [S2f]

private lemma combine_key (hN : 0 < N) {t : ℝ} (ht : 0 < t) :
    -I * ((2 : ℂ) ^ 2 * wf N t) = (t : ℂ) * (((2 * N : ℝ) : ℂ) / tf N t) := by
  have hτ : tf N t ≠ 0 := tf_ne ht
  simp only [wf]
  push_cast
  field_simp
  linear_combination (-(N : ℂ) * (t : ℂ)) * Complex.I_sq

private lemma combine (hN : 0 < N) {t : ℝ} (ht : 0 < t) :
    S1f N t = ((N : ℂ) / ((-I * tf N t) ^ (1 / 2 : ℂ) *
      (((2 * N : ℝ) : ℂ) / tf N t) ^ (1 / 2 : ℂ))) * S2f N t := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hτ : tf N t ≠ 0 := tf_ne ht
  have hst : (Real.sqrt t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ht).ne'
  have hbase1 : -I * tf N t ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ
  have hbase2 : ((2 * N : ℝ) : ℂ) / tf N t ≠ 0 :=
    div_ne_zero (ofReal_ne_zero.mpr (by positivity)) hτ
  have hP : (-I * tf N t) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    rintro ⟨h, -⟩
    exact hbase1 h
  have hQ : (((2 * N : ℝ) : ℂ) / tf N t) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    rintro ⟨h, -⟩
    exact hbase2 h
  have hC := step3 hN ht
  rw [combine_key hN ht, cpow_half_ofReal_pos_mul ht hbase2] at hC
  have heq : (1 / (((N : ℝ) * Real.sqrt t : ℝ) : ℂ)) * S1f N t
      = (1 / ((-I * tf N t) ^ (1 / 2 : ℂ))) *
        ((1 / ((Real.sqrt t : ℂ) * (((2 * N : ℝ) : ℂ) / tf N t) ^ (1 / 2 : ℂ))) * S2f N t) := by
    rw [← step1 hN ht, theta_fe_zero (tf N t), hC]
  have hNst : ((((N : ℝ) * Real.sqrt t : ℝ)) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (by positivity)
  have h6 := congrArg (fun z => ((((N : ℝ) * Real.sqrt t : ℝ)) : ℂ) * z) heq
  simp only at h6
  rw [← mul_assoc, mul_one_div, div_self hNst, one_mul] at h6
  rw [h6]
  push_cast
  field_simp

private lemma C_lim (hN : 0 < N) :
    Tendsto (fun t : ℝ => (N : ℂ) / ((-I * tf N t) ^ (1 / 2 : ℂ) *
        (((2 * N : ℝ) : ℂ) / tf N t) ^ (1 / 2 : ℂ)))
      (𝓝[>] (0:ℝ)) (𝓝 ((N : ℂ) / ((-I * ((2 / (N : ℝ) : ℝ) : ℂ)) ^ (1 / 2 : ℂ) * (N : ℂ)))) := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hc0 : ((2 / (N : ℝ) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have htf : Tendsto (fun t : ℝ => tf N t) (𝓝[>] (0:ℝ)) (𝓝 ((2 / (N : ℝ) : ℝ) : ℂ)) := by
    simp only [tf]
    have hc : Continuous fun t : ℝ => ((2 / (N : ℝ) : ℝ) : ℂ) + I * (t : ℝ) := by continuity
    have h := tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (0:ℝ)) (hc.tendsto 0)
    simpa using h
  have hP : Tendsto (fun t : ℝ => (-I * tf N t) ^ (1 / 2 : ℂ)) (𝓝[>] (0:ℝ))
      (𝓝 ((-I * ((2 / (N : ℝ) : ℝ) : ℂ)) ^ (1 / 2 : ℂ))) := by
    have hbase : Tendsto (fun t : ℝ => -I * tf N t) (𝓝[>] (0:ℝ))
        (𝓝 (-I * ((2 / (N : ℝ) : ℝ) : ℂ))) := tendsto_const_nhds.mul htf
    have hsp : -I * ((2 / (N : ℝ) : ℝ) : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      refine Or.inr ?_
      have him : (-I * ((2 / (N : ℝ) : ℝ) : ℂ)).im = -(2 / (N : ℝ)) := by simp
      rw [him]
      exact neg_ne_zero.mpr (by positivity)
    exact (continuousAt_cpow_const hsp).tendsto.comp hbase
  have hQ : Tendsto (fun t : ℝ => (((2 * N : ℝ) : ℂ) / tf N t) ^ (1 / 2 : ℂ)) (𝓝[>] (0:ℝ))
      (𝓝 (N : ℂ)) := by
    have hbase : Tendsto (fun t : ℝ => ((2 * N : ℝ) : ℂ) / tf N t) (𝓝[>] (0:ℝ))
        (𝓝 (((2 * N : ℝ) : ℂ) / ((2 / (N : ℝ) : ℝ) : ℂ))) :=
      tendsto_const_nhds.div htf hc0
    have hval : ((2 * N : ℝ) : ℂ) / ((2 / (N : ℝ) : ℝ) : ℂ) = (((N : ℝ) ^ 2 : ℝ) : ℂ) := by
      push_cast
      field_simp
    rw [hval] at hbase
    have hsp : (((N : ℝ) ^ 2 : ℝ) : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      refine Or.inl ?_
      have hre : ((((N : ℝ) ^ 2 : ℝ) : ℂ)).re = (N : ℝ) ^ 2 := Complex.ofReal_re _
      rw [hre]
      exact pow_pos hNR 2
    have h2 := ((continuousAt_cpow_const (b := (1 / 2 : ℂ)) hsp).tendsto).comp hbase
    have hvv : ((((N : ℝ) ^ 2 : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = (N : ℂ) := by
      rw [cpow_half_ofReal_nonneg _ (by positivity), Real.sqrt_sq hNR.le]
      norm_cast
    rwa [hvv] at h2
  have hden : (-I * ((2 / (N : ℝ) : ℝ) : ℂ)) ^ (1 / 2 : ℂ) * (N : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ hNC
    rw [Ne, Complex.cpow_eq_zero_iff]
    rintro ⟨h, -⟩
    exact (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hc0) h
  exact tendsto_const_nhds.div (hP.mul hQ) hden

theorem gauss_value (N : ℕ) (hN : 0 < N) :
    gq 1 N = (1 + I) * (1 + (-I) ^ N) / 2 * ((Real.sqrt N : ℝ) : ℂ) := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h1 : Tendsto (S1f N) (𝓝[>] (0:ℝ)) (𝓝 (gq 1 N)) := S1_lim hN
  have h2 : Tendsto (S1f N) (𝓝[>] (0:ℝ))
      (𝓝 (((N : ℂ) / ((-I * ((2 / (N : ℝ) : ℝ) : ℂ)) ^ (1 / 2 : ℂ) * (N : ℂ))) *
        (1 + (-I) ^ N))) := by
    have h := (C_lim hN).mul (S2_lim hN)
    refine Tendsto.congr' ?_ h
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (combine hN ht).symm
  have hval := tendsto_nhds_unique h1 h2
  -- evaluate the cpow
  have hc0R : (0 : ℝ) < 2 / (N : ℝ) := by positivity
  have hcomm : -I * ((2 / (N : ℝ) : ℝ) : ℂ) = ((2 / (N : ℝ) : ℝ) : ℂ) * (-I) := by ring
  have hcpow : (-I * ((2 / (N : ℝ) : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
      = ((Real.sqrt (2 / (N : ℝ)) : ℝ) : ℂ) * (((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 - I)) := by
    rw [hcomm, cpow_half_ofReal_pos_mul hc0R (by simp), neg_I_cpow_half]
  rw [hcpow] at hval
  have hs2 : Real.sqrt (2 / (N : ℝ)) * Real.sqrt N * Real.sqrt 2 = 2 := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 / (N : ℝ)) (N : ℝ),
      div_mul_cancel₀ _ hNR.ne']
    exact Real.mul_self_sqrt (by norm_num)
  have hsne : ((Real.sqrt (2 / (N : ℝ)) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hc0R).ne'
  have h1I : (1 : ℂ) - I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have hs2C : ((Real.sqrt (2 / (N : ℝ)) : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) *
      ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hs2]
    norm_num
  have hs22 : ((Real.sqrt 2 / 2 : ℝ) : ℂ) ≠ 0 := by
    refine ofReal_ne_zero.mpr ?_
    positivity
  have hD : ((Real.sqrt (2 / (N : ℝ)) : ℝ) : ℂ) * (((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 - I)) *
      (N : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hsne (mul_ne_zero hs22 h1I)) hNC
  rw [hval, div_mul_eq_mul_div, div_eq_iff hD]
  push_cast
  linear_combination (-(1 + (-I) ^ N) * (N : ℂ) / 2) * hs2C +
    ((1 + (-I) ^ N) * (N : ℂ) * (((Real.sqrt (2 / (N : ℝ)) : ℝ) : ℂ) *
      ((Real.sqrt (N : ℝ) : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)) / 4) * Complex.I_sq

end GaussValue

end OEIS48153

end

/-! # Section from Dev/GaussAlg.lean -/

section

open Complex Finset

namespace OEIS48153

/-! ## Powers and vanishing criteria for `E` -/

lemma E_nat_mul (n : ℕ) (x : ℝ) : E (n * x) = E x ^ n := by
  induction n with
  | zero => simp [E_zero]
  | succ n ih =>
    have : ((n + 1 : ℕ) : ℝ) * x = (n : ℝ) * x + x := by push_cast; ring
    rw [this, E_add, ih, pow_succ]

lemma E_eq_one_iff (x : ℝ) : E x = 1 ↔ ∃ k : ℤ, x = k := by
  rw [E, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    have h2 : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
      simp [Real.pi_ne_zero, I_ne_zero]
    have h3 : (x : ℂ) * (2 * (Real.pi : ℂ) * I) = (n : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      rw [← hn]; ring
    have hx : (x : ℂ) = (n : ℂ) := mul_right_cancel₀ h2 h3
    exact ⟨n, by exact_mod_cast hx⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; ring⟩

/-- Full-period geometric character sum. -/
lemma sum_E_lin (j q : ℕ) (hq : 0 < q) :
    ∑ k ∈ range q, E (((j * k : ℕ) : ℝ) / q) = if q ∣ j then (q : ℂ) else 0 := by
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hterm : ∀ k : ℕ, E (((j * k : ℕ) : ℝ) / q) = E ((j : ℝ) / q) ^ k := by
    intro k
    rw [← E_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  by_cases h : q ∣ j
  · have h1 : E ((j : ℝ) / q) = 1 := by
      obtain ⟨c, rfl⟩ := h
      rw [E_eq_one_iff]
      refine ⟨c, ?_⟩
      push_cast
      field_simp
    simp [h1, h]
  · have h1 : E ((j : ℝ) / q) ≠ 1 := by
      rw [Ne, E_eq_one_iff]
      rintro ⟨k, hk⟩
      apply h
      rw [div_eq_iff hqR] at hk
      have hj : (j : ℤ) = q * k := by
        have : (j : ℝ) = (k : ℝ) * q := hk
        exact_mod_cast (by linarith : (j : ℝ) = (q : ℝ) * k)
      have hdvd : (q : ℤ) ∣ (j : ℤ) := ⟨k, hj⟩
      exact_mod_cast hdvd
    rw [geom_sum_eq h1, if_neg h]
    have hq' : E ((j : ℝ) / q) ^ q = 1 := by
      rw [← E_nat_mul, E_eq_one_iff]
      refine ⟨j, ?_⟩
      push_cast
      field_simp
    rw [hq', sub_self, zero_div]

/-- Splitting a sum over `range (a * b)` by base-`a` digits. -/
lemma sum_range_mul_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a b : ℕ) (ha : 0 < a) :
    ∑ k ∈ range (a * b), f k = ∑ y ∈ range b, ∑ x ∈ range a, f (x + a * y) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun k => (k / a, k % a)) (fun p => p.2 + a * p.1) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨Nat.div_lt_of_lt_mul hk, Nat.mod_lt _ ha⟩
  · intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    rw [Finset.mem_range]
    calc p.2 + a * p.1 < a + a * p.1 := by omega
    _ = a * (p.1 + 1) := by ring
    _ ≤ a * b := Nat.mul_le_mul_left a hp.1
  · intro k _
    show k % a + a * (k / a) = k
    exact Nat.mod_add_div k a
  · intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    have h1 : (p.2 + a * p.1) / a = p.1 := by
      rw [Nat.add_mul_div_left _ _ ha, Nat.div_eq_of_lt hp.2, zero_add]
    have h2 : (p.2 + a * p.1) % a = p.2 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.2]
    simp [h1, h2]
  · intro k _
    exact congrArg f (Nat.mod_add_div k a).symm

/-- Extracting multiples of `p` from a sum against the indicator of divisibility. -/
lemma sum_multiples (g : ℕ → ℂ) (p L : ℕ) (hp : 0 < p) :
    ∑ x ∈ range (p * L), g x * (if p ∣ x then (p : ℂ) else 0) =
      p * ∑ y ∈ range L, g (p * y) := by
  rw [sum_range_mul_split _ p L hp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hp)]
  · rw [zero_add, if_pos (Dvd.intro y rfl)]
    ring
  · intro x hx hx0
    rw [Finset.mem_range] at hx
    rw [if_neg, mul_zero]
    intro hdvd
    have h1 : p ∣ x := by
      have h2 := Nat.dvd_sub hdvd (Dvd.intro y rfl)
      simpa using h2
    exact hx0 (Nat.eq_zero_of_dvd_of_lt h1 hx)

/-! ## The splitting engine for Gauss sums over prime powers -/

/-- Core splitting engine: if the argument decomposes as indicated, the Gauss-type
sum over `range (D * B)` collapses to a divisibility-restricted sum over `range D`. -/
lemma sum_split_engine (m Q D B c : ℕ) (hB : 0 < B)
    (key : ∀ x j : ℕ, j < B → ∃ R : ℕ, ((m * (x + D * j) ^ 2 : ℕ) : ℝ) / Q
      = ((m * x ^ 2 : ℕ) : ℝ) / Q + (((c * x * j : ℕ) : ℝ) / B + (R : ℝ))) :
    ∑ k ∈ range (D * B), E (((m * k ^ 2 : ℕ) : ℝ) / Q)
      = ∑ x ∈ range D, E (((m * x ^ 2 : ℕ) : ℝ) / Q) * (if B ∣ c * x then (B : ℂ) else 0) := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    simp
  rw [sum_range_mul_split _ D B hD]
  have hterm : ∀ j ∈ range B, ∀ x ∈ range D,
      E (((m * (x + D * j) ^ 2 : ℕ) : ℝ) / Q)
        = E (((m * x ^ 2 : ℕ) : ℝ) / Q) * E (((c * x * j : ℕ) : ℝ) / B) := by
    intro j hj x _
    obtain ⟨R, hR⟩ := key x j (Finset.mem_range.mp hj)
    rw [hR, E_add, E_add, E_natCast, mul_one]
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun x hx => hterm j hj x hx,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact sum_E_lin (c * x) B hB

/-! ## Odd prime power recursion -/

theorem gq_pp_step {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ} (hm : ¬ p ∣ m) (d : ℕ) :
    gq m (p ^ (d + 2)) = p * gq m (p ^ d) := by
  have hppos : 0 < p := hp.pos
  have hpR : ((p : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hppos.ne'
  have hr : gq m (p ^ (d + 2)) = ∑ k ∈ range (p ^ (d + 1) * p),
      E (((m * k ^ 2 : ℕ) : ℝ) / ((p ^ (d + 2) : ℕ) : ℝ)) := by
    rw [gq]
    congr 1
  have key : ∀ x j : ℕ, j < p → ∃ R : ℕ, ((m * (x + p ^ (d + 1) * j) ^ 2 : ℕ) : ℝ) / (p ^ (d + 2) : ℕ)
      = ((m * x ^ 2 : ℕ) : ℝ) / (p ^ (d + 2) : ℕ) + (((2 * m * x * j : ℕ) : ℝ) / p + (R : ℝ)) := by
    intro x j _
    refine ⟨m * p ^ d * j ^ 2, ?_⟩
    push_cast
    field_simp
    ring
  rw [hr, sum_split_engine m (p ^ (d + 2)) (p ^ (d + 1)) p (2 * m) hppos key]
  have hcond : ∀ x : ℕ, (if p ∣ 2 * m * x then (p : ℂ) else 0)
      = (if p ∣ x then (p : ℂ) else 0) := by
    intro x
    congr 1
    simp only [eq_iff_iff]
    constructor
    · intro hd
      rcases hp.dvd_mul.mp hd with h1 | h1
      · rcases hp.dvd_mul.mp h1 with h2 | h2
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2) hp2
        · exact absurd h2 hm
      · exact h1
    · exact fun h => h.mul_left (2 * m)
  simp_rw [hcond]
  have hr2 : ∑ x ∈ range (p ^ (d + 1)), E (((m * x ^ 2 : ℕ) : ℝ) / ((p ^ (d + 2) : ℕ) : ℝ)) *
      (if p ∣ x then (p : ℂ) else 0)
      = ∑ x ∈ range (p * p ^ d), E (((m * x ^ 2 : ℕ) : ℝ) / ((p ^ (d + 2) : ℕ) : ℝ)) *
        (if p ∣ x then (p : ℂ) else 0) := by
    congr 1
    rw [pow_succ']
  rw [hr2, sum_multiples _ p (p ^ d) hppos]
  congr 1
  rw [gq]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  push_cast
  field_simp
  ring

/-! ## The additive character `ep q` on `ZMod q` -/

/-- The standard additive character `x ↦ e(x/q)` on `ZMod q`. -/
noncomputable def ep (q : ℕ) (x : ZMod q) : ℂ := E ((x.val : ℝ) / q)

lemma ep_natCast (q : ℕ) [NeZero q] (a : ℕ) : ep q ((a : ZMod q)) = E ((a : ℝ) / q) := by
  rw [ep, ZMod.val_natCast]
  exact E_div_congr (Nat.mod_mod_of_dvd a dvd_rfl)

lemma gq_eq_sum_ep (m q : ℕ) [NeZero q] :
    gq m q = ∑ x : ZMod q, ep q ((m : ZMod q) * x ^ 2) := by
  rw [gq_eq_sum_zmod]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : ((m * x.val ^ 2 : ℕ) : ZMod q) = (m : ZMod q) * x ^ 2 := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
  rw [← h1, ep_natCast]

lemma sum_ep_mul (q : ℕ) [NeZero q] (c : ZMod q) :
    ∑ x : ZMod q, ep q (c * x) = if c = 0 then (q : ℂ) else 0 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have h1 : ∀ x : ZMod q, ep q (c * x) = E (((c.val * x.val : ℕ) : ℝ) / q) := by
    intro x
    rw [ep, ZMod.val_mul]
    exact E_div_congr (Nat.mod_mod_of_dvd _ dvd_rfl)
  simp_rw [h1]
  rw [sum_zmod_eq_sum_range q (fun k => E (((c.val * k : ℕ) : ℝ) / q))]
  rw [sum_E_lin c.val q hq]
  congr 1
  simp only [eq_iff_iff]
  constructor
  · intro hd
    have := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt c)
    · exact (ZMod.val_eq_zero c).mp this
  · intro hc
    subst hc
    simp
  
/-! ## The quadratic Gauss sum at an odd prime -/

theorem gq_prime (p : ℕ) [hpi : Fact p.Prime] (hp2 : p ≠ 2) {m : ℕ} (hm : ¬ p ∣ m) :
    gq m p = (legendreSym p m : ℂ) * gq 1 p := by
  haveI : NeZero p := ⟨hpi.out.pos.ne'⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  set χ := quadraticChar (ZMod p) with hχ
  set S : ℂ := ∑ a : ZMod p, ((χ a : ℤ) : ℂ) * ep p a with hS
  have main : ∀ c : ZMod p, c ≠ 0 →
      ∑ x : ZMod p, ep p (c * x ^ 2) = ((χ c : ℤ) : ℂ) * S := by
    intro c hc
    have hfib : ∑ x : ZMod p, ep p (c * x ^ 2)
        = ∑ a : ZMod p, (((χ a : ℤ) + 1 : ℤ) : ℂ) * ep p (c * a) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : ZMod p => x ^ 2)
        (fun x _ => Finset.mem_univ _) (fun x => ep p (c * x ^ 2))]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hinner : ∀ x ∈ Finset.univ.filter (fun x : ZMod p => x ^ 2 = a),
          ep p (c * x ^ 2) = ep p (c * a) := by
        intro x hx
        rw [(Finset.mem_filter.mp hx).2]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
      congr 1
      have hcard := quadraticChar_card_sqrts hchar a
      have hset : {x : ZMod p | x ^ 2 = a}.toFinset
          = Finset.univ.filter (fun x : ZMod p => x ^ 2 = a) := Set.toFinset_setOf _
      rw [hset] at hcard
      rw [← hχ] at hcard
      rw [← hcard]
      push_cast
      ring
    have hsplit : ∑ a : ZMod p, (((χ a : ℤ) + 1 : ℤ) : ℂ) * ep p (c * a)
        = (∑ a : ZMod p, ((χ a : ℤ) : ℂ) * ep p (c * a)) + ∑ a : ZMod p, ep p (c * a) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      push_cast
      ring
    rw [hfib, hsplit, sum_ep_mul p c, if_neg hc, add_zero]
    have hbij : Function.Bijective (fun a : ZMod p => c * a) := (Equiv.mulLeft₀ c hc).bijective
    have hre := Fintype.sum_bijective _ hbij
      (fun a : ZMod p => ((χ (c * a) : ℤ) : ℂ) * ep p (c * a))
      (fun b : ZMod p => ((χ b : ℤ) : ℂ) * ep p b) (fun a => rfl)
    have hsq : ((χ c : ℤ) : ℂ) * ((χ c : ℤ) : ℂ) = 1 := by
      have h1 : χ c ^ 2 = 1 := quadraticChar_sq_one hc
      have h2 : ((χ c ^ 2 : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by rw [h1]
      push_cast at h2
      rw [← h2]
      ring
    calc ∑ a : ZMod p, ((χ a : ℤ) : ℂ) * ep p (c * a)
        = ((χ c : ℤ) : ℂ) * (((χ c : ℤ) : ℂ) *
            ∑ a : ZMod p, ((χ a : ℤ) : ℂ) * ep p (c * a)) := by
          rw [← mul_assoc, hsq, one_mul]
      _ = ((χ c : ℤ) : ℂ) * ∑ a : ZMod p, ((χ (c * a) : ℤ) : ℂ) * ep p (c * a) := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hχ]
          simp only [map_mul]
          push_cast
          ring
      _ = ((χ c : ℤ) : ℂ) * S := by rw [hre, hS]
  have hm' : ((m : ZMod p)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hm
  have h1 := main (m : ZMod p) hm'
  have h2 := main 1 one_ne_zero
  have hone : ((χ 1 : ℤ) : ℂ) = 1 := by
    rw [map_one]
    norm_num
  rw [gq_eq_sum_ep m p, gq_eq_sum_ep 1 p, h1, Nat.cast_one, h2, hone, one_mul]
  congr 2
  rw [legendreSym]
  congr 1
  push_cast
  rfl

/-! ## Trivial modulus -/

lemma gq_one (m : ℕ) : gq m 1 = 1 := by
  simp [gq, E_zero]

/-! ## Chinese remainder multiplicativity -/

theorem gq_mul_coprime {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (h : Nat.Coprime A B) (m : ℕ) :
    gq m (A * B) = gq (m * B) A * gq (m * A) B := by
  haveI : NeZero A := ⟨hA.ne'⟩
  haveI : NeZero B := ⟨hB.ne'⟩
  haveI : NeZero (A * B) := ⟨(Nat.mul_pos hA hB).ne'⟩
  have hAR : (A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hA.ne'
  have hBR : (B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
  set f : ZMod A × ZMod B → ZMod (A * B) :=
    fun p => ((B * p.1.val + A * p.2.val : ℕ) : ZMod (A * B)) with hf
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    simp only [hf] at hab
    have hcastA := congrArg (ZMod.castHom (dvd_mul_right A B) (ZMod A)) hab
    have hcastB := congrArg (ZMod.castHom (dvd_mul_left B A) (ZMod B)) hab
    rw [map_natCast, map_natCast] at hcastA hcastB
    have hA1 : (B : ZMod A) * a = (B : ZMod A) * a' := by
      have h1 : ((B * a.val + A * b.val : ℕ) : ZMod A) = (B : ZMod A) * a := by
        push_cast
        simp [ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_self]
      have h2 : ((B * a'.val + A * b'.val : ℕ) : ZMod A) = (B : ZMod A) * a' := by
        push_cast
        simp [ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_self]
      rw [h1, h2] at hcastA
      exact hcastA
    have hB1 : (A : ZMod B) * b = (A : ZMod B) * b' := by
      have h1 : ((B * a.val + A * b.val : ℕ) : ZMod B) = (A : ZMod B) * b := by
        push_cast
        simp [ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_self]
      have h2 : ((B * a'.val + A * b'.val : ℕ) : ZMod B) = (A : ZMod B) * b' := by
        push_cast
        simp [ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_self]
      rw [h1, h2] at hcastB
      exact hcastB
    have huA : IsUnit (B : ZMod A) := by
      rw [← ZMod.coe_unitOfCoprime B h.symm]
      exact (ZMod.unitOfCoprime B h.symm).isUnit
    have huB : IsUnit (A : ZMod B) := by
      rw [← ZMod.coe_unitOfCoprime A h]
      exact (ZMod.unitOfCoprime A h).isUnit
    have ha : a = a' := huA.mul_left_cancel hA1
    have hb : b = b' := huB.mul_left_cancel hB1
    simp [ha, hb]
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp [ZMod.card]⟩
  have hsum := Fintype.sum_bijective f hbij
    (fun p : ZMod A × ZMod B => ep (A * B) ((m : ZMod (A * B)) * (f p) ^ 2))
    (fun x : ZMod (A * B) => ep (A * B) ((m : ZMod (A * B)) * x ^ 2)) (fun p => rfl)
  rw [gq_eq_sum_ep m (A * B), ← hsum]
  have hterm : ∀ p : ZMod A × ZMod B,
      ep (A * B) ((m : ZMod (A * B)) * (f p) ^ 2)
        = E (((m * B * p.1.val ^ 2 : ℕ) : ℝ) / A) * E (((m * A * p.2.val ^ 2 : ℕ) : ℝ) / B) := by
    rintro ⟨a, b⟩
    have h1 : (m : ZMod (A * B)) * (f (a, b)) ^ 2
        = ((m * (B * a.val + A * b.val) ^ 2 : ℕ) : ZMod (A * B)) := by
      simp only [hf]
      push_cast
      ring
    rw [h1, ep_natCast]
    have h2 : ((m * (B * a.val + A * b.val) ^ 2 : ℕ) : ℝ) / ((A * B : ℕ) : ℝ)
        = ((m * B * a.val ^ 2 : ℕ) : ℝ) / A + (((m * A * b.val ^ 2 : ℕ) : ℝ) / B
          + ((2 * m * a.val * b.val : ℕ) : ℝ)) := by
      push_cast
      field_simp
      ring
    rw [h2, E_add, E_add, E_natCast, mul_one]
  rw [Finset.sum_congr rfl fun p _ => hterm p]
  rw [Fintype.sum_prod_type]
  rw [gq_eq_sum_zmod (m * B) A, gq_eq_sum_zmod (m * A) B, Finset.sum_mul_sum]

/-! ## Odd prime powers -/

theorem gq_odd_pp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ} (hm : ¬ p ∣ m) :
    ∀ e : ℕ, gq m (p ^ e) = (jacobiSym m (p ^ e) : ℂ) * gq 1 (p ^ e) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hgcd : Int.gcd (m : ℤ) p = 1 := by
    have h1 : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
    simpa [Int.gcd_natCast_natCast] using h1.symm
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    match e with
    | 0 =>
      simp [pow_zero, gq_one, jacobiSym.one_right]
    | 1 =>
      rw [pow_one, gq_prime p hp2 hm]
      congr 2
      exact jacobiSym.legendreSym.to_jacobiSym p m
    | (d + 2) =>
      rw [gq_pp_step hp hp2 hm d, ih d (by omega),
        gq_pp_step hp hp2 (m := 1) (fun hdvd => hp.one_lt.ne' (Nat.dvd_one.mp hdvd)) d]
      have hJ : jacobiSym m (p ^ (d + 2)) = jacobiSym m (p ^ d) := by
        rw [jacobiSym.pow_right, jacobiSym.pow_right, pow_add, jacobiSym.sq_one hgcd, mul_one]
      rw [hJ]
      ring

/-! ## The main theorem for odd moduli -/

theorem gq_odd : ∀ q : ℕ, Odd q → ∀ m : ℕ, Nat.Coprime m q →
    gq m q = (jacobiSym m q : ℂ) * gq 1 q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq m hm
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp [Nat.odd_iff] at hq
    rcases eq_or_ne q 1 with rfl | hq1
    · simp [gq_one, jacobiSym.one_right]
    -- q > 1
    set p := q.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime hq1
    have hpdvd : p ∣ q := Nat.minFac_dvd q
    have hp2 : p ≠ 2 := by
      intro h
      rw [h] at hpdvd
      rw [Nat.odd_iff] at hq
      omega
    set e := q.factorization p with hedef
    set t := ordCompl[p] q with htdef
    have hqe : p ^ e * t = q := Nat.ordProj_mul_ordCompl_eq_self q p
    have he1 : 1 ≤ e := hp.factorization_pos_of_dvd hq0 hpdvd
    have hpt : ¬ p ∣ t := Nat.not_dvd_ordCompl hp hq0
    have hcop : Nat.Coprime (p ^ e) t :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpt)
    have hpm : ¬ p ∣ m := by
      intro hdvd
      have h1 : Nat.Coprime m p := hm.coprime_dvd_right hpdvd
      have h2 : p ∣ 1 := h1 ▸ Nat.dvd_gcd hdvd dvd_rfl
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
    have hppos : 0 < p ^ e := pow_pos hp.pos e
    have htpos : 0 < t := Nat.ordCompl_pos p hq0
    have htdvd : t ∣ q := Nat.ordCompl_dvd q p
    have htodd : Odd t := by
      rcases Nat.even_or_odd t with hev | hod
      · exfalso
        have h2q : (2 : ℕ) ∣ q := dvd_trans hev.two_dvd htdvd
        rw [Nat.odd_iff] at hq
        omega
      · exact hod
    rcases eq_or_ne t 1 with ht1 | ht1
    · -- q = p ^ e
      have hq_eq : q = p ^ e := by rw [← hqe, ht1, mul_one]
      rw [hq_eq]
      exact gq_odd_pp hp hp2 hpm e
    · -- proper splitting
      have hte : t < q := by
        have h2 : 2 ≤ p ^ e := by
          calc 2 ≤ p := hp.two_le
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he1
        calc t < 2 * t := by omega
        _ ≤ p ^ e * t := Nat.mul_le_mul_right t h2
        _ = q := hqe
      have hmt : Nat.Coprime m t := hm.coprime_dvd_right htdvd
      have hmpe : ¬ p ∣ m * t := by
        intro hdvd
        rcases hp.dvd_mul.mp hdvd with h1 | h1
        · exact hpm h1
        · exact hpt h1
      have h1 : gq m q = gq (m * t) (p ^ e) * gq (m * p ^ e) t := by
        rw [← hqe]
        exact gq_mul_coprime hppos htpos hcop m
      have h2 : gq 1 q = gq t (p ^ e) * gq (p ^ e) t := by
        rw [← hqe]
        have := gq_mul_coprime hppos htpos hcop 1
        rwa [one_mul, one_mul] at this
      have h3 := gq_odd_pp hp hp2 hmpe e
      have h4 : gq (m * p ^ e) t = (jacobiSym (m * p ^ e) t : ℂ) * gq 1 t :=
        ih t hte htodd (m * p ^ e) (hmt.mul hcop)
      have h5 := gq_odd_pp hp hp2 hpt e
      have h6 : gq (p ^ e) t = (jacobiSym (p ^ e) t : ℂ) * gq 1 t :=
        ih t hte htodd (p ^ e) hcop
      have hJm : jacobiSym m q = jacobiSym m (p ^ e) * jacobiSym m t := by
        rw [← hqe]
        haveI : NeZero (p ^ e) := ⟨hppos.ne'⟩
        haveI : NeZero t := ⟨htpos.ne'⟩
        exact jacobiSym.mul_right m (p ^ e) t
      rw [h1, h3, h4, h2, h5, h6, hJm]
      push_cast [jacobiSym.mul_left]
      ring

/-! ## Special values of `E` -/

lemma E_half : E ((1 : ℝ) / 2) = -1 := by
  rw [E]
  have h : 2 * (Real.pi : ℂ) * I * (((1 : ℝ) / 2 : ℝ) : ℂ) = Real.pi * I := by
    push_cast; ring
  rw [h, Complex.exp_pi_mul_I]

lemma E_quarter : E ((1 : ℝ) / 4) = I := by
  rw [E]
  have h : 2 * (Real.pi : ℂ) * I * (((1 : ℝ) / 4 : ℝ) : ℂ) = (Real.pi / 2 : ℂ) * I := by
    push_cast; ring
  rw [h, Complex.exp_pi_div_two_mul_I]

lemma E_nat_div_two {m : ℕ} (hm : Odd m) : E ((m : ℝ) / 2) = -1 := by
  obtain ⟨j, rfl⟩ := hm
  have h : ((2 * j + 1 : ℕ) : ℝ) / 2 = (1 : ℝ) / 2 + (j : ℕ) := by push_cast; ring
  rw [h, E_add_nat, E_half]

lemma E_nat_div_four (m : ℕ) : E ((m : ℝ) / 4) = I ^ m := by
  have h : (m : ℝ) / 4 = (m : ℕ) * ((1 : ℝ) / 4) := by push_cast; ring
  rw [h, E_nat_mul, E_quarter]

/-! ## Gauss sums for small powers of two -/

lemma gq_two {m : ℕ} (hm : Odd m) : gq m 2 = 0 := by
  rw [gq, Finset.sum_range_succ, Finset.sum_range_one]
  have h0 : ((m * 0 ^ 2 : ℕ) : ℝ) / (2 : ℕ) = 0 := by push_cast; ring
  have h1 : ((m * 1 ^ 2 : ℕ) : ℝ) / (2 : ℕ) = (m : ℝ) / 2 := by push_cast; ring
  rw [h0, h1, E_zero, E_nat_div_two hm]
  ring

lemma gq_four (m : ℕ) : gq m 4 = 2 * (1 + I ^ m) := by
  rw [gq, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  have h0 : ((m * 0 ^ 2 : ℕ) : ℝ) / (4 : ℕ) = 0 := by push_cast; ring
  have h1 : ((m * 1 ^ 2 : ℕ) : ℝ) / (4 : ℕ) = (m : ℝ) / 4 := by push_cast; ring
  have h2 : ((m * 2 ^ 2 : ℕ) : ℝ) / (4 : ℕ) = ((m : ℕ) : ℝ) := by push_cast; ring
  have h3 : ((m * 3 ^ 2 : ℕ) : ℝ) / (4 : ℕ) = (m : ℝ) / 4 + ((2 * m : ℕ) : ℝ) := by
    push_cast; ring
  rw [h0, h1, h2, h3, E_zero, E_natCast, E_add, E_natCast, E_nat_div_four]
  ring

lemma gq_eight {m : ℕ} (hm : Odd m) : gq m 8 = 4 * E ((m : ℝ) / 8) := by
  rw [gq, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one]
  have h0 : ((m * 0 ^ 2 : ℕ) : ℝ) / (8 : ℕ) = 0 := by push_cast; ring
  have h1 : ((m * 1 ^ 2 : ℕ) : ℝ) / (8 : ℕ) = (m : ℝ) / 8 := by push_cast; ring
  have h2 : ((m * 2 ^ 2 : ℕ) : ℝ) / (8 : ℕ) = (m : ℝ) / 2 := by push_cast; ring
  have h3 : ((m * 3 ^ 2 : ℕ) : ℝ) / (8 : ℕ) = (m : ℝ) / 8 + ((m : ℕ) : ℝ) := by push_cast; ring
  have h4 : ((m * 4 ^ 2 : ℕ) : ℝ) / (8 : ℕ) = ((2 * m : ℕ) : ℝ) := by push_cast; ring
  have h5 : ((m * 5 ^ 2 : ℕ) : ℝ) / (8 : ℕ) = (m : ℝ) / 8 + ((3 * m : ℕ) : ℝ) := by
    push_cast; ring
  have h6 : ((m * 6 ^ 2 : ℕ) : ℝ) / (8 : ℕ) = (m : ℝ) / 2 + ((4 * m : ℕ) : ℝ) := by
    push_cast; ring
  have h7 : ((m * 7 ^ 2 : ℕ) : ℝ) / (8 : ℕ) = (m : ℝ) / 8 + ((6 * m : ℕ) : ℝ) := by
    push_cast; ring
  rw [h0, h1, h2, h3, h4, h5, h6, h7, E_zero, E_natCast, E_add, E_add, E_add, E_add,
    E_natCast, E_natCast, E_natCast, E_natCast, E_nat_div_two hm]
  ring

/-! ## Two-power recursion -/

lemma gq_two_pow_A (m d : ℕ) :
    gq m (2 ^ (d + 2)) = 2 * ∑ x ∈ range (2 ^ (d + 1)),
      E (((m * x ^ 2 : ℕ) : ℝ) / ((2 ^ (d + 2) : ℕ) : ℝ)) := by
  have hr : gq m (2 ^ (d + 2)) = ∑ k ∈ range (2 ^ (d + 1) * 2),
      E (((m * k ^ 2 : ℕ) : ℝ) / ((2 ^ (d + 2) : ℕ) : ℝ)) := by
    rw [gq]
    congr 1
  have key : ∀ x j : ℕ, j < 2 → ∃ R : ℕ,
      ((m * (x + 2 ^ (d + 1) * j) ^ 2 : ℕ) : ℝ) / (2 ^ (d + 2) : ℕ)
      = ((m * x ^ 2 : ℕ) : ℝ) / (2 ^ (d + 2) : ℕ) + (((0 * x * j : ℕ) : ℝ) / 2 + (R : ℝ)) := by
    intro x j _
    refine ⟨m * x * j + m * 2 ^ d * j ^ 2, ?_⟩
    push_cast
    field_simp
    ring
  rw [hr, sum_split_engine m (2 ^ (d + 2)) (2 ^ (d + 1)) 2 0 (by norm_num) key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [if_pos (by simp : (2 : ℕ) ∣ 0 * x)]
  ring

lemma gq_two_pow_step {m : ℕ} (hm : Odd m) (d : ℕ) :
    gq m (2 ^ (d + 4)) = 2 * gq m (2 ^ (d + 2)) := by
  have hm2 : ¬ (2 ∣ m) := by
    rw [Nat.odd_iff] at hm
    omega
  rw [gq_two_pow_A m (d + 2), gq_two_pow_A m d]
  congr 1
  have hstep : ∑ x ∈ range (2 ^ (d + 3)), E (((m * x ^ 2 : ℕ) : ℝ) / ((2 ^ (d + 4) : ℕ) : ℝ))
      = ∑ k ∈ range (2 ^ (d + 2) * 2), E (((m * k ^ 2 : ℕ) : ℝ) / ((2 ^ (d + 4) : ℕ) : ℝ)) := by
    congr 1
  have key : ∀ x j : ℕ, j < 2 → ∃ R : ℕ,
      ((m * (x + 2 ^ (d + 2) * j) ^ 2 : ℕ) : ℝ) / (2 ^ (d + 4) : ℕ)
      = ((m * x ^ 2 : ℕ) : ℝ) / (2 ^ (d + 4) : ℕ) + (((m * x * j : ℕ) : ℝ) / 2 + (R : ℝ)) := by
    intro x j _
    refine ⟨m * 2 ^ d * j ^ 2, ?_⟩
    push_cast
    field_simp
    ring
  rw [hstep, sum_split_engine m (2 ^ (d + 4)) (2 ^ (d + 2)) 2 m (by norm_num) key]
  have hcond : ∀ x : ℕ, (if (2 : ℕ) ∣ m * x then ((2 : ℕ) : ℂ) else 0)
      = (if (2 : ℕ) ∣ x then ((2 : ℕ) : ℂ) else 0) := by
    intro x
    congr 1
    simp only [eq_iff_iff]
    constructor
    · intro hd
      rcases (Nat.prime_two.dvd_mul.mp hd) with h1 | h1
      · exact absurd h1 hm2
      · exact h1
    · exact fun h => h.mul_left m
  simp_rw [hcond]
  have hr2 : ∑ x ∈ range (2 ^ (d + 2)), E (((m * x ^ 2 : ℕ) : ℝ) / ((2 ^ (d + 4) : ℕ) : ℝ)) *
      (if (2 : ℕ) ∣ x then ((2 : ℕ) : ℂ) else 0)
      = ∑ x ∈ range (2 * 2 ^ (d + 1)), E (((m * x ^ 2 : ℕ) : ℝ) / ((2 ^ (d + 4) : ℕ) : ℝ)) *
        (if (2 : ℕ) ∣ x then ((2 : ℕ) : ℂ) else 0) := by
    congr 1
    rw [pow_succ']
  rw [hr2, sum_multiples _ 2 (2 ^ (d + 1)) (by norm_num)]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  push_cast
  field_simp
  ring

/-! ## Closed forms for two-power Gauss sums -/

lemma gq_two_pow_even {m : ℕ} (hm : Odd m) (k : ℕ) :
    gq m (2 ^ (2 * k + 2)) = ((2 ^ (k + 1) : ℕ) : ℂ) * (1 + I ^ m) := by
  induction k with
  | zero =>
    rw [show (2 : ℕ) ^ (2 * 0 + 2) = 4 by norm_num, gq_four m]
    norm_num
  | succ k ih =>
    have hidx : 2 * (k + 1) + 2 = (2 * k) + 4 := by ring
    rw [hidx, gq_two_pow_step hm (2 * k), ih]
    push_cast
    ring

lemma gq_two_pow_odd {m : ℕ} (hm : Odd m) (k : ℕ) :
    gq m (2 ^ (2 * k + 3)) = ((2 ^ (k + 2) : ℕ) : ℂ) * E ((m : ℝ) / 8) := by
  induction k with
  | zero =>
    rw [show (2 : ℕ) ^ (2 * 0 + 3) = 8 by norm_num, gq_eight hm]
    norm_num
  | succ k ih =>
    have hidx : 2 * (k + 1) + 3 = (2 * k + 1) + 4 := by ring
    have hidx2 : (2 * k + 1) + 2 = 2 * k + 3 := by ring
    rw [hidx, gq_two_pow_step hm (2 * k + 1), hidx2, ih]
    push_cast
    ring

end OEIS48153

end

/-! # Section from Dev/Kernel.lean -/

section

open Complex Finset

namespace OEIS48153

/-- The cotangent value `cot (π m / q)` written as a quotient. -/
noncomputable def ctn (q m : ℕ) : ℝ := Real.cos (Real.pi * m / q) / Real.sin (Real.pi * m / q)

/-! ## The finite cotangent kernel -/

lemma cot_sin_identity (θ : ℝ) (hθ : Real.sin θ ≠ 0) (a : ℕ) :
    Real.cos θ / Real.sin θ * Real.sin (2 * a * θ)
      = 2 * (∑ j ∈ range (a + 1), Real.cos (2 * j * θ)) - 1 - Real.cos (2 * a * θ) := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    have e1 : 2 * ((a : ℝ) + 1) * θ = (2 * a + 1) * θ + θ := by ring
    have e2 : 2 * (a : ℝ) * θ = (2 * a + 1) * θ - θ := by ring
    have hsin : Real.sin (2 * ((a : ℝ) + 1) * θ)
        = Real.sin (2 * (a : ℝ) * θ) + 2 * Real.sin θ * Real.cos ((2 * (a : ℝ) + 1) * θ) := by
      rw [e1, e2, Real.sin_add, Real.sin_sub]
      ring
    have hcos : 2 * Real.cos θ * Real.cos ((2 * (a : ℝ) + 1) * θ)
        = Real.cos (2 * ((a : ℝ) + 1) * θ) + Real.cos (2 * (a : ℝ) * θ) := by
      rw [e1, e2, Real.cos_add, Real.cos_sub]
      ring
    have hstep : Real.cos θ / Real.sin θ * Real.sin (2 * ((a + 1 : ℕ) : ℝ) * θ)
        = Real.cos θ / Real.sin θ * Real.sin (2 * (a : ℝ) * θ)
          + 2 * Real.cos θ * Real.cos ((2 * (a : ℝ) + 1) * θ) := by
      push_cast
      rw [hsin]
      field_simp
    rw [hstep, ih, hcos]
    conv_rhs => rw [Finset.sum_range_succ]
    push_cast
    ring

lemma sum_cos_full (n j : ℕ) (hn : 0 < n) :
    ∑ m ∈ range n, Real.cos (2 * Real.pi * ((j * m : ℕ) : ℝ) / n)
      = if n ∣ j then (n : ℝ) else 0 := by
  have h := congrArg Complex.re (sum_E_lin j n hn)
  rw [Complex.re_sum] at h
  have hterm : ∀ m : ℕ, (E (((j * m : ℕ) : ℝ) / n)).re
      = Real.cos (2 * Real.pi * ((j * m : ℕ) : ℝ) / n) := by
    intro m
    rw [E_re]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun m _ => hterm m] at h
  rw [h]
  split_ifs <;> simp

lemma kernel_sum {n : ℕ} (hn : 0 < n) {a : ℕ} (ha : a < n) :
    ∑ m ∈ Ico 1 n, ctn n m * Real.sin (2 * (a : ℝ) * (Real.pi * m / n))
      = if a = 0 then 0 else (n : ℝ) - 2 * a := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsin : ∀ m ∈ Ico 1 n, Real.sin (Real.pi * m / n) ≠ 0 := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
    have hmn : (m : ℝ) < n := by exact_mod_cast hm.2
    have h0 : 0 < Real.pi * m / n := by
      have := Real.pi_pos
      positivity
    have h1 : Real.pi * m / n < Real.pi := by
      rw [div_lt_iff₀ hnR]
      have := Real.pi_pos
      nlinarith
    exact (Real.sin_pos_of_pos_of_lt_pi h0 h1).ne'
  have hterm : ∀ m ∈ Ico 1 n, ctn n m * Real.sin (2 * (a : ℝ) * (Real.pi * m / n))
      = 2 * (∑ j ∈ range (a + 1), Real.cos (2 * (j : ℝ) * (Real.pi * m / n))) - 1
        - Real.cos (2 * (a : ℝ) * (Real.pi * m / n)) := by
    intro m hm
    rw [ctn]
    exact cot_sin_identity _ (hsin m hm) a
  rw [Finset.sum_congr rfl hterm]
  have hinner : ∀ j : ℕ, j < n →
      ∑ m ∈ Ico 1 n, Real.cos (2 * (j : ℝ) * (Real.pi * m / n))
        = (if j = 0 then (n : ℝ) else 0) - 1 := by
    intro j hj
    have h1 : ∑ m ∈ range n, Real.cos (2 * (j : ℝ) * (Real.pi * m / n))
        = if n ∣ j then (n : ℝ) else 0 := by
      rw [← sum_cos_full n j hn]
      refine Finset.sum_congr rfl fun m _ => ?_
      congr 1
      push_cast
      ring
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn] at h1
    have h0 : Real.cos (2 * (j : ℝ) * (Real.pi * ((0 : ℕ) : ℝ) / n)) = 1 := by
      norm_num
    rw [h0] at h1
    have hdvd : (n ∣ j) ↔ (j = 0) := by
      constructor
      · intro hd
        exact Nat.eq_zero_of_dvd_of_lt hd hj
      · rintro rfl
        exact dvd_zero n
    rw [if_congr hdvd rfl rfl] at h1
    linarith
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm]
  have hcard : ∑ _m ∈ Ico 1 n, (1 : ℝ) = (n : ℝ) - 1 := by
    rw [Finset.sum_const, Nat.card_Ico]
    have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ n := hn
      push_cast [Nat.cast_sub h1]
      ring
    simp [this]
  have hsumj : ∑ j ∈ range (a + 1), ∑ m ∈ Ico 1 n, Real.cos (2 * (j : ℝ) * (Real.pi * m / n))
      = (n : ℝ) - (a + 1) := by
    have h1 : ∀ j ∈ range (a + 1), ∑ m ∈ Ico 1 n, Real.cos (2 * (j : ℝ) * (Real.pi * m / n))
        = (if j = 0 then (n : ℝ) else 0) - 1 := by
      intro j hj
      rw [Finset.mem_range] at hj
      exact hinner j (by omega)
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib]
    have h2 : ∑ j ∈ range (a + 1), (if j = 0 then (n : ℝ) else 0) = n := by
      rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos a))]
      · simp
      · intro j _ hj0
        rw [if_neg hj0]
    rw [h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  rw [hsumj, hcard, hinner a ha]
  split_ifs with h
  · subst h
    push_cast
    ring
  · push_cast
    ring

/-! ## The imaginary part of the Gauss sum and the deficiency identity -/

/-- `aa n = A048153 n`, the sum of `k² mod n`. -/
def aa (n : ℕ) : ℕ := ∑ k ∈ range n, k ^ 2 % n

/-- The mirror sum of `(-k²) mod n`. -/
def aneg (n : ℕ) : ℕ := ∑ k ∈ range n, (n - k ^ 2 % n) % n

lemma gq_im_eq (n : ℕ) (m : ℕ) :
    (gq m n).im = ∑ k ∈ range n, Real.sin (2 * ((k ^ 2 % n : ℕ) : ℝ) * (Real.pi * m / n)) := by
  rw [gq, Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : E (((m * k ^ 2 : ℕ) : ℝ) / n) = E (((m * (k ^ 2 % n) : ℕ) : ℝ) / n) :=
    E_div_congr (Nat.ModEq.mul_left m (Nat.mod_modEq (k ^ 2) n).symm)
  rw [h1, E_im]
  congr 1
  push_cast
  ring

/-- The master identity: the cotangent-weighted sum of `Im (gq m n)` equals
`aneg n - aa n`. -/
theorem delta_eq (n : ℕ) (hn : 0 < n) :
    ∑ m ∈ Ico 1 n, ctn n m * (gq m n).im = (aneg n : ℝ) - (aa n : ℝ) := by
  have h1 : ∑ m ∈ Ico 1 n, ctn n m * (gq m n).im
      = ∑ k ∈ range n, ∑ m ∈ Ico 1 n,
          ctn n m * Real.sin (2 * ((k ^ 2 % n : ℕ) : ℝ) * (Real.pi * m / n)) := by
    rw [Finset.sum_congr rfl fun m _ => by rw [gq_im_eq n m, Finset.mul_sum]]
    exact Finset.sum_comm
  rw [h1]
  have h2 : ∀ k ∈ range n, ∑ m ∈ Ico 1 n,
      ctn n m * Real.sin (2 * ((k ^ 2 % n : ℕ) : ℝ) * (Real.pi * m / n))
      = if k ^ 2 % n = 0 then 0 else (n : ℝ) - 2 * ((k ^ 2 % n : ℕ) : ℝ) := by
    intro k _
    exact kernel_sum hn (Nat.mod_lt _ hn)
  rw [Finset.sum_congr rfl h2, aneg, aa]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k ^ 2 % n = 0
  · rw [if_pos hk, hk]
    simp
  · rw [if_neg hk]
    have hlt : k ^ 2 % n < n := Nat.mod_lt _ hn
    have h3 : (n - k ^ 2 % n) % n = n - k ^ 2 % n := Nat.mod_eq_of_lt (by omega)
    rw [h3]
    have h4 : ((n - k ^ 2 % n : ℕ) : ℝ) = (n : ℝ) - ((k ^ 2 % n : ℕ) : ℝ) := by
      rw [Nat.cast_sub hlt.le]
    rw [h4]
    ring

/-! ## Splitting over divisors -/

/-- The local quantity `V(q)`: cotangent-weighted sum of `Im (gq m q)` over
residues coprime to `q`. -/
noncomputable def Vq (q : ℕ) : ℝ :=
  ∑ m ∈ (Ico 1 q).filter (fun m => Nat.Coprime m q), ctn q m * (gq m q).im

theorem delta_divisor_split (n : ℕ) (hn : 0 < n) :
    ∑ m ∈ Ico 1 n, ctn n m * (gq m n).im
      = ∑ q ∈ n.divisors.filter (fun q => 1 < q), ((n / q : ℕ) : ℝ) * Vq q := by
  have hnR : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- write the right-hand side as a sum over a set of pairs
  simp only [Vq, Finset.mul_sum]
  rw [← Finset.sum_finset_product' (r := ((n.divisors.filter (fun q => 1 < q)) ×ˢ Ico 1 n).filter
    (fun p => p.2 < p.1 ∧ Nat.Coprime p.2 p.1))
    (s := n.divisors.filter (fun q => 1 < q))
    (t := fun q => (Ico 1 q).filter (fun m => Nat.Coprime m q)) ?memiff]
  case memiff =>
    rintro ⟨q, m⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨⟨hqd, hn0⟩, hq1⟩, ⟨hm1, hmn⟩⟩, hmq, hcop⟩
      exact ⟨⟨⟨hqd, hn0⟩, hq1⟩, ⟨⟨hm1, hmq⟩, hcop⟩⟩
    · rintro ⟨⟨⟨hqd, hn0⟩, hq1⟩, ⟨⟨hm1, hmq⟩, hcop⟩⟩
      have hqn : q ≤ n := Nat.le_of_dvd hn hqd
      exact ⟨⟨⟨⟨hqd, hn0⟩, hq1⟩, ⟨hm1, by omega⟩⟩, hmq, hcop⟩
  -- now a bijection between pairs and `Ico 1 n`
  refine Finset.sum_nbij' (fun m : ℕ => ((n / Nat.gcd m n, m / Nat.gcd m n) : ℕ × ℕ))
    (fun p : ℕ × ℕ => (n / p.1) * p.2) ?_ ?_ ?_ ?_ ?_
  · -- maps into the pair set
    intro m hm
    rw [Finset.mem_Ico] at hm
    obtain ⟨hm1, hmn⟩ := hm
    have hmpos : 0 < m := hm1
    have hg0 : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n hmpos
    have hgm : Nat.gcd m n ∣ m := Nat.gcd_dvd_left m n
    have hgn : Nat.gcd m n ∣ n := Nat.gcd_dvd_right m n
    have hq1 : 1 < n / Nat.gcd m n := by
      have hqpos : 0 < n / Nat.gcd m n := Nat.div_pos (Nat.le_of_dvd hn hgn) hg0
      rcases Nat.lt_or_ge 1 (n / Nat.gcd m n) with h | h
      · exact h
      · exfalso
        have hq1' : n / Nat.gcd m n = 1 := by omega
        have hgeq : Nat.gcd m n = n := by
          have := Nat.div_mul_cancel hgn
          rw [hq1', one_mul] at this
          exact this
        have hnm : n ∣ m := hgeq ▸ hgm
        exact absurd (Nat.le_of_dvd hmpos hnm) (by omega)
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, Nat.mem_divisors,
      Finset.mem_Ico]
    refine ⟨⟨⟨⟨Nat.div_dvd_of_dvd hgn, hn.ne'⟩, hq1⟩,
      ⟨Nat.div_pos (Nat.le_of_dvd hmpos hgm) hg0, ?_⟩⟩,
      Nat.div_lt_div_of_lt_of_dvd hgn hmn, Nat.coprime_div_gcd_div_gcd hg0⟩
    calc m / Nat.gcd m n ≤ m := Nat.div_le_self _ _
    _ < n := hmn
  · -- maps back into `Ico 1 n`
    rintro ⟨q, m'⟩ hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, Nat.mem_divisors,
      Finset.mem_Ico] at hp
    obtain ⟨⟨⟨⟨hqd, -⟩, hq1⟩, ⟨hm'1, -⟩⟩, hm'q, -⟩ := hp
    have hqpos : 0 < q := by omega
    have hdq : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hn hqd) hqpos
    rw [Finset.mem_Ico]
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hdq.ne' (by omega))
    · show n / q * m' < n
      have h1 : (n / q) * m' < (n / q) * q := mul_lt_mul_of_pos_left hm'q hdq
      have h2 : (n / q) * q = n := Nat.div_mul_cancel hqd
      omega
  · -- left inverse
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hmpos : 0 < m := hm.1
    have hgm : Nat.gcd m n ∣ m := Nat.gcd_dvd_left m n
    have hgn : Nat.gcd m n ∣ n := Nat.gcd_dvd_right m n
    show (n / (n / Nat.gcd m n)) * (m / Nat.gcd m n) = m
    rw [Nat.div_div_self hgn hn.ne', Nat.mul_div_cancel' hgm]
  · -- right inverse
    rintro ⟨q, m'⟩ hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, Nat.mem_divisors,
      Finset.mem_Ico] at hp
    obtain ⟨⟨⟨⟨hqd, -⟩, hq1⟩, ⟨hm'1, -⟩⟩, hm'q, hcop⟩ := hp
    have hqpos : 0 < q := by omega
    have hdq : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hn hqd) hqpos
    set D := n / q with hDdef
    have hDq : D * q = n := Nat.div_mul_cancel hqd
    have hgcd : Nat.gcd (D * m') n = D := by
      rw [← hDq, Nat.gcd_mul_left, hcop, mul_one]
    have h1 : n / Nat.gcd (D * m') n = q := by
      rw [hgcd, hDdef, Nat.div_div_self hqd hn.ne']
    have h2 : (D * m') / Nat.gcd (D * m') n = m' := by
      rw [hgcd, Nat.mul_div_cancel_left m' hdq]
    show ((n / Nat.gcd (D * m') n, (D * m') / Nat.gcd (D * m') n) : ℕ × ℕ) = (q, m')
    rw [h1, h2]
  · -- value equality
    intro m hm
    rw [Finset.mem_Ico] at hm
    obtain ⟨hm1, hmn⟩ := hm
    have hmpos : 0 < m := hm1
    set g := Nat.gcd m n with hgdef
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_left n hmpos
    have hgm : g ∣ m := Nat.gcd_dvd_left m n
    have hgn : g ∣ n := Nat.gcd_dvd_right m n
    set q := n / g with hqdef
    set m' := m / g with hm'def
    have hqpos : 0 < q := Nat.div_pos (Nat.le_of_dvd hn hgn) hg0
    have hqR : ((q : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hqpos.ne'
    have hqd : q ∣ n := Nat.div_dvd_of_dvd hgn
    have hkey : m * q = m' * n := by
      have h1 : g * (m * q) = g * (m' * n) := by
        calc g * (m * q) = m * (g * q) := by ring
        _ = m * n := by rw [hqdef, Nat.mul_div_cancel' hgn]
        _ = (g * m') * n := by rw [hm'def, Nat.mul_div_cancel' hgm]
        _ = g * (m' * n) := by ring
      exact Nat.eq_of_mul_eq_mul_left hg0 h1
    have hkeyR : (m : ℝ) * q = (m' : ℝ) * n := by exact_mod_cast hkey
    have hctn : ctn n m = ctn q m' := by
      rw [ctn, ctn]
      have harg : Real.pi * m / n = Real.pi * m' / q := by
        rw [div_eq_div_iff hnR hqR]
        linear_combination Real.pi * hkeyR
      rw [harg]
    have hgq : gq m n = (n / q : ℕ) • gq m' q := by
      rw [← sum_range_E_dvd m' q n hqd, gq]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      rw [div_eq_div_iff hnR ?_]
      · push_cast
        linear_combination ((k : ℝ)) ^ 2 * hkeyR
      · exact hqR
    have him : (gq m n).im = ((n / q : ℕ) : ℝ) * (gq m' q).im := by
      rw [hgq, nsmul_eq_mul]
      simp [Complex.mul_im]
    show ctn n m * (gq m n).im
      = ((n / (n / g) : ℕ) : ℝ) * (ctn (n / g) (m / g) * (gq (m / g) (n / g)).im)
    rw [Nat.div_div_self hgn hn.ne']
    rw [hctn, him]
    have hnq : n / q = g := by
      rw [hqdef, Nat.div_div_self hgn hn.ne']
    rw [hnq]
    ring

end OEIS48153

end

/-! # Section from Dev/LSeries.lean -/

section

open Finset Filter Topology

namespace OEIS48153

/-! ### Real cotangent partial fraction expansion -/

theorem coe_mem_integerComplement_of_Ioo {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    (x : ℂ) ∈ Complex.integerComplement := by
  simp only [Complex.integerComplement, Set.mem_compl_iff, Set.mem_range, not_exists]
  intro n hn
  have hx : (n : ℝ) = x := by
    have := congrArg Complex.re hn
    simpa using this
  rcases le_or_gt n 0 with h | h
  · have : (n : ℝ) ≤ 0 := by exact_mod_cast h
    linarith
  · have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    linarith

theorem real_cot_hasSum {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    HasSum (fun n : ℕ => 1 / (x - (n + 1)) + 1 / (x + (n + 1)))
      (Real.pi * Real.cot (Real.pi * x) - 1 / x) := by
  have hz := coe_mem_integerComplement_of_Ioo h0 h1
  have hs : HasSum (fun n : ℕ => cotTerm (x : ℂ) n)
      (↑Real.pi * Complex.cot (↑Real.pi * (x : ℂ)) - 1 / (x : ℂ)) := by
    have h := (Summable_cotTerm hz).hasSum
    simp only [cotTerm] at h ⊢
    rwa [← cot_series_rep' hz] at h
  rw [← Complex.hasSum_ofReal]
  convert hs using 1
  · funext n
    simp only [cotTerm]
    push_cast
    ring
  · push_cast [Complex.ofReal_cot]
    ring

/-- The per-residue partial fraction block. -/
theorem block_hasSum {q m : ℕ} (hm1 : 1 ≤ m) (hmq : m < q) :
    HasSum (fun n : ℕ => 1 / ((m : ℝ) + ((n : ℝ) + 1) * q) - 1 / (((n : ℝ) + 1) * q - m))
      (Real.pi / q * ctn q m - 1 / m) := by
  have hqn : 0 < q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmq' : (m : ℝ) < q := by exact_mod_cast hmq
  have hx0 : 0 < (m : ℝ) / q := div_pos hm0 hq0
  have hx1 : (m : ℝ) / q < 1 := (div_lt_one hq0).mpr hmq'
  have h := (real_cot_hasSum hx0 hx1).div_const q
  have hterm : ∀ n : ℕ,
      (1 / ((m : ℝ) / q - ((n : ℝ) + 1)) + 1 / ((m : ℝ) / q + ((n : ℝ) + 1))) / q
        = 1 / ((m : ℝ) + ((n : ℝ) + 1) * q) - 1 / (((n : ℝ) + 1) * q - m) := by
    intro n
    have hq' := hq0.ne'
    have e1 : ((m : ℝ) / q - ((n : ℝ) + 1)) * q = (m : ℝ) - ((n : ℝ) + 1) * q := by
      rw [sub_mul, div_mul_cancel₀ _ hq']
    have e2 : ((m : ℝ) / q + ((n : ℝ) + 1)) * q = (m : ℝ) + ((n : ℝ) + 1) * q := by
      rw [add_mul, div_mul_cancel₀ _ hq']
    rw [add_div, div_div, div_div, e1, e2,
      show (m : ℝ) - ((n : ℝ) + 1) * q = -(((n : ℝ) + 1) * q - m) by ring, div_neg]
    ring
  have hval : (Real.pi * Real.cot (Real.pi * ((m : ℝ) / q)) - 1 / ((m : ℝ) / q)) / q
      = Real.pi / q * ctn q m - 1 / m := by
    have hctn : ctn q m = Real.cot (Real.pi * m / q) := by
      rw [Real.cot_eq_cos_div_sin]; rfl
    rw [hctn, show Real.pi * ((m : ℝ) / q) = Real.pi * m / q by ring]
    field_simp
  convert h using 1
  · exact funext fun n => (hterm n).symm
  · exact hval.symm

/-! ### Character-type sums -/

section CharSum

variable {q : ℕ} {ψ : ℕ → ℝ}

theorem psi_zero (hper : ∀ n, ψ (n + q) = ψ n)
    (hodd : ∀ a b, a + b = q → ψ a = -ψ b) : ψ 0 = 0 := by
  have h1 := hodd 0 q (zero_add q)
  have h2 := hper 0
  rw [zero_add] at h2
  linarith

theorem psi_period_mul (hper : ∀ n, ψ (n + q) = ψ n) :
    ∀ j a, ψ (j * q + a) = ψ a := by
  intro j
  induction j with
  | zero => intro a; simp
  | succ j ih =>
    intro a
    have hrw : (j + 1) * q + a = j * q + a + q := by ring
    rw [hrw, hper, ih]

theorem psi_ico_sum_zero (hodd : ∀ a b, a + b = q → ψ a = -ψ b) :
    ∑ m ∈ Ico 1 q, ψ m = 0 := by
  have key : ∑ m ∈ Ico 1 q, ψ m = ∑ m ∈ Ico 1 q, -ψ m := by
    refine Finset.sum_nbij' (fun m => q - m) (fun m => q - m) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [mem_Ico] at ha ⊢
      omega
    · intro a ha
      simp only [mem_Ico] at ha ⊢
      omega
    · intro a ha
      simp only [mem_Ico] at ha
      show q - (q - a) = a
      omega
    · intro a ha
      simp only [mem_Ico] at ha
      show q - (q - a) = a
      omega
    · intro a ha
      simp only [mem_Ico] at ha
      show ψ a = -ψ (q - a)
      exact hodd a (q - a) (by omega)
  have h2 : ∑ m ∈ Ico 1 q, ψ m = -∑ m ∈ Ico 1 q, ψ m := by
    conv_lhs => rw [key]
    rw [Finset.sum_neg_distrib]
  linarith

/-- Blocks of the Dirichlet series over one period. -/
noncomputable def Cb (ψ : ℕ → ℝ) (q : ℕ) (s : ℝ) (j : ℕ) : ℝ :=
  ∑ a ∈ Ico 1 q, ψ a * ((j * q + a : ℕ) : ℝ) ^ (-s)

theorem Cb_one_eq (ψ : ℕ → ℝ) (q j : ℕ) :
    Cb ψ q 1 j = ∑ a ∈ Ico 1 q, ψ a * (1 / ((j : ℝ) * q + a)) := by
  simp only [Cb]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Real.rpow_neg_one]
  push_cast
  ring

/-- Elementary bound for differences of negative powers. -/
theorem rpow_diff_bound {u v s : ℝ} (hu1 : 1 ≤ u) (huv : u ≤ v)
    (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    u ^ (-s) - v ^ (-s) ≤ (v - u) * (v + u) / (u * v ^ 2) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu1
  have hv0 : (0 : ℝ) < v := lt_of_lt_of_le hu0 huv
  have hx0 : 0 < u / v := div_pos hu0 hv0
  have hx1 : u / v ≤ 1 := (div_le_one hv0).mpr huv
  have hA : u ^ (-s) ≤ u⁻¹ := by
    have h := Real.rpow_le_rpow_of_exponent_le hu1 (neg_le_neg hs1)
    rwa [Real.rpow_neg_one] at h
  have hB : (u / v) ^ (2 : ℝ) ≤ (u / v) ^ s :=
    Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hs2
  have hC : (u / v) ^ s ≤ 1 := Real.rpow_le_one hx0.le hx1 (by linarith)
  have hus : (0 : ℝ) < u ^ s := Real.rpow_pos_of_pos hu0 s
  have hvs : (0 : ℝ) < v ^ s := Real.rpow_pos_of_pos hv0 s
  have hus' := hus.ne'
  have hvs' := hvs.ne'
  have hEq : u ^ (-s) - v ^ (-s) = u ^ (-s) * (1 - (u / v) ^ s) := by
    rw [Real.div_rpow hu0.le hv0.le, Real.rpow_neg hu0.le, Real.rpow_neg hv0.le]
    field_simp
  calc u ^ (-s) - v ^ (-s) = u ^ (-s) * (1 - (u / v) ^ s) := hEq
    _ ≤ u⁻¹ * (1 - (u / v) ^ (2 : ℝ)) := by
        apply mul_le_mul hA (by linarith) (by linarith) (inv_nonneg.mpr hu0.le)
    _ = (v - u) * (v + u) / (u * v ^ 2) := by
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        have hu' := hu0.ne'
        have hv' := hv0.ne'
        field_simp
        ring

theorem Cb_bound_zero (hbound : ∀ n, |ψ n| ≤ 1) {s : ℝ} (hs : 1 ≤ s) :
    |Cb ψ q s 0| ≤ (q : ℝ) := by
  simp only [Cb]
  calc |∑ a ∈ Ico 1 q, ψ a * ((0 * q + a : ℕ) : ℝ) ^ (-s)|
      ≤ ∑ a ∈ Ico 1 q, |ψ a * ((0 * q + a : ℕ) : ℝ) ^ (-s)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Ico 1 q, (1 : ℝ) := by
        refine Finset.sum_le_sum fun a ha => ?_
        have ha1 : 1 ≤ a := (Finset.mem_Ico.mp ha).1
        have hcast : (1 : ℝ) ≤ ((0 * q + a : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 1 ≤ 0 * q + a)
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
        have h1 : ((0 * q + a : ℕ) : ℝ) ^ (-s) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hcast (by linarith)
        have h2 := mul_le_mul (hbound a) h1 (Real.rpow_nonneg (by positivity) _) zero_le_one
        simpa using h2
    _ = ((q - 1 : ℕ) : ℝ) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    _ ≤ (q : ℝ) := by exact_mod_cast Nat.sub_le q 1

theorem Cb_bound_pos (hq : 2 ≤ q) (hodd : ∀ a b, a + b = q → ψ a = -ψ b)
    (hbound : ∀ n, |ψ n| ≤ 1) {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2)
    {j : ℕ} (hj : 1 ≤ j) : |Cb ψ q s j| ≤ 2 / (j : ℝ) ^ 2 := by
  have hzero := psi_ico_sum_zero hodd
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hCb : Cb ψ q s j = ∑ a ∈ Ico 1 q,
      ψ a * (((j * q + a : ℕ) : ℝ) ^ (-s) - ((j * q + q : ℕ) : ℝ) ^ (-s)) := by
    simp only [Cb, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hzero, zero_mul, sub_zero]
  rw [hCb]
  have hbnd : ∀ a ∈ Ico 1 q,
      |ψ a * (((j * q + a : ℕ) : ℝ) ^ (-s) - ((j * q + q : ℕ) : ℝ) ^ (-s))|
        ≤ 2 / ((q : ℝ) * (j : ℝ) ^ 2) := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_Ico.mp ha
    set u : ℝ := ((j * q + a : ℕ) : ℝ) with hu
    set v : ℝ := ((j * q + q : ℕ) : ℝ) with hv
    have huE : u = (j : ℝ) * q + a := by rw [hu]; push_cast; ring
    have hvE : v = (j : ℝ) * q + q := by rw [hv]; push_cast; ring
    have haR1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
    have haRq : (a : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast (by omega : a + 1 ≤ q)
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have huv : u ≤ v := by rw [huE, hvE]; linarith
    have hu1 : (1 : ℝ) ≤ u := by rw [huE]; nlinarith
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu1
    have hv0 : (0 : ℝ) < v := lt_of_lt_of_le hu0 huv
    have hd := rpow_diff_bound hu1 huv hs1 hs2
    have hd0 : 0 ≤ u ^ (-s) - v ^ (-s) :=
      sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos hu0 huv (by linarith))
    rw [abs_mul, abs_of_nonneg hd0]
    have h1 : |ψ a| * (u ^ (-s) - v ^ (-s)) ≤ u ^ (-s) - v ^ (-s) := by
      nlinarith [hbound a, abs_nonneg (ψ a)]
    refine le_trans h1 (le_trans hd ?_)
    have hQJu : (j : ℝ) * q ≤ u := by rw [huE]; nlinarith
    have hQJv : (j : ℝ) * q ≤ v := by rw [hvE]; nlinarith
    have hkey : ((j : ℝ) * q) * ((j : ℝ) * q) ≤ u * v :=
      mul_le_mul hQJu hQJv (by positivity) (by linarith)
    rw [div_le_div_iff₀ (mul_pos hu0 (pow_pos hv0 2)) (mul_pos hq0 (pow_pos hj0 2))]
    have h1' : v - u ≤ (q : ℝ) := by rw [huE, hvE]; linarith
    have h2' : v + u ≤ 2 * v := by linarith
    have hs1' : (v - u) * (v + u) ≤ (q : ℝ) * (2 * v) := by nlinarith
    have hs2' : (v - u) * (v + u) * ((q : ℝ) * (j : ℝ) ^ 2)
        ≤ (q : ℝ) * (2 * v) * ((q : ℝ) * (j : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hs1' (by positivity)
    have hs3' : ((j : ℝ) * q) * ((j : ℝ) * q) * (2 * v) ≤ u * v * (2 * v) :=
      mul_le_mul_of_nonneg_right hkey (by linarith)
    nlinarith [hs2', hs3']
  calc |∑ a ∈ Ico 1 q, ψ a * (((j * q + a : ℕ) : ℝ) ^ (-s) - ((j * q + q : ℕ) : ℝ) ^ (-s))|
      ≤ ∑ a ∈ Ico 1 q,
          |ψ a * (((j * q + a : ℕ) : ℝ) ^ (-s) - ((j * q + q : ℕ) : ℝ) ^ (-s))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Ico 1 q, 2 / ((q : ℝ) * (j : ℝ) ^ 2) := Finset.sum_le_sum hbnd
    _ = ((q - 1 : ℕ) : ℝ) * (2 / ((q : ℝ) * (j : ℝ) ^ 2)) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ (q : ℝ) * (2 / ((q : ℝ) * (j : ℝ) ^ 2)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Nat.sub_le q 1
    _ = 2 / (j : ℝ) ^ 2 := by
        field_simp

/-- Dominating sequence. -/
noncomputable def Mb (q : ℕ) (j : ℕ) : ℝ := if j = 0 then (q : ℝ) else 2 / (j : ℝ) ^ 2

theorem Mb_summable (q : ℕ) : Summable (Mb q) := by
  rw [← summable_nat_add_iff 1]
  have h0 : Summable fun n : ℕ => 1 / ((n : ℝ)) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have h1 : Summable fun n : ℕ => (2 : ℝ) * (1 / (((n + 1 : ℕ) : ℝ)) ^ 2) :=
    ((summable_nat_add_iff 1).mpr h0).mul_left 2
  refine h1.congr fun n => ?_
  have hne : n + 1 ≠ 0 := Nat.succ_ne_zero n
  simp only [Mb, hne, if_false]
  rw [mul_one_div]

theorem psi_norm_summable (hbound : ∀ n, |ψ n| ≤ 1) {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ => ‖ψ n * (n : ℝ) ^ (-s)‖ := by
  have hbase : Summable fun n : ℕ => ((n : ℝ) ^ s)⁻¹ := Real.summable_nat_rpow_inv.mpr hs
  refine Summable.of_norm_bounded hbase fun n => ?_
  rw [norm_norm, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    Real.rpow_neg (Nat.cast_nonneg n)]
  exact le_trans (mul_le_mul_of_nonneg_right (hbound n) (by positivity))
    (le_of_eq (one_mul _))

theorem psi_summable (hbound : ∀ n, |ψ n| ≤ 1) {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ => ψ n * (n : ℝ) ^ (-s) :=
  (psi_norm_summable hbound hs).of_norm

/-- Positivity of the L-value via the Euler product. -/
theorem L_nonneg (hmul : ∀ a b, ψ (a * b) = ψ a * ψ b) (hone : ψ 1 = 1)
    (hzero : ψ 0 = 0) (hbound : ∀ n, |ψ n| ≤ 1) {s : ℝ} (hs : 1 < s) :
    0 ≤ ∑' n : ℕ, ψ n * (n : ℝ) ^ (-s) := by
  set f : ℕ →*₀ ℝ :=
    { toFun := fun n => ψ n * (n : ℝ) ^ (-s)
      map_zero' := by simp [hzero]
      map_one' := by simp [hone]
      map_mul' := by
        intro a b
        show ψ (a * b) * ((a * b : ℕ) : ℝ) ^ (-s)
          = (ψ a * (a : ℝ) ^ (-s)) * (ψ b * (b : ℝ) ^ (-s))
        push_cast
        rw [Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b), hmul]
        ring } with hfdef
  have hsum : Summable fun n => ‖f n‖ := psi_norm_summable hbound hs
  have hprod := EulerProduct.eulerProduct_completely_multiplicative_hasProd hsum
  have hfactor : ∀ p : Nat.Primes, 0 ≤ (1 - f p)⁻¹ := by
    intro p
    have hp2 : 2 ≤ (p : ℕ) := p.prop.two_le
    have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < (p : ℕ))
    have hlt : ((p : ℕ) : ℝ) ^ (-s) < 1 := by
      rw [Real.rpow_neg (by positivity)]
      have h1s : (1 : ℝ) < ((p : ℕ) : ℝ) ^ s :=
        (Real.one_lt_rpow_iff_of_pos (by positivity)).mpr (Or.inl ⟨hp1, by linarith⟩)
      exact inv_lt_one_of_one_lt₀ h1s
    have habs : |f p| ≤ ((p : ℕ) : ℝ) ^ (-s) := by
      show |ψ p * ((p : ℕ) : ℝ) ^ (-s)| ≤ _
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact le_trans (mul_le_mul_of_nonneg_right (hbound p) (by positivity))
        (le_of_eq (one_mul _))
    have hfp : f p < 1 := lt_of_le_of_lt (le_trans (le_abs_self _) habs) hlt
    exact inv_nonneg.mpr (by linarith)
  have ht : Filter.Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S, (1 - f p)⁻¹)
      (SummationFilter.unconditional Nat.Primes).filter (𝓝 (∑' n, f n)) := hprod
  have hge : 0 ≤ ∑' n, f n :=
    ge_of_tendsto' ht fun S => Finset.prod_nonneg fun p _ => hfactor p
  exact hge

/-- Regrouping the Dirichlet series into blocks. -/
theorem L_hasSum_Cb (hq : 2 ≤ q) (hper : ∀ n, ψ (n + q) = ψ n) (hzero : ψ 0 = 0)
    {s : ℝ} (hsummable : Summable fun n : ℕ => ψ n * (n : ℝ) ^ (-s)) :
    HasSum (fun j => Cb ψ q s j) (∑' n : ℕ, ψ n * (n : ℝ) ^ (-s)) := by
  haveI : NeZero q := ⟨by omega⟩
  have hf : HasSum ((fun n : ℕ => ψ n * (n : ℝ) ^ (-s)) ∘ (Nat.divModEquiv q).symm)
      (∑' n : ℕ, ψ n * (n : ℝ) ^ (-s)) :=
    ((Nat.divModEquiv q).symm.hasSum_iff).mpr hsummable.hasSum
  refine HasSum.prod_fiberwise hf fun j => ?_
  have hval : ∑ c : Fin q, ψ (j * q + (c : ℕ)) * ((j * q + (c : ℕ) : ℕ) : ℝ) ^ (-s)
      = Cb ψ q s j := by
    rw [Fin.sum_univ_eq_sum_range (fun a => ψ (j * q + a) * ((j * q + a : ℕ) : ℝ) ^ (-s)) q]
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < q)]
    have h0 : ψ (j * q + 0) * ((j * q + 0 : ℕ) : ℝ) ^ (-s) = 0 := by
      rw [psi_period_mul hper j 0, hzero, zero_mul]
    rw [h0, zero_add]
    simp only [zero_add, Cb]
    exact Finset.sum_congr rfl fun a _ => by rw [psi_period_mul hper]
  have hfin := hasSum_fintype
    (fun c : Fin q => ψ (j * q + (c : ℕ)) * ((j * q + (c : ℕ) : ℕ) : ℝ) ^ (-s))
  rw [hval] at hfin
  convert hfin using 1

theorem Cb_continuous (ψ : ℕ → ℝ) (q j : ℕ) : Continuous fun s : ℝ => Cb ψ q s j := by
  simp only [Cb]
  apply continuous_finset_sum
  intro a ha
  have ha1 : 1 ≤ a := (Finset.mem_Ico.mp ha).1
  have hpos : (0 : ℝ) < ((j * q + a : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < j * q + a)
  have hrw : (fun s : ℝ => ψ a * ((j * q + a : ℕ) : ℝ) ^ (-s))
      = fun s : ℝ => ψ a * Real.exp (Real.log ((j * q + a : ℕ) : ℝ) * (-s)) := by
    funext s
    rw [Real.rpow_def_of_pos hpos]
  rw [hrw]
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_neg))

/-- Termwise identity for the blocks. -/
theorem blocks_eq (hodd : ∀ a b, a + b = q → ψ a = -ψ b) (n : ℕ) :
    ∑ m ∈ Ico 1 q, ψ m * (1 / ((m : ℝ) + ((n : ℝ) + 1) * q) - 1 / (((n : ℝ) + 1) * q - m))
      = Cb ψ q 1 (n + 1) + Cb ψ q 1 n := by
  have hsplit : ∀ m ∈ Ico 1 q,
      ψ m * (1 / ((m : ℝ) + ((n : ℝ) + 1) * q) - 1 / (((n : ℝ) + 1) * q - m))
        = ψ m * (1 / ((m : ℝ) + ((n : ℝ) + 1) * q))
          + (-ψ m) * (1 / (((n : ℝ) + 1) * q - m)) := fun m _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  congr 1
  · rw [Cb_one_eq]
    refine Finset.sum_congr rfl fun a ha => ?_
    show ψ a * (1 / ((a : ℝ) + ((n : ℝ) + 1) * q)) = ψ a * (1 / (((n + 1 : ℕ) : ℝ) * q + a))
    have hden : (a : ℝ) + ((n : ℝ) + 1) * q = ((n + 1 : ℕ) : ℝ) * q + a := by
      push_cast; ring
    rw [hden]
  · rw [Cb_one_eq]
    refine Finset.sum_nbij' (fun m => q - m) (fun m => q - m) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [mem_Ico] at ha ⊢
      omega
    · intro a ha
      simp only [mem_Ico] at ha ⊢
      omega
    · intro a ha
      simp only [mem_Ico] at ha
      show q - (q - a) = a
      omega
    · intro a ha
      simp only [mem_Ico] at ha
      show q - (q - a) = a
      omega
    · intro m hm
      simp only [mem_Ico] at hm
      have h1 : ψ (q - m) = -ψ m := hodd (q - m) m (by omega)
      show (-ψ m) * (1 / (((n : ℝ) + 1) * (q : ℝ) - (m : ℝ)))
          = ψ (q - m) * (1 / ((n : ℝ) * (q : ℝ) + ((q - m : ℕ) : ℝ)))
      rw [h1, Nat.cast_sub (by omega : m ≤ q)]
      have hden : (n : ℝ) * (q : ℝ) + ((q : ℝ) - (m : ℝ)) = ((n : ℝ) + 1) * (q : ℝ) - (m : ℝ) := by
        ring
      rw [hden]

theorem blocks_value_eq :
    ∑ m ∈ Ico 1 q, ψ m * (Real.pi / q * ctn q m - 1 / m)
      = Real.pi / q * (∑ m ∈ Ico 1 q, ψ m * ctn q m) - Cb ψ q 1 0 := by
  rw [Cb_one_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h : ((0 : ℕ) : ℝ) * q + m = (m : ℝ) := by push_cast; ring
  rw [h]
  ring

/-- **Main theorem of this file**: nonnegativity of odd-character cotangent sums. -/
theorem cot_char_sum_nonneg {q : ℕ} (hq : 2 ≤ q) (ψ : ℕ → ℝ)
    (hper : ∀ n, ψ (n + q) = ψ n) (hmul : ∀ a b, ψ (a * b) = ψ a * ψ b)
    (hbound : ∀ n, |ψ n| ≤ 1) (hodd : ∀ a b, a + b = q → ψ a = -ψ b) :
    0 ≤ ∑ m ∈ Ico 1 q, ψ m * ctn q m := by
  by_cases hone : ψ 1 = 1
  swap
  · have h1 : ψ 1 * ψ 1 = ψ 1 := by
      have h := hmul 1 1
      rw [mul_one] at h
      linarith
    have h2 : ψ 1 * (ψ 1 - 1) = 0 := by rw [mul_sub, mul_one, h1, sub_self]
    have h0 : ψ 1 = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd (by linarith : ψ 1 = 1) hone
    have hall : ∀ m, ψ m = 0 := by
      intro m
      have h := hmul m 1
      rw [mul_one, h0, mul_zero] at h
      exact h
    simp [hall]
  · have hzero : ψ 0 = 0 := psi_zero hper hodd
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    -- Step 1: the blocks have the cotangent sum as their value
    have hm : ∀ m ∈ Ico 1 q, HasSum
        (fun n : ℕ => ψ m * (1 / ((m : ℝ) + ((n : ℝ) + 1) * q) - 1 / (((n : ℝ) + 1) * q - m)))
        (ψ m * (Real.pi / q * ctn q m - 1 / m)) := by
      intro m hm'
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hm'
      exact (block_hasSum h1 h2).mul_left (ψ m)
    have hblocks0 := hasSum_sum hm
    have hblocks : HasSum (fun n : ℕ => Cb ψ q 1 (n + 1) + Cb ψ q 1 n)
        (Real.pi / q * (∑ m ∈ Ico 1 q, ψ m * ctn q m) - Cb ψ q 1 0) := by
      convert hblocks0 using 1
      · exact funext fun n => (blocks_eq hodd n).symm
      · exact blocks_value_eq.symm
    -- Step 2: summability of the s = 1 blocks
    have hMb := Mb_summable q
    have hCb1bound : ∀ j, ‖Cb ψ q 1 j‖ ≤ Mb q j := by
      intro j
      rw [Real.norm_eq_abs]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simpa [Mb] using Cb_bound_zero hbound le_rfl
      · have h := Cb_bound_pos hq hodd hbound le_rfl one_le_two hj
        have hjne : j ≠ 0 := by omega
        simpa [Mb, hjne] using h
    have hCb1sum : Summable (Cb ψ q 1) := Summable.of_norm_bounded hMb hCb1bound
    -- Step 3: dominated convergence as s → 1⁺
    have hcont : ∀ j, Tendsto (fun s : ℝ => Cb ψ q s j) (𝓝[>] (1 : ℝ)) (𝓝 (Cb ψ q 1 j)) :=
      fun j => ((Cb_continuous ψ q j).tendsto 1).mono_left nhdsWithin_le_nhds
    have hbnd : ∀ᶠ s in 𝓝[>] (1 : ℝ), ∀ j, ‖Cb ψ q s j‖ ≤ Mb q j := by
      filter_upwards [Ioc_mem_nhdsGT one_lt_two] with s hs j
      obtain ⟨hs1, hs2⟩ := hs
      rw [Real.norm_eq_abs]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simpa [Mb] using Cb_bound_zero hbound hs1.le
      · have h := Cb_bound_pos hq hodd hbound hs1.le hs2 hj
        have hjne : j ≠ 0 := by omega
        simpa [Mb, hjne] using h
    have hDCT := tendsto_tsum_of_dominated_convergence hMb hcont hbnd
    -- Step 4: nonnegativity of the limit
    have hnn : ∀ᶠ s in 𝓝[>] (1 : ℝ), 0 ≤ ∑' j, Cb ψ q s j := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs1 : (1 : ℝ) < s := hs
      have hsummable := psi_summable hbound hs1
      have hHS := L_hasSum_Cb hq hper hzero hsummable
      rw [hHS.tsum_eq]
      exact L_nonneg hmul hone hzero hbound hs1
    have hL : 0 ≤ ∑' j, Cb ψ q 1 j := ge_of_tendsto hDCT hnn
    -- Step 5: assemble
    have h1 : HasSum (Cb ψ q 1) (∑' j, Cb ψ q 1 j) := hCb1sum.hasSum
    have h2 : HasSum (fun n => Cb ψ q 1 (n + 1))
        ((∑' j, Cb ψ q 1 j) - ∑ i ∈ range 1, Cb ψ q 1 i) :=
      (hasSum_nat_add_iff' 1).mpr h1
    have h3 := h2.add h1
    have h4 := h3.unique hblocks
    rw [Finset.sum_range_one] at h4
    have hπq : (0 : ℝ) < Real.pi / q := div_pos Real.pi_pos hq0
    by_contra hneg
    push_neg at hneg
    nlinarith [h4, hL, hπq, mul_pos hπq (neg_pos.mpr hneg)]

end CharSum

end OEIS48153

end

/-! # Section from Dev/Chars.lean -/

section

open Finset Complex

namespace OEIS48153

/-! ### Elementary sign characters mod 4 and mod 8 -/

noncomputable def c4 (m : ℕ) : ℝ :=
  if m % 4 = 1 then 1 else if m % 4 = 3 then -1 else 0

noncomputable def c8 (m : ℕ) : ℝ :=
  if m % 8 = 1 ∨ m % 8 = 7 then 1 else if m % 8 = 3 ∨ m % 8 = 5 then -1 else 0

noncomputable def c8' (m : ℕ) : ℝ :=
  if m % 8 = 1 ∨ m % 8 = 3 then 1 else if m % 8 = 5 ∨ m % 8 = 7 then -1 else 0

noncomputable def codd (m : ℕ) : ℝ := if m % 2 = 1 then 1 else 0

lemma c4_mul (a b : ℕ) : c4 (a * b) = c4 a * c4 b := by
  have h : (a * b) % 4 = a % 4 * (b % 4) % 4 := Nat.mul_mod a b 4
  rcases (by omega : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3) with ha | ha | ha | ha <;>
    rcases (by omega : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3) with hb | hb | hb | hb <;>
    simp [c4, h, ha, hb]

lemma c8_mul (a b : ℕ) : c8 (a * b) = c8 a * c8 b := by
  have h : (a * b) % 8 = a % 8 * (b % 8) % 8 := Nat.mul_mod a b 8
  rcases (by omega : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨
      a % 8 = 6 ∨ a % 8 = 7) with ha | ha | ha | ha | ha | ha | ha | ha <;>
    rcases (by omega : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨
      b % 8 = 6 ∨ b % 8 = 7) with hb | hb | hb | hb | hb | hb | hb | hb <;>
    simp [c8, h, ha, hb]

lemma c8'_mul (a b : ℕ) : c8' (a * b) = c8' a * c8' b := by
  have h : (a * b) % 8 = a % 8 * (b % 8) % 8 := Nat.mul_mod a b 8
  rcases (by omega : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨
      a % 8 = 6 ∨ a % 8 = 7) with ha | ha | ha | ha | ha | ha | ha | ha <;>
    rcases (by omega : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨
      b % 8 = 6 ∨ b % 8 = 7) with hb | hb | hb | hb | hb | hb | hb | hb <;>
    simp [c8', h, ha, hb]

lemma codd_mul (a b : ℕ) : codd (a * b) = codd a * codd b := by
  have h : (a * b) % 2 = a % 2 * (b % 2) % 2 := Nat.mul_mod a b 2
  rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with ha | ha <;>
    rcases (by omega : b % 2 = 0 ∨ b % 2 = 1) with hb | hb <;>
    simp [codd, h, ha, hb]

lemma c4_abs (m : ℕ) : |c4 m| ≤ 1 := by
  unfold c4; split_ifs <;> norm_num

lemma c8_abs (m : ℕ) : |c8 m| ≤ 1 := by
  unfold c8; split_ifs <;> norm_num

lemma c8'_abs (m : ℕ) : |c8' m| ≤ 1 := by
  unfold c8'; split_ifs <;> norm_num

lemma codd_abs (m : ℕ) : |codd m| ≤ 1 := by
  unfold codd; split_ifs <;> norm_num

lemma c4_even {m : ℕ} (hm : m % 2 = 0) : c4 m = 0 := by
  have h1 : m % 4 ≠ 1 := by omega
  have h3 : m % 4 ≠ 3 := by omega
  simp [c4, h1, h3]

lemma c8_even {m : ℕ} (hm : m % 2 = 0) : c8 m = 0 := by
  have h1 : ¬(m % 8 = 1 ∨ m % 8 = 7) := by omega
  have h3 : ¬(m % 8 = 3 ∨ m % 8 = 5) := by omega
  simp [c8, h1, h3]

lemma c8'_even {m : ℕ} (hm : m % 2 = 0) : c8' m = 0 := by
  have h1 : ¬(m % 8 = 1 ∨ m % 8 = 3) := by omega
  have h3 : ¬(m % 8 = 5 ∨ m % 8 = 7) := by omega
  simp [c8', h1, h3]

lemma codd_even {m : ℕ} (hm : m % 2 = 0) : codd m = 0 := by
  simp [codd, hm]

lemma codd_odd {m : ℕ} (hm : m % 2 = 1) : codd m = 1 := by
  simp [codd, hm]

lemma c4_one_val {w : ℕ} (h : w % 4 = 1) : c4 w = 1 := by
  simp [c4, h]

lemma c4_sq_odd {m : ℕ} (hm : m % 2 = 1) : c4 m ^ 2 = 1 := by
  rcases (by omega : m % 4 = 1 ∨ m % 4 = 3) with h | h <;> simp [c4, h] <;> norm_num

lemma c8_sq_odd {w : ℕ} (hw : w % 2 = 1) : c8 w ^ 2 = 1 := by
  rcases (by omega : w % 8 = 1 ∨ w % 8 = 3 ∨ w % 8 = 5 ∨ w % 8 = 7) with h | h | h | h <;>
    simp [c8, h] <;> norm_num

lemma c8'_mul_c8_of_one {w : ℕ} (hw : w % 2 = 1) (h4 : w % 4 = 1) : c8' w * c8 w = 1 := by
  rcases (by omega : w % 8 = 1 ∨ w % 8 = 5) with h | h <;> simp [c8, c8', h] <;> norm_num

/-! ### Periodicity and reflection -/

lemma c4_period {q : ℕ} (h4 : 4 ∣ q) (n : ℕ) : c4 (n + q) = c4 n := by
  have h : (n + q) % 4 = n % 4 := by omega
  simp only [c4, h]

lemma c8_period {q : ℕ} (h8 : 8 ∣ q) (n : ℕ) : c8 (n + q) = c8 n := by
  have h : (n + q) % 8 = n % 8 := by omega
  simp only [c8, h]

lemma c8'_period {q : ℕ} (h8 : 8 ∣ q) (n : ℕ) : c8' (n + q) = c8' n := by
  have h : (n + q) % 8 = n % 8 := by omega
  simp only [c8', h]

lemma codd_period {q : ℕ} (h2 : 2 ∣ q) (n : ℕ) : codd (n + q) = codd n := by
  have h : (n + q) % 2 = n % 2 := by omega
  simp only [codd, h]

lemma c4_reflect {q b : ℕ} (h4 : 4 ∣ q) (hb : b ≤ q) : c4 (q - b) = -c4 b := by
  rcases (by omega : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3) with h | h | h | h
  · have hqb : (q - b) % 4 = 0 := by omega
    simp [c4, h, hqb]
  · have hqb : (q - b) % 4 = 3 := by omega
    simp [c4, h, hqb]
  · have hqb : (q - b) % 4 = 2 := by omega
    simp [c4, h, hqb]
  · have hqb : (q - b) % 4 = 1 := by omega
    simp [c4, h, hqb]

lemma c8_reflect {q b : ℕ} (h8 : 8 ∣ q) (hb : b ≤ q) : c8 (q - b) = c8 b := by
  rcases (by omega : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨
      b % 8 = 6 ∨ b % 8 = 7) with h | h | h | h | h | h | h | h
  · have hqb : (q - b) % 8 = 0 := by omega
    simp [c8, h, hqb]
  · have hqb : (q - b) % 8 = 7 := by omega
    simp [c8, h, hqb]
  · have hqb : (q - b) % 8 = 6 := by omega
    simp [c8, h, hqb]
  · have hqb : (q - b) % 8 = 5 := by omega
    simp [c8, h, hqb]
  · have hqb : (q - b) % 8 = 4 := by omega
    simp [c8, h, hqb]
  · have hqb : (q - b) % 8 = 3 := by omega
    simp [c8, h, hqb]
  · have hqb : (q - b) % 8 = 2 := by omega
    simp [c8, h, hqb]
  · have hqb : (q - b) % 8 = 1 := by omega
    simp [c8, h, hqb]

lemma c8'_reflect {q b : ℕ} (h8 : 8 ∣ q) (hb : b ≤ q) : c8' (q - b) = -c8' b := by
  rcases (by omega : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨
      b % 8 = 6 ∨ b % 8 = 7) with h | h | h | h | h | h | h | h
  · have hqb : (q - b) % 8 = 0 := by omega
    simp [c8', h, hqb]
  · have hqb : (q - b) % 8 = 7 := by omega
    simp [c8', h, hqb]
  · have hqb : (q - b) % 8 = 6 := by omega
    simp [c8', h, hqb]
  · have hqb : (q - b) % 8 = 5 := by omega
    simp [c8', h, hqb]
  · have hqb : (q - b) % 8 = 4 := by omega
    simp [c8', h, hqb]
  · have hqb : (q - b) % 8 = 3 := by omega
    simp [c8', h, hqb]
  · have hqb : (q - b) % 8 = 2 := by omega
    simp [c8', h, hqb]
  · have hqb : (q - b) % 8 = 1 := by omega
    simp [c8', h, hqb]

lemma codd_reflect {q b : ℕ} (h2 : 2 ∣ q) (hb : b ≤ q) : codd (q - b) = codd b := by
  rcases (by omega : b % 2 = 0 ∨ b % 2 = 1) with h | h
  · have hqb : (q - b) % 2 = 0 := by omega
    simp [codd, h, hqb]
  · have hqb : (q - b) % 2 = 1 := by omega
    simp [codd, h, hqb]

/-! ### The Jacobi symbol as a real-valued function -/

noncomputable def jc (m w : ℕ) : ℝ := ((jacobiSym (m : ℤ) w : ℤ) : ℝ)

lemma jc_mul (a b w : ℕ) : jc (a * b) w = jc a w * jc b w := by
  unfold jc
  push_cast [jacobiSym.mul_left]
  ring

lemma jc_one_left (w : ℕ) : jc 1 w = 1 := by
  unfold jc
  norm_num [jacobiSym.one_left]

lemma jc_pow (a e w : ℕ) : jc (a ^ e) w = jc a w ^ e := by
  induction e with
  | zero => simpa using jc_one_left w
  | succ e ih => rw [pow_succ, jc_mul, ih, pow_succ]

lemma jc_abs (m w : ℕ) : |jc m w| ≤ 1 := by
  rcases jacobiSym.trichotomy (m : ℤ) w with h | h | h <;> simp [jc, h]

lemma jc_zero_of_not_coprime {m w : ℕ} (hw : w ≠ 0) (h : ¬ Nat.Coprime m w) : jc m w = 0 := by
  have hz : jacobiSym (m : ℤ) w = 0 :=
    jacobiSym.eq_zero_iff.mpr ⟨hw, by rw [Int.gcd_natCast_natCast]; exact h⟩
  simp [jc, hz]

lemma jc_add_dvd {w q : ℕ} (h : w ∣ q) (n : ℕ) : jc (n + q) w = jc n w := by
  unfold jc
  congr 1
  apply jacobiSym.mod_left'
  obtain ⟨t, rfl⟩ := h
  push_cast
  rw [Int.add_mul_emod_self_left]

lemma jc_reflect {w q b : ℕ} (hqw : w ∣ q) (hbq : b ≤ q) :
    jc (q - b) w = ((jacobiSym (-1) w : ℤ) : ℝ) * jc b w := by
  unfold jc
  rw [← Int.cast_mul, ← jacobiSym.mul_left]
  congr 1
  apply jacobiSym.mod_left'
  obtain ⟨t, rfl⟩ := hqw
  rw [Nat.cast_sub hbq]
  push_cast
  rw [show (w : ℤ) * t - b = -1 * b + w * t by ring, Int.add_mul_emod_self_left]

lemma jacobi_neg_one_of_one {w : ℕ} (hw : Odd w) (h4 : w % 4 = 1) :
    jacobiSym (-1) w = 1 := by
  rw [jacobiSym.at_neg_one hw, ZMod.χ₄_nat_eq_if_mod_four]
  have h2 := Nat.odd_iff.mp hw
  rw [if_neg (by omega), if_pos h4]

lemma jacobi_neg_one_of_three {w : ℕ} (hw : Odd w) (h4 : w % 4 = 3) :
    jacobiSym (-1) w = -1 := by
  rw [jacobiSym.at_neg_one hw, ZMod.χ₄_nat_eq_if_mod_four]
  have h2 := Nat.odd_iff.mp hw
  rw [if_neg (by omega), if_neg (by omega)]

lemma jc_two {w : ℕ} (hw : Odd w) : jc 2 w = c8 w := by
  unfold jc c8
  rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, jacobiSym.at_two hw, ZMod.χ₈_nat_eq_if_mod_eight]
  have h2 := Nat.odd_iff.mp hw
  rw [if_neg (by omega)]
  by_cases h : w % 8 = 1 ∨ w % 8 = 7
  · rw [if_pos h, if_pos h]; norm_num
  · rw [if_neg h, if_neg h, if_pos (by omega)]; norm_num

/-! ### Auxiliary facts -/

lemma coprime_two_of_odd {m : ℕ} (h : m % 2 = 1) : Nat.Coprime m 2 :=
  Nat.coprime_comm.mp ((Nat.prime_two.coprime_iff_not_dvd).mpr (by omega))

lemma abs_mul_le_one {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |x * y| ≤ 1 := by
  rw [abs_mul]
  calc |x| * |y| ≤ 1 * 1 := mul_le_mul hx hy (abs_nonneg y) zero_le_one
    _ = 1 := one_mul 1

/-! ### Complex value helpers -/

lemma I_pow_mod_four (m : ℕ) : I ^ m = I ^ (m % 4) := by
  conv_lhs => rw [← Nat.div_add_mod m 4]
  rw [pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

lemma I_pow_odd {m : ℕ} (hm : Odd m) : I ^ m = ((c4 m : ℝ) : ℂ) * I := by
  have h2 : m % 2 = 1 := Nat.odd_iff.mp hm
  rw [I_pow_mod_four]
  rcases (by omega : m % 4 = 1 ∨ m % 4 = 3) with h | h
  · rw [h, pow_one]
    have hc : c4 m = 1 := by simp [c4, h]
    rw [hc]
    norm_num
  · rw [h]
    have hc : c4 m = -1 := by simp [c4, h]
    rw [hc, show I ^ 3 = I ^ 2 * I from by ring, Complex.I_sq]
    push_cast
    ring

lemma neg_I_pow_four : (-I) ^ 4 = 1 := by
  rw [show (-I) ^ 4 = (I ^ 2) ^ 2 from by ring, Complex.I_sq]
  norm_num

lemma neg_I_pow_mod_four (m : ℕ) : (-I) ^ m = (-I) ^ (m % 4) := by
  conv_lhs => rw [← Nat.div_add_mod m 4]
  rw [pow_add, pow_mul, neg_I_pow_four, one_pow, one_mul]

lemma gq_one_mod_one {w : ℕ} (hw : 0 < w) (h4 : w % 4 = 1) :
    gq 1 w = ((Real.sqrt w : ℝ) : ℂ) := by
  rw [gauss_value w hw, neg_I_pow_mod_four, h4, pow_one]
  rw [show (1 + I) * (1 + -I) / 2 = 1 from by linear_combination (-(1 : ℂ) / 2) * Complex.I_sq]
  rw [one_mul]

lemma gq_one_mod_three {w : ℕ} (hw : 0 < w) (h4 : w % 4 = 3) :
    gq 1 w = I * ((Real.sqrt w : ℝ) : ℂ) := by
  rw [gauss_value w hw, neg_I_pow_mod_four, h4]
  rw [show (-I) ^ 3 = I from by linear_combination (-I) * Complex.I_sq]
  rw [show (1 + I) * (1 + I) / 2 = I from by linear_combination ((1 : ℂ) / 2) * Complex.I_sq]

lemma E_cos_sin (x : ℝ) :
    E x = ((Real.cos (2 * Real.pi * x) : ℝ) : ℂ)
        + ((Real.sin (2 * Real.pi * x) : ℝ) : ℂ) * I := by
  rw [E_eq_exp_mul_I, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

lemma E_eighth {m : ℕ} (hm : Odd m) :
    E ((m : ℝ) / 8) = ((Real.sqrt 2 / 2 * c8 m : ℝ) : ℂ)
      + ((Real.sqrt 2 / 2 * c8' m : ℝ) : ℂ) * I := by
  have h2 : m % 2 = 1 := Nat.odd_iff.mp hm
  have hred : E ((m : ℝ) / 8) = E (((m % 8 : ℕ) : ℝ) / 8) := by
    have hmod : m % 8 = (m % 8) % 8 := by omega
    simpa using E_div_congr (n := 8) hmod
  rcases (by omega : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7) with h | h | h | h
  · rw [hred, h, E_cos_sin]
    have ha : 2 * Real.pi * (((1 : ℕ) : ℝ) / 8) = Real.pi / 4 := by push_cast; ring
    rw [ha, Real.cos_pi_div_four, Real.sin_pi_div_four]
    have hc : c8 m = 1 := by simp [c8, h]
    have hc' : c8' m = 1 := by simp [c8', h]
    rw [hc, hc']
    norm_num
  · rw [hred, h, E_cos_sin]
    have ha : 2 * Real.pi * (((3 : ℕ) : ℝ) / 8) = Real.pi - Real.pi / 4 := by push_cast; ring
    rw [ha, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
    have hc : c8 m = -1 := by simp [c8, h]
    have hc' : c8' m = 1 := by simp [c8', h]
    rw [hc, hc']
    push_cast
    ring
  · rw [hred, h, E_cos_sin]
    have ha : 2 * Real.pi * (((5 : ℕ) : ℝ) / 8) = Real.pi / 4 + Real.pi := by push_cast; ring
    rw [ha, Real.cos_add_pi, Real.sin_add_pi, Real.cos_pi_div_four, Real.sin_pi_div_four]
    have hc : c8 m = -1 := by simp [c8, h]
    have hc' : c8' m = -1 := by simp [c8', h]
    rw [hc, hc']
    push_cast
    ring
  · rw [hred, h, E_cos_sin]
    have ha : 2 * Real.pi * (((7 : ℕ) : ℝ) / 8) = 2 * Real.pi - Real.pi / 4 := by push_cast; ring
    rw [ha, Real.cos_two_pi_sub, Real.sin_two_pi_sub, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
    have hc : c8 m = 1 := by simp [c8, h]
    have hc' : c8' m = -1 := by simp [c8', h]
    rw [hc, hc']
    push_cast
    ring

end OEIS48153

end

/-! # Section from Dev/Final.lean -/

section

open Finset Complex

namespace OEIS48153

/-! ### The bridge lemma: from a character formula for `Im (gq m q)` to `0 ≤ Vq q` -/

lemma Vq_nonneg_of_psi {q : ℕ} (hq : 2 ≤ q) (ψ : ℕ → ℝ)
    (hper : ∀ n, ψ (n + q) = ψ n) (hmul : ∀ a b, ψ (a * b) = ψ a * ψ b)
    (hbound : ∀ n, |ψ n| ≤ 1) (hodd : ∀ a b, a + b = q → ψ a = -ψ b)
    (hvanish : ∀ m, ¬ Nat.Coprime m q → ψ m = 0)
    (c : ℝ) (hc : 0 ≤ c)
    (him : ∀ m ∈ Ico 1 q, Nat.Coprime m q → (gq m q).im = c * ψ m) :
    0 ≤ Vq q := by
  have h1 : Vq q = c * ∑ m ∈ Ico 1 q, ψ m * ctn q m := by
    rw [Vq, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m hm => ?_
    by_cases hcop : Nat.Coprime m q
    · rw [if_pos hcop, him m hm hcop]
      ring
    · rw [if_neg hcop, hvanish m hcop]
      ring
  rw [h1]
  exact mul_nonneg hc (cot_char_sum_nonneg hq ψ hper hmul hbound hodd)

/-! ### Case: `q ≡ 1 (mod 4)` -/

lemma Vq_mod_four_one {q : ℕ} (hq : 2 ≤ q) (h4 : q % 4 = 1) : Vq q = 0 := by
  rw [Vq]
  refine Finset.sum_eq_zero fun m hm => ?_
  obtain ⟨hmem, hcop⟩ := Finset.mem_filter.mp hm
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  rw [gq_odd q hqodd m hcop, gq_one_mod_one (by omega) h4]
  simp

/-! ### Case: `q ≡ 3 (mod 4)` -/

lemma Vq_mod_four_three {q : ℕ} (hq : 2 ≤ q) (h4 : q % 4 = 3) : 0 ≤ Vq q := by
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  refine Vq_nonneg_of_psi hq (fun m => jc m q) ?_ ?_ ?_ ?_ ?_ (Real.sqrt q)
    (Real.sqrt_nonneg _) ?_
  · intro n
    beta_reduce
    exact jc_add_dvd dvd_rfl n
  · intro a b
    beta_reduce
    exact jc_mul a b q
  · intro n
    beta_reduce
    exact jc_abs n q
  · intro a b hab
    have ha : a = q - b := by omega
    have hb : b ≤ q := by omega
    beta_reduce
    rw [ha, jc_reflect dvd_rfl hb, jacobi_neg_one_of_three hqodd h4]
    push_cast
    ring
  · intro m hm
    beta_reduce
    exact jc_zero_of_not_coprime (by omega) hm
  · intro m hm hcop
    beta_reduce
    rw [gq_odd q hqodd m hcop, gq_one_mod_three (by omega) h4]
    simp only [jc, Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring

/-! ### Case: `q ≡ 2 (mod 4)` -/

lemma Vq_mod_four_two {q : ℕ} (hq : 2 ≤ q) (h4 : q % 4 = 2) : Vq q = 0 := by
  rw [Vq]
  refine Finset.sum_eq_zero fun m hm => ?_
  obtain ⟨hmem, hcop⟩ := Finset.mem_filter.mp hm
  set w := q / 2 with hwdef
  have hqe : q = 2 * w := by omega
  have hw_odd : Odd w := Nat.odd_iff.mpr (by omega)
  have hw0 : 0 < w := by omega
  have hm_odd : m % 2 = 1 := by
    by_contra hc
    have h2m : 2 ∣ m := by omega
    have h2q : 2 ∣ q := by omega
    have := Nat.dvd_gcd h2m h2q
    rw [Nat.Coprime] at hcop
    omega
  have hcop2w : Nat.Coprime 2 w := (Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)
  have hmw_odd : Odd (m * w) := (Nat.odd_iff.mpr hm_odd).mul hw_odd
  rw [hqe, gq_mul_coprime (by norm_num) hw0 hcop2w m, gq_two hmw_odd, zero_mul,
    Complex.zero_im, mul_zero]

/-! ### Cases with `4 ∣ q` -/

section FourDvd

variable {k w : ℕ}

/-- Common setup facts for `q = 2^E * w`. -/
lemma coprime_pow_two_odd (E : ℕ) {w : ℕ} (hw : Odd w) : Nat.Coprime (2 ^ E) w :=
  Nat.Coprime.pow_left E
    (Nat.coprime_comm.mp (coprime_two_of_odd (Nat.odd_iff.mp hw)))

lemma odd_of_coprime_even {m q : ℕ} (h2q : 2 ∣ q) (hcop : Nat.Coprime m q) : m % 2 = 1 := by
  by_contra hc
  have h2m : 2 ∣ m := by omega
  have := Nat.dvd_gcd h2m h2q
  rw [Nat.Coprime] at hcop
  omega

lemma Vq_even_one (hw0 : 0 < w) (hw : Odd w) (h4 : w % 4 = 1) :
    0 ≤ Vq (2 ^ (2 * k + 2) * w) := by
  set q := 2 ^ (2 * k + 2) * w with hqdef
  have h4q : 4 ∣ q := ⟨2 ^ (2 * k) * w, by rw [hqdef]; ring⟩
  have hwq : w ∣ q := ⟨2 ^ (2 * k + 2), by rw [hqdef]; ring⟩
  have h2q : 2 ∣ q := Dvd.dvd.trans (by norm_num) h4q
  have hq2 : 2 ≤ q := by
    have h1 : 4 ≤ 2 ^ (2 * k + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ≤ 4 * 1 := by norm_num
    _ ≤ 2 ^ (2 * k + 2) * w := Nat.mul_le_mul h1 hw0
  have hcop2E : Nat.Coprime (2 ^ (2 * k + 2)) w := coprime_pow_two_odd _ hw
  refine Vq_nonneg_of_psi hq2 (fun m => c4 m * jc m w) ?_ ?_ ?_ ?_ ?_
    (((2 ^ (k + 1) : ℕ) : ℝ) * Real.sqrt w) (by positivity) ?_
  · intro n
    beta_reduce
    rw [c4_period h4q, jc_add_dvd hwq]
  · intro a b
    beta_reduce
    rw [c4_mul, jc_mul]
    ring
  · exact fun n => abs_mul_le_one (c4_abs n) (jc_abs n w)
  · intro a b hab
    have ha : a = q - b := by omega
    have hb : b ≤ q := by omega
    beta_reduce
    rw [ha, c4_reflect h4q hb, jc_reflect hwq hb, jacobi_neg_one_of_one hw h4]
    push_cast
    ring
  · intro m hm
    beta_reduce
    by_cases h2 : m % 2 = 0
    · rw [c4_even h2, zero_mul]
    · have hw' : ¬ Nat.Coprime m w := by
        intro hcw
        exact hm (Nat.Coprime.mul_right ((coprime_two_of_odd (by omega)).pow_right _) hcw)
      rw [jc_zero_of_not_coprime hw0.ne' hw', mul_zero]
  · intro m hmem hcop
    beta_reduce
    have hm_odd : m % 2 = 1 := odd_of_coprime_even h2q hcop
    have hmodd : Odd m := Nat.odd_iff.mpr hm_odd
    have hmw_odd : Odd (m * w) := hmodd.mul hw
    have hcopw : Nat.Coprime m w := Nat.Coprime.coprime_dvd_right hwq hcop
    have hcop' : Nat.Coprime (m * 2 ^ (2 * k + 2)) w := Nat.Coprime.mul hcopw hcop2E
    have h1 : gq m q = gq (m * w) (2 ^ (2 * k + 2)) * gq (m * 2 ^ (2 * k + 2)) w := by
      rw [hqdef]
      exact gq_mul_coprime (pow_pos (by norm_num : (0:ℕ) < 2) _) hw0 hcop2E m
    have h3 : gq (m * 2 ^ (2 * k + 2)) w
        = ((jc (m * 2 ^ (2 * k + 2)) w : ℝ) : ℂ) * gq 1 w := by
      rw [gq_odd w hw _ hcop', jc]
      norm_cast
    have hJ : jc (m * 2 ^ (2 * k + 2)) w = jc m w := by
      rw [jc_mul, jc_pow, jc_two hw, show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul,
        c8_sq_odd (Nat.odd_iff.mp hw), one_pow, mul_one]
    have hc4 : c4 (m * w) = c4 m := by
      rw [c4_mul, c4_one_val h4, mul_one]
    rw [h1, gq_two_pow_even hmw_odd k, h3, hJ, I_pow_odd hmw_odd, hc4,
      gq_one_mod_one hw0 h4]
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
      Complex.one_im, Complex.one_re, Complex.I_im, Complex.I_re, Complex.ofReal_im,
      Complex.ofReal_re, Complex.natCast_im, Complex.natCast_re]
    push_cast
    ring

lemma Vq_even_three (hw0 : 0 < w) (hw : Odd w) (h4 : w % 4 = 3) :
    0 ≤ Vq (2 ^ (2 * k + 2) * w) := by
  set q := 2 ^ (2 * k + 2) * w with hqdef
  have h4q : 4 ∣ q := ⟨2 ^ (2 * k) * w, by rw [hqdef]; ring⟩
  have hwq : w ∣ q := ⟨2 ^ (2 * k + 2), by rw [hqdef]; ring⟩
  have h2q : 2 ∣ q := Dvd.dvd.trans (by norm_num) h4q
  have hq2 : 2 ≤ q := by
    have h1 : 4 ≤ 2 ^ (2 * k + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ≤ 4 * 1 := by norm_num
    _ ≤ 2 ^ (2 * k + 2) * w := Nat.mul_le_mul h1 hw0
  have hcop2E : Nat.Coprime (2 ^ (2 * k + 2)) w := coprime_pow_two_odd _ hw
  refine Vq_nonneg_of_psi hq2 (fun m => codd m * jc m w) ?_ ?_ ?_ ?_ ?_
    (((2 ^ (k + 1) : ℕ) : ℝ) * Real.sqrt w) (by positivity) ?_
  · intro n
    beta_reduce
    rw [codd_period h2q, jc_add_dvd hwq]
  · intro a b
    beta_reduce
    rw [codd_mul, jc_mul]
    ring
  · exact fun n => abs_mul_le_one (codd_abs n) (jc_abs n w)
  · intro a b hab
    have ha : a = q - b := by omega
    have hb : b ≤ q := by omega
    beta_reduce
    rw [ha, codd_reflect h2q hb, jc_reflect hwq hb, jacobi_neg_one_of_three hw h4]
    push_cast
    ring
  · intro m hm
    beta_reduce
    by_cases h2 : m % 2 = 0
    · rw [codd_even h2, zero_mul]
    · have hw' : ¬ Nat.Coprime m w := by
        intro hcw
        exact hm (Nat.Coprime.mul_right ((coprime_two_of_odd (by omega)).pow_right _) hcw)
      rw [jc_zero_of_not_coprime hw0.ne' hw', mul_zero]
  · intro m hmem hcop
    beta_reduce
    have hm_odd : m % 2 = 1 := odd_of_coprime_even h2q hcop
    have hmodd : Odd m := Nat.odd_iff.mpr hm_odd
    have hmw_odd : Odd (m * w) := hmodd.mul hw
    have hcopw : Nat.Coprime m w := Nat.Coprime.coprime_dvd_right hwq hcop
    have hcop' : Nat.Coprime (m * 2 ^ (2 * k + 2)) w := Nat.Coprime.mul hcopw hcop2E
    have h1 : gq m q = gq (m * w) (2 ^ (2 * k + 2)) * gq (m * 2 ^ (2 * k + 2)) w := by
      rw [hqdef]
      exact gq_mul_coprime (pow_pos (by norm_num : (0:ℕ) < 2) _) hw0 hcop2E m
    have h3 : gq (m * 2 ^ (2 * k + 2)) w
        = ((jc (m * 2 ^ (2 * k + 2)) w : ℝ) : ℂ) * gq 1 w := by
      rw [gq_odd w hw _ hcop', jc]
      norm_cast
    have hJ : jc (m * 2 ^ (2 * k + 2)) w = jc m w := by
      rw [jc_mul, jc_pow, jc_two hw, show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul,
        c8_sq_odd (Nat.odd_iff.mp hw), one_pow, mul_one]
    have hcodd : codd m = 1 := codd_odd hm_odd
    rw [h1, gq_two_pow_even hmw_odd k, h3, hJ, I_pow_odd hmw_odd,
      gq_one_mod_three hw0 h4, hcodd]
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
      Complex.one_im, Complex.one_re, Complex.I_im, Complex.I_re, Complex.ofReal_im,
      Complex.ofReal_re, Complex.natCast_im, Complex.natCast_re]
    push_cast
    ring

lemma Vq_odd_one (hw0 : 0 < w) (hw : Odd w) (h4 : w % 4 = 1) :
    0 ≤ Vq (2 ^ (2 * k + 3) * w) := by
  set q := 2 ^ (2 * k + 3) * w with hqdef
  have h8q : 8 ∣ q := ⟨2 ^ (2 * k) * w, by rw [hqdef]; ring⟩
  have hwq : w ∣ q := ⟨2 ^ (2 * k + 3), by rw [hqdef]; ring⟩
  have h2q : 2 ∣ q := Dvd.dvd.trans (by norm_num) h8q
  have hq2 : 2 ≤ q := by
    have h1 : 8 ≤ 2 ^ (2 * k + 3) := by
      calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ≤ 8 * 1 := by norm_num
    _ ≤ 2 ^ (2 * k + 3) * w := Nat.mul_le_mul h1 hw0
  have hcop2E : Nat.Coprime (2 ^ (2 * k + 3)) w := coprime_pow_two_odd _ hw
  refine Vq_nonneg_of_psi hq2 (fun m => c8' m * jc m w) ?_ ?_ ?_ ?_ ?_
    (((2 ^ (k + 2) : ℕ) : ℝ) * (Real.sqrt 2 / 2) * Real.sqrt w) (by positivity) ?_
  · intro n
    beta_reduce
    rw [c8'_period h8q, jc_add_dvd hwq]
  · intro a b
    beta_reduce
    rw [c8'_mul, jc_mul]
    ring
  · exact fun n => abs_mul_le_one (c8'_abs n) (jc_abs n w)
  · intro a b hab
    have ha : a = q - b := by omega
    have hb : b ≤ q := by omega
    beta_reduce
    rw [ha, c8'_reflect h8q hb, jc_reflect hwq hb, jacobi_neg_one_of_one hw h4]
    push_cast
    ring
  · intro m hm
    beta_reduce
    by_cases h2 : m % 2 = 0
    · rw [c8'_even h2, zero_mul]
    · have hw' : ¬ Nat.Coprime m w := by
        intro hcw
        exact hm (Nat.Coprime.mul_right ((coprime_two_of_odd (by omega)).pow_right _) hcw)
      rw [jc_zero_of_not_coprime hw0.ne' hw', mul_zero]
  · intro m hmem hcop
    beta_reduce
    have hm_odd : m % 2 = 1 := odd_of_coprime_even h2q hcop
    have hmodd : Odd m := Nat.odd_iff.mpr hm_odd
    have hmw_odd : Odd (m * w) := hmodd.mul hw
    have hcopw : Nat.Coprime m w := Nat.Coprime.coprime_dvd_right hwq hcop
    have hcop' : Nat.Coprime (m * 2 ^ (2 * k + 3)) w := Nat.Coprime.mul hcopw hcop2E
    have h1 : gq m q = gq (m * w) (2 ^ (2 * k + 3)) * gq (m * 2 ^ (2 * k + 3)) w := by
      rw [hqdef]
      exact gq_mul_coprime (pow_pos (by norm_num : (0:ℕ) < 2) _) hw0 hcop2E m
    have h3 : gq (m * 2 ^ (2 * k + 3)) w
        = ((jc (m * 2 ^ (2 * k + 3)) w : ℝ) : ℂ) * gq 1 w := by
      rw [gq_odd w hw _ hcop', jc]
      norm_cast
    have hJ : jc (m * 2 ^ (2 * k + 3)) w = jc m w * c8 w := by
      rw [jc_mul, jc_pow, jc_two hw, show 2 * k + 3 = 2 * (k + 1) + 1 by ring, pow_succ,
        pow_mul, c8_sq_odd (Nat.odd_iff.mp hw), one_pow, one_mul]
    have hsplit : c8' (m * w) = c8' m * c8' w := c8'_mul m w
    have hprod : c8' w * c8 w = 1 := c8'_mul_c8_of_one (Nat.odd_iff.mp hw) h4
    have hval : c8' (m * w) * (jc m w * c8 w) = c8' m * jc m w := by
      rw [hsplit]
      calc c8' m * c8' w * (jc m w * c8 w) = c8' m * jc m w * (c8' w * c8 w) := by ring
        _ = c8' m * jc m w := by rw [hprod, mul_one]
    rw [h1, gq_two_pow_odd hmw_odd k, h3, hJ, E_eighth hmw_odd,
      gq_one_mod_one hw0 h4]
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
      Complex.one_im, Complex.one_re, Complex.I_im, Complex.I_re, Complex.ofReal_im,
      Complex.ofReal_re, Complex.natCast_im, Complex.natCast_re]
    push_cast
    linear_combination (((2 : ℝ) ^ (k + 2)) * Real.sqrt w * (Real.sqrt 2 / 2)) * hval

lemma Vq_odd_three (hw0 : 0 < w) (hw : Odd w) (h4 : w % 4 = 3) :
    0 ≤ Vq (2 ^ (2 * k + 3) * w) := by
  set q := 2 ^ (2 * k + 3) * w with hqdef
  have h8q : 8 ∣ q := ⟨2 ^ (2 * k) * w, by rw [hqdef]; ring⟩
  have hwq : w ∣ q := ⟨2 ^ (2 * k + 3), by rw [hqdef]; ring⟩
  have h2q : 2 ∣ q := Dvd.dvd.trans (by norm_num) h8q
  have hq2 : 2 ≤ q := by
    have h1 : 8 ≤ 2 ^ (2 * k + 3) := by
      calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ≤ 8 * 1 := by norm_num
    _ ≤ 2 ^ (2 * k + 3) * w := Nat.mul_le_mul h1 hw0
  have hcop2E : Nat.Coprime (2 ^ (2 * k + 3)) w := coprime_pow_two_odd _ hw
  refine Vq_nonneg_of_psi hq2 (fun m => c8 m * jc m w) ?_ ?_ ?_ ?_ ?_
    (((2 ^ (k + 2) : ℕ) : ℝ) * (Real.sqrt 2 / 2) * Real.sqrt w) (by positivity) ?_
  · intro n
    beta_reduce
    rw [c8_period h8q, jc_add_dvd hwq]
  · intro a b
    beta_reduce
    rw [c8_mul, jc_mul]
    ring
  · exact fun n => abs_mul_le_one (c8_abs n) (jc_abs n w)
  · intro a b hab
    have ha : a = q - b := by omega
    have hb : b ≤ q := by omega
    beta_reduce
    rw [ha, c8_reflect h8q hb, jc_reflect hwq hb, jacobi_neg_one_of_three hw h4]
    push_cast
    ring
  · intro m hm
    beta_reduce
    by_cases h2 : m % 2 = 0
    · rw [c8_even h2, zero_mul]
    · have hw' : ¬ Nat.Coprime m w := by
        intro hcw
        exact hm (Nat.Coprime.mul_right ((coprime_two_of_odd (by omega)).pow_right _) hcw)
      rw [jc_zero_of_not_coprime hw0.ne' hw', mul_zero]
  · intro m hmem hcop
    beta_reduce
    have hm_odd : m % 2 = 1 := odd_of_coprime_even h2q hcop
    have hmodd : Odd m := Nat.odd_iff.mpr hm_odd
    have hmw_odd : Odd (m * w) := hmodd.mul hw
    have hcopw : Nat.Coprime m w := Nat.Coprime.coprime_dvd_right hwq hcop
    have hcop' : Nat.Coprime (m * 2 ^ (2 * k + 3)) w := Nat.Coprime.mul hcopw hcop2E
    have h1 : gq m q = gq (m * w) (2 ^ (2 * k + 3)) * gq (m * 2 ^ (2 * k + 3)) w := by
      rw [hqdef]
      exact gq_mul_coprime (pow_pos (by norm_num : (0:ℕ) < 2) _) hw0 hcop2E m
    have h3 : gq (m * 2 ^ (2 * k + 3)) w
        = ((jc (m * 2 ^ (2 * k + 3)) w : ℝ) : ℂ) * gq 1 w := by
      rw [gq_odd w hw _ hcop', jc]
      norm_cast
    have hJ : jc (m * 2 ^ (2 * k + 3)) w = jc m w * c8 w := by
      rw [jc_mul, jc_pow, jc_two hw, show 2 * k + 3 = 2 * (k + 1) + 1 by ring, pow_succ,
        pow_mul, c8_sq_odd (Nat.odd_iff.mp hw), one_pow, one_mul]
    have hsplit : c8 (m * w) = c8 m * c8 w := c8_mul m w
    have hsq : c8 w ^ 2 = 1 := c8_sq_odd (Nat.odd_iff.mp hw)
    have hval : c8 (m * w) * (jc m w * c8 w) = c8 m * jc m w := by
      rw [hsplit]
      calc c8 m * c8 w * (jc m w * c8 w) = c8 m * jc m w * (c8 w ^ 2) := by ring
        _ = c8 m * jc m w := by rw [hsq, mul_one]
    rw [h1, gq_two_pow_odd hmw_odd k, h3, hJ, E_eighth hmw_odd,
      gq_one_mod_three hw0 h4]
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
      Complex.one_im, Complex.one_re, Complex.I_im, Complex.I_re, Complex.ofReal_im,
      Complex.ofReal_re, Complex.natCast_im, Complex.natCast_re]
    push_cast
    linear_combination (((2 : ℝ) ^ (k + 2)) * Real.sqrt w * (Real.sqrt 2 / 2)) * hval

end FourDvd

/-! ### The master nonnegativity result -/

theorem Vq_nonneg_all (q : ℕ) (hq : 2 ≤ q) : 0 ≤ Vq q := by
  rcases (by omega : q % 4 = 0 ∨ q % 4 = 1 ∨ q % 4 = 2 ∨ q % 4 = 3) with h | h | h | h
  · -- 4 ∣ q : decompose q = 2^E * w
    have hqne : q ≠ 0 := by omega
    obtain ⟨E, w, hqe, hw_odd, hw0, hE2⟩ :
        ∃ E w, 2 ^ E * w = q ∧ Odd w ∧ 0 < w ∧ 2 ≤ E := by
      refine ⟨q.factorization 2, q / 2 ^ (q.factorization 2),
        Nat.ordProj_mul_ordCompl_eq_self q 2, ?_, Nat.ordCompl_pos 2 hqne, ?_⟩
      · have hwodd : ¬ 2 ∣ (q / 2 ^ (q.factorization 2)) :=
          Nat.not_dvd_ordCompl Nat.prime_two hqne
        exact Nat.odd_iff.mpr (by omega)
      · have h4dvd : (2 : ℕ) ^ 2 ∣ q := by
          have : (4 : ℕ) ∣ q := by omega
          simpa using this
        exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hqne).mp h4dvd
    have hwmod := Nat.odd_iff.mp hw_odd
    rcases Nat.even_or_odd E with hpar | hpar
    · have hp := Nat.even_iff.mp hpar
      obtain ⟨k, hk⟩ : ∃ k, E = 2 * k + 2 := ⟨(E - 2) / 2, by omega⟩
      rcases (by omega : w % 4 = 1 ∨ w % 4 = 3) with h1 | h3
      · rw [← hqe, hk]
        exact Vq_even_one hw0 hw_odd h1
      · rw [← hqe, hk]
        exact Vq_even_three hw0 hw_odd h3
    · have hp := Nat.odd_iff.mp hpar
      obtain ⟨k, hk⟩ : ∃ k, E = 2 * k + 3 := ⟨(E - 3) / 2, by omega⟩
      rcases (by omega : w % 4 = 1 ∨ w % 4 = 3) with h1 | h3
      · rw [← hqe, hk]
        exact Vq_odd_one hw0 hw_odd h1
      · rw [← hqe, hk]
        exact Vq_odd_three hw0 hw_odd h3
  · exact le_of_eq (Vq_mod_four_one hq h).symm
  · exact le_of_eq (Vq_mod_four_two hq h).symm
  · exact Vq_mod_four_three hq h

/-! ### Conclusion -/

theorem aa_le_aneg (n : ℕ) (hn : 0 < n) : aa n ≤ aneg n := by
  have h := delta_eq n hn
  rw [delta_divisor_split n hn] at h
  have hnn : 0 ≤ ∑ q ∈ n.divisors.filter (fun q => 1 < q), ((n / q : ℕ) : ℝ) * Vq q := by
    refine Finset.sum_nonneg fun q hq => ?_
    obtain ⟨_, h2⟩ := Finset.mem_filter.mp hq
    exact mul_nonneg (Nat.cast_nonneg _) (Vq_nonneg_all q h2)
  have : (aa n : ℝ) ≤ (aneg n : ℝ) := by linarith
  exact_mod_cast this

theorem aa_add_aneg_le (n : ℕ) (hn : 0 < n) : aa n + aneg n ≤ n * (n - 1) := by
  rw [aa, aneg, ← Finset.sum_add_distrib]
  have hterm : ∀ k ∈ range n, k ^ 2 % n + (n - k ^ 2 % n) % n ≤ if k = 0 then 0 else n := by
    intro k _
    by_cases hk0 : k = 0
    · subst hk0
      simp [Nat.zero_mod, Nat.mod_self]
    · rw [if_neg hk0]
      have h1 : k ^ 2 % n < n := Nat.mod_lt _ hn
      by_cases hr : k ^ 2 % n = 0
      · rw [hr]
        simp [Nat.mod_self]
      · have h2 : (n - k ^ 2 % n) % n = n - k ^ 2 % n := Nat.mod_eq_of_lt (by omega)
        omega
  calc ∑ k ∈ range n, (k ^ 2 % n + (n - k ^ 2 % n) % n)
      ≤ ∑ k ∈ range n, (if k = 0 then 0 else n) := Finset.sum_le_sum hterm
    _ = n * (n - 1) := by
        rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn]
        rw [if_pos rfl, zero_add]
        rw [Finset.sum_congr rfl fun k hk =>
          if_neg (by simp only [Finset.mem_Ico] at hk; omega)]
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
        exact Nat.mul_comm _ _

theorem aa_main (n : ℕ) (h : 1 ≤ n) : aa n ≤ (n ^ 2 - 1) / 2 := by
  have h1 : aa n ≤ aneg n := aa_le_aneg n h
  have h2 : aa n + aneg n ≤ n * (n - 1) := aa_add_aneg_le n h
  have h5 : n * (n - 1) + n = n ^ 2 := by
    obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  generalize hB : n * (n - 1) = B at *
  generalize hA : n ^ 2 = A at *
  omega

end OEIS48153

end


/--
Conjecture: a(n) <= (n^2-1)/2. - _Aspen A.M. Meissner_, Mar 06 2025
We require $n \ge 1$ for the difference $n^2 - 1$ to be a natural number.
The division `/ 2` is natural number (integer) division.
-/
theorem oeis_48153_conjecture_0 (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 :=
OEIS48153.aa_main n h
