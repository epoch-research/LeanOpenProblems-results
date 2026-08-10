import FormalConjectures.Util.ProblemImports

open Int

/--
A122589: Expansion of $1/(1 - 11x + 45x^2 - 84x^3 + 70x^4 - 21x^5 + x^6)$.
The sequence is defined by the linear recurrence relation:
$a(n) = 11 a(n-1) - 45 a(n-2) + 84 a(n-3) - 70 a(n-4) + 21 a(n-5) - a(n-6)$ for $n \ge 6$.
The initial values are $a(0)=1, a(1)=11, a(2)=76, a(3)=425, a(4)=2109, a(5)=9709$.
-/
def a (n : ℕ) : ℕ :=
  let rec a_int : ℕ → ℤ := fun n =>
    match n with
    | 0 => 1
    | 1 => 11
    | 2 => 76
    | 3 => 425
    | 4 => 2109
    | 5 => 9709
    | k + 6 =>
      11 * a_int (k + 5)
      - 45 * a_int (k + 4)
      + 84 * a_int (k + 3)
      - 70 * a_int (k + 2)
      + 21 * a_int (k + 1)
      - a_int k
  (a_int n).toNat

open Polynomial

/-- `g(2 cos(2πn/13)) = 0` for `1 ≤ n ≤ 12`, where
    `g(y) = y^6 + y^5 - 5y^4 - 4y^3 + 6y^2 + 3y - 1`. -/
private theorem g_cos_zero (n : ℕ) (hn1 : 1 ≤ n) (hn2 : n ≤ 12) :
    let y := 2 * Real.cos (2 * Real.pi * n / 13)
    y^6 + y^5 - 5*y^4 - 4*y^3 + 6*y^2 + 3*y - 1 = 0 := by
  intro y
  set θ : ℝ := 2 * Real.pi * n / 13 with hθ
  set ζ : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hζdef
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  -- ζ^13 = 1
  have hζ13 : ζ^13 = 1 := by
    rw [hζdef, ← Complex.exp_nat_mul]
    convert Complex.exp_nat_mul_two_pi_mul_I n using 2
    rw [hθ]; push_cast; ring
  -- ζ ≠ 1
  have hζ1 : ζ ≠ 1 := by
    intro hcon
    rw [hζdef, Complex.exp_eq_one_iff] at hcon
    obtain ⟨m, hm⟩ := hcon
    have h2 : (θ : ℂ) * Complex.I = ((m : ℂ) * (2 * (Real.pi:ℂ))) * Complex.I := by
      rw [hm]; ring
    have hθc : (θ : ℂ) = (m : ℂ) * (2 * (Real.pi:ℂ)) := mul_right_cancel₀ Complex.I_ne_zero h2
    have hθr : θ = (m : ℝ) * (2 * Real.pi) := by exact_mod_cast hθc
    rw [hθ] at hθr
    have h2pi : (2 * Real.pi) ≠ 0 := by positivity
    rw [show 2 * Real.pi * (n:ℝ) / 13 = (2 * Real.pi) * ((n:ℝ)/13) by ring,
        show (m:ℝ) * (2 * Real.pi) = (2 * Real.pi) * (m:ℝ) by ring] at hθr
    have hn13 : (n:ℝ)/13 = (m:ℝ) := mul_left_cancel₀ h2pi hθr
    have hnr : (n : ℝ) = (m : ℝ) * 13 := by field_simp at hn13; linarith
    have hnint : (n : ℤ) = m * 13 := by exact_mod_cast hnr
    omega
  -- geometric sum is zero
  have hgeom : (1 + ζ + ζ^2 + ζ^3 + ζ^4 + ζ^5 + ζ^6 + ζ^7 + ζ^8 + ζ^9 + ζ^10 + ζ^11 + ζ^12) = 0 := by
    have hprod : (ζ - 1) * (1 + ζ + ζ^2 + ζ^3 + ζ^4 + ζ^5 + ζ^6 + ζ^7 + ζ^8 + ζ^9 + ζ^10 + ζ^11 + ζ^12) = ζ^13 - 1 := by
      ring
    rw [hζ13] at hprod
    have : (ζ - 1) * (1 + ζ + ζ^2 + ζ^3 + ζ^4 + ζ^5 + ζ^6 + ζ^7 + ζ^8 + ζ^9 + ζ^10 + ζ^11 + ζ^12) = 0 := by
      rw [hprod]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hζ1
    · exact h
  -- s := ζ + ζ⁻¹ = 2 cos θ
  have hs : ζ + ζ⁻¹ = 2 * (Real.cos θ : ℂ) := by
    rw [Complex.ofReal_cos, Complex.two_cos, hζdef, ← Complex.exp_neg, neg_mul]
  -- algebraic identity
  have hident : ζ^6 * ((ζ + ζ⁻¹)^6 + (ζ + ζ⁻¹)^5 - 5*(ζ + ζ⁻¹)^4 - 4*(ζ + ζ⁻¹)^3
      + 6*(ζ + ζ⁻¹)^2 + 3*(ζ + ζ⁻¹) - 1)
      = 1 + ζ + ζ^2 + ζ^3 + ζ^4 + ζ^5 + ζ^6 + ζ^7 + ζ^8 + ζ^9 + ζ^10 + ζ^11 + ζ^12 := by
    field_simp
    ring
  rw [hgeom] at hident
  have hz6 : ζ^6 ≠ 0 := pow_ne_zero _ hζ0
  have hgval : (ζ + ζ⁻¹)^6 + (ζ + ζ⁻¹)^5 - 5*(ζ + ζ⁻¹)^4 - 4*(ζ + ζ⁻¹)^3
      + 6*(ζ + ζ⁻¹)^2 + 3*(ζ + ζ⁻¹) - 1 = 0 := by
    rcases mul_eq_zero.1 hident with h | h
    · exact absurd h hz6
    · exact h
  rw [hs] at hgval
  have hyθ : y = 2 * Real.cos θ := by rw [hθ]
  rw [hyθ]
  exact_mod_cast hgval

private noncomputable def cc (k : ℕ) : ℝ := 4 * Real.cos (Real.pi * (k.succ : ℝ) / 13) ^ 2

private theorem cos_pos_aux (k : ℕ) (hk : k < 6) :
    0 < Real.cos (Real.pi * (k.succ : ℝ) / 13) := by
  apply Real.cos_pos_of_mem_Ioo
  have hkr : (k.succ : ℝ) ≤ 6 := by
    have : k.succ ≤ 6 := by omega
    exact_mod_cast this
  have hpi := Real.pi_pos
  constructor
  · have : (0:ℝ) < Real.pi * (k.succ:ℝ) / 13 := by positivity
    linarith
  · rw [div_lt_iff₀ (by norm_num : (13:ℝ) > 0)]
    nlinarith [Real.pi_pos]

private theorem cc_pos (k : ℕ) (hk : k < 6) : 0 < cc k := by
  unfold cc
  have := cos_pos_aux k hk
  positivity

private theorem hH_cc (k : ℕ) (hk : k < 6) :
    (cc k)^6 - 11*(cc k)^5 + 45*(cc k)^4 - 84*(cc k)^3 + 70*(cc k)^2 - 21*(cc k) + 1 = 0 := by
  have hg := g_cos_zero (k+1) (by omega) (by omega)
  simp only at hg
  have hy : 2 * Real.cos (2 * Real.pi * ((k+1:ℕ):ℝ) / 13) = cc k - 2 := by
    unfold cc
    rw [show 2 * Real.pi * ((k+1:ℕ):ℝ) / 13 = 2 * (Real.pi * ((k.succ:ℕ):ℝ) / 13) by push_cast; ring]
    rw [Real.cos_two_mul]
    ring
  rw [hy] at hg
  linear_combination hg

private theorem cc_injOn : Set.InjOn cc (Finset.range 6) := by
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  have hca : 0 < Real.cos (Real.pi * (i.succ : ℝ) / 13) := cos_pos_aux i hi
  have hcb : 0 < Real.cos (Real.pi * (j.succ : ℝ) / 13) := cos_pos_aux j hj
  set a : ℝ := Real.pi * (i.succ : ℝ) / 13 with ha
  set b : ℝ := Real.pi * (j.succ : ℝ) / 13 with hb
  unfold cc at hij
  rw [← ha, ← hb] at hij
  have hsq : Real.cos a ^ 2 = Real.cos b ^ 2 := by linarith [hij]
  have hcoseq : Real.cos a = Real.cos b := by
    rw [← Real.sqrt_sq hca.le, ← Real.sqrt_sq hcb.le, hsq]
  have hpi := Real.pi_pos
  have hai : i.succ ≤ 6 := by omega
  have haj : j.succ ≤ 6 := by omega
  have hmemA : a ∈ Set.Icc 0 Real.pi := by
    constructor
    · rw [ha]; positivity
    · rw [ha, div_le_iff₀ (by norm_num : (13:ℝ) > 0)]
      have : (i.succ : ℝ) ≤ 6 := by exact_mod_cast hai
      nlinarith [Real.pi_pos]
  have hmemB : b ∈ Set.Icc 0 Real.pi := by
    constructor
    · rw [hb]; positivity
    · rw [hb, div_le_iff₀ (by norm_num : (13:ℝ) > 0)]
      have : (j.succ : ℝ) ≤ 6 := by exact_mod_cast haj
      nlinarith [Real.pi_pos]
  have hab : a = b := Real.injOn_cos hmemA hmemB hcoseq
  rw [ha, hb] at hab
  have key : Real.pi * (i.succ : ℝ) = Real.pi * (j.succ : ℝ) := by linear_combination 13 * hab
  have hij' : (i.succ : ℝ) = (j.succ : ℝ) := mul_left_cancel₀ (ne_of_gt Real.pi_pos) key
  have : i.succ = j.succ := by exact_mod_cast hij'
  omega

/--
The conjecture suggested by the study of polynomials associated with the regular 13-gon
is that the denominator of the generating function for A122589 factors based on
the cosines of the angles of a regular 13-gon.
Specifically, let $P(x)$ be the denominator of the generating function. Then
$$P(x) = 1 - 11x + 45x^2 - 84x^3 + 70x^4 - 21x^5 + x^6 = \prod_{k=1}^6 \left(1 - 4 \cos^2\left(\frac{\pi k}{13}\right) x\right)$$
-/
theorem oeis_a122589_conjecture_0 :
    (C (1 : ℝ) - C (11 : ℝ) * X + C (45 : ℝ) * X^2 - C (84 : ℝ) * X^3 + C (70 : ℝ) * X^4 - C (21 : ℝ) * X^5 + C (1 : ℝ) * X^6)
    = Finset.prod (Finset.range 6)
        (fun k : ℕ => C (1 : ℝ) - C (4 * Real.cos (Real.pi * (k.succ : ℝ) / 13) ^ 2) * X) := by
  set P : ℝ[X] := C (1 : ℝ) - C (11 : ℝ) * X + C (45 : ℝ) * X^2 - C (84 : ℝ) * X^3 + C (70 : ℝ) * X^4 - C (21 : ℝ) * X^5 + C (1 : ℝ) * X^6 with hP
  show P = Finset.prod (Finset.range 6) (fun k : ℕ => C (1 : ℝ) - C (cc k) * X)
  set f : ℝ[X] := ∏ k ∈ Finset.range 6, (X - C ((cc k)⁻¹)) with hf
  -- degrees and monicity
  have hPmonic : P.Monic := by rw [hP]; monicity!
  have hPdeg : P.natDegree = 6 := by rw [hP]; compute_degree!
  have hfmonic : f.Monic := by
    rw [hf]; exact monic_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)
  have hfdeg : f.natDegree = 6 := by
    rw [hf, natDegree_finset_prod_X_sub_C_eq_card, Finset.card_range]
  -- P evaluates to 0 at (cc k)⁻¹
  have hPeval : ∀ k ∈ Finset.range 6, P.eval ((cc k)⁻¹) = 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hne : cc k ≠ 0 := ne_of_gt (cc_pos k hk)
    have hHk := hH_cc k hk
    rw [hP]
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
    field_simp
    linear_combination hHk
  -- f evaluates to 0 at (cc k)⁻¹
  have hfeval : ∀ k ∈ Finset.range 6, f.eval ((cc k)⁻¹) = 0 := by
    intro k hk
    rw [hf, eval_prod]
    apply Finset.prod_eq_zero hk
    simp
  -- P = f
  have hPf : P = f := by
    by_contra hne
    have hsubne : P - f ≠ 0 := sub_ne_zero.2 hne
    have hdegsub : (P - f).natDegree < 6 := by
      have hd : (P - f).degree < P.degree := by
        apply degree_sub_lt
        · rw [P.degree_eq_natDegree hPmonic.ne_zero, f.degree_eq_natDegree hfmonic.ne_zero, hPdeg, hfdeg]
        · exact hPmonic.ne_zero
        · rw [hPmonic.leadingCoeff, hfmonic.leadingCoeff]
      rw [P.degree_eq_natDegree hPmonic.ne_zero, hPdeg] at hd
      exact (Polynomial.natDegree_lt_iff_degree_lt hsubne).2 hd
    -- the 6 distinct roots
    have hr_inj : Set.InjOn (fun k => (cc k)⁻¹) (Finset.range 6) := by
      intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      simp only at hij
      have hcni : cc i ≠ 0 := ne_of_gt (cc_pos i hi)
      have hcnj : cc j ≠ 0 := ne_of_gt (cc_pos j hj)
      have hcceq : cc i = cc j := by
        field_simp at hij; linarith [hij]
      exact cc_injOn (Finset.mem_coe.mpr (Finset.mem_range.mpr hi))
        (Finset.mem_coe.mpr (Finset.mem_range.mpr hj)) hcceq
    set Z : Finset ℝ := (Finset.range 6).image (fun k => (cc k)⁻¹) with hZ
    have hZcard : Z.card = 6 := by
      rw [hZ, Finset.card_image_of_injOn hr_inj, Finset.card_range]
    have hsub : Z.val ⊆ (P - f).roots := by
      intro x hx
      rw [Finset.mem_val, hZ, Finset.mem_image] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      rw [Polynomial.mem_roots']
      refine ⟨hsubne, ?_⟩
      rw [Polynomial.IsRoot.def, eval_sub, hPeval k hk, hfeval k hk, sub_zero]
    have := card_le_degree_of_subset_roots hsub
    rw [hZcard] at this
    omega
  -- factor rewriting for RHS
  have factor_eq : ∀ k ∈ Finset.range 6,
      C (1:ℝ) - C (cc k) * X = C (-(cc k)) * (X - C ((cc k)⁻¹)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have h1 : cc k * (cc k)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt (cc_pos k hk))
    rw [C_neg, neg_mul, mul_sub, ← C_mul, h1, map_one]
    ring
  have hRHS : (Finset.prod (Finset.range 6) (fun k : ℕ => C (1 : ℝ) - C (cc k) * X))
      = (∏ k ∈ Finset.range 6, C (-(cc k))) * f := by
    rw [Finset.prod_congr rfl factor_eq, Finset.prod_mul_distrib, ← hf]
  -- ∏ (-(cc k)) = 1
  have hcprod : (∏ k ∈ Finset.range 6, (-(cc k))) = 1 := by
    have h0 : f.eval 0 = 1 := by rw [← hPf, hP]; simp
    have hrprod : (∏ k ∈ Finset.range 6, (-(cc k)⁻¹)) = 1 := by
      rw [hf, eval_prod] at h0
      simp only [eval_sub, eval_X, eval_C, zero_sub] at h0
      exact h0
    have hcomb : (∏ k ∈ Finset.range 6, (-(cc k))) * (∏ k ∈ Finset.range 6, (-(cc k)⁻¹)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro k hk
      rw [Finset.mem_range] at hk
      have := ne_of_gt (cc_pos k hk)
      field_simp
    rw [hrprod, mul_one] at hcomb
    exact hcomb
  rw [hRHS, ← map_prod, hcprod, map_one, one_mul]
  exact hPf

instance : Coe ℕ ℝ where
  coe := Nat.cast
