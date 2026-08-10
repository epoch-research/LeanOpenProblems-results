import Mathlib
open Polynomial Finset

noncomputable def Pp (n : ℕ) : Polynomial ℕ :=
 (Icc 1 n).prod fun j => (Finset.range j).sum fun i => C (1 : ℕ) * (X : Polynomial ℕ) ^ i

-- factor = geometric sum
lemma factor_eq (j : ℕ) : (Finset.range j).sum (fun i => C (1:ℕ) * (X:Polynomial ℕ)^i)
    = (Finset.range j).sum (fun i => (X:Polynomial ℕ)^i) := by
  simp

-- eval at 1 of a factor = j
lemma factor_eval_one (j : ℕ) :
    Polynomial.eval 1 ((Finset.range j).sum (fun i => C (1:ℕ) * (X:Polynomial ℕ)^i)) = j := by
  simp

lemma prod_Icc_one_id (n : ℕ) : ∏ x ∈ Icc 1 n, x = n.factorial := by
  induction n with
  | zero => simp
  | succ m ih => rw [← Ico_add_one_right_eq_Icc 1, Finset.prod_Ico_succ_top (by omega)]
                 rw [Ico_add_one_right_eq_Icc 1, ih, Nat.factorial_succ]; ring

-- coefficient sum = n!
lemma Pp_eval_one (n : ℕ) : Polynomial.eval 1 (Pp n) = n.factorial := by
  unfold Pp
  rw [Polynomial.eval_prod]
  simp only [factor_eval_one]
  rw [prod_Icc_one_id]

open Complex

-- The coefficient function (Mahonian numbers)
noncomputable def cc (n m : ℕ) : ℕ := (Pp n).coeff m

-- characteristic-like function: Φ_n(θ) = ∑_m c_m e^{i m θ} = P_n(e^{iθ}) over ℂ
noncomputable def Phi (n : ℕ) (θ : ℝ) : ℂ :=
  ((Pp n).map (Nat.castRingHom ℂ)).eval (Complex.exp (θ * Complex.I))

-- product form
lemma Phi_eq_prod (n : ℕ) (θ : ℝ) :
    Phi n θ = ∏ j ∈ Icc 1 n, ∑ i ∈ Finset.range j, Complex.exp (θ * Complex.I) ^ i := by
  unfold Phi Pp
  rw [Polynomial.map_prod, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.map_sum, Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

lemma factor_natDegree_le (j : ℕ) :
    (((Finset.range j).sum fun i => C (1:ℕ) * (X:Polynomial ℕ)^i)).natDegree ≤ j - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  simp only [Finset.mem_range] at hi
  calc (C (1:ℕ) * (X:Polynomial ℕ)^i).natDegree ≤ i := by
              rw [C_1, one_mul]; simp [Polynomial.natDegree_pow]
        _ ≤ j - 1 := by omega

lemma Pp_natDegree_le (n : ℕ) : (Pp n).natDegree ≤ n * (n-1) / 2 := by
  unfold Pp
  calc (∏ j ∈ Icc 1 n, ((Finset.range j).sum fun i => C (1:ℕ) * (X:Polynomial ℕ)^i)).natDegree
        ≤ ∑ j ∈ Icc 1 n, (((Finset.range j).sum fun i => C (1:ℕ) * (X:Polynomial ℕ)^i)).natDegree :=
          Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ j ∈ Icc 1 n, (j - 1) := Finset.sum_le_sum (fun j _ => factor_natDegree_le j)
    _ = n * (n-1) / 2 := by
          have h : ∑ j ∈ Icc 1 n, (j - 1) = ∑ i ∈ range n, i := by
            rw [Finset.range_eq_Ico, show Icc 1 n = Ico 1 (n+1) from by rw [Ico_add_one_right_eq_Icc]]
            rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]; simp
          rw [h, Finset.sum_range_id]

lemma Pp_map_natDegree_le (n : ℕ) :
    ((Pp n).map (Nat.castRingHom ℂ)).natDegree ≤ n * (n-1)/2 :=
  le_trans (Polynomial.natDegree_map_le) (Pp_natDegree_le n)

lemma Phi_eq_sum (n : ℕ) (θ : ℝ) :
    Phi n θ = ∑ m ∈ range (n*(n-1)/2 + 1), (cc n m : ℂ) * Complex.exp (θ * Complex.I) ^ m := by
  unfold Phi
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (Pp_map_natDegree_le n))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Polynomial.coeff_map]
  simp [cc]

open Real Filter Asymptotics

-- mirror of Spec definitions
noncomputable def Ak (k n : ℕ) : ℝ :=
  (Finset.range (n*(n-1)/2 + 1)).sum fun j => ((Pp n).coeff j : ℝ)^k

noncomputable def qterm (k n : ℕ) : ℝ :=
  let k_r : ℝ := k
  let n_r : ℝ := n
  let k_minus_one_half := (k_r - 1) / 2
  let c_k : ℝ := ((2:ℝ)^k_minus_one_half * (3:ℝ)^(k_r-1)) / (Real.sqrt k_r * Real.pi ^ k_minus_one_half)
  c_k * ((n.factorial:ℝ)^k_r / (n_r ^ (3*k_minus_one_half)))

-- variance and constants
noncomputable def Sig (n : ℕ) : ℝ := Real.sqrt (∑ j ∈ Finset.Icc 1 n, (((j:ℝ)^2 - 1)/12))
noncomputable def Ck (k : ℕ) : ℝ :=
  ((2:ℝ)^(((k:ℝ)-1)/2) * (3:ℝ)^((k:ℝ)-1)) / (Real.sqrt k * Real.pi ^ (((k:ℝ)-1)/2))
noncomputable def Ik (k : ℕ) : ℝ := (2*Real.pi)^(-((k:ℝ)-1)/2) / Real.sqrt k

-- Fourier orthogonality machinery
theorem orth (k : ℤ) (hk : k ≠ 0) :
    ∫ θ in (-Real.pi)..Real.pi, Complex.exp ((k:ℂ) * θ * Complex.I) = 0 := by
  have hrw : ∀ x:ℝ, ((k:ℂ) * x * Complex.I) = ((k:ℂ)*Complex.I) * x := by intro x; ring
  simp_rw [hrw]
  rw [integral_exp_mul_complex (by simp [hk, Complex.I_ne_zero])]
  have key : Complex.exp ((k:ℂ)*Complex.I * (Real.pi:ℝ)) = Complex.exp ((k:ℂ)*Complex.I * ((-Real.pi):ℝ)) := by
    have h1 : (k:ℂ)*Complex.I*(Real.pi:ℝ) = (k:ℂ)*Complex.I*((-Real.pi):ℝ) + (k:ℂ)*(2*(Real.pi:ℝ)*Complex.I) := by
      push_cast; ring
    rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [key, sub_self, zero_div]

theorem orth_nat (a b : ℕ) : ∫ θ in (-Real.pi)..Real.pi,
    Complex.exp ((a:ℝ)*θ*Complex.I) * Complex.exp (-(b:ℝ)*θ*Complex.I)
    = if a = b then (2*Real.pi:ℂ) else 0 := by
  have h : ∀ θ:ℝ, Complex.exp ((a:ℝ)*θ*Complex.I) * Complex.exp (-(b:ℝ)*θ*Complex.I)
      = Complex.exp ((((a:ℤ)-(b:ℤ):ℤ):ℂ)*θ*Complex.I) := by
    intro θ; rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [h]
  by_cases hab : a = b
  · subst hab; simp; ring
  · rw [if_neg hab]; exact orth _ (by intro hc; apply hab; omega)

theorem orth_nat_mul (C:ℂ) (a b : ℕ) : ∫ θ in (-Real.pi)..Real.pi,
    C * Complex.exp ((a:ℝ)*θ*Complex.I) * Complex.exp (-(b:ℝ)*θ*Complex.I)
    = C * (if a = b then (2*Real.pi:ℂ) else 0) := by
  have : ∫ θ in (-Real.pi)..Real.pi, C * Complex.exp ((a:ℝ)*θ*Complex.I) * Complex.exp (-(b:ℝ)*θ*Complex.I)
       = ∫ θ in (-Real.pi)..Real.pi, C * (Complex.exp ((a:ℝ)*θ*Complex.I) * Complex.exp (-(b:ℝ)*θ*Complex.I)) := by
    apply intervalIntegral.integral_congr; intro θ _; simp; ring
  rw [this, intervalIntegral.integral_const_mul, orth_nat]

-- Φ as explicit trig polynomial
lemma Phi_eq_sum' (n : ℕ) (θ : ℝ) :
    Phi n θ = ∑ m ∈ Finset.range (n*(n-1)/2 + 1), (cc n m : ℂ) * Complex.exp ((m:ℝ)*θ*Complex.I) := by
  rw [Phi_eq_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Complex.exp_nat_mul]; congr 2; push_cast; ring

-- Fourier inversion: coefficient extraction
lemma fourier_inv (n m : ℕ) (hm : m ≤ n*(n-1)/2) :
    (∫ θ in (-Real.pi)..Real.pi, Phi n θ * Complex.exp (-(m:ℝ)*θ*Complex.I)) = 2*Real.pi*(cc n m) := by
  have hcont : ∀ m':ℕ, IntervalIntegrable (fun θ => (cc n m':ℂ)*Complex.exp ((m':ℝ)*θ*Complex.I) * Complex.exp (-(m:ℝ)*θ*Complex.I)) MeasureTheory.volume (-Real.pi) Real.pi := by
    intro m'; apply Continuous.intervalIntegrable
    exact (continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))).mul (Complex.continuous_exp.comp (by fun_prop))
  simp_rw [Phi_eq_sum', Finset.sum_mul]
  rw [intervalIntegral.integral_finset_sum (fun m' _ => hcont m')]
  rw [Finset.sum_eq_single m]
  · rw [orth_nat_mul, if_pos rfl]; ring
  · intro m' _ hne; rw [orth_nat_mul, if_neg hne, mul_zero]
  · intro hmem; exfalso; apply hmem; simp only [Finset.mem_range]; omega

-- Character function magnitude machinery
noncomputable def fac (j : ℕ) (θ : ℝ) : ℂ := ∑ i ∈ Finset.range j, Complex.exp (θ*Complex.I)^i

lemma Phi_eq_prod_fac (n : ℕ) (θ : ℝ) : Phi n θ = ∏ j ∈ Finset.Icc 1 n, fac j θ := by
  rw [Phi_eq_prod]; rfl

lemma fac_norm_le (j:ℕ) (θ:ℝ) : ‖fac j θ‖ ≤ j := by
  unfold fac
  calc ‖∑ i ∈ Finset.range j, Complex.exp (θ*Complex.I)^i‖
      ≤ ∑ i ∈ Finset.range j, ‖Complex.exp (θ*Complex.I)^i‖ := norm_sum_le _ _
    _ = j := by simp [norm_pow, Complex.norm_exp]

lemma fac_normSq_le (j:ℕ) (θ:ℝ) : Complex.normSq (fac j θ) ≤ (j:ℝ)^2 := by
  rw [Complex.normSq_eq_norm_sq]; have := fac_norm_le j θ; nlinarith [norm_nonneg (fac j θ)]

lemma fac_normSq_cos (j : ℕ) (θ : ℝ) :
    Complex.normSq (fac j θ)
    = ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j, Real.cos ((i:ℝ)*θ - (i':ℝ)*θ) := by
  unfold fac
  have hconj : (starRingEnd ℂ) (Complex.exp (θ*Complex.I)) = Complex.exp (-(θ*Complex.I)) := by
    rw [← Complex.exp_conj]; congr 1; simp
  have h2 : (∑ i ∈ Finset.range j, Complex.exp (θ*Complex.I)^i) * (starRingEnd ℂ) (∑ i ∈ Finset.range j, Complex.exp (θ*Complex.I)^i)
      = ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j, Complex.exp (((i:ℝ)*θ - (i':ℝ)*θ)*Complex.I) := by
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro i' _
    rw [map_pow, hconj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  have h1 : (Complex.normSq (∑ i ∈ Finset.range j, Complex.exp (θ*Complex.I)^i) : ℂ)
      = ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j, Complex.exp (((i:ℝ)*θ - (i':ℝ)*θ)*Complex.I) := by
    rw [← h2, Complex.mul_conj]
  have h3 := congrArg Complex.re h1
  rw [Complex.ofReal_re, Complex.re_sum] at h3
  rw [h3]
  apply Finset.sum_congr rfl; intro i _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl; intro i' _
  rw [show ((i:ℝ)*θ - (i':ℝ)*θ)*Complex.I = ((((i:ℝ)*θ - (i':ℝ)*θ):ℝ):ℂ)*Complex.I from by norm_cast,
      Complex.exp_ofReal_mul_I_re]

lemma prod_le_exp_neg_sum {s : Finset ℕ} (g : ℕ → ℝ) (hg : ∀ i ∈ s, g i ≤ 1) :
    ∏ i ∈ s, (1 - g i) ≤ Real.exp (-∑ i ∈ s, g i) := by
  have h1 : Real.exp (-∑ i ∈ s, g i) = ∏ i ∈ s, Real.exp (-g i) := by
    rw [← Real.exp_sum]; congr 1; rw [Finset.sum_neg_distrib]
  rw [h1]
  apply Finset.prod_le_prod
  · intro i hi; linarith [(hg i hi)]
  · intro i hi; linarith [Real.add_one_le_exp (-g i)]

-- g_j = 1 - normSq(fac)/j²
noncomputable def gg (j : ℕ) (θ : ℝ) : ℝ := 1 - Complex.normSq (fac j θ)/(j:ℝ)^2

lemma gg_nonneg {j:ℕ} (hj : 1 ≤ j) (θ:ℝ) : 0 ≤ gg j θ := by
  unfold gg
  have hj2 : (0:ℝ) < (j:ℝ)^2 := by positivity
  rw [sub_nonneg, div_le_one hj2]; exact fac_normSq_le j θ

lemma gg_le_one {j:ℕ} (hj : 1 ≤ j) (θ:ℝ) : gg j θ ≤ 1 := by
  unfold gg
  have : (0:ℝ) ≤ Complex.normSq (fac j θ)/(j:ℝ)^2 :=
    div_nonneg (Complex.normSq_nonneg _) (by positivity)
  linarith

-- KEY: |φ_n(θ)|² ≤ exp(-∑ g_j)
lemma phi_normSq_bound (n : ℕ) (θ : ℝ) :
    Complex.normSq (Phi n θ) / (n.factorial:ℝ)^2 ≤ Real.exp (-∑ j ∈ Finset.Icc 1 n, gg j θ) := by
  have hfact : (n.factorial:ℝ) = ∏ j ∈ Finset.Icc 1 n, (j:ℝ) := by
    rw [← prod_Icc_one_id]; push_cast; rfl
  have hprod : Complex.normSq (Phi n θ) / (n.factorial:ℝ)^2 = ∏ j ∈ Finset.Icc 1 n, (1 - gg j θ) := by
    rw [Phi_eq_prod_fac, map_prod, hfact]
    rw [← Finset.prod_pow]
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl; intro j hj
    unfold gg; ring
  rw [hprod]
  exact prod_le_exp_neg_sum _ (fun j hj => gg_le_one (Finset.mem_Icc.mp hj).1 θ)

-- Geometric bound for tail
lemma fac_mul (j:ℕ)(θ:ℝ) : fac j θ * (Complex.exp (θ*Complex.I) - 1) = Complex.exp (θ*Complex.I)^j - 1 := by
  unfold fac; rw [geom_sum_mul]
lemma nsq_zsub1 (θ:ℝ) : Complex.normSq (Complex.exp (θ*Complex.I) - 1) = 4*Real.sin (θ/2)^2 := by
  rw [Complex.exp_mul_I]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
    Complex.sin_ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
  have h1 : Real.cos θ = 1 - 2*Real.sin (θ/2)^2 := by
    have := Real.cos_two_mul (θ/2); rw [show 2*(θ/2)=θ from by ring] at this
    nlinarith [Real.sin_sq_add_cos_sq (θ/2)]
  nlinarith [Real.sin_sq_add_cos_sq θ, h1]
lemma nsq_zjsub1_le (j:ℕ)(θ:ℝ) : Complex.normSq (Complex.exp (θ*Complex.I)^j - 1) ≤ 4 := by
  have h2 : ‖Complex.exp (θ*Complex.I)^j - 1‖ ≤ 2 := by
    calc ‖Complex.exp (θ*Complex.I)^j - 1‖ ≤ ‖Complex.exp (θ*Complex.I)^j‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, Complex.norm_exp]; norm_num
  rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (Complex.exp (θ*Complex.I)^j - 1)]
lemma fac_normSq_le_csc (j:ℕ)(θ:ℝ) (hθ : Real.sin (θ/2) ≠ 0) :
    Complex.normSq (fac j θ) ≤ 1/Real.sin (θ/2)^2 := by
  have hb : (0:ℝ) < Real.sin (θ/2)^2 := by positivity
  have key : Complex.normSq (fac j θ) * (4*Real.sin (θ/2)^2)
      = Complex.normSq (Complex.exp (θ*Complex.I)^j - 1) := by rw [← nsq_zsub1, ← map_mul, fac_mul]
  rw [le_div_iff₀ hb]; nlinarith [key, nsq_zjsub1_le j θ]

-- per-term tail: gg ≥ 3/4 when j large
lemma gg_ge_tail {n j : ℕ} (θ:ℝ) (hj1 : 1 ≤ j) (hjn : n ≤ 2*j)
    (hn : 4 ≤ n) (hθ1 : 4*Real.pi/n ≤ θ) (hθ2 : θ ≤ Real.pi) : (3:ℝ)/4 ≤ gg j θ := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hθ2' : θ/2 ≤ Real.pi/2 := by linarith
  have hθ0 : 0 ≤ θ/2 := by
    have : (0:ℝ) < 4*Real.pi/n := by positivity
    linarith
  have hsin : 4/(n:ℝ) ≤ Real.sin (θ/2) := by
    have hj : 2/Real.pi * (θ/2) ≤ Real.sin (θ/2) := mul_le_sin hθ0 hθ2'
    have h4n : 4/(n:ℝ) ≤ 2/Real.pi * (θ/2) := by
      have he : 2/Real.pi*(θ/2) = θ/Real.pi := by ring
      rw [he, div_le_div_iff₀ hnpos Real.pi_pos]
      rw [div_le_iff₀ hnpos] at hθ1; nlinarith [hθ1]
    linarith
  have hsinpos : (0:ℝ) < Real.sin (θ/2) := by
    have : (0:ℝ) < 4/(n:ℝ) := by positivity
    linarith
  have hjr : (n:ℝ)/2 ≤ (j:ℝ) := by
    rw [div_le_iff₀ (by norm_num)]
    have : (n:ℝ) ≤ 2*(j:ℝ) := by exact_mod_cast hjn
    linarith
  have hjsin : (2:ℝ) ≤ (j:ℝ) * Real.sin (θ/2) := by
    have hp : (n:ℝ)/2 * (4/(n:ℝ)) = 2 := by field_simp; ring
    have := mul_le_mul hjr hsin (by positivity) (by positivity : (0:ℝ) ≤ (j:ℝ))
    rw [hp] at this; exact this
  have hjsq : (4:ℝ) ≤ (j:ℝ)^2 * Real.sin (θ/2)^2 := by nlinarith [hjsin, hsinpos]
  have hle := fac_normSq_le_csc j θ hsinpos.ne'
  unfold gg
  have hjpos : (0:ℝ) < (j:ℝ)^2 := by
    have : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj1
    positivity
  have : Complex.normSq (fac j θ)/(j:ℝ)^2 ≤ 1/4 := by
    rw [div_le_iff₀ hjpos]
    calc Complex.normSq (fac j θ) ≤ 1/Real.sin (θ/2)^2 := hle
      _ ≤ 1/4 * (j:ℝ)^2 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith [hjsq]
  linarith

lemma gg_tail_sum {n:ℕ} (hn : 4 ≤ n) (θ:ℝ) (hθ1 : 4*Real.pi/n ≤ θ) (hθ2 : θ ≤ Real.pi) :
    (3:ℝ)/8 * n ≤ ∑ j ∈ Finset.Icc 1 n, gg j θ := by
  have hsub : Finset.Icc (n/2+1) n ⊆ Finset.Icc 1 n :=
    Finset.Icc_subset_Icc (by omega) (le_refl n)
  have hcard : (Finset.Icc (n/2+1) n).card = n - n/2 := by rw [Nat.card_Icc]; omega
  have hstep1 : ∑ j ∈ Finset.Icc (n/2+1) n, (3/4:ℝ) ≤ ∑ j ∈ Finset.Icc (n/2+1) n, gg j θ := by
    apply Finset.sum_le_sum
    intro j hj
    simp only [Finset.mem_Icc] at hj
    exact gg_ge_tail θ (by omega) (by omega) hn hθ1 hθ2
  have hstep2 : ∑ j ∈ Finset.Icc (n/2+1) n, gg j θ ≤ ∑ j ∈ Finset.Icc 1 n, gg j θ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro j hj _; exact gg_nonneg (Finset.mem_Icc.mp hj).1 θ
  have hconst : ∑ j ∈ Finset.Icc (n/2+1) n, (3/4:ℝ) = (3/4) * ((n - n/2 : ℕ):ℝ) := by
    rw [Finset.sum_const, hcard]; simp [mul_comm]
  have hnn : (3:ℝ)/8 * n ≤ (3/4) * ((n - n/2 : ℕ):ℝ) := by
    have : (n:ℝ) ≤ 2 * ((n - n/2 : ℕ):ℝ) := by
      have : n ≤ 2*(n - n/2) := by omega
      exact_mod_cast this
    linarith
  linarith [hnn, hconst ▸ hstep1, hstep2]

-- Central bound (Need-1) pieces
lemma sumR_id (j:ℕ) : ∑ i ∈ Finset.range j, (i:ℝ) = (j:ℝ)*((j:ℝ)-1)/2 := by
  induction j with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
lemma sumR_sq (j:ℕ) : ∑ i ∈ Finset.range j, (i:ℝ)^2 = (j:ℝ)*((j:ℝ)-1)*(2*(j:ℝ)-1)/6 := by
  induction j with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
lemma sum_sq_diff (j:ℕ) : ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j, ((i:ℝ)-(i':ℝ))^2
    = (j:ℝ)^2*((j:ℝ)^2-1)/6 := by
  have h : ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j, ((i:ℝ)-(i':ℝ))^2
      = 2*(j:ℝ)*(∑ i ∈ Finset.range j, (i:ℝ)^2) - 2*(∑ i ∈ Finset.range j,(i:ℝ))^2 := by
    have e : ∀ i i':ℕ, ((i:ℝ)-(i':ℝ))^2 = (i:ℝ)^2 - 2*(i:ℝ)*(i':ℝ) + (i':ℝ)^2 := fun _ _ => by ring
    simp_rw [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
  rw [h, sumR_id, sumR_sq]; ring

lemma abs_sin_ge (y:ℝ) (hy : |y| ≤ Real.pi/2) : 2/Real.pi*|y| ≤ |Real.sin y| := by
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h] at hy ⊢
    rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [Real.pi_pos]))]
    exact mul_le_sin h hy
  · rw [abs_of_nonpos h] at hy ⊢
    rw [abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h (by linarith [Real.pi_pos])), ← Real.sin_neg]
    exact mul_le_sin (by linarith) hy
lemma one_sub_cos_lb (x:ℝ) (hx : |x| ≤ Real.pi) : 2*x^2/Real.pi^2 ≤ 1 - Real.cos x := by
  have hcos : Real.cos x = 1 - 2*Real.sin (x/2)^2 := by
    have := Real.cos_two_mul (x/2); rw [show 2*(x/2)=x from by ring] at this
    nlinarith [Real.sin_sq_add_cos_sq (x/2)]
  have hy : |x/2| ≤ Real.pi/2 := by rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith [hx]
  have hs := abs_sin_ge (x/2) hy
  have h0 : 0 ≤ 2/Real.pi*|x/2| := by positivity
  have hsq0 : (2/Real.pi*|x/2|)^2 ≤ |Real.sin (x/2)|^2 := by nlinarith [hs, h0]
  rw [sq_abs] at hsq0
  have e1 : (2/Real.pi*|x/2|)^2 = x^2/Real.pi^2 := by rw [mul_pow, sq_abs]; ring
  rw [e1] at hsq0
  rw [hcos, mul_div_assoc]; nlinarith [hsq0]

-- gg as double sum of (1-cos)
lemma gg_eq_sum {j:ℕ} (hj : 1 ≤ j) (θ:ℝ) : gg j θ
    = (∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j, (1 - Real.cos ((i:ℝ)*θ-(i':ℝ)*θ)))/(j:ℝ)^2 := by
  have hj2 : (0:ℝ) < (j:ℝ)^2 := by
    have : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj
    positivity
  unfold gg
  rw [fac_normSq_cos]
  have hsum1 : (∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j, (1:ℝ)) = (j:ℝ)^2 := by
    simp [Finset.sum_const, Finset.card_range]; ring
  have key : (∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j, (1 - Real.cos ((i:ℝ)*θ-(i':ℝ)*θ)))
      = (j:ℝ)^2 - ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j, Real.cos ((i:ℝ)*θ-(i':ℝ)*θ) := by
    simp_rw [Finset.sum_sub_distrib]; rw [hsum1]
  rw [key, sub_div, div_self hj2.ne']

lemma gg_central_term {j:ℕ} (hj : 1 ≤ j) {θ:ℝ} (hθ0 : 0 ≤ θ) (hjθ : (j:ℝ)*θ ≤ Real.pi) :
    θ^2/(3*Real.pi^2)*((j:ℝ)^2-1) ≤ gg j θ := by
  have hj2 : (0:ℝ) < (j:ℝ)^2 := by
    have : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj
    positivity
  rw [gg_eq_sum hj, le_div_iff₀ hj2]
  have hlb : θ^2/(3*Real.pi^2)*((j:ℝ)^2-1)*(j:ℝ)^2
      = (2/Real.pi^2)*θ^2*(∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j, ((i:ℝ)-(i':ℝ))^2) := by
    rw [sum_sq_diff]
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp; ring
  rw [hlb]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro i' hi'
  simp only [Finset.mem_range] at hi hi'
  have hx : |(i:ℝ)*θ - (i':ℝ)*θ| ≤ Real.pi := by
    rw [show (i:ℝ)*θ-(i':ℝ)*θ = ((i:ℝ)-(i':ℝ))*θ from by ring, abs_mul, abs_of_nonneg hθ0]
    have h1 : |(i:ℝ)-(i':ℝ)| ≤ (j:ℝ) := by
      rw [abs_le]
      have hib : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast le_of_lt hi
      have hib' : (i':ℝ) ≤ (j:ℝ) := by exact_mod_cast le_of_lt hi'
      have hi0 : (0:ℝ) ≤ (i:ℝ) := by positivity
      have hi0' : (0:ℝ) ≤ (i':ℝ) := by positivity
      constructor <;> linarith
    calc |(i:ℝ)-(i':ℝ)| * θ ≤ (j:ℝ)*θ := mul_le_mul_of_nonneg_right h1 hθ0
      _ ≤ Real.pi := hjθ
  have hc := one_sub_cos_lb ((i:ℝ)*θ-(i':ℝ)*θ) hx
  rw [show (2/Real.pi^2)*θ^2*((i:ℝ)-(i':ℝ))^2 = 2*((i:ℝ)*θ-(i':ℝ)*θ)^2/Real.pi^2 from by ring]
  linarith [hc]

lemma log1p_bound {u : ℝ} (hu : -1/2 ≤ u) : |Real.log (1+u) - u| ≤ 2*u^2 := by
  have h1u : (0:ℝ) < 1 + u := by linarith
  have hup : Real.log (1+u) ≤ u := by
    have := Real.log_le_sub_one_of_pos h1u; linarith
  have hlow0 := Real.one_sub_inv_le_log_of_pos h1u
  have heq : 1 - (1+u)⁻¹ = u/(1+u) := by field_simp; ring
  have hlow : u/(1+u) ≤ Real.log (1+u) := by rw [heq] at hlow0; exact hlow0
  have hden : u^2/(1+u) ≤ 2*u^2 := by
    rw [div_le_iff₀ h1u]; nlinarith [sq_nonneg u]
  have h2 : u/(1+u) - u = -(u^2/(1+u)) := by field_simp; ring
  rw [abs_le]
  refine ⟨by linarith [hlow, hden], by linarith [hup, sq_nonneg u]⟩

lemma log_sinc_bound {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    |Real.log (Real.sin x / x) + x^2/6| ≤ x^3 := by
  have hxa : |x| = x := abs_of_pos hx0
  have hxle : |x| ≤ 1 := by rw [hxa]; exact hx1
  set u := Real.sin x / x - 1 with hu_def
  have hw : |u + x^2/6| ≤ (5/96) * x^3 := by
    have hb := Real.sin_bound hxle
    have : u + x^2/6 = (Real.sin x - (x - x^3/6))/x := by
      rw [hu_def]; field_simp; ring
    rw [this, abs_div, hxa, div_le_iff₀ hx0]
    calc |Real.sin x - (x - x^3/6)| ≤ |x|^4 * (5/96) := hb
      _ = (5/96)*x^3 * x := by rw [hxa]; ring
  have hub : |u| ≤ (21/96) * x^2 := by
    have h1 : |u| ≤ |u + x^2/6| + |x^2/6| := by
      calc |u| = |(u + x^2/6) - x^2/6| := by ring_nf
        _ ≤ |u+x^2/6| + |x^2/6| := abs_sub _ _
    calc |u| ≤ |u+x^2/6| + |x^2/6| := h1
      _ ≤ (5/96)*x^3 + x^2/6 := by
          have hx26 : |x^2/6| = x^2/6 := abs_of_nonneg (by positivity)
          rw [hx26]; linarith [hw]
      _ ≤ (21/96)*x^2 := by nlinarith [hx0.le, hx1, sq_nonneg x]
  have huge : -1/2 ≤ u := by
    have := abs_le.mp hub
    nlinarith [this.1, this.2, hx1, hx0.le, sq_nonneg x]
  have hlog := log1p_bound huge
  have hsinc : Real.sin x / x = 1 + u := by rw [hu_def]; ring
  rw [hsinc]
  have hkey : Real.log (1+u) + x^2/6 = (Real.log (1+u) - u) + (u + x^2/6) := by ring
  rw [hkey]
  calc |(Real.log (1+u) - u) + (u + x^2/6)| ≤ |Real.log (1+u) - u| + |u + x^2/6| := abs_add_le _ _
    _ ≤ 2*u^2 + (5/96)*x^3 := by gcongr
    _ ≤ x^3 := by nlinarith [hub, abs_nonneg u, sq_abs u, hx0.le, hx1, sq_nonneg x]

-- variance asymptotic
lemma Vclosed (n:ℕ) : (∑ j ∈ Finset.Icc 1 n, ((j:ℝ)^2-1)/12) = (2*(n:ℝ)^3+3*n^2-5*n)/72 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [← Ico_add_one_right_eq_Icc 1, Finset.sum_Ico_succ_top (by omega),
        Ico_add_one_right_eq_Icc 1, ih]; push_cast; ring

-- POINTWISE CLT MACHINERY (centered normalized characteristic function Rn)
noncomputable def Rn (n : ℕ) (θ : ℝ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 n, Real.sin (j*θ/2)/(j*Real.sin (θ/2))

noncomputable def gsinc (x : ℝ) : ℝ := Real.log (Real.sin x / x)

lemma sin_pos_of_le_one {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) : 0 < Real.sin a :=
  Real.sin_pos_of_pos_of_lt_pi ha (by linarith [Real.pi_gt_three])

lemma log_Rn_eq {n : ℕ} {θ : ℝ} (hθ : 0 < θ) (hn : 1 ≤ n) (hb : (n:ℝ)*θ/2 ≤ 1) :
    Real.log (Rn n θ) = (∑ j ∈ Finset.Icc 1 n, gsinc ((j:ℝ)*θ/2)) - n * gsinc (θ/2) := by
  have hθ2 : 0 < θ/2 := by linarith
  have hθ2le : θ/2 ≤ 1 := by
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    nlinarith [hb]
  have hsθ : 0 < Real.sin (θ/2) := sin_pos_of_le_one hθ2 hθ2le
  have hfacpos : ∀ j ∈ Finset.Icc 1 n, 0 < Real.sin (j*θ/2)/(j*Real.sin (θ/2)) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hj1 : 1 ≤ j := hj.1
    have hjn : j ≤ n := hj.2
    have hja : 0 < (j:ℝ)*θ/2 := by
      have : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj1
      positivity
    have hja1 : (j:ℝ)*θ/2 ≤ 1 := by
      have : (j:ℝ) ≤ (n:ℝ) := by exact_mod_cast hjn
      nlinarith [hb, hθ.le]
    have hsj : 0 < Real.sin (j*θ/2) := sin_pos_of_le_one hja hja1
    have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj1
    positivity
  rw [Rn, Real.log_prod (fun j hj => (hfacpos j hj).ne')]
  have hterm : ∀ j ∈ Finset.Icc 1 n,
      Real.log (Real.sin (j*θ/2)/(j*Real.sin (θ/2))) = gsinc ((j:ℝ)*θ/2) - gsinc (θ/2) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hj1 : 1 ≤ j := hj.1
    have hjn : j ≤ n := hj.2
    have hja : 0 < (j:ℝ)*θ/2 := by
      have : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj1
      positivity
    have hja1 : (j:ℝ)*θ/2 ≤ 1 := by
      have : (j:ℝ) ≤ (n:ℝ) := by exact_mod_cast hjn
      nlinarith [hb, hθ.le]
    have hsj : 0 < Real.sin (j*θ/2) := sin_pos_of_le_one hja hja1
    have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj1
    unfold gsinc
    have hA : Real.sin ((j:ℝ)*θ/2)/((j:ℝ)*θ/2) ≠ 0 := by positivity
    have hB : Real.sin (θ/2)/(θ/2) ≠ 0 := by positivity
    rw [← Real.log_div hA hB]
    congr 1
    field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const,
      Nat.card_Icc, nsmul_eq_mul]
  push_cast
  ring

lemma logRn_close {n : ℕ} {θ : ℝ} (hθ : 0 < θ) (hn : 1 ≤ n) (hb : (n:ℝ)*θ/2 ≤ 1) :
    |Real.log (Rn n θ) + θ^2/24 * (∑ j ∈ Finset.Icc 1 n, ((j:ℝ)^2-1))|
      ≤ 2*(θ/2)^3*(n:ℝ)^4 := by
  have hnr : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hθ2 : 0 < θ/2 := by linarith
  have hθ2le : θ/2 ≤ 1 := by
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    nlinarith [hb]
  rw [log_Rn_eq hθ hn hb]
  have e1 : (∑ j ∈ Finset.Icc 1 n, ((j:ℝ)*θ/2)^2/6)
      = θ^2/24*(∑ j ∈ Finset.Icc 1 n, ((j:ℝ)^2-1)) + (n:ℝ)*(θ/2)^2/6 := by
    rw [Finset.mul_sum]
    rw [show (n:ℝ)*(θ/2)^2/6 = ∑ _j ∈ Finset.Icc 1 n, θ^2/24 by
          rw [Finset.sum_const, Nat.card_Icc]; push_cast; ring]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  have hcomb : (∑ j ∈ Finset.Icc 1 n, gsinc ((j:ℝ)*θ/2)) - (n:ℝ) * gsinc (θ/2)
        + θ^2/24 * (∑ j ∈ Finset.Icc 1 n, ((j:ℝ)^2-1))
      = (∑ j ∈ Finset.Icc 1 n, (gsinc ((j:ℝ)*θ/2) + ((j:ℝ)*θ/2)^2/6))
        - (n:ℝ) * (gsinc (θ/2) + (θ/2)^2/6) := by
    rw [Finset.sum_add_distrib, e1]; ring
  rw [hcomb]
  have htri : |(∑ j ∈ Finset.Icc 1 n, (gsinc ((j:ℝ)*θ/2) + ((j:ℝ)*θ/2)^2/6))
        - (n:ℝ) * (gsinc (θ/2) + (θ/2)^2/6)|
      ≤ |∑ j ∈ Finset.Icc 1 n, (gsinc ((j:ℝ)*θ/2) + ((j:ℝ)*θ/2)^2/6)|
        + (n:ℝ) * |gsinc (θ/2) + (θ/2)^2/6| := by
    calc _ ≤ |∑ j ∈ Finset.Icc 1 n, (gsinc ((j:ℝ)*θ/2) + ((j:ℝ)*θ/2)^2/6)|
              + |(n:ℝ) * (gsinc (θ/2) + (θ/2)^2/6)| := abs_sub _ _
      _ = _ := by rw [abs_mul, abs_of_nonneg hnr.le]
  refine htri.trans ?_
  have hsumbd : |∑ j ∈ Finset.Icc 1 n, (gsinc ((j:ℝ)*θ/2) + ((j:ℝ)*θ/2)^2/6)|
      ≤ (θ/2)^3*(n:ℝ)^4 := by
    calc |∑ j ∈ Finset.Icc 1 n, (gsinc ((j:ℝ)*θ/2) + ((j:ℝ)*θ/2)^2/6)|
        ≤ ∑ j ∈ Finset.Icc 1 n, |gsinc ((j:ℝ)*θ/2) + ((j:ℝ)*θ/2)^2/6| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.Icc 1 n, (θ/2)^3*(n:ℝ)^3 := by
          apply Finset.sum_le_sum; intro j hj
          simp only [Finset.mem_Icc] at hj
          have hj1 : 1 ≤ j := hj.1
          have hjn : j ≤ n := hj.2
          have hja : 0 < (j:ℝ)*θ/2 := by
            have : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj1
            positivity
          have hja1 : (j:ℝ)*θ/2 ≤ 1 := by
            have : (j:ℝ) ≤ (n:ℝ) := by exact_mod_cast hjn
            nlinarith [hb, hθ.le]
          have hjnr : (j:ℝ) ≤ (n:ℝ) := by exact_mod_cast hjn
          have := log_sinc_bound hja hja1
          calc |gsinc ((j:ℝ)*θ/2) + ((j:ℝ)*θ/2)^2/6| ≤ ((j:ℝ)*θ/2)^3 := this
            _ = (θ/2)^3*(j:ℝ)^3 := by ring
            _ ≤ (θ/2)^3*(n:ℝ)^3 := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact pow_le_pow_left₀ (by positivity) hjnr 3
      _ = (θ/2)^3*(n:ℝ)^4 := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  have hsecbd : (n:ℝ) * |gsinc (θ/2) + (θ/2)^2/6| ≤ (n:ℝ)*(θ/2)^3 := by
    apply mul_le_mul_of_nonneg_left _ hnr.le
    exact log_sinc_bound hθ2 hθ2le
  have hn14 : (n:ℝ)*(θ/2)^3 ≤ (θ/2)^3*(n:ℝ)^4 := by
    have h3 : (0:ℝ) ≤ (θ/2)^3 := by positivity
    have : (n:ℝ) ≤ (n:ℝ)^4 := by nlinarith [hnr, pow_le_pow_right₀ (by exact_mod_cast hn : (1:ℝ) ≤ n) (by norm_num : 1 ≤ 4)]
    nlinarith [this, h3]
  nlinarith [hsumbd, hsecbd, hn14]

lemma Vnonneg (n:ℕ) : 0 ≤ ∑ j ∈ Finset.Icc 1 n, ((j:ℝ)^2-1)/12 := by
  apply Finset.sum_nonneg; intro j hj
  simp only [Finset.mem_Icc] at hj
  have h1 : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj.1
  have h2 : (1:ℝ) ≤ (j:ℝ)^2 := by nlinarith
  linarith [h2]

lemma Sig_sq (n:ℕ) : (Sig n)^2 = ∑ j ∈ Finset.Icc 1 n, ((j:ℝ)^2-1)/12 := by
  unfold Sig; rw [Real.sq_sqrt (Vnonneg n)]

lemma Vge {n:ℕ} (hn : 2 ≤ n) : (n:ℝ)^3/72 ≤ (Sig n)^2 := by
  rw [Sig_sq, Vclosed]
  have : (2:ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [this]

lemma Sig_pos' {n:ℕ} (hn : 2 ≤ n) : 0 < Sig n := by
  have h := Vge hn
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn3 : 0 < (n:ℝ)^3 := by positivity
  have hpos : 0 < (Sig n)^2 := by nlinarith
  have hnn : 0 ≤ Sig n := Real.sqrt_nonneg _
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exfalso; rw [← h] at hpos; simp at hpos

lemma tendsto_of_sq {a : ℕ → ℝ} (hnn : ∀ᶠ n in atTop, 0 ≤ a n)
    (h : Tendsto (fun n => (a n)^2) atTop (nhds 0)) : Tendsto a atTop (nhds 0) := by
  have hsq : Tendsto (fun n => Real.sqrt ((a n)^2)) atTop (nhds 0) := by
    have hc := (Real.continuous_sqrt.tendsto 0).comp h
    simpa using hc
  apply hsq.congr'
  filter_upwards [hnn] with n hn
  rw [Real.sqrt_sq hn]

lemma pointwise_CLT {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n => Real.log (Rn n (s / Sig n))) atTop (nhds (-(s^2)/2)) := by
  set E : ℕ → ℝ := fun n => 2*((s/Sig n)/2)^3*(n:ℝ)^4 with hE
  have hEto : Tendsto E atTop (nhds 0) := by
    apply tendsto_of_sq
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hSig := Sig_pos' hn
      positivity
    · have hCn : Tendsto (fun n:ℕ => (s^6*72^3/16)/(n:ℝ)) atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      apply squeeze_zero_norm' _ hCn
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hSig := Sig_pos' hn
      have hVge := Vge hn
      have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hSig6 : (n:ℝ)^9/72^3 ≤ (Sig n)^6 := by
        have he : (Sig n)^6 = ((Sig n)^2)^3 := by ring
        rw [he]
        have h1 : ((n:ℝ)^3/72)^3 ≤ ((Sig n)^2)^3 :=
          pow_le_pow_left₀ (by positivity) hVge 3
        calc (n:ℝ)^9/72^3 = ((n:ℝ)^3/72)^3 := by ring
          _ ≤ ((Sig n)^2)^3 := h1
      have hEsq : (E n)^2 = s^6 * (n:ℝ)^8/(16*(Sig n)^6) := by
        rw [hE]; field_simp; ring
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hEsq]
      rw [div_le_div_iff₀ (by positivity) hnpos]
      have hSig6pos : (0:ℝ) < (Sig n)^6 := by positivity
      nlinarith [hSig6, hnpos, pow_pos hnpos 8, pow_pos hs 6, hSig6pos,
                 mul_le_mul_of_nonneg_left hSig6 (by positivity : (0:ℝ) ≤ s^6*16)]
  have hbound : ∀ᶠ n in atTop, |Real.log (Rn n (s/Sig n)) - (-(s^2)/2)| ≤ E n := by
    obtain ⟨N, hN⟩ := exists_nat_ge (18*s^2)
    filter_upwards [eventually_ge_atTop (max 2 N)] with n hn
    have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
    have hnN : N ≤ n := le_trans (le_max_right _ _) hn
    have hnNr : (18*s^2 : ℝ) ≤ (n:ℝ) := le_trans hN (by exact_mod_cast hnN)
    have hSig := Sig_pos' hn2
    have hVge := Vge hn2
    have hnr : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    set θ := s / Sig n with hθdef
    have hθpos : 0 < θ := div_pos hs hSig
    have hSigge : (n:ℝ)*s/2 ≤ Sig n := by
      have hsq : ((n:ℝ)*s/2)^2 ≤ (Sig n)^2 := by
        nlinarith [hVge, hnr, hs, mul_nonneg (sub_nonneg.mpr hnNr) (sq_nonneg (n:ℝ))]
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq hSig.le] at this
    have hb : (n:ℝ)*θ/2 ≤ 1 := by
      rw [hθdef]
      have hrw : (n:ℝ)*(s/Sig n)/2 = (n:ℝ)*s/(2*Sig n) := by
        rw [mul_div_assoc, div_div, mul_comm (Sig n) (2:ℝ), mul_div_assoc]
      rw [hrw, div_le_one (by positivity)]
      linarith [hSigge]
    have hn1 : 1 ≤ n := by omega
    have hclose := logRn_close hθpos hn1 hb
    have hconv : θ^2/24 * (∑ j ∈ Finset.Icc 1 n, ((j:ℝ)^2-1)) = s^2/2 := by
      have h12 : (∑ j ∈ Finset.Icc 1 n, ((j:ℝ)^2-1)) = 12*(Sig n)^2 := by
        rw [Sig_sq, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring
      rw [h12, hθdef]
      field_simp
      ring
    rw [hconv] at hclose
    have heq : Real.log (Rn n (s/Sig n)) - (-(s^2)/2) = Real.log (Rn n θ) + s^2/2 := by
      rw [hθdef]; ring
    rw [heq]
    have hEeq : E n = 2*(θ/2)^3*(n:ℝ)^4 := by rw [hE, hθdef]
    rw [hEeq]
    exact hclose
  have hdiff : Tendsto (fun n => Real.log (Rn n (s/Sig n)) - (-(s^2)/2)) atTop (nhds 0) :=
    squeeze_zero_norm' hbound hEto
  have := hdiff.add (tendsto_const_nhds (x := -(s^2)/2))
  simpa using this

lemma Rn_pos {n : ℕ} {θ : ℝ} (hθ : 0 < θ) (hn : 1 ≤ n) (hb : (n:ℝ)*θ/2 ≤ 1) : 0 < Rn n θ := by
  have hθ2 : 0 < θ/2 := by linarith
  have hθ2le : θ/2 ≤ 1 := by
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    nlinarith [hb]
  have hsθ : 0 < Real.sin (θ/2) := sin_pos_of_le_one hθ2 hθ2le
  apply Finset.prod_pos
  intro j hj
  simp only [Finset.mem_Icc] at hj
  have hja : 0 < (j:ℝ)*θ/2 := by
    have : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj.1
    positivity
  have hja1 : (j:ℝ)*θ/2 ≤ 1 := by
    have : (j:ℝ) ≤ (n:ℝ) := by exact_mod_cast hj.2
    nlinarith [hb, hθ.le]
  have hsj : 0 < Real.sin (j*θ/2) := sin_pos_of_le_one hja hja1
  have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj.1
  positivity

lemma pointwise_CLT' {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n => Rn n (s / Sig n)) atTop (nhds (Real.exp (-(s^2)/2))) := by
  have hlog := pointwise_CLT hs
  have h2 : Tendsto (fun n => Real.exp (Real.log (Rn n (s/Sig n)))) atTop
      (nhds (Real.exp (-(s^2)/2))) := (Real.continuous_exp.tendsto _).comp hlog
  apply h2.congr'
  obtain ⟨N, hN⟩ := exists_nat_ge (18*s^2)
  filter_upwards [eventually_ge_atTop (max 2 N)] with n hn
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hnN : N ≤ n := le_trans (le_max_right _ _) hn
  have hnNr : (18*s^2 : ℝ) ≤ (n:ℝ) := le_trans hN (by exact_mod_cast hnN)
  have hSig := Sig_pos' hn2
  have hVge := Vge hn2
  have hnr : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hθpos : 0 < s / Sig n := div_pos hs hSig
  have hSigge : (n:ℝ)*s/2 ≤ Sig n := by
    have hsq : ((n:ℝ)*s/2)^2 ≤ (Sig n)^2 := by
      nlinarith [hVge, hnr, hs, mul_nonneg (sub_nonneg.mpr hnNr) (sq_nonneg (n:ℝ))]
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq hSig.le] at this
  have hb : (n:ℝ)*(s/Sig n)/2 ≤ 1 := by
    have hrw : (n:ℝ)*(s/Sig n)/2 = (n:ℝ)*s/(2*Sig n) := by
      rw [mul_div_assoc, div_div, mul_comm (Sig n) (2:ℝ), mul_div_assoc]
    rw [hrw, div_le_one (by positivity)]; linarith [hSigge]
  rw [Real.exp_log (Rn_pos hθpos (by omega) hb)]

-- BRIDGE: Phi = n! * exp(iμθ) * Rn
lemma expdiff (z : ℂ) :
    Complex.exp (z*Complex.I) - Complex.exp (-(z*Complex.I)) = 2*Complex.I*Complex.sin z := by
  rw [Complex.sin]
  have h : (2:ℂ)*Complex.I*((Complex.exp (-z*Complex.I)-Complex.exp (z*Complex.I))*Complex.I/2)
      = (Complex.exp (-z*Complex.I)-Complex.exp (z*Complex.I))*(Complex.I*Complex.I) := by ring
  rw [h, Complex.I_mul_I]
  rw [show -z*Complex.I = -(z*Complex.I) from by ring]
  ring

lemma expsub1 (φ : ℝ) :
    Complex.exp (φ*Complex.I) - 1
      = Complex.exp ((φ/2)*Complex.I) * (2*Complex.I*(Real.sin (φ/2):ℂ)) := by
  have hd := expdiff ((φ/2 : ℝ) : ℂ)
  rw [← Complex.ofReal_sin] at hd
  rw [← hd, mul_sub, ← Complex.exp_add, ← Complex.exp_add]
  have hA : (φ:ℂ)/2*Complex.I + ((φ/2:ℝ):ℂ)*Complex.I = (φ:ℝ)*Complex.I := by push_cast; ring
  have hB : (φ:ℂ)/2*Complex.I + -(((φ/2:ℝ):ℂ)*Complex.I) = 0 := by push_cast; ring
  rw [hA, hB, Complex.exp_zero]

lemma fac_closed (j:ℕ) (θ:ℝ) (hθ : Real.sin (θ/2) ≠ 0) :
    fac j θ = Complex.exp ((((j:ℝ)-1)*θ/2)*Complex.I) * ((Real.sin (j*θ/2)/Real.sin (θ/2) : ℝ) : ℂ) := by
  have hsne : ((Real.sin (θ/2):ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hθ
  have hz1 : Complex.exp (θ*Complex.I) - 1 ≠ 0 := by
    rw [expsub1 θ]
    exact mul_ne_zero (Complex.exp_ne_zero _)
      (mul_ne_zero (by norm_num [Complex.I_ne_zero]) hsne)
  have key := fac_mul j θ
  have hfac : fac j θ = (Complex.exp (θ*Complex.I)^j - 1)/(Complex.exp (θ*Complex.I) - 1) :=
    eq_div_of_mul_eq hz1 key
  rw [hfac]
  have hpow : Complex.exp (θ*Complex.I)^j = Complex.exp (((j*θ:ℝ):ℂ)*Complex.I) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [hpow, expsub1 (j*θ), expsub1 θ, Complex.ofReal_div]
  rw [mul_div_mul_comm, ← Complex.exp_sub]
  congr 1
  · congr 1; push_cast; ring
  · rw [mul_div_mul_left _ _ (by simp [Complex.I_ne_zero] : (2*Complex.I:ℂ) ≠ 0)]

lemma sum_jm1 (n : ℕ) (θ : ℝ) : ∑ j ∈ Finset.Icc 1 n, (((j:ℝ)-1)*θ/2) = (n*(n-1)/4)*θ := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [← Finset.Ico_add_one_right_eq_Icc 1, Finset.sum_Ico_succ_top (by omega),
        Finset.Ico_add_one_right_eq_Icc 1, ih]
    push_cast; ring

lemma prod_ratio (n : ℕ) (θ : ℝ) (hθ : Real.sin (θ/2) ≠ 0) :
    ∏ j ∈ Finset.Icc 1 n, (Real.sin (j*θ/2)/Real.sin (θ/2)) = (n.factorial:ℝ) * Rn n θ := by
  rw [Rn, ← prod_Icc_one_id n, Nat.cast_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.mem_Icc] at hj
  have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj.1
  field_simp

lemma Phi_factored (n : ℕ) (θ : ℝ) (hθ : Real.sin (θ/2) ≠ 0) :
    Phi n θ = (n.factorial:ℂ) * Complex.exp (((n*(n-1)/4:ℝ))*θ*Complex.I) * ((Rn n θ:ℝ):ℂ) := by
  rw [Phi_eq_prod_fac, Finset.prod_congr rfl (fun j _ => fac_closed j θ hθ),
      Finset.prod_mul_distrib, ← Complex.exp_sum, ← Complex.ofReal_prod, prod_ratio n θ hθ]
  have hcast : (∑ j ∈ Finset.Icc 1 n, ((((j:ℝ)-1)*θ/2)*Complex.I))
      = ((∑ j ∈ Finset.Icc 1 n, (((j:ℝ)-1)*θ/2) : ℝ):ℂ)*Complex.I := by
    rw [Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _; push_cast; ring
  rw [hcast, sum_jm1]
  push_cast
  ring

lemma Phi_continuous (n:ℕ) : Continuous (fun θ => Phi n θ) := by
  simp_rw [Phi_eq_sum']
  apply continuous_finset_sum
  intro m _
  exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))

open MeasureTheory in
lemma cc_real_integral (n m : ℕ) (hm : m ≤ n*(n-1)/2) :
    (2*Real.pi) * (cc n m : ℝ)
      = (n.factorial:ℝ) * ∫ θ in (-Real.pi)..Real.pi, Rn n θ * Real.cos (((m:ℝ) - n*(n-1)/4)*θ) := by
  set μ : ℝ := (n:ℝ)*((n:ℝ)-1)/4 with hμ
  set F : ℝ → ℂ := fun θ => Phi n θ * Complex.exp (-(m:ℝ)*θ*Complex.I) with hF
  set G : ℝ → ℂ := fun θ => (n.factorial:ℂ) * Complex.exp ((μ-(m:ℝ))*θ*Complex.I) * ((Rn n θ:ℝ):ℂ) with hG
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Set.uIoc (-Real.pi) Real.pi → F θ = G θ := by
    have h0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 := by
      have : ({(0:ℝ)}ᶜ) ∈ (ae (volume:Measure ℝ)) := by
        rw [mem_ae_iff, compl_compl]; exact measure_singleton 0
      filter_upwards [this] with θ hθ; simpa using hθ
    filter_upwards [h0] with θ hθ0 hmem
    rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hmem
    simp only [hF, hG]
    have hsin : Real.sin (θ/2) ≠ 0 := by
      intro h
      have hlt1 : -Real.pi < θ/2 := by linarith [hmem.1, Real.pi_pos]
      have hlt2 : θ/2 < Real.pi := by linarith [hmem.2, Real.pi_pos]
      rw [Real.sin_eq_zero_iff_of_lt_of_lt hlt1 hlt2] at h
      exact hθ0 (by linarith)
    rw [Phi_factored n θ hsin]
    rw [mul_assoc, mul_assoc]
    rw [show ((μ-(m:ℝ))*θ*Complex.I) = ((μ:ℝ)*θ*Complex.I) + (-(m:ℝ)*θ*Complex.I) from by push_cast [hμ]; ring]
    rw [Complex.exp_add]
    ring
  have hFint : IntervalIntegrable F volume (-Real.pi) Real.pi :=
    (Continuous.mul (Phi_continuous n) (Complex.continuous_exp.comp (by fun_prop))).intervalIntegrable _ _
  have hGint : IntervalIntegrable G volume (-Real.pi) Real.pi :=
    hFint.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae)
  have hFG : (∫ θ in (-Real.pi)..Real.pi, F θ) = ∫ θ in (-Real.pi)..Real.pi, G θ :=
    intervalIntegral.integral_congr_ae hae
  have hFcc : (∫ θ in (-Real.pi)..Real.pi, F θ) = 2*Real.pi*(cc n m) := fourier_inv n m hm
  have hGcc : (∫ θ in (-Real.pi)..Real.pi, G θ) = ((2*Real.pi*(cc n m:ℝ):ℝ):ℂ) := by
    rw [← hFG, hFcc]; push_cast; ring
  have hre : (∫ θ in (-Real.pi)..Real.pi, (G θ).re)
      = (∫ θ in (-Real.pi)..Real.pi, G θ).re :=
    Complex.reCLM.intervalIntegral_comp_comm hGint
  have hGre : ∀ θ, (G θ).re = (n.factorial:ℝ) * Rn n θ * Real.cos ((μ - (m:ℝ))*θ) := by
    intro θ
    rw [hG]; dsimp only
    have harg : ((μ:ℂ)-(m:ℝ))*(θ:ℂ)*Complex.I = (((μ-(m:ℝ))*θ:ℝ):ℂ)*Complex.I := by
      rw [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_natCast]
    rw [harg]
    simp only [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.natCast_re, Complex.natCast_im]
    ring
  have hcalc : (∫ θ in (-Real.pi)..Real.pi, (G θ).re)
      = (n.factorial:ℝ) * ∫ θ in (-Real.pi)..Real.pi, Rn n θ * Real.cos (((m:ℝ) - n*(n-1)/4)*θ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only []
    rw [hGre, show (μ-(m:ℝ))*θ = -(((m:ℝ)-μ)*θ) from by ring, Real.cos_neg, hμ]; ring
  rw [hre, hGcc, Complex.ofReal_re] at hcalc
  linarith [hcalc]

-- THE HARD ANALYTIC CORE (LCLT)
axiom hcore (k : ℕ) (hk : 0 < k) :
  Tendsto (fun n => (Sig n)^(k-1) * (Ak k n / (n.factorial:ℝ)^k)) atTop (nhds (Ik k))

lemma hvar : Tendsto (fun n:ℕ => (n:ℝ)^(3/2:ℝ) / Sig n) atTop (nhds 6) := by
  have hR : Tendsto (fun n:ℕ => (∑ j ∈ Finset.Icc 1 n, ((j:ℝ)^2-1)/12)/(n:ℝ)^3) atTop (nhds (1/36)) := by
    have h1 : Tendsto (fun n:ℕ => 1/(n:ℝ)) atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
    have hg : Tendsto (fun n:ℕ => (2 + 3*(1/(n:ℝ)) - 5*(1/(n:ℝ))^2)/72) atTop (nhds ((2+3*0-5*0^2)/72)) :=
      Tendsto.div_const ((tendsto_const_nhds.add ((tendsto_const_nhds).mul h1)).sub ((tendsto_const_nhds).mul (h1.pow 2))) _
    rw [show ((2:ℝ)+3*0-5*0^2)/72 = 1/36 from by norm_num] at hg
    apply hg.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    rw [Vclosed]; field_simp
  have hsqrt : Tendsto (fun n:ℕ => Sig n/(n:ℝ)^(3/2:ℝ)) atTop (nhds (1/6)) := by
    have hc : Tendsto (fun n:ℕ => Real.sqrt ((∑ j ∈ Finset.Icc 1 n, ((j:ℝ)^2-1)/12)/(n:ℝ)^3)) atTop (nhds (Real.sqrt (1/36))) :=
      (Real.continuous_sqrt.tendsto (1/36)).comp hR
    rw [show Real.sqrt (1/36) = 1/6 from by
        rw [show (1/36:ℝ)=(1/6)^2 from by norm_num, Real.sqrt_sq (by norm_num)]] at hc
    apply hc.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnn : (0:ℝ) ≤ (n:ℝ) := by positivity
    have hSpos : (0:ℝ) ≤ ∑ j ∈ Finset.Icc 1 n, ((j:ℝ)^2-1)/12 := by
      rw [Vclosed]
      have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      nlinarith [h1]
    unfold Sig
    rw [Real.sqrt_div hSpos, show (n:ℝ)^(3/2:ℝ) = Real.sqrt ((n:ℝ)^3) from by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (n:ℝ) 3, ← Real.rpow_mul hnn]; norm_num]
  have hinv : Tendsto (fun n:ℕ => (Sig n/(n:ℝ)^(3/2:ℝ))⁻¹) atTop (nhds ((1/6:ℝ)⁻¹)) :=
    hsqrt.inv₀ (by norm_num)
  rw [show ((1/6:ℝ)⁻¹) = 6 from by norm_num] at hinv
  apply hinv.congr'
  filter_upwards with n
  rw [inv_div]

lemma Ck_pos (k : ℕ) (hk : 0 < k) : 0 < Ck k := by
  unfold Ck
  apply div_pos
  · exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)
  · refine mul_pos (Real.sqrt_pos.2 ?_) (Real.rpow_pos_of_pos Real.pi_pos _)
    exact_mod_cast hk

lemma hCid (k : ℕ) (hk : 0 < k) : Ik k * (6:ℝ)^(k-1) = Ck k := by
  unfold Ik Ck
  have hd : ((k-1:ℕ):ℝ) = (k:ℝ) - 1 := by rw [Nat.cast_sub hk]; simp
  rw [show (6:ℝ)^(k-1) = (6:ℝ)^((k:ℝ)-1) from by rw [← hd, Real.rpow_natCast]]
  set d := (k:ℝ) - 1 with hddef
  rw [show (6:ℝ) = 2*3 from by norm_num]
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) ≤ 3)]
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.pi_pos.le)]
  rw [show (-d/2 : ℝ) = -(d/2) from by ring]
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_neg Real.pi_pos.le]
  rw [show (2:ℝ)^d = 2^(d/2)*2^(d/2) from by rw [← Real.rpow_add (by norm_num)]; ring_nf]
  have h2 : (2:ℝ)^(d/2) ≠ 0 := by positivity
  have hpi : Real.pi^(d/2) ≠ 0 := by positivity
  field_simp

-- Sig positive for n ≥ 2
lemma Sig_pos {n : ℕ} (hn : 2 ≤ n) : 0 < Sig n := by
  unfold Sig
  rw [Real.sqrt_pos]
  have hmem : (2:ℕ) ∈ Finset.Icc 1 n := by simp; omega
  apply Finset.sum_pos' (fun j hj => by
    simp only [Finset.mem_Icc] at hj
    have : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj.1
    nlinarith [this])
  exact ⟨2, hmem, by norm_num⟩

lemma qterm_eq (k n : ℕ) (hk : 0 < k) :
    qterm k n = Ck k * ((n.factorial:ℝ)^k) / ((n:ℝ)^(3*((k:ℝ)-1)/2)) := by
  unfold qterm Ck
  simp only
  rw [Real.rpow_natCast (n.factorial:ℝ) k]
  rw [show (3:ℝ) * (((k:ℝ)-1)/2) = 3*((k:ℝ)-1)/2 from by ring]
  ring

lemma ratio_eq {k : ℕ} (hk : 0 < k) {n : ℕ} (hn : 2 ≤ n) :
    Ak k n / qterm k n
    = (Sig n)^(k-1) * (Ak k n / (n.factorial:ℝ)^k) * (1/Ck k)
      * (((n:ℝ)^(3/2:ℝ) / Sig n)^(k-1)) := by
  have hd : ((k-1:ℕ):ℝ) = (k:ℝ) - 1 := by rw [Nat.cast_sub hk]; simp
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hS : Sig n ≠ 0 := (Sig_pos hn).ne'
  have hF : ((n.factorial:ℝ))^k ≠ 0 := by positivity
  have hC : Ck k ≠ 0 := (Ck_pos k hk).ne'
  -- x^(k-1) = n^(3(k-1)/2)
  have hx : ((n:ℝ)^(3/2:ℝ))^(k-1) = (n:ℝ)^(3*((k:ℝ)-1)/2) := by
    rw [← Real.rpow_natCast ((n:ℝ)^(3/2:ℝ)) (k-1), ← Real.rpow_mul hnpos.le, hd]
    congr 1; ring
  rw [qterm_eq k n hk]
  rw [div_pow]
  rw [hx]
  field_simp

lemma qterm_pos (k n : ℕ) (hk : 0 < k) (hn : 1 ≤ n) : 0 < qterm k n := by
  rw [qterm_eq k n hk]
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  apply div_pos
  · exact mul_pos (Ck_pos k hk) (by positivity)
  · exact Real.rpow_pos_of_pos hnpos _

lemma ratio_tendsto (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n => Ak k n / qterm k n) atTop (nhds 1) := by
  have hQ : Tendsto (fun n => (Sig n)^(k-1) * (Ak k n / (n.factorial:ℝ)^k) * (1/Ck k)
      * (((n:ℝ)^(3/2:ℝ) / Sig n)^(k-1))) atTop
      (nhds (Ik k * (1/Ck k) * (6:ℝ)^(k-1))) :=
    ((hcore k hk).mul tendsto_const_nhds).mul (hvar.pow (k-1))
  have hval : Ik k * (1/Ck k) * (6:ℝ)^(k-1) = 1 := by
    rw [show Ik k * (1/Ck k) * (6:ℝ)^(k-1) = (Ik k * (6:ℝ)^(k-1)) * (1/Ck k) from by ring,
        hCid k hk]
    rw [mul_one_div, div_self (Ck_pos k hk).ne']
  rw [hval] at hQ
  apply hQ.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact (ratio_eq hk hn).symm

theorem main (k : ℕ) (hk : 0 < k) :
    IsEquivalent atTop (fun n => Ak k n) (qterm k) := by
  rw [isEquivalent_iff_tendsto_one]
  · exact ratio_tendsto k hk
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (qterm_pos k n hk hn).ne'

