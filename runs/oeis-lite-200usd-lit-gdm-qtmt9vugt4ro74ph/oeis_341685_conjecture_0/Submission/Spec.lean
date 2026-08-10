import FormalConjectures.Util.ProblemImports

open Nat BigOperators Filter Topology Polynomial

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

lemma padicValNat_factorial_ge (k : ℕ) : padicValNat 3 k.factorial ≥ k / 3 := by
  by_cases h : k < 3
  · -- Case k < 3
    have hk : k / 3 = 0 := Nat.div_eq_of_lt h
    rw [hk]
    exact Nat.zero_le _
  · -- Case k ≥ 3
    push_neg at h
    let b := log 3 k + 1
    have hlog : log 3 k < b := lt_add_one (log 3 k)
    have h_eq : padicValNat 3 k.factorial = ∑ i ∈ Finset.Ico 1 b, k / 3 ^ i := padicValNat_factorial hlog
    rw [h_eq]
    have h1 : 1 ∈ Finset.Ico 1 b := by
      rw [Finset.mem_Ico]
      constructor
      · exact le_refl 1
      · -- we need to show 1 < b = log 3 k + 1
        -- since k ≥ 3, log 3 k ≥ 1
        have hk3 : 3 ≤ k := h
        have h_log_ge : 1 ≤ log 3 k := by
          have h_pow : 3 ^ 1 ≤ k := by simpa using hk3
          exact le_log_of_pow_le (by norm_num) h_pow
        linarith
    have h_le := Finset.single_le_sum (f := fun i => k / 3 ^ i) (hf := fun i _ => Nat.zero_le _) h1
    dsimp at h_le
    exact h_le

lemma norm_factorial_eq (k : ℕ) : ‖(k.factorial : Padic 3)‖ = (3 : ℝ) ^ (- (padicValNat 3 k.factorial : ℤ)) := by
  have h_cast : (k.factorial : Padic 3) = ((k.factorial : ℚ) : Padic 3) := by
    push_cast; rfl
  rw [h_cast]
  rw [Padic.eq_padicNorm]
  have hnz : (k.factorial : ℚ) ≠ 0 := by
    exact_mod_cast factorial_ne_zero k
  rw [padicNorm.eq_zpow_of_nonzero hnz]
  rw [← padicValRat_of_nat]
  push_cast
  rfl

lemma norm_factorial_le (k : ℕ) : ‖(k.factorial : Padic 3)‖ ≤ (3 : ℝ) ^ (- ( (k / 3 : ℕ) : ℤ )) := by
  rw [norm_factorial_eq]
  have h_ge := padicValNat_factorial_ge k
  have h_ge_z : (padicValNat 3 k.factorial : ℤ) ≥ ( (k / 3 : ℕ) : ℤ ) := by
    exact_mod_cast h_ge
  have h_neg : - (padicValNat 3 k.factorial : ℤ) ≤ - ( (k / 3 : ℕ) : ℤ ) := by
    linarith
  exact zpow_le_zpow_right₀ (by norm_num) h_neg

lemma tendsto_div_three : Tendsto (fun k : ℕ => k / 3) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  use 3 * M
  intro k hk
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  linarith

lemma tendsto_upper_bound : Tendsto (fun k : ℕ => (3 : ℝ) ^ (- ( (k / 3 : ℕ) : ℤ ))) atTop (𝓝 0) := by
  have h_pow : Tendsto (fun m : ℕ => ((3 : ℝ)⁻¹) ^ m) atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · norm_num
    · norm_num
  have h_comp := Tendsto.comp h_pow tendsto_div_three
  have h_eq : (fun k : ℕ => (3 : ℝ) ^ (- ( (k / 3 : ℕ) : ℤ ))) = (fun k : ℕ => (3⁻¹ : ℝ) ^ (k / 3)) := by
    funext k
    rw [zpow_neg]
    rw [zpow_natCast]
    rw [inv_pow]
  rw [h_eq]
  exact h_comp

lemma tendsto_norm_factorial_zero : Tendsto (fun k : ℕ => ‖(k.factorial : Padic 3)‖) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_upper_bound
  · intro k
    exact norm_nonneg _
  · intro k
    exact norm_factorial_le k

theorem summable_factorial : Summable (fun k : ℕ => (Nat.factorial k : Padic 3)) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  rw [Nat.cofinite_eq_atTop]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact tendsto_norm_factorial_zero

noncomputable def xi_3 : Padic 3 :=
  tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

def s_nat (n : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), i.factorial

lemma s_nat_succ (n : ℕ) : s_nat (n + 1) = s_nat n + (n + 1).factorial := by
  dsimp [s_nat]
  rw [Finset.sum_range_succ]

lemma s_nat_strictMono : StrictMono s_nat := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [s_nat_succ]
  have h_fact : (n + 1).factorial > 0 := Nat.factorial_pos (n + 1)
  omega

lemma s_nat_injective : Function.Injective s_nat :=
  s_nat_strictMono.injective

def s (n : ℕ) : Padic 3 := (s_nat n : Padic 3)

lemma s_eq_sum (n : ℕ) : s n = ∑ i ∈ Finset.range (n + 1), (i.factorial : Padic 3) := by
  dsimp [s, s_nat]
  push_cast
  rfl

lemma s_injective : Function.Injective s := by
  intro x y h
  have h_cast : ((s_nat x : Padic 3) = (s_nat y : Padic 3)) := h
  rw [Nat.cast_inj] at h_cast
  exact s_nat_injective h_cast

noncomputable local instance : DecidableEq (Padic 3) := Classical.decEq _

lemma eventually_ne_zero (q : (Padic 3)[X]) (hq : q ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, q.eval (s n) ≠ 0 := by
  let R : Finset (Padic 3) := q.roots.toFinset
  let I : Finset ℕ := R.preimage s (fun _ _ _ _ h => s_injective h)
  let N := I.sup id + 1
  use N
  intro n hn
  by_contra hc
  have h_root : s n ∈ R := by
    dsimp [R]
    rw [Multiset.mem_toFinset]
    rw [mem_roots hq]
    exact hc
  have h_mem : n ∈ I := by
    dsimp [I]
    rw [Finset.mem_preimage]
    exact h_root
  have h_le := Finset.le_sup (f := id) h_mem
  dsimp at h_le
  omega

lemma s_succ_sub_one (n : ℕ) (hn : n > 0) : s n = s (n-1) + (n.factorial : Padic 3) := by
  have h_sub : n = (n-1) + 1 := (Nat.sub_add_cancel hn).symm
  have h_eq : s_nat n = s_nat (n-1) + n.factorial := by
    conv_lhs => rw [h_sub]
    conv_rhs => rw [h_sub]
    exact s_nat_succ (n-1)
  dsimp [s]
  rw [h_eq]
  push_cast
  rfl

lemma norm_natCast_le_one (m : ℕ) : ‖(m : Padic 3)‖ ≤ 1 := by
  have h : (m : Padic 3) = ((m : ℤ) : Padic 3) := by push_cast; rfl
  rw [h]
  exact Padic.norm_int_le_one (m : ℤ)

lemma pow_add_divisibility_bound (x y : Padic 3) (hx : ‖x‖ ≤ 2) (hy : ‖y‖ ≤ 2) (n : ℕ) :
    ∃ d : Padic 3, (x + y)^n = x^n + y * d ∧ ‖d‖ ≤ (4 : ℝ)^n := by
  induction n with
  | zero =>
    use 0
    constructor
    · simp
    · simp
  | succ n ih =>
    rcases ih with ⟨dn, hdn, hdn_norm⟩
    use x^n + dn * (x + y)
    constructor
    · rw [pow_succ, hdn]
      ring
    · have h_max : ‖x^n + dn * (x + y)‖ ≤ max ‖x^n‖ ‖dn * (x + y)‖ := by
        exact Padic.nonarchimedean _ _
      have h_xn : ‖x^n‖ ≤ (4 : ℝ)^n := by
        rw [norm_pow]
        have h1 : ‖x‖^n ≤ (2 : ℝ)^n := by gcongr
        have h2 : (2 : ℝ)^n ≤ 4^n := by gcongr; norm_num
        linarith
      have h_dn_xy : ‖dn * (x + y)‖ ≤ (4 : ℝ)^n * 2 := by
        rw [norm_mul]
        have h_xy : ‖x + y‖ ≤ 2 := by
          have h_max_xy := Padic.nonarchimedean x y
          have h_le : max ‖x‖ ‖y‖ ≤ 2 := max_le hx hy
          exact le_trans h_max_xy h_le
        apply mul_le_mul hdn_norm h_xy (norm_nonneg _) (by positivity)
      have h_max_le : max ‖x^n‖ ‖dn * (x + y)‖ ≤ (4 : ℝ)^(n + 1) := by
        apply max_le
        · rw [pow_succ]
          have h_pos : 0 ≤ (4 : ℝ)^n := by positivity
          nlinarith
        · rw [pow_succ]
          have h_pos : 0 ≤ (4 : ℝ)^n := by positivity
          nlinarith
      linarith

lemma eval_add_divisibility_bound (p : (Padic 3)[X]) :
    ∃ C : ℝ, C > 0 ∧ ∀ (x y : Padic 3) (hx : ‖x‖ ≤ 2) (hy : ‖y‖ ≤ 2),
      ∃ d : Padic 3, p.eval (x + y) = p.eval x + y * d ∧ ‖d‖ ≤ C := by
  induction p using Polynomial.induction_on with
  | C a =>
    use 1
    constructor
    · norm_num
    · intro x y _ _
      use 0
      constructor
      · simp
      · norm_num
  | add p g ih_p ih_g =>
    rcases ih_p with ⟨Cp, hCp_pos, hp_bound⟩
    rcases ih_g with ⟨Cg, hCg_pos, hg_bound⟩
    use Cp + Cg
    constructor
    · linarith
    · intro x y hx hy
      rcases hp_bound x y hx hy with ⟨dp, hdp, hdp_norm⟩
      rcases hg_bound x y hx hy with ⟨dg, hdg, hdg_norm⟩
      use dp + dg
      constructor
      · rw [eval_add, eval_add, hdp, hdg]
        ring
      · have h_add := Padic.nonarchimedean dp dg
        have h_max : max ‖dp‖ ‖dg‖ ≤ Cp + Cg := by
          apply max_le
          · linarith
          · linarith
        exact le_trans h_add h_max
  | monomial n a ih =>
    use ‖a‖ * 4^(n + 1) + 1
    constructor
    · positivity
    · intro x y hx hy
      rcases pow_add_divisibility_bound x y hx hy (n + 1) with ⟨d, hd, hd_norm⟩
      use a * d
      constructor
      · simp [hd]
        ring
      · rw [norm_mul]
        have h_d_le : ‖a‖ * ‖d‖ ≤ ‖a‖ * 4^(n+1) := by
          apply mul_le_mul_of_nonneg_left hd_norm (norm_nonneg a)
        linarith

lemma h_bound_step (q : (Padic 3)[X]) (C : ℝ)
    (h_bound_all : ∀ (x y : Padic 3) (hx : ‖x‖ ≤ 2) (hy : ‖y‖ ≤ 2), ∃ (d : Padic 3), q.eval (x + y) = q.eval x + y * d ∧ ‖d‖ ≤ C) :
    ∀ n > 0, ∃ d : Padic 3, q.eval (s n) = q.eval (s (n-1)) + (n.factorial : Padic 3) * d ∧ ‖d‖ ≤ C := by
  intro n hn
  have h_s := s_succ_sub_one n hn
  have hx_le : ‖s (n-1)‖ ≤ 2 := by
    have h_le : ‖s (n-1)‖ ≤ 1 := norm_natCast_le_one (s_nat (n-1))
    linarith
  have hy_le : ‖(n.factorial : Padic 3)‖ ≤ 2 := by
    have h_le : ‖(n.factorial : Padic 3)‖ ≤ 1 := norm_natCast_le_one (n.factorial)
    linarith
  rcases h_bound_all (s (n-1)) (n.factorial : Padic 3) hx_le hy_le with ⟨d, hd1, hd2⟩
  use d
  constructor
  · rw [← h_s] at hd1
    exact hd1
  · exact hd2

lemma tendsto_s : Tendsto s atTop (𝓝 xi_3) := by
  have h_sum := summable_factorial.hasSum
  have h_tendsto := h_sum.tendsto_sum_nat
  have h_shift : Tendsto (fun n ↦ n + 1) atTop atTop := tendsto_add_atTop_nat 1
  have h_comp := Tendsto.comp h_tendsto h_shift
  have h_eq : s = fun n ↦ ∑ i ∈ Finset.range (n + 1), (i.factorial : Padic 3) := by
    funext n
    exact s_eq_sum n
  rw [h_eq]
  exact h_comp

lemma norm_add_eq_max_of_norm_ne {x y : Padic 3} (h : ‖x‖ ≠ ‖y‖) : ‖x + y‖ = max ‖x‖ ‖y‖ := by
  have h_dist : dist (x + y) 0 = max (dist (x + y) x) (dist x 0) := by
    apply IsUltrametricDist.dist_eq_max_of_dist_ne_dist
    simp [h.symm]
  simp only [dist_eq_norm_sub, sub_zero, add_sub_cancel_left] at h_dist
  rw [h_dist]
  exact max_comm ‖y‖ ‖x‖

lemma norm_eval_s_constant_simple (q : (Padic 3)[X]) (C : ℝ) (N : ℕ) (_h_eval : q.eval (s N) ≠ 0)
    (h_bound : ∀ n > N, ∃ d : Padic 3, q.eval (s n) = q.eval (s (n-1)) + (n.factorial : Padic 3) * d ∧ ‖d‖ ≤ C)
    (N_1 : ℕ) (hN_ge : N ≥ N_1) (h_limit : ∀ n ≥ N_1, ‖(n.factorial : Padic 3)‖ * C < ‖q.eval (s N)‖) :
    ∀ n ≥ N, ‖q.eval (s n)‖ = ‖q.eval (s N)‖ := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn' ih =>
    have h_succ_gt : n + 1 > N := by omega
    rcases h_bound (n + 1) h_succ_gt with ⟨d, h_eq, hd_norm⟩
    have h_succ_sub : n + 1 - 1 = n := by omega
    rw [h_succ_sub] at h_eq
    have h_norm_eq : ‖q.eval (s (n + 1))‖ = ‖q.eval (s n) + ((n + 1).factorial : Padic 3) * d‖ := by
      rw [h_eq]
    have h_lt : ‖((n + 1).factorial : Padic 3) * d‖ < ‖q.eval (s n)‖ := by
      rw [norm_mul]
      rw [ih]
      have h_ge : n + 1 ≥ N_1 := by omega
      have h_lim := h_limit (n + 1) h_ge
      have h_mul_le : ‖((n + 1).factorial : Padic 3)‖ * ‖d‖ ≤ ‖((n + 1).factorial : Padic 3)‖ * C := by
        apply mul_le_mul_of_nonneg_left hd_norm (norm_nonneg _)
      linarith
    have h_ne : ‖q.eval (s n)‖ ≠ ‖((n + 1).factorial : Padic 3) * d‖ := ne_of_gt h_lt
    have h_ult := norm_add_eq_max_of_norm_ne h_ne
    rw [h_norm_eq, h_ult]
    rw [max_eq_left (le_of_lt h_lt)]
    exact ih

lemma factorial_limit_step (C : ℝ) (hC : C > 0) (V : ℝ) (hV : V > 0) :
    ∃ N_1 : ℕ, ∀ n ≥ N_1, ‖(n.factorial : Padic 3)‖ * C < V := by
  have h_lim : Tendsto (fun n : ℕ ↦ ‖((n.factorial : ℕ) : Padic 3)‖ * C) atTop (𝓝 0) := by
    have h_mul := Tendsto.mul_const C tendsto_norm_factorial_zero
    rw [zero_mul] at h_mul
    exact h_mul
  rw [Metric.tendsto_atTop] at h_lim
  rcases h_lim V hV with ⟨N_1, hN1⟩
  use N_1
  intro n hn
  have h_dist := hN1 n hn
  rw [Real.dist_0_eq_abs] at h_dist
  have h_nonneg : ‖((n.factorial : ℕ) : Padic 3)‖ * C ≥ 0 := by
    have h1 : ‖((n.factorial : ℕ) : Padic 3)‖ ≥ 0 := norm_nonneg _
    have h2 : C ≥ 0 := le_of_lt hC
    positivity
  rw [abs_of_nonneg h_nonneg] at h_dist
  exact h_dist

lemma eventually_constant_zero {f : ℕ → ℝ} {c : ℝ} {N : ℕ} (hc : ∀ n ≥ N, f n = c) (hl : Tendsto f atTop (𝓝 0)) : c = 0 := by
  have hl' : Tendsto (fun n : ℕ ↦ c) atTop (𝓝 0) := by
    apply Tendsto.congr' _ hl
    have h_ev := eventually_ge_atTop N
    filter_upwards [h_ev] with n hn
    exact hc n hn
  have hc_lim : Tendsto (fun n : ℕ ↦ c) atTop (𝓝 c) := tendsto_const_nhds
  exact tendsto_nhds_unique hc_lim hl'

lemma tendsto_eval (q : (Padic 3)[X]) : Tendsto (fun n ↦ q.eval (s n)) atTop (𝓝 (q.eval xi_3)) := by
  have hc : Continuous (fun x ↦ q.eval x) := q.continuous
  exact (hc.tendsto xi_3).comp tendsto_s

lemma norm_factorial_mono {n N : ℕ} (h : N ≤ n) : ‖(n.factorial : Padic 3)‖ ≤ ‖(N.factorial : Padic 3)‖ := by
  rcases Nat.factorial_dvd_factorial h with ⟨k, hk⟩
  have h_cast : (n.factorial : Padic 3) = (N.factorial : Padic 3) * (k : Padic 3) := by
    rw [hk]
    push_cast
    rfl
  rw [h_cast, norm_mul]
  have h_le : ‖(k : Padic 3)‖ ≤ 1 := norm_natCast_le_one k
  have h_norm_nonneg : ‖(N.factorial : Padic 3)‖ ≥ 0 := norm_nonneg _
  nlinarith

theorem oeis_341685_conjecture_0 : ¬ IsAlgebraic ℚ (xi_3) := by
  intro h
  rcases h with ⟨p, hp1, hp2⟩
  let q := p.map (algebraMap ℚ (Padic 3))
  have hq_eval : q.eval xi_3 = 0 := by
    rw [aeval_def, ← eval_map] at hp2
    exact hp2
  have hq : q ≠ 0 := by
    rw [ne_eq, Polynomial.map_eq_zero_iff]
    · exact hp1
    · exact FaithfulSMul.algebraMap_injective ℚ (Padic 3)
  rcases eventually_ne_zero q hq with ⟨n_0_start, hn0_start⟩
  rcases eval_add_divisibility_bound q with ⟨C, hC_pos, h_bound_all⟩
  have h_bound : ∀ n > 0, ∃ d : Padic 3, q.eval (s n) = q.eval (s (n-1)) + (n.factorial : Padic 3) * d ∧ ‖d‖ ≤ C :=
    h_bound_step q C h_bound_all

  have hn0_start_ne : q.eval (s n_0_start) ≠ 0 := hn0_start n_0_start (le_refl n_0_start)
  let V_init_raw := ‖q.eval (s n_0_start)‖
  have hV_init_raw_pos : V_init_raw > 0 := norm_pos_iff.mpr hn0_start_ne
  rcases factorial_limit_step C hC_pos V_init_raw hV_init_raw_pos with ⟨N_1, hN1⟩

  let n_0_raw_init_init := max n_0_start N_1
  have hn0_raw_init_init : ∀ n ≥ n_0_raw_init_init, q.eval (s n) ≠ 0 := by
    intro n hn
    apply hn0_start
    have h_le : n_0_start ≤ n_0_raw_init_init := le_max_left _ _
    omega

  have hn0_raw_init_init_ne : q.eval (s n_0_raw_init_init) ≠ 0 := hn0_raw_init_init n_0_raw_init_init (le_refl n_0_raw_init_init)
  let V_init := ‖q.eval (s n_0_raw_init_init)‖
  have hV_init_pos : V_init > 0 := norm_pos_iff.mpr hn0_raw_init_init_ne

  let n_0_raw_init := n_0_raw_init_init + 1
  have hn0_raw_init_ne : q.eval (s n_0_raw_init) ≠ 0 := by
    apply hn0_raw_init_init
    omega
  let V_raw_init := ‖q.eval (s n_0_raw_init)‖
  have hV_raw_init_pos : V_raw_init > 0 := norm_pos_iff.mpr hn0_raw_init_ne
  rcases factorial_limit_step C hC_pos V_raw_init hV_raw_init_pos with ⟨N_2, hN2⟩

  let n_0_raw := max n_0_raw_init N_2 + 1
  have hn0_raw_ne : q.eval (s n_0_raw) ≠ 0 := by
    apply hn0_raw_init_init
    have h1 : n_0_raw_init_init + 1 ≤ n_0_raw_init := by omega
    have h2 : n_0_raw_init ≤ n_0_raw := by omega
    omega
  let V_raw := ‖q.eval (s n_0_raw)‖
  have hV_raw_pos : V_raw > 0 := norm_pos_iff.mpr hn0_raw_ne
  rcases factorial_limit_step C hC_pos V_raw hV_raw_pos with ⟨N_3, hN3⟩

  let n_0 := max n_0_raw N_3 + 1
  have hn0_ne : q.eval (s n_0) ≠ 0 := by
    apply hn0_raw_init_init
    have h1 : n_0_raw_init_init + 1 ≤ n_0_raw_init := by omega
    have h2 : n_0_raw_init ≤ n_0_raw := by omega
    have h3 : n_0_raw ≤ n_0 := by omega
    omega
  let V_0 := ‖q.eval (s n_0)‖
  have hV0_pos : V_0 > 0 := norm_pos_iff.mpr hn0_ne

  have h_exists_N : ∃ N ≥ n_0, ‖(N.factorial : Padic 3)‖ * C < ‖q.eval (s N)‖ := by
    by_contra h_no
    push_neg at h_no
    have h_all : ∀ N ≥ n_0, ‖q.eval (s N)‖ ≤ ‖(N.factorial : Padic 3)‖ * C := h_no

    have h_ge_raw_init_raw : V_raw_init ≤ V_raw := by
      by_contra h_lt_init
      push_neg at h_lt_init
      have h_gt : n_0_raw > max n_0_raw_init N_2 := by omega
      have h_exists_P : ∃ m, m > max n_0_raw_init N_2 ∧ ‖q.eval (s m)‖ < V_raw_init := ⟨n_0_raw, h_gt, h_lt_init⟩
      let M := Nat.find h_exists_P
      have hM_prop := Nat.find_spec h_exists_P
      have hM_gt : M > max n_0_raw_init N_2 := hM_prop.1
      have hM_lt : ‖q.eval (s M)‖ < V_raw_init := hM_prop.2
      have hM_le : M ≤ n_0_raw := Nat.find_min' h_exists_P ⟨h_gt, h_lt_init⟩
      have hM_sub : ‖q.eval (s (M - 1))‖ ≥ V_raw_init := by
        by_cases h_sub : M - 1 = max n_0_raw_init N_2
        · rw [h_sub]
          by_cases h_max : N_2 ≤ n_0_raw_init
          · have h_eq : max n_0_raw_init N_2 = n_0_raw_init := max_eq_left h_max
            rw [h_eq]
          · push_neg at h_max
            have h_eq : max n_0_raw_init N_2 = N_2 := max_eq_right (by omega)
            rw [h_eq]
            by_contra h_lt
            push_neg at h_lt
            have h_exists_alt : ∃ m, m > n_0_raw_init ∧ ‖q.eval (s m)‖ < V_raw_init := ⟨N_2, ⟨by omega, h_lt⟩⟩
            let M_alt := Nat.find h_exists_alt
            have hM_alt_prop := Nat.find_spec h_exists_alt
            have hM_alt_gt : M_alt > n_0_raw_init := hM_alt_prop.1
            have hM_alt_lt : ‖q.eval (s M_alt)‖ < V_raw_init := hM_alt_prop.2
            have hM_alt_le : M_alt ≤ N_2 := Nat.find_min' h_exists_alt ⟨by omega, h_lt⟩
            have hM_alt_sub : ‖q.eval (s (M_alt - 1))‖ ≥ V_raw_init := by
              by_cases h_sub' : M_alt - 1 = n_0_raw_init
              · rw [h_sub']
              · have h_sub_gt : M_alt - 1 > n_0_raw_init := by omega
                have h_sub_lt : M_alt - 1 < M_alt := by omega
                have h_not_P := Nat.find_min h_exists_alt h_sub_lt
                push_neg at h_not_P
                exact h_not_P h_sub_gt
            have h_diff_le' : ‖q.eval (s M_alt) - q.eval (s (M_alt - 1))‖ ≤ ‖(M_alt.factorial : Padic 3)‖ * C := by
              have h_succ_gt : M_alt > 0 := by omega
              rcases h_bound M_alt h_succ_gt with ⟨d', h_eq', hd_norm'⟩
              rw [h_eq']
              have h_simp : q.eval (s (M_alt - 1)) + (M_alt.factorial : Padic 3) * d' - q.eval (s (M_alt - 1)) = (M_alt.factorial : Padic 3) * d' := by ring
              rw [h_simp]
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left hd_norm' (norm_nonneg _)
            have h_diff_eq' : ‖q.eval (s M_alt) - q.eval (s (M_alt - 1))‖ = ‖q.eval (s (M_alt - 1))‖ := by
              have h_ne : ‖q.eval (s M_alt)‖ ≠ ‖- q.eval (s (M_alt - 1))‖ := by
                rw [norm_neg]
                linarith
              have h_add := norm_add_eq_max_of_norm_ne h_ne
              have h_sub_eq' : q.eval (s M_alt) - q.eval (s (M_alt - 1)) = q.eval (s M_alt) + - q.eval (s (M_alt - 1)) := by ring
              rw [h_sub_eq', h_add]
              rw [norm_neg]
              apply max_eq_right
              linarith
            have h_M_alt_ge_N1 : M_alt ≥ N_1 := by
              have h_le : N_1 ≤ n_0_raw_init_init := le_max_right _ _
              omega
            have h_fact_lt' := hN1 M_alt h_M_alt_ge_N1
            have h_ge_raw_init_raw_init : V_init ≤ V_raw_init := by
              by_contra h_lt_init_init
              push_neg at h_lt_init_init
              have h_exists_P_init : ∃ m, m > n_0_raw_init_init ∧ ‖q.eval (s m)‖ < V_init := ⟨n_0_raw_init, by omega, h_lt_init_init⟩
              let M_init := Nat.find h_exists_P_init
              have hM_init_prop := Nat.find_spec h_exists_P_init
              have hM_init_gt : M_init > n_0_raw_init_init := hM_init_prop.1
              have hM_init_lt : ‖q.eval (s M_init)‖ < V_init := hM_init_prop.2
              have hM_init_le : M_init ≤ n_0_raw_init := Nat.find_min' h_exists_P_init ⟨by omega, h_lt_init_init⟩
              have hM_init_sub : ‖q.eval (s (M_init - 1))‖ ≥ V_init := by
                by_cases h_sub : M_init - 1 = n_0_raw_init_init
                · rw [h_sub]
                · have h_sub_gt : M_init - 1 > n_0_raw_init_init := by omega
                  have h_sub_lt : M_init - 1 < M_init := by omega
                  have h_not_P := Nat.find_min h_exists_P_init h_sub_lt
                  push_neg at h_not_P
                  exact h_not_P h_sub_gt
              have h_diff_le_init : ‖q.eval (s M_init) - q.eval (s (M_init - 1))‖ ≤ ‖(M_init.factorial : Padic 3)‖ * C := by
                have h_succ_gt : M_init > 0 := by omega
                rcases h_bound M_init h_succ_gt with ⟨d, h_eq, hd_norm⟩
                rw [h_eq]
                have h_simp : q.eval (s (M_init - 1)) + (M_init.factorial : Padic 3) * d - q.eval (s (M_init - 1)) = (M_init.factorial : Padic 3) * d := by ring
                rw [h_simp]
                rw [norm_mul]
                exact mul_le_mul_of_nonneg_left hd_norm (norm_nonneg _)
              have h_diff_eq_init : ‖q.eval (s M_init) - q.eval (s (M_init - 1))‖ = ‖q.eval (s (M_init - 1))‖ := by
                have h_ne : ‖q.eval (s M_init)‖ ≠ ‖- q.eval (s (M_init - 1))‖ := by
                  rw [norm_neg]
                  linarith
                have h_add := norm_add_eq_max_of_norm_ne h_ne
                have h_sub_eq : q.eval (s M_init) - q.eval (s (M_init - 1)) = q.eval (s M_init) + - q.eval (s (M_init - 1)) := by ring
                rw [h_sub_eq, h_add]
                rw [norm_neg]
                apply max_eq_right
                linarith
              have h_fact_lt_init : ‖(M_init.factorial : Padic 3)‖ * C < V_init := by
                have h_ge : M_init ≥ n_0_raw_init_init + 1 := by omega
                have h_mono := norm_factorial_mono h_ge
                have h_mul_le : ‖(M_init.factorial : Padic 3)‖ * C ≤ ‖((n_0_raw_init_init + 1).factorial : Padic 3)‖ * C := mul_le_mul_of_nonneg_right h_mono (by linarith)
                have h_ge2 : n_0_raw_init_init + 1 ≥ N_1 := by
                  have h_le : N_1 ≤ n_0_raw_init_init := le_max_right _ _
                  omega
                have h_lt := hN1 (n_0_raw_init_init + 1) h_ge2
                linarith
              linarith
            linarith
        · have h_sub_gt : M - 1 > max n_0_raw_init N_2 := by omega
          have h_sub_lt : M - 1 < M := by omega
          have h_not_P := Nat.find_min h_exists_P h_sub_lt
          push_neg at h_not_P
          exact h_not_P h_sub_gt
      have h_diff_le : ‖q.eval (s M) - q.eval (s (M - 1))‖ ≤ ‖(M.factorial : Padic 3)‖ * C := by
        have h_succ_gt : M > 0 := by omega
        rcases h_bound M h_succ_gt with ⟨d, h_eq, hd_norm⟩
        rw [h_eq]
        have h_simp : q.eval (s (M - 1)) + (M.factorial : Padic 3) * d - q.eval (s (M - 1)) = (M.factorial : Padic 3) * d := by ring
        rw [h_simp]
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hd_norm (norm_nonneg _)
      have h_diff_eq' : ‖q.eval (s M) - q.eval (s (M - 1))‖ = ‖q.eval (s (M - 1))‖ := by
        have h_ne : ‖q.eval (s M)‖ ≠ ‖- q.eval (s (M - 1))‖ := by
          rw [norm_neg]
          linarith
        have h_add := norm_add_eq_max_of_norm_ne h_ne
        have h_sub_eq' : q.eval (s M) - q.eval (s (M - 1)) = q.eval (s M) + - q.eval (s (M - 1)) := by ring
        rw [h_sub_eq', h_add]
        rw [norm_neg]
        apply max_eq_right
        linarith
      have h_M_ge_N2 : M ≥ N_2 := by
        have h_le : N_2 ≤ max n_0_raw_init N_2 := le_max_right _ _
        omega
      have h_fact_lt := hN2 M h_M_ge_N2
      linarith

    have h_ge_raw : V_raw ≤ V_0 := by
      by_contra h_lt_init
      push_neg at h_lt_init
      have h_gt : n_0 > max n_0_raw N_3 := by omega
      have h_exists_P : ∃ m, m > max n_0_raw N_3 ∧ ‖q.eval (s m)‖ < V_raw := ⟨n_0, h_gt, h_lt_init⟩
      let M := Nat.find h_exists_P
      have hM_prop := Nat.find_spec h_exists_P
      have hM_gt : M > max n_0_raw N_3 := hM_prop.1
      have hM_lt : ‖q.eval (s M)‖ < V_raw := hM_prop.2
      have hM_le : M ≤ n_0 := Nat.find_min' h_exists_P ⟨h_gt, h_lt_init⟩
      have hM_sub : ‖q.eval (s (M - 1))‖ ≥ V_raw := by
        by_cases h_sub : M - 1 = max n_0_raw N_3
        · rw [h_sub]
          by_cases h_max : N_3 ≤ n_0_raw
          · have h_eq : max n_0_raw N_3 = n_0_raw := max_eq_left h_max
            rw [h_eq]
          · push_neg at h_max
            have h_eq : max n_0_raw N_3 = N_3 := max_eq_right (by omega)
            rw [h_eq]
            by_contra h_lt
            push_neg at h_lt
            have h_exists_alt : ∃ m, m > n_0_raw ∧ ‖q.eval (s m)‖ < V_raw := ⟨N_3, ⟨by omega, h_lt⟩⟩
            let M_alt := Nat.find h_exists_alt
            have hM_alt_prop := Nat.find_spec h_exists_alt
            have hM_alt_gt : M_alt > n_0_raw := hM_alt_prop.1
            have hM_alt_lt : ‖q.eval (s M_alt)‖ < V_raw := hM_alt_prop.2
            have hM_alt_le : M_alt ≤ N_3 := Nat.find_min' h_exists_alt ⟨by omega, h_lt⟩
            have hM_alt_sub : ‖q.eval (s (M_alt - 1))‖ ≥ V_raw := by
              by_cases h_sub' : M_alt - 1 = n_0_raw
              · rw [h_sub']
              · have h_sub_gt : M_alt - 1 > n_0_raw := by omega
                have h_sub_lt : M_alt - 1 < M_alt := by omega
                have h_not_P := Nat.find_min h_exists_alt h_sub_lt
                push_neg at h_not_P
                exact h_not_P h_sub_gt
            have h_diff_le' : ‖q.eval (s M_alt) - q.eval (s (M_alt - 1))‖ ≤ ‖(M_alt.factorial : Padic 3)‖ * C := by
              have h_succ_gt : M_alt > 0 := by omega
              rcases h_bound M_alt h_succ_gt with ⟨d', h_eq', hd_norm'⟩
              rw [h_eq']
              have h_simp : q.eval (s (M_alt - 1)) + (M_alt.factorial : Padic 3) * d' - q.eval (s (M_alt - 1)) = (M_alt.factorial : Padic 3) * d' := by ring
              rw [h_simp]
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left hd_norm' (norm_nonneg _)
            have h_diff_eq' : ‖q.eval (s M_alt) - q.eval (s (M_alt - 1))‖ = ‖q.eval (s (M_alt - 1))‖ := by
              have h_ne : ‖q.eval (s M_alt)‖ ≠ ‖- q.eval (s (M_alt - 1))‖ := by
                rw [norm_neg]
                linarith
              have h_add := norm_add_eq_max_of_norm_ne h_ne
              have h_sub_eq' : q.eval (s M_alt) - q.eval (s (M_alt - 1)) = q.eval (s M_alt) + - q.eval (s (M_alt - 1)) := by ring
              rw [h_sub_eq', h_add]
              rw [norm_neg]
              apply max_eq_right
              linarith
            have h_M_alt_ge_N2 : M_alt ≥ N_2 := by
              have h_le : N_2 ≤ max n_0_raw_init N_2 := le_max_right _ _
              omega
            have h_fact_lt' := hN2 M_alt h_M_alt_ge_N2
            linarith
        · have h_sub_gt : M - 1 > max n_0_raw N_3 := by omega
          have h_sub_lt : M - 1 < M := by omega
          have h_not_P := Nat.find_min h_exists_P h_sub_lt
          push_neg at h_not_P
          exact h_not_P h_sub_gt
      have h_diff_le : ‖q.eval (s M) - q.eval (s (M - 1))‖ ≤ ‖(M.factorial : Padic 3)‖ * C := by
        have h_succ_gt : M > 0 := by omega
        rcases h_bound M h_succ_gt with ⟨d, h_eq, hd_norm⟩
        rw [h_eq]
        have h_simp : q.eval (s (M - 1)) + (M.factorial : Padic 3) * d - q.eval (s (M - 1)) = (M.factorial : Padic 3) * d := by ring
        rw [h_simp]
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hd_norm (norm_nonneg _)
      have h_diff_eq' : ‖q.eval (s M) - q.eval (s (M - 1))‖ = ‖q.eval (s (M - 1))‖ := by
        have h_ne : ‖q.eval (s M)‖ ≠ ‖- q.eval (s (M - 1))‖ := by
          rw [norm_neg]
          linarith
        have h_add := norm_add_eq_max_of_norm_ne h_ne
        have h_sub_eq' : q.eval (s M) - q.eval (s (M - 1)) = q.eval (s M) + - q.eval (s (M - 1)) := by ring
        rw [h_sub_eq', h_add]
        rw [norm_neg]
        apply max_eq_right
        linarith
      have h_M_ge_N3 : M ≥ N_3 := by
        have h_le : N_3 ≤ max n_0_raw N_3 := le_max_right _ _
        omega
      have h_fact_lt := hN3 M h_M_ge_N3
      linarith

    have h_n0_le : V_0 ≤ ‖(n_0.factorial : Padic 3)‖ * C := h_all n_0 (le_refl n_0)
    have h_limit_n0 := hN3 n_0 (by omega)
    linarith

  rcases h_exists_N with ⟨N, hN_ge, h_lt_N⟩
  have hn_ne : q.eval (s N) ≠ 0 := by
    apply hn0_raw_init_init
    have h1 : n_0_raw_init_init + 1 ≤ n_0_raw_init := by omega
    have h2 : n_0_raw_init ≤ n_0_raw := by omega
    have h3 : n_0_raw ≤ n_0 := by omega
    have h4 : n_0 ≤ N := hN_ge
    omega
  have h_bound_N : ∀ n > N, ∃ d : Padic 3, q.eval (s n) = q.eval (s (n-1)) + (n.factorial : Padic 3) * d ∧ ‖d‖ ≤ C := by
    intro n hn
    have hn_pos : n > 0 := by omega
    exact h_bound n hn_pos
  have h_const : ∀ n ≥ N, ‖q.eval (s n)‖ = ‖q.eval (s N)‖ := by
    apply norm_eval_s_constant_simple q C N hn_ne h_bound_N N (le_refl N)
    intro n hn
    have h_le_N := norm_factorial_mono hn
    have h_mul_le : ‖(n.factorial : Padic 3)‖ * C ≤ ‖(N.factorial : Padic 3)‖ * C :=
      mul_le_mul_of_nonneg_right h_le_N (le_of_lt hC_pos)
    linarith

  have h_lim_zero : Tendsto (fun n ↦ ‖q.eval (s n)‖) atTop (𝓝 0) := by
    have h_lim := tendsto_eval q
    rw [hq_eval] at h_lim
    rw [tendsto_zero_iff_norm_tendsto_zero] at h_lim
    exact h_lim
  have h_const_val : ‖q.eval (s N)‖ = 0 :=
    eventually_constant_zero h_const h_lim_zero
  have h_VN_pos : ‖q.eval (s N)‖ > 0 := norm_pos_iff.mpr hn_ne
  linarith
