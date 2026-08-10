import FormalConjectures.Util.ProblemImports

open Nat BigOperators Filter Topology Algebra Polynomial

instance : Fact (Nat.Prime 3) := by
  constructor
  norm_num

def approx_3_adic_sum_factorial (m : ℕ) : ℕ :=
  let p := 3
  if m = 0 then 0
  else
    let upper_k := p * m
    (Finset.range upper_k).sum Nat.factorial % (p ^ m)

noncomputable def a (n : ℕ) : ℕ :=
  let p := 3
  let X_n_plus_1 := approx_3_adic_sum_factorial (n + 1)
  let X_n := approx_3_adic_sum_factorial n
  (X_n_plus_1 - X_n) / (p ^ n)

lemma pow_prime_dvd_factorial_mul_self (p : ℕ) [hp : Fact p.Prime] (r : ℕ) : p ^ r ∣ (p * r).factorial := by
  induction r with
  | zero =>
    simp
  | succ r ih =>
    have h1 : p * r + p = p * (r + 1) := by ring
    rw [← h1]
    have h2 : (p * r).factorial * p.factorial ∣ (p * r + p).factorial := factorial_mul_factorial_dvd_factorial_add (p * r) p
    have h3 : p ∣ p.factorial := by
      cases p with
      | zero =>
        exfalso
        exact Nat.Prime.ne_zero hp.out rfl
      | succ p =>
        rw [factorial_succ]
        exact ⟨p.factorial, rfl⟩
    have h4 : p ^ r * p ∣ (p * r).factorial * p.factorial := mul_dvd_mul ih h3
    rw [← pow_succ] at h4
    exact dvd_trans h4 h2

lemma pow_prime_dvd_factorial_of_mul_le (p : ℕ) [hp : Fact p.Prime] (r : ℕ) (n : ℕ) (h : p * r ≤ n) : p ^ r ∣ n.factorial := by
  exact dvd_trans (pow_prime_dvd_factorial_mul_self p r) (factorial_dvd_factorial h)

lemma norm_factorial_le (r : ℕ) (x : ℕ) (h : 3 * r ≤ x) : ‖(x.factorial : Padic 3)‖ ≤ (3 : ℝ) ^ (-(r : ℤ)) := by
  have h_dvd : 3 ^ r ∣ x.factorial := pow_prime_dvd_factorial_of_mul_le 3 r x h
  have h_dvd_int : (3 ^ r : ℤ) ∣ (x.factorial : ℤ) := by
    exact_mod_cast h_dvd
  have h_norm : ‖((x.factorial : ℤ) : Padic 3)‖ ≤ (3 : ℝ) ^ (-(r : ℤ)) ↔ (3 ^ r : ℤ) ∣ (x.factorial : ℤ) := by
    exact_mod_cast Padic.norm_int_le_pow_iff_dvd (p := 3) (x.factorial : ℤ) r
  have h_cast : (x.factorial : Padic 3) = ((x.factorial : ℤ) : Padic 3) := by norm_cast
  rw [h_cast, h_norm]
  exact h_dvd_int

lemma tendsto_norm_factorial_zero : Tendsto (fun x : ℕ => ‖(x.factorial : Padic 3)‖) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (1 / 3 : ℝ) ^ r < ε := by
    apply exists_pow_lt_of_lt_one hε
    norm_num
  use 3 * r
  intro x hx
  rw [_root_.dist_zero_right]
  have h_lt : (3 : ℝ) ^ (-(r : ℤ)) = (1 / 3 : ℝ) ^ r := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    norm_num
  have h_le := norm_factorial_le r x hx
  rw [h_lt] at h_le
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact lt_of_le_of_lt h_le hr

theorem summable_factorial : Summable (fun k : ℕ => (Nat.factorial k : Padic 3)) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  rw [Nat.cofinite_eq_atTop]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact tendsto_norm_factorial_zero

noncomputable def xi_3 : Padic 3 :=
  tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

noncomputable def S (n : ℕ) : Padic 3 :=
  (Finset.range n).sum (fun k : ℕ => (Nat.factorial k : Padic 3))

lemma tendsto_S : Tendsto S atTop (nhds xi_3) := by
  have h_sum : HasSum (fun k : ℕ => (Nat.factorial k : Padic 3)) xi_3 := by
    exact summable_factorial.hasSum
  exact h_sum.tendsto_sum_nat

lemma S_succ (n : ℕ) : S (n + 1) = (n.factorial : Padic 3) + S n := by
  dsimp [S]
  rw [Finset.sum_range_succ, add_comm]

lemma S_eq_algebraMap (n : ℕ) : S n = algebraMap ℚ (Padic 3) (∑ k ∈ Finset.range n, (Nat.factorial k : ℚ)) := by
  dsimp [S]
  simp

lemma S_mono : StrictMono (fun n : ℕ => (∑ k ∈ Finset.range n, (Nat.factorial k : ℚ))) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [Finset.sum_range_succ]
  simp only [lt_add_iff_pos_right]
  positivity

lemma S_injective : Function.Injective S := by
  have h_inj : Function.Injective (algebraMap ℚ (Padic 3)) := FaithfulSMul.algebraMap_injective ℚ (Padic 3)
  have h_mono_inj := S_mono.injective
  intro x y h
  rw [S_eq_algebraMap x, S_eq_algebraMap y] at h
  have h2 := h_inj h
  exact h_mono_inj h2

lemma exists_ne_zero_of_injective {K : Type*} [Field K] [DecidableEq K] (p : K[X]) (hp : p ≠ 0) {f : ℕ → K} (hf : Function.Injective f) : ∃ n, p.eval (f n) ≠ 0 := by
  by_contra! h
  have h_roots : ∀ n, f n ∈ p.roots := by
    intro n
    rw [mem_roots hp]
    exact h n
  let s := (Finset.range (p.natDegree + 2)).map ⟨f, hf⟩
  have h_sub : s ⊆ p.roots.toFinset := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨y, _, rfl⟩
    rw [Multiset.mem_toFinset]
    exact h_roots y
  have h_card := Finset.card_le_card h_sub
  rw [Finset.card_map, Finset.card_range] at h_card
  have h_roots_card := p.roots.toFinset_card_le.trans p.card_roots'
  linarith

lemma exists_S_ne_zero_ge (p : (Padic 3)[X]) (hp : p ≠ 0) (M : ℕ) : ∃ n ≥ M, p.eval (S n) ≠ 0 := by
  classical
  let g : ℕ → Padic 3 := fun n => S (n + M)
  have hg : Function.Injective g := by
    intro x y h
    have h_inj := S_injective h
    exact Nat.add_right_cancel h_inj
  obtain ⟨n, hn⟩ := exists_ne_zero_of_injective p hp hg
  use n + M
  refine ⟨by linarith, hn⟩

lemma norm_add_eq_left_of_norm_lt {S : Type*} [NormedAddCommGroup S] [IsUltrametricDist S] {x y : S} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  have hne : ‖x‖ ≠ ‖y‖ := ne_of_gt h
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne]
  exact max_eq_left (le_of_lt h)

lemma norm_sub_le_of_diff_lt {S : Type*} [NormedAddCommGroup S] [IsUltrametricDist S] {x : ℕ → S} {K : ℕ} {V : ℝ} (hV : V > 0) (h_diff : ∀ n ≥ K, ‖x (n + 1) - x n‖ < V) :
  ∀ a ≥ K, ∀ b ≥ a, ‖x b - x a‖ < V := by
  intro a ha b hab
  induction b, hab using Nat.le_induction with
  | base =>
    simp only [sub_self, _root_.norm_zero]
    exact hV
  | succ m hm ih =>
    have h_eq : x (m + 1) - x a = (x m - x a) + (x (m + 1) - x m) := by abel
    rw [h_eq]
    have h1 : ‖x (m + 1) - x m‖ < V := h_diff m (by linarith)
    have h2 : ‖x m - x a‖ < V := ih
    have h_max := IsUltrametricDist.norm_add_le_max (x m - x a) (x (m + 1) - x m)
    exact lt_of_le_of_lt h_max (max_lt h2 h1)

lemma norm_eq_of_diff_lt {S : Type*} [NormedAddCommGroup S] [IsUltrametricDist S] {x : ℕ → S} {K : ℕ} {V : ℝ} (hV : V > 0) (h_diff : ∀ n ≥ K, ‖x (n + 1) - x n‖ < V) :
  ∀ a ≥ K, ∀ b ≥ K, ‖x a‖ ≥ V → ‖x b‖ = ‖x a‖ := by
  intro a ha b hb h_ge
  rcases le_total a b with hab | hab
  · have h_lt : ‖x b - x a‖ < ‖x a‖ := by
      have h_sub := norm_sub_le_of_diff_lt hV h_diff a ha b hab
      exact lt_of_lt_of_le h_sub h_ge
    have h_eq : x b = x a + (x b - x a) := by abel
    rw [h_eq]
    exact norm_add_eq_left_of_norm_lt h_lt
  · have h_lt : ‖x a - x b‖ < ‖x a‖ := by
      have h_sub := norm_sub_le_of_diff_lt hV h_diff b hb a hab
      exact lt_of_lt_of_le h_sub h_ge
    have h_eq : x b = x a + (x b - x a) := by abel
    rw [h_eq]
    have h_lt' : ‖x b - x a‖ < ‖x a‖ := by
      rw [norm_sub_rev]
      exact h_lt
    exact norm_add_eq_left_of_norm_lt h_lt'

lemma norm_add_sum_eq_first {S : Type*} [NormedAddCommGroup S] [IsUltrametricDist S] {A : S} {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → S) (h : ∀ i ∈ s, ‖f i‖ < ‖A‖) : ‖A + ∑ i ∈ s, f i‖ = ‖A‖ := by
  induction s using Finset.induction with
  | empty =>
    simp
  | insert hx ht h_not_in ih =>
    simp only [Finset.mem_insert] at h
    have h_x := h _ (Or.inl rfl)
    have h_t : ∀ i ∈ ht, ‖f i‖ < ‖A‖ := fun i hi => h i (Or.inr hi)
    have ih_t := ih h_t
    rw [Finset.sum_insert h_not_in]
    have h_assoc : A + (f hx + ∑ x ∈ ht, f x) = (A + ∑ x ∈ ht, f x) + f hx := by abel
    rw [h_assoc]
    have h_lt : ‖f hx‖ < ‖A + ∑ x ∈ ht, f x‖ := by
      rw [ih_t]
      exact h_x
    rw [norm_add_eq_left_of_norm_lt h_lt]
    exact ih_t

lemma taylor_expansion_exact {R : Type*} [CommRing R] (f : R[X]) (r s : R) :
  f.eval (s + r) = f.eval r + ∑ i ∈ Finset.range f.natDegree, ((hasseDeriv (i + 1) f).eval r) * s ^ (i + 1) := by
  rw [← taylor_eval]
  rw [eval_eq_sum_range]
  rw [natDegree_taylor]
  rw [Finset.sum_range_succ']
  simp only [taylor_coeff_zero, pow_zero, mul_one]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [taylor_coeff]

lemma hasseDeriv_map_local {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : R[X]) (k : ℕ) :
  hasseDeriv k (p.map f) = (hasseDeriv k p).map f := by
  ext n
  simp [hasseDeriv_coeff]

lemma taylor_expansion_aeval (p : ℚ[X]) (r s : Padic 3) :
  aeval (s + r) p = aeval r p + ∑ i ∈ Finset.range p.natDegree, aeval r (hasseDeriv (i + 1) p) * s ^ (i + 1) := by
  simp_rw [aeval_def, ← eval_map]
  have h_inj : Function.Injective (algebraMap ℚ (Padic 3)) := FaithfulSMul.algebraMap_injective ℚ (Padic 3)
  rw [taylor_expansion_exact (p.map (algebraMap ℚ (Padic 3))) r s]
  rw [natDegree_map_eq_of_injective h_inj]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hasseDeriv_map_local]

def max_of_fn (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => max (f n) (max_of_fn f n)

lemma le_max_of_fn (f : ℕ → ℕ) (d : ℕ) {i : ℕ} (hi : i < d) : f i ≤ max_of_fn f d := by
  induction d with
  | zero => omega
  | succ d ih =>
    rw [max_of_fn]
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with h | h
    · subst h
      exact le_max_left _ _
    · have := ih h
      exact le_trans this (le_max_right _ _)

lemma pow_le_self_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (i : ℕ) (hi : i ≥ 1) : x ^ i ≤ x := by
  induction i with
  | zero => omega
  | succ i ih =>
    by_cases hi0 : i = 0
    · subst hi0
      simp
    · have h_pos : i ≥ 1 := by omega
      have ih_val := ih h_pos
      rw [pow_succ]
      have : x ^ i * x ≤ x ^ i * 1 := mul_le_mul_of_nonneg_left hx1 (by positivity)
      rw [mul_one] at this
      exact le_trans this ih_val


lemma valuation_eventually_constant_of_deg_zero (p : ℚ[X]) (hp : p ≠ 0) (hdeg : p.natDegree = 0) (S : ℕ → Padic 3) :
  ∃ V : ℤ, ∃ N : ℕ, ∀ n ≥ N, ‖(aeval (S n) p : Padic 3)‖ = (3 : ℝ) ^ V := by
  have h_eq : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
  generalize p.coeff 0 = c at *
  subst h_eq
  have h_coeff : c ≠ 0 := by
    intro hc
    subst hc
    exact hp C_0
  have h_padic : algebraMap ℚ (Padic 3) c ≠ 0 := by
    have h_inj : Function.Injective (algebraMap ℚ (Padic 3)) := FaithfulSMul.algebraMap_injective ℚ (Padic 3)
    exact (map_ne_zero_iff (algebraMap ℚ (Padic 3)) h_inj).mpr h_coeff
  use - (algebraMap ℚ (Padic 3) c).valuation
  use 0
  intro n _
  simp only [aeval_C]
  exact Padic.norm_eq_zpow_neg_valuation h_padic

lemma antitone_eventually_constant (f : ℕ → ℤ) (hf : ∀ m, f (m + 1) ≤ f m) (b : ℤ) (hb : ∀ m, b ≤ f m) :
  ∃ V, ∃ M_0, ∀ M ≥ M_0, f M = V := by
  have h_mono : ∀ x y, x ≤ y → f y ≤ f x := by
    intro x y h
    induction y, h using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      exact le_trans (hf m) ih
  let d := (f 0 - b).toNat
  induction' hd : d using Nat.strong_induction_on with n ih generalizing f
  by_cases h_const : ∀ m, f m = f 0
  · use f 0, 0
    intro M _
    exact h_const M
  · push_neg at h_const
    obtain ⟨m_0, hm_0⟩ := h_const
    have h_lt : f m_0 < f 0 := by
      rcases lt_or_gt_of_ne hm_0 with h | h
      · exact h
      · have : f m_0 ≤ f 0 := h_mono 0 m_0 (by omega)
        omega
    let g := fun x => f (x + m_0)
    have hg_mono : ∀ m, g (m + 1) ≤ g m := by
      intro m
      dsimp [g]
      have h1 : m + 1 + m_0 = m + m_0 + 1 := by omega
      rw [h1]
      exact hf (m + m_0)
    have hg_b : ∀ m, b ≤ g m := fun m => hb (m + m_0)
    have h_g0 : g 0 = f m_0 := by
      dsimp [g]
      rw [zero_add]
    let d_g := (g 0 - b).toNat
    have h_dg_lt : d_g < n := by
      have hb_m0 : b ≤ f m_0 := hb m_0
      have hb_0 : b ≤ f 0 := hb 0
      dsimp [d_g, d] at *
      rw [h_g0]
      omega
    have hg_mono_gen : ∀ x y, x ≤ y → g y ≤ g x := by
      intro x y hxy
      dsimp [g]
      apply h_mono
      omega
    obtain ⟨V, M_g, hM_g⟩ := ih d_g h_dg_lt g hg_mono hg_b hg_mono_gen rfl
    use V, M_g + m_0
    intro M hM
    have h_ge : M - m_0 ≥ M_g := by omega
    have h_eq : M = (M - m_0) + m_0 := by omega
    have h_g_val := hM_g (M - m_0) h_ge
    dsimp [g] at h_g_val
    rw [← h_eq] at h_g_val
    exact h_g_val



lemma norm_S_le (n : ℕ) : ‖S n‖ ≤ 1 := by
  induction n with
  | zero =>
    dsimp [S]
    simp
  | succ n ih =>
    rw [S_succ]
    have h_max := IsUltrametricDist.norm_add_le_max ((n.factorial : Padic 3)) (S n)
    have h_fac : ‖(n.factorial : Padic 3)‖ ≤ 1 := by
      have h1 : (n.factorial : Padic 3) = ((n.factorial : ℤ) : Padic 3) := by norm_cast
      rw [h1]
      have h2 : ‖((n.factorial : ℤ) : Padic 3)‖ ≤ (3 : ℝ) ^ (-(0 : ℤ)) ↔ (3 ^ 0 : ℤ) ∣ (n.factorial : ℤ) := by
        exact_mod_cast Padic.norm_int_le_pow_iff_dvd (p := 3) (n.factorial : ℤ) 0
      have h_pow : (3 : ℝ) ^ (-(0 : ℤ)) = 1 := by norm_num
      rw [h_pow] at h2
      rw [h2]
      simp
    exact le_trans h_max (max_le h_fac ih)

lemma lt_three_pow (v : ℕ) : v < 3 ^ v := by
  induction v with
  | zero => simp
  | succ v ih =>
    have h1 : 3 ^ (v + 1) = 3 ^ v * 3 := rfl
    have h2 : 3 ^ v * 3 = 3 ^ v + 3 ^ v * 2 := by ring
    rw [h1, h2]
    have ih_le : v + 1 ≤ 3 ^ v := ih
    have h_pos : 3 ^ v * 2 > 0 := by positivity
    omega

lemma zpow_three_ge_self (v : ℤ) : (3 : ℝ) ^ v ≥ v := by
  rcases le_or_gt 0 v with hv | hv
  · lift v to ℕ using hv
    simp only [zpow_natCast]
    have h_lt := lt_three_pow v
    have h_le : (v : ℝ) ≤ (3 : ℝ) ^ v := by
      exact_mod_cast (Nat.le_of_lt h_lt)
    exact h_le
  · have h_pos : (3 : ℝ) ^ v > 0 := by positivity
    have h_v : (v : ℝ) < 0 := by exact_mod_cast hv
    linarith

lemma exists_int_bound_of_zpow_le (C : ℝ) : ∃ B : ℤ, ∀ v : ℤ, (3 : ℝ) ^ v ≤ C → v ≤ B := by
  obtain ⟨B, hB⟩ := exists_int_ge C
  use max 0 B
  intro v hv
  have h_ge := zpow_three_ge_self v
  have h_trans : (v : ℝ) ≤ C := le_trans h_ge hv
  have h_le_B : (v : ℝ) ≤ B := le_trans h_trans hB
  have h_v_le_B : v ≤ B := by exact_mod_cast h_le_B
  exact le_trans h_v_le_B (le_max_right 0 B)

lemma norm_aeval_S_le (p : ℚ[X]) : ∃ C : ℝ, ∀ n : ℕ, ‖aeval (S n) p‖ ≤ C := by
  let p_padic := p.map (algebraMap ℚ (Padic 3))
  use ∑ i ∈ p_padic.support, ‖p_padic.coeff i‖
  intro n
  rw [aeval_def, ← eval_map]
  rw [eval_eq_sum]
  have h_le := norm_sum_le p_padic.support (fun i => p_padic.coeff i * S n ^ i)
  apply le_trans h_le
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul, norm_pow]
  have h_Sn := norm_S_le n
  have h_Sn_pow : ‖S n‖ ^ i ≤ 1 := by
    apply pow_le_one₀ (norm_nonneg _) h_Sn
  have h_coeff_nonneg : 0 ≤ ‖p_padic.coeff i‖ := norm_nonneg _
  have h_mul : ‖p_padic.coeff i‖ * ‖S n‖ ^ i ≤ ‖p_padic.coeff i‖ := by
    nlinarith
  exact h_mul

lemma exists_max_valuation_ge (p : ℚ[X]) (hp : p ≠ 0) (M : ℕ) :
  ∃ V_max : ℤ, ∃ N_max ≥ M, aeval (S N_max) p ≠ 0 ∧
  (∀ n ≥ M, aeval (S n) p ≠ 0 → - (aeval (S n) p : Padic 3).valuation ≤ V_max) ∧
  - (aeval (S N_max) p : Padic 3).valuation = V_max := by
  let P := fun V => ∃ n ≥ M, aeval (S n) p ≠ 0 ∧ - (aeval (S n) p : Padic 3).valuation = V
  have h_dec : DecidablePred P := fun V => Classical.dec (P V)
  have h_bdd : ∃ b, ∀ x, P x → x ≤ b := by
    obtain ⟨C, hC⟩ := norm_aeval_S_le p
    obtain ⟨B, hB⟩ := exists_int_bound_of_zpow_le C
    use B
    intro V hV
    rcases hV with ⟨n, hn, h_ne, rfl⟩
    have h_norm := hC n
    rw [Padic.norm_eq_zpow_neg_valuation h_ne] at h_norm
    exact hB _ h_norm
  have h_nonempty : ∃ V, P V := by
    have p_padic_ne : p.map (algebraMap ℚ (Padic 3)) ≠ 0 := by
      have h_inj : Function.Injective (algebraMap ℚ (Padic 3)) := FaithfulSMul.algebraMap_injective ℚ (Padic 3)
      exact (Polynomial.map_ne_zero_iff h_inj).mpr hp
    obtain ⟨n, hn_ge, hn_val⟩ := exists_S_ne_zero_ge (p.map (algebraMap ℚ (Padic 3))) p_padic_ne M
    have h_ne_aeval : aeval (S n) p ≠ 0 := by
      rwa [aeval_def, ← eval_map]
    use - (aeval (S n) p).valuation
    use n, hn_ge, h_ne_aeval
  obtain ⟨V_max, h_P, h_max⟩ := Int.exists_greatest_of_bdd h_bdd h_nonempty
  use V_max
  rcases h_P with ⟨N_max, hN_max_ge, h_ne, rfl⟩
  use N_max, hN_max_ge
  refine ⟨h_ne, ?_, rfl⟩
  intro n hn h_ne'
  apply h_max
  use n, hn, h_ne'


lemma eventually_constant_norm_of_ne_zero (p : ℚ[X]) (h_root : aeval xi_3 p ≠ 0) :
  ∃ V : ℤ, ∃ N : ℕ, ∀ n ≥ N, ‖(aeval (S n) p : Padic 3)‖ = (3 : ℝ) ^ V := by
  have h_cont : Continuous (fun x : Padic 3 => (aeval x p : Padic 3)) := by
    simp_rw [aeval_def]
    exact Polynomial.continuous_eval₂ p (algebraMap ℚ (Padic 3))
  have h_lim := h_cont.tendsto xi_3 |>.comp tendsto_S
  have h_pos : ‖aeval xi_3 p‖ > 0 := norm_pos_iff.mpr h_root
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h_lim ‖aeval xi_3 p‖ h_pos
  use - (aeval xi_3 p).valuation, N
  intro n hn
  have h_dist := hN n hn
  rw [dist_eq_norm] at h_dist
  change ‖aeval (S n) p - aeval xi_3 p‖ < ‖aeval xi_3 p‖ at h_dist
  have h_eq : aeval (S n) p = aeval xi_3 p + (aeval (S n) p - aeval xi_3 p) := by ring
  have h_norm_eq : ‖aeval (S n) p‖ = ‖aeval xi_3 p‖ := by
    rw [h_eq, norm_add_eq_left_of_norm_lt h_dist]
  rw [h_norm_eq, Padic.norm_eq_zpow_neg_valuation h_root]
  rfl

lemma derivative_minpoly_ne_zero (hx : IsIntegral ℚ xi_3) : aeval xi_3 (derivative (minpoly ℚ xi_3)) ≠ 0 := by
  intro h_eval
  let p := minpoly ℚ xi_3
  have hp_monic : p.Monic := minpoly.monic hx
  have hp_ne_zero : p ≠ 0 := hp_monic.ne_zero
  have hp_deg_ne_zero : p.natDegree ≠ 0 := by
    intro h_zero
    have h_coeff : p.coeff 0 = 1 := by
      have h_lc := hp_monic
      rw [Monic, leadingCoeff, h_zero] at h_lc
      exact h_lc
    have h_eq : p = C 1 := by
      rw [← h_coeff]
      exact eq_C_of_natDegree_eq_zero h_zero
    have h_eval_p : aeval xi_3 p = 0 := minpoly.aeval ℚ xi_3
    rw [h_eq, aeval_C, map_one] at h_eval_p
    norm_num at h_eval_p
  by_cases h_deriv_zero : derivative p = 0
  · have h_deg_zero : p.natDegree = 0 := natDegree_eq_zero_of_derivative_eq_zero h_deriv_zero
    exact hp_deg_ne_zero h_deg_zero
  · have h_lt := natDegree_derivative_lt hp_deg_ne_zero
    have h_dvd := minpoly.dvd ℚ xi_3 h_eval
    rcases h_dvd with ⟨q, hq⟩
    have hq_ne : q ≠ 0 := by
      intro hq_zero
      rw [hq_zero, mul_zero] at hq
      exact h_deriv_zero hq
    have h_deg_eq : (derivative p).natDegree = p.natDegree + q.natDegree := by
      rw [hq, natDegree_mul hp_ne_zero hq_ne]
    omega

lemma eq_of_eval_minpoly_eq_zero {x : Padic 3} (hx : IsIntegral ℚ x) (q : ℚ) (h_eval : (minpoly ℚ x).eval q = 0) : x = q := by
  let p := minpoly ℚ x
  have hp_monic := minpoly.monic hx
  have hp_irred := minpoly.irreducible hx
  have h_dvd : (X - C q) ∣ p := dvd_iff_isRoot.mpr h_eval
  have h_assoc := (irreducible_X_sub_C q).associated_of_dvd hp_irred h_dvd
  have h_eq : p = X - C q := eq_of_monic_of_associated hp_monic (monic_X_sub_C q) h_assoc.symm
  have h_eval_p : aeval x p = 0 := minpoly.aeval ℚ x
  rw [h_eq, map_sub, aeval_X, aeval_C] at h_eval_p
  have h_eq_x : x - algebraMap ℚ (Padic 3) q = 0 := h_eval_p
  rw [sub_eq_zero] at h_eq_x
  exact_mod_cast h_eq_x

lemma norm_factorial_lt_of_dvd_succ (n : ℕ) (h_dvd : 3 ∣ n + 1) : ‖((n + 1).factorial : Padic 3)‖ < ‖(n.factorial : Padic 3)‖ := by
  rw [Nat.factorial_succ]
  push_cast
  rw [norm_mul]
  have h_norm : ‖(n + 1 : Padic 3)‖ < 1 := by
    have h_dvd_int : (3 ^ 1 : ℤ) ∣ (n + 1 : ℤ) := by
      simp only [pow_one]
      exact_mod_cast h_dvd
    have h_norm_le_iff : ‖((n + 1 : ℤ) : Padic 3)‖ ≤ (3 : ℝ) ^ (-(1 : ℤ)) ↔ (3 ^ 1 : ℤ) ∣ (n + 1 : ℤ) := by
      exact_mod_cast Padic.norm_int_le_pow_iff_dvd (p := 3) (n + 1 : ℤ) 1
    have h_norm_le : ‖((n + 1 : ℤ) : Padic 3)‖ ≤ (3 : ℝ) ^ (-(1 : ℤ)) := h_norm_le_iff.mpr h_dvd_int
    have h_pow : (3 : ℝ) ^ (-(1 : ℤ)) = 1 / 3 := by norm_num
    rw [h_pow] at h_norm_le
    have h_cast : (n + 1 : Padic 3) = ((n + 1 : ℤ) : Padic 3) := by norm_cast
    rw [h_cast]
    linarith
  have h_pos : ‖(n.factorial : Padic 3)‖ > 0 := norm_pos_iff.mpr (by exact_mod_cast Nat.factorial_ne_zero n)
  nlinarith

lemma norm_natCast_le_one (n : ℕ) : ‖(n : Padic 3)‖ ≤ 1 := by
  induction n with
  | zero =>
    simp only [CharP.cast_eq_zero]
    rw [_root_.norm_zero]
    norm_num
  | succ n ih =>
    push_cast
    have h_max := IsUltrametricDist.norm_add_le_max (n : Padic 3) 1
    rw [norm_one] at h_max
    exact h_max.trans (max_le ih (le_refl _))

lemma norm_factorial_mono {n k : ℕ} (h : n ≤ k) : ‖(k.factorial : Padic 3)‖ ≤ ‖(n.factorial : Padic 3)‖ := by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [Nat.factorial_succ]
    push_cast
    rw [norm_mul]
    have h_le_one : ‖(m : Padic 3) + 1‖ ≤ 1 := by
      have h_cast : ((m + 1 : ℕ) : Padic 3) = (m : Padic 3) + 1 := by push_cast; rfl
      rw [← h_cast]
      exact norm_natCast_le_one (m + 1)
    have h_mul : ‖(m : Padic 3) + 1‖ * ‖(m.factorial : Padic 3)‖ ≤ 1 * ‖(m.factorial : Padic 3)‖ := mul_le_mul_of_nonneg_right h_le_one (norm_nonneg _)
    rw [one_mul] at h_mul
    exact h_mul.trans ih

lemma norm_sum_Ico_le_first {n m : ℕ} (h : n ≤ m) :
  ‖(∑ k ∈ Finset.Ico (n + 1) (m + 1), (k.factorial : Padic 3))‖ ≤ ‖((n + 1).factorial : Padic 3)‖ := by
  induction m, h using Nat.le_induction with
  | base =>
    simp only [Finset.Ico_self, Finset.sum_empty]
    rw [_root_.norm_zero]
    exact norm_nonneg _
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    have h_max := IsUltrametricDist.norm_add_le_max (∑ k ∈ Finset.Ico (n + 1) (m + 1), (k.factorial : Padic 3)) ((m + 1).factorial : Padic 3)
    apply h_max.trans
    have h_le_first : ‖((m + 1).factorial : Padic 3)‖ ≤ ‖((n + 1).factorial : Padic 3)‖ := norm_factorial_mono (by omega)
    exact max_le ih h_le_first

lemma xi_3_ne_S_n_0 (n_0 : ℕ) (h_dvd : 3 ∣ n_0 + 1) : xi_3 ≠ S n_0 := by
  intro h_eq
  have h_lim := tendsto_S
  rw [h_eq] at h_lim
  have h_lim_dist : Tendsto (fun m => dist (S m) (S n_0)) atTop (nhds 0) := by
    rwa [tendsto_iff_dist_tendsto_zero] at h_lim
  have h_lim_sub : Tendsto (fun m => ‖S m - S n_0‖) atTop (nhds 0) := by
    simp_rw [dist_eq_norm] at h_lim_dist
    exact h_lim_dist
  have h_const : ∀ m ≥ n_0 + 1, ‖S m - S n_0‖ = ‖(n_0.factorial : Padic 3)‖ := by
    intro m hm
    have h_eq_add : S m - S n_0 = (n_0.factorial : Padic 3) + ∑ k ∈ Finset.Ico (n_0 + 1) m, (k.factorial : Padic 3) := by
      dsimp [S]
      rw [← Finset.sum_range_add_sum_Ico (fun k => (k.factorial : Padic 3)) (by omega : n_0 ≤ m)]
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : n_0 < m)]
      abel
    rw [h_eq_add]
    have h_lt : ‖∑ k ∈ Finset.Ico (n_0 + 1) m, (k.factorial : Padic 3)‖ < ‖(n_0.factorial : Padic 3)‖ := by
      have h_le_first : ‖∑ k ∈ Finset.Ico (n_0 + 1) m, (k.factorial : Padic 3)‖ ≤ ‖((n_0 + 1).factorial : Padic 3)‖ := by
        have : n_0 + 1 ≤ m := hm
        have h_sum := norm_sum_Ico_le_first (by omega : n_0 ≤ m - 1)
        have h_eq_sum : (∑ k ∈ Finset.Ico (n_0 + 1) m, (k.factorial : Padic 3)) = ∑ k ∈ Finset.Ico (n_0 + 1) (m - 1 + 1), (k.factorial : Padic 3) := by
          congr 2; omega
        rw [h_eq_sum]
        exact h_sum
      have h_lt_first := norm_factorial_lt_of_dvd_succ n_0 h_dvd
      exact lt_of_le_of_lt h_le_first h_lt_first
    exact norm_add_eq_left_of_norm_lt h_lt
  have h_lim_const : Tendsto (fun m => ‖S m - S n_0‖) atTop (nhds ‖(n_0.factorial : Padic 3)‖) := by
    exact tendsto_atTop_of_eventually_const h_const
  have h_unique := tendsto_nhds_unique h_lim_sub h_lim_const
  have h_norm_zero : ‖(n_0.factorial : Padic 3)‖ = 0 := by
    exact_mod_cast h_unique.symm
  have h_ne_zero : (n_0.factorial : Padic 3) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n_0
  exact h_ne_zero (norm_eq_zero.mp h_norm_zero)

lemma norm_sub_eq_first (p : ℚ[X]) (V_deriv : ℤ) (N_base : ℕ)
  (h_diff : ∀ n ≥ N_base, ‖aeval (S (n + 1)) p - aeval (S n) p‖ = (3 : ℝ) ^ V_deriv * ‖(n.factorial : Padic 3)‖)
  {K_start : ℕ} (h_K_start_ge : K_start ≥ N_base) (h_dvd : 3 ∣ K_start + 1) (M : ℕ) (hM : M ≥ K_start + 1) :
  ‖aeval (S M) p - aeval (S K_start) p‖ = (3 : ℝ) ^ V_deriv * ‖(K_start.factorial : Padic 3)‖ := by
  induction' hM : M - (K_start + 1) with k ih generalizing M
  · have h_eq : M = K_start + 1 := by omega
    subst h_eq
    exact h_diff K_start h_K_start_ge
  · have h_eq : M = K_start + 1 + (k + 1) := by omega
    have h_M_ge : M ≥ K_start + 1 := by omega
    have h_M_minus_1 : M - 1 ≥ K_start + 1 := by omega
    have ih_val := ih (M - 1) h_M_minus_1 (by omega)
    have h_eq_add : aeval (S M) p - aeval (S K_start) p = (aeval (S (M - 1)) p - aeval (S K_start) p) + (aeval (S M) p - aeval (S (M - 1)) p) := by ring
    rw [h_eq_add]
    rw [norm_add_eq_left_of_norm_lt]
    · exact ih_val
    · rw [ih_val]
      have h_diff_val := h_diff (M - 1) (le_trans h_K_start_ge (by omega))
      have h_eq_succ : M - 1 + 1 = M := by omega
      rw [h_eq_succ] at h_diff_val
      rw [h_diff_val]
      have h_deriv_pos : (3 : ℝ) ^ V_deriv > 0 := by positivity
      apply mul_lt_mul_of_pos_left _ h_deriv_pos
      have h_le : ‖((M - 1).factorial : Padic 3)‖ ≤ ‖((K_start + 1).factorial : Padic 3)‖ := norm_factorial_mono (by omega)
      have h_lt := norm_factorial_lt_of_dvd_succ K_start h_dvd
      exact lt_of_le_of_lt h_le h_lt

theorem oeis_341685_conjecture_0 : ¬ IsAlgebraic ℚ (xi_3) := by
  intro h
  rw [isAlgebraic_iff_isIntegral] at h
  let p := minpoly ℚ xi_3
  have hp_monic : p.Monic := minpoly.monic h
  have hp_ne : p ≠ 0 := hp_monic.ne_zero
  have hp_deg_ne : p.natDegree ≠ 0 := by
    intro h_zero
    have h_coeff : p.coeff 0 = 1 := by
      have h_lc := hp_monic
      rw [Monic, leadingCoeff, h_zero] at h_lc
      exact h_lc
    have h_eq : p = C 1 := by
      rw [← h_coeff]
      exact eq_C_of_natDegree_eq_zero h_zero
    have h_eval_p : aeval xi_3 p = 0 := minpoly.aeval ℚ xi_3
    rw [h_eq, aeval_C, map_one] at h_eval_p
    norm_num at h_eval_p
  have h_root_deriv : aeval xi_3 (derivative p) ≠ 0 := derivative_minpoly_ne_zero h
  have h_deriv_ne : derivative p ≠ 0 := by
    intro h_zero
    exact h_root_deriv (by rw [h_zero, aeval_zero])
  obtain ⟨V_deriv, N_deriv, hN_deriv⟩ := eventually_constant_norm_of_ne_zero (derivative p) h_root_deriv

  let d := p.natDegree
  have hd : d ≠ 0 := hp_deg_ne

  have h_cont : Continuous (fun x : Padic 3 => (aeval x p : Padic 3)) := by
    simp_rw [aeval_def]
    exact Polynomial.continuous_eval₂ p (algebraMap ℚ (Padic 3))
  have h_lim := h_cont.tendsto xi_3 |>.comp tendsto_S
  have h_eval_zero : aeval xi_3 p = 0 := minpoly.aeval ℚ xi_3
  rw [h_eval_zero] at h_lim
  have h_lim_norm : Tendsto (fun n => ‖(aeval (S n) p : Padic 3)‖) atTop (nhds 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.mp h_lim

  have h_exists : ∀ i, ∃ V : ℤ, ∃ N : ℕ, ∀ n ≥ N, ‖aeval (S n) (hasseDeriv (i + 1) p)‖ ≤ (3 : ℝ) ^ V := by
    intro i
    obtain ⟨C, hC⟩ := norm_aeval_S_le (hasseDeriv (i + 1) p)
    obtain ⟨B, hB⟩ := exists_int_bound_of_zpow_le C
    use B, 0
    intro n _
    have hCn := hC n
    by_cases hq : aeval (S n) (hasseDeriv (i + 1) p) = 0
    · rw [hq, _root_.norm_zero]
      positivity
    · rw [Padic.norm_eq_zpow_neg_valuation hq]
      rw [Padic.norm_eq_zpow_neg_valuation hq] at hCn
      have h_le := hB _ hCn
      have h_base : (1 : ℝ) < 3 := by norm_num
      exact (zpow_right_strictMono₀ h_base).monotone h_le

  classical
  choose V_of N_of h_bound using h_exists
  let N_rem := max_of_fn N_of d
  have h_N_rem : ∀ i < d, N_of i ≤ N_rem := fun i hi => le_max_of_fn N_of d hi

  have h_exists_K : ∀ i, ∃ K : ℕ, ∀ n ≥ K, i ≥ 1 → ‖(n.factorial : Padic 3)‖ ^ i < (3 : ℝ) ^ (V_deriv - V_of i) := by
    intro i
    by_cases hi1 : i ≥ 1
    · have h_pos : (3 : ℝ) ^ (V_deriv - V_of i) > 0 := by positivity
      have h_eps : min (1 / 2) ((3 : ℝ) ^ (V_deriv - V_of i) / 2) > 0 := by
        apply lt_min (by norm_num) (by linarith)
      obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp tendsto_norm_factorial_zero (min (1 / 2) ((3 : ℝ) ^ (V_deriv - V_of i) / 2)) h_eps
      use K
      intro n hn _
      have hk := hK n hn
      rw [_root_.dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hk
      have hk1 : ‖(n.factorial : Padic 3)‖ < 1 := by
        have : min (1 / 2) ((3 : ℝ) ^ (V_deriv - V_of i) / 2) ≤ 1 / 2 := min_le_left _ _
        linarith
      have hk2 : ‖(n.factorial : Padic 3)‖ < (3 : ℝ) ^ (V_deriv - V_of i) := by
        have : min (1 / 2) ((3 : ℝ) ^ (V_deriv - V_of i) / 2) ≤ (3 : ℝ) ^ (V_deriv - V_of i) / 2 := min_le_right _ _
        linarith
      have h_pow : ‖(n.factorial : Padic 3)‖ ^ i ≤ ‖(n.factorial : Padic 3)‖ := by
        exact pow_le_self_of_le_one (norm_nonneg _) (le_of_lt hk1) i hi1
      exact lt_of_le_of_lt h_pow hk2
    · use 0
      intro n _ h_contra
      omega

  choose K_of h_K_bound using h_exists_K
  let K_rem := max_of_fn K_of d
  have h_K_rem : ∀ i < d, K_of i ≤ K_rem := fun i hi => le_max_of_fn K_of d hi

  let N_base := max N_deriv (max N_rem K_rem)
  have h_N_deriv : N_base ≥ N_deriv := le_max_left _ _
  have h_N_rem_le : N_base ≥ N_rem := le_trans (le_max_left _ _) (le_max_right _ _)
  have h_K_rem_le : N_base ≥ K_rem := le_trans (le_max_right _ _) (le_max_right _ _)

  have h_diff_eq : ∀ n ≥ N_base, ‖aeval (S (n + 1)) p - aeval (S n) p‖ = (3 : ℝ) ^ V_deriv * ‖(n.factorial : Padic 3)‖ := by
    intro n hn
    rw [S_succ n]
    rw [taylor_expansion_aeval p (S n) n.factorial]
    have h_eq_add : aeval (S n) p + ∑ i ∈ Finset.range p.natDegree, aeval (S n) (hasseDeriv (i + 1) p) * (n.factorial : Padic 3) ^ (i + 1) - aeval (S n) p =
      ∑ i ∈ Finset.range p.natDegree, aeval (S n) (hasseDeriv (i + 1) p) * (n.factorial : Padic 3) ^ (i + 1) := by ring
    rw [h_eq_add]
    have hd_eq : p.natDegree = d := rfl
    rw [hd_eq]
    have hd_eq_succ : d = (d - 1) + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero hd)).symm
    rw [hd_eq_succ]
    rw [Finset.sum_range_succ']
    simp only [zero_add, pow_one, hasseDeriv_one]
    have h_lt : ∀ i ∈ Finset.range (d - 1), ‖aeval (S n) (hasseDeriv (i + 2) p) * (n.factorial : Padic 3) ^ (i + 2)‖ < ‖aeval (S n) p.derivative * (n.factorial : Padic 3)‖ := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hi_lt : i + 1 < d := by omega
      have h_i1 : i + 1 ≥ 1 := by omega
      have h_norm_A : ‖aeval (S n) p.derivative * (n.factorial : Padic 3)‖ = (3 : ℝ) ^ V_deriv * ‖(n.factorial : Padic 3)‖ := by
        rw [norm_mul, hN_deriv n (by linarith)]
      rw [h_norm_A]
      have h_val_q : ‖aeval (S n) (hasseDeriv (i + 2) p)‖ ≤ (3 : ℝ) ^ (V_of (i + 1)) := by
        have hn_ge : n ≥ N_of (i + 1) := by
          have : N_of (i + 1) ≤ N_rem := h_N_rem (i + 1) hi_lt
          linarith
        exact h_bound (i + 1) n hn_ge
      have h_val_K : ‖(n.factorial : Padic 3)‖ ^ (i + 1) < (3 : ℝ) ^ (V_deriv - V_of (i + 1)) := by
        have hn_ge : n ≥ K_of (i + 1) := by
          have : K_of (i + 1) ≤ K_rem := h_K_rem (i + 1) hi_lt
          linarith
        exact h_K_bound (i + 1) n hn_ge h_i1
      have h_norm_B : ‖aeval (S n) (hasseDeriv (i + 2) p) * (n.factorial : Padic 3) ^ (i + 2)‖ = ‖aeval (S n) (hasseDeriv (i + 2) p)‖ * (‖(n.factorial : Padic 3)‖ ^ (i + 1) * ‖(n.factorial : Padic 3)‖) := by
        rw [norm_mul, norm_pow, pow_succ]
      rw [h_norm_B]
      have h_mul_temp : ‖aeval (S n) (hasseDeriv (i + 2) p)‖ * ‖(n.factorial : Padic 3)‖ ^ (i + 1) < (3 : ℝ) ^ (V_of (i + 1)) * (3 : ℝ) ^ (V_deriv - V_of (i + 1)) := by
        have ha : 0 ≤ ‖(n.factorial : Padic 3)‖ ^ (i + 1) := by positivity
        have hc : 0 ≤ ‖aeval (S n) (hasseDeriv (i + 2) p)‖ := norm_nonneg _
        have hd : 0 < (3 : ℝ) ^ (V_of (i + 1)) := by positivity
        nlinarith
      have h_mul_eq : (3 : ℝ) ^ (V_of (i + 1)) * (3 : ℝ) ^ (V_deriv - V_of (i + 1)) = (3 : ℝ) ^ V_deriv := by
        rw [mul_comm]
        rw [← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_add (by norm_num)]
        congr 1
        push_cast
        ring
      have h_mul1 : ‖aeval (S n) (hasseDeriv (i + 2) p)‖ * ‖(n.factorial : Padic 3)‖ ^ (i + 1) < (3 : ℝ) ^ V_deriv := by
        rwa [h_mul_eq] at h_mul_temp
      have h_fac_pos : ‖(n.factorial : Padic 3)‖ > 0 := norm_pos_iff.mpr (by exact_mod_cast Nat.factorial_ne_zero n)
      have h_assoc_eq : ‖aeval (S n) (hasseDeriv (i + 2) p)‖ * (‖(n.factorial : Padic 3)‖ ^ (i + 1) * ‖(n.factorial : Padic 3)‖) = ‖aeval (S n) (hasseDeriv (i + 2) p)‖ * ‖(n.factorial : Padic 3)‖ ^ (i + 1) * ‖(n.factorial : Padic 3)‖ := by ring
      rw [h_assoc_eq]
      exact mul_lt_mul_of_pos_right h_mul1 h_fac_pos
    rw [add_comm]
    rw [norm_add_sum_eq_first (Finset.range (d - 1)) (fun i => aeval (S n) (hasseDeriv (i + 2) p) * (n.factorial : Padic 3) ^ (i + 2)) h_lt]
    rw [norm_mul, hN_deriv n (by linarith)]

  have p_padic_ne : p.map (algebraMap ℚ (Padic 3)) ≠ 0 := by
    have h_inj : Function.Injective (algebraMap ℚ (Padic 3)) := FaithfulSMul.algebraMap_injective ℚ (Padic 3)
    exact (Polynomial.map_ne_zero_iff h_inj).mpr hp_ne

  let n_0 := 3 * N_base + 2
  have hn_0_ge : n_0 ≥ N_base := by dsimp [n_0]; omega
  have h_dvd_n0 : 3 ∣ n_0 + 1 := by
    use N_base + 1
    ring

  have h_ne_aeval_n0 : aeval (S n_0) p ≠ 0 := by
    intro h_zero
    have h_eval_map : eval (S n_0) (p.map (algebraMap ℚ (Padic 3))) = 0 := by
      rwa [aeval_def, ← eval_map] at h_zero
    have h_eq_alg : S n_0 = algebraMap ℚ (Padic 3) (∑ k ∈ Finset.range n_0, (Nat.factorial k : ℚ)) := S_eq_algebraMap n_0
    rw [h_eq_alg] at h_eval_map
    rw [eval_map_apply] at h_eval_map
    have h_inj : Function.Injective (algebraMap ℚ (Padic 3)) := FaithfulSMul.algebraMap_injective ℚ (Padic 3)
    have h_eval_eq : p.eval (∑ k ∈ Finset.range n_0, (Nat.factorial k : ℚ)) = 0 := by
      apply h_inj
      rw [map_zero]
      exact h_eval_map
    have h_xi_S : xi_3 = (∑ k ∈ Finset.range n_0, (Nat.factorial k : ℚ) : ℚ) := by
      exact eq_of_eval_minpoly_eq_zero h _ h_eval_eq
    have h_xi_S_padic : xi_3 = S n_0 := by
      rw [h_xi_S]
      exact (S_eq_algebraMap n_0).symm
    exact xi_3_ne_S_n_0 n_0 h_dvd_n0 h_xi_S_padic

  let V_temp := - (aeval (S n_0) p).valuation
  have h_pow_pos : (3 : ℝ) ^ (V_temp - V_deriv) > 0 := by positivity
  obtain ⟨K_fac_temp, hK_fac_temp⟩ := Metric.tendsto_atTop.mp tendsto_norm_factorial_zero ((3 : ℝ) ^ (V_temp - V_deriv)) h_pow_pos

  let K_start := 3 * (max n_0 K_fac_temp) + 2
  have hK_start_ge_n0 : K_start ≥ n_0 := by
    have : max n_0 K_fac_temp ≥ n_0 := le_max_left _ _
    dsimp [K_start]; omega
  have hK_start_ge_base : K_start ≥ N_base := le_trans hn_0_ge hK_start_ge_n0
  have hK_start_ge_fac : K_start ≥ K_fac_temp := by
    have : max n_0 K_fac_temp ≥ K_fac_temp := le_max_right _ _
    dsimp [K_start]; omega
  have h_dvd_K_start : 3 ∣ K_start + 1 := by
    use (max n_0 K_fac_temp) + 1
    ring

  have h_ne_aeval_K_start : aeval (S K_start) p ≠ 0 := by
    intro h_zero
    have h_eval_map : eval (S K_start) (p.map (algebraMap ℚ (Padic 3))) = 0 := by
      rwa [aeval_def, ← eval_map] at h_zero
    have h_eq_alg : S K_start = algebraMap ℚ (Padic 3) (∑ k ∈ Finset.range K_start, (Nat.factorial k : ℚ)) := S_eq_algebraMap K_start
    rw [h_eq_alg] at h_eval_map
    rw [eval_map_apply] at h_eval_map
    have h_inj : Function.Injective (algebraMap ℚ (Padic 3)) := FaithfulSMul.algebraMap_injective ℚ (Padic 3)
    have h_eval_eq : p.eval (∑ k ∈ Finset.range K_start, (Nat.factorial k : ℚ)) = 0 := by
      apply h_inj
      rw [map_zero]
      exact h_eval_map
    have h_xi_S : xi_3 = (∑ k ∈ Finset.range K_start, (Nat.factorial k : ℚ) : ℚ) := by
      exact eq_of_eval_minpoly_eq_zero h _ h_eval_eq
    have h_xi_S_padic : xi_3 = S K_start := by
      rw [h_xi_S]
      exact (S_eq_algebraMap K_start).symm
    exact xi_3_ne_S_n_0 K_start h_dvd_K_start h_xi_S_padic

  let V_K_start := - (aeval (S K_start) p).valuation

  let N_nonempty := K_start + 3
  have h_nonempty_ge_K_start : N_nonempty ≥ K_start := by dsimp [N_nonempty]; omega
  have h_nonempty_ge_base : N_nonempty ≥ N_base := le_trans hK_start_ge_base h_nonempty_ge_K_start
  have h_dvd_nonempty : 3 ∣ N_nonempty + 1 := by
    obtain ⟨q, hq⟩ := h_dvd_K_start
    use q + 1
    dsimp [N_nonempty]
    omega

  have h_deriv_pos_N_nonempty : (3 : ℝ) ^ V_deriv * ‖(N_nonempty.factorial : Padic 3)‖ > 0 := by
    have : (3 : ℝ) ^ V_deriv > 0 := by positivity
    have : ‖(N_nonempty.factorial : Padic 3)‖ > 0 := norm_pos_iff.mpr (by exact_mod_cast Nat.factorial_ne_zero N_nonempty)
    positivity
  obtain ⟨M_start, hM_start⟩ := Metric.tendsto_atTop.mp h_lim_norm ((3 : ℝ) ^ V_deriv * ‖(N_nonempty.factorial : Padic 3)‖) h_deriv_pos_N_nonempty
  let M := max (K_start + 4) M_start
  have hM_ge : M ≥ K_start + 1 := by dsimp [M]; omega
  have hM_ge_start : M ≥ M_start := le_max_right _ _
  have h_M_val : ‖aeval (S M) p‖ < (3 : ℝ) ^ V_deriv * ‖(N_nonempty.factorial : Padic 3)‖ := by
    have h_val := hM_start M hM_ge_start
    rw [_root_.dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h_val
    exact h_val

  have h_M_val_K_start : ‖aeval (S M) p‖ < (3 : ℝ) ^ V_deriv * ‖(K_start.factorial : Padic 3)‖ := by
    have h_deriv_pos : (3 : ℝ) ^ V_deriv > 0 := by positivity
    have h_fac_lt : (3 : ℝ) ^ V_deriv * ‖(N_nonempty.factorial : Padic 3)‖ < (3 : ℝ) ^ V_deriv * ‖(K_start.factorial : Padic 3)‖ := by
      apply mul_lt_mul_of_pos_left _ h_deriv_pos
      have h_le : ‖(N_nonempty.factorial : Padic 3)‖ ≤ ‖((K_start + 1).factorial : Padic 3)‖ := norm_factorial_mono (by dsimp [N_nonempty]; omega)
      have h_lt := norm_factorial_lt_of_dvd_succ K_start h_dvd_K_start
      exact lt_of_le_of_lt h_le h_lt
    exact lt_trans h_M_val h_fac_lt

  have h_sub_eq_M := norm_sub_eq_first p V_deriv N_base h_diff_eq hK_start_ge_base h_dvd_K_start M hM_ge

  have h_eq_K_start : aeval (S K_start) p = aeval (S M) p - (aeval (S M) p - aeval (S K_start) p) := by ring
  have h_lt_K_start : ‖aeval (S M) p‖ < ‖aeval (S M) p - aeval (S K_start) p‖ := by
    rw [h_sub_eq_M]
    exact h_M_val_K_start
  have h_norm_K_start : ‖aeval (S K_start) p‖ = (3 : ℝ) ^ V_deriv * ‖(K_start.factorial : Padic 3)‖ := by
    have h_sub_eq_symm : aeval (S M) p - aeval (S K_start) p = - (aeval (S K_start) p - aeval (S M) p) := by ring
    have h_sub_norm_eq : ‖aeval (S M) p - aeval (S K_start) p‖ = ‖aeval (S K_start) p - aeval (S M) p‖ := by
      rw [h_sub_eq_symm, norm_neg]
    have h_lt_K_start' : ‖aeval (S M) p‖ < ‖aeval (S K_start) p - aeval (S M) p‖ := by
      rwa [← h_sub_norm_eq]
    have h_add_eq : ‖aeval (S K_start) p‖ = ‖aeval (S K_start) p - aeval (S M) p‖ := by
      have h_sum : aeval (S K_start) p = (aeval (S K_start) p - aeval (S M) p) + aeval (S M) p := by ring
      have h_norm_eq : ‖aeval (S K_start) p‖ = ‖(aeval (S K_start) p - aeval (S M) p) + aeval (S M) p‖ := congrArg norm h_sum
      have h_norm_sum : ‖(aeval (S K_start) p - aeval (S M) p) + aeval (S M) p‖ = ‖aeval (S K_start) p - aeval (S M) p‖ := by
        exact norm_add_eq_left_of_norm_lt h_lt_K_start'
      exact h_norm_eq.trans h_norm_sum
    rw [h_add_eq, ← h_sub_norm_eq, h_sub_eq_M]

  have h_ne_aeval : aeval (S N_nonempty) p ≠ 0 := by
    intro h_zero
    have h_eval_map : eval (S N_nonempty) (p.map (algebraMap ℚ (Padic 3))) = 0 := by
      rwa [aeval_def, ← eval_map] at h_zero
    have h_eq_alg : S N_nonempty = algebraMap ℚ (Padic 3) (∑ k ∈ Finset.range N_nonempty, (Nat.factorial k : ℚ)) := S_eq_algebraMap N_nonempty
    rw [h_eq_alg] at h_eval_map
    rw [eval_map_apply] at h_eval_map
    have h_inj : Function.Injective (algebraMap ℚ (Padic 3)) := FaithfulSMul.algebraMap_injective ℚ (Padic 3)
    have h_eval_eq : p.eval (∑ k ∈ Finset.range N_nonempty, (Nat.factorial k : ℚ)) = 0 := by
      apply h_inj
      rw [map_zero]
      exact h_eval_map
    have h_xi_S : xi_3 = (∑ k ∈ Finset.range N_nonempty, (Nat.factorial k : ℚ) : ℚ) := by
      exact_mod_cast eq_of_eval_minpoly_eq_zero h _ h_eval_eq
    have h_xi_S_padic : xi_3 = S N_nonempty := by
      rw [h_xi_S]
      exact (S_eq_algebraMap N_nonempty).symm
    exact xi_3_ne_S_n_0 N_nonempty h_dvd_nonempty h_xi_S_padic

  let V_0 := - (aeval (S N_nonempty) p).valuation
  have hN_val : ‖aeval (S N_nonempty) p‖ = (3 : ℝ) ^ V_0 := Padic.norm_eq_zpow_neg_valuation h_ne_aeval

  have h_M_ge_nonempty : M ≥ N_nonempty + 1 := by
    dsimp [M]
    have : M_start ≥ 0 := by positivity
    omega

  have h_sub_eq_N_nonempty := norm_sub_eq_first p V_deriv N_base h_diff_eq h_nonempty_ge_base h_dvd_nonempty M h_M_ge_nonempty

  have h_norm_N_nonempty : ‖aeval (S N_nonempty) p‖ = (3 : ℝ) ^ V_deriv * ‖(N_nonempty.factorial : Padic 3)‖ := by
    have h_sub_eq_symm : aeval (S M) p - aeval (S N_nonempty) p = - (aeval (S N_nonempty) p - aeval (S M) p) := by ring
    have h_sub_norm_eq : ‖aeval (S M) p - aeval (S N_nonempty) p‖ = ‖aeval (S N_nonempty) p - aeval (S M) p‖ := by
      rw [h_sub_eq_symm, norm_neg]
    have h_lt_nonempty' : ‖aeval (S M) p‖ < ‖aeval (S N_nonempty) p - aeval (S M) p‖ := by
      rw [← h_sub_norm_eq, h_sub_eq_N_nonempty]
      exact h_M_val
    have h_add_eq : ‖aeval (S N_nonempty) p‖ = ‖aeval (S N_nonempty) p - aeval (S M) p‖ := by
      have h_sum : aeval (S N_nonempty) p = (aeval (S N_nonempty) p - aeval (S M) p) + aeval (S M) p := by ring
      have h_norm_eq : ‖aeval (S N_nonempty) p‖ = ‖(aeval (S N_nonempty) p - aeval (S M) p) + aeval (S M) p‖ := congrArg norm h_sum
      have h_norm_sum : ‖(aeval (S N_nonempty) p - aeval (S M) p) + aeval (S M) p‖ = ‖aeval (S N_nonempty) p - aeval (S M) p‖ := by
        exact norm_add_eq_left_of_norm_lt h_lt_nonempty'
      exact h_norm_eq.trans h_norm_sum
    rw [h_add_eq, ← h_sub_norm_eq, h_sub_eq_N_nonempty]

  let N_const_1 := 3 * N_nonempty + 2
  have hn_const_1_ge_base : N_const_1 ≥ N_base := by dsimp [N_const_1]; omega
  have hn_const_1_dvd : 3 ∣ N_const_1 + 1 := by
    use N_nonempty + 1
    dsimp [N_const_1]
    ring

  have h_deriv_pos_N_const_1 : (3 : ℝ) ^ V_deriv * ‖(N_const_1.factorial : Padic 3)‖ > 0 := by
    have : (3 : ℝ) ^ V_deriv > 0 := by positivity
    have : ‖(N_const_1.factorial : Padic 3)‖ > 0 := norm_pos_iff.mpr (by exact_mod_cast Nat.factorial_ne_zero N_const_1)
    positivity
  obtain ⟨M_const_1, hM_const_1⟩ := Metric.tendsto_atTop.mp h_lim_norm ((3 : ℝ) ^ V_deriv * ‖(N_const_1.factorial : Padic 3)‖) h_deriv_pos_N_const_1
  let M1 := max (N_const_1 + 1) M_const_1
  have hM1_ge : M1 ≥ N_const_1 + 1 := le_max_left _ _
  have h_M1_val : ‖aeval (S M1) p‖ < (3 : ℝ) ^ V_deriv * ‖(N_const_1.factorial : Padic 3)‖ := by
    have h_val := hM_const_1 M1 (le_max_right _ _)
    rw [_root_.dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h_val
    exact h_val

  have h_eq_norm_N_const_1 := norm_sub_eq_first p V_deriv N_base h_diff_eq hn_const_1_ge_base hn_const_1_dvd M1 hM1_ge

  have h_norm_N_const_1 : ‖aeval (S N_const_1) p‖ = (3 : ℝ) ^ V_deriv * ‖(N_const_1.factorial : Padic 3)‖ := by
    have h_sub_eq_symm : aeval (S M1) p - aeval (S N_const_1) p = - (aeval (S N_const_1) p - aeval (S M1) p) := by ring
    have h_sub_norm_eq : ‖aeval (S M1) p - aeval (S N_const_1) p‖ = ‖aeval (S N_const_1) p - aeval (S M1) p‖ := by
      rw [h_sub_eq_symm, norm_neg]
    have h_lt_nonempty'' : ‖aeval (S M1) p‖ < ‖aeval (S N_const_1) p - aeval (S M1) p‖ := by
      rwa [← h_sub_norm_eq, h_eq_norm_N_const_1]
    have h_add_eq : ‖aeval (S N_const_1) p‖ = ‖aeval (S N_const_1) p - aeval (S M1) p‖ := by
      have h_sum : aeval (S N_const_1) p = (aeval (S N_const_1) p - aeval (S M1) p) + aeval (S M1) p := by ring
      have h_norm_eq : ‖aeval (S N_const_1) p‖ = ‖(aeval (S N_const_1) p - aeval (S M1) p) + aeval (S M1) p‖ := congrArg norm h_sum
      have h_norm_sum : ‖(aeval (S N_const_1) p - aeval (S M1) p) + aeval (S M1) p‖ = ‖aeval (S N_const_1) p - aeval (S M1) p‖ := by
        exact norm_add_eq_left_of_norm_lt h_lt_nonempty''
      exact h_norm_eq.trans h_norm_sum
    rw [h_add_eq, ← h_sub_norm_eq, h_eq_norm_N_const_1]

  let N_const_2 := 3 * N_const_1 + 2
  have hn_const_2_ge_base : N_const_2 ≥ N_base := by dsimp [N_const_2]; omega
  have hn_const_2_dvd : 3 ∣ N_const_2 + 1 := by
    use N_const_1 + 1
    dsimp [N_const_2]
    ring

  have h_deriv_pos_N_const_2 : (3 : ℝ) ^ V_deriv * ‖(N_const_2.factorial : Padic 3)‖ > 0 := by
    have : (3 : ℝ) ^ V_deriv > 0 := by positivity
    have : ‖(N_const_2.factorial : Padic 3)‖ > 0 := norm_pos_iff.mpr (by exact_mod_cast Nat.factorial_ne_zero N_const_2)
    positivity
  obtain ⟨M_const_2, hM_const_2⟩ := Metric.tendsto_atTop.mp h_lim_norm ((3 : ℝ) ^ V_deriv * ‖(N_const_2.factorial : Padic 3)‖) h_deriv_pos_N_const_2
  let M2 := max (N_const_2 + 1) M_const_2
  have hM2_ge : M2 ≥ N_const_2 + 1 := le_max_left _ _
  have h_M2_val : ‖aeval (S M2) p‖ < (3 : ℝ) ^ V_deriv * ‖(N_const_2.factorial : Padic 3)‖ := by
    have h_val := hM_const_2 M2 (le_max_right _ _)
    rw [_root_.dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h_val
    exact h_val

  have h_eq_norm_N_const_2 := norm_sub_eq_first p V_deriv N_base h_diff_eq hn_const_2_ge_base hn_const_2_dvd M2 hM2_ge

  have h_norm_N_const_2 : ‖aeval (S N_const_2) p‖ = (3 : ℝ) ^ V_deriv * ‖(N_const_2.factorial : Padic 3)‖ := by
    have h_sub_eq_symm : aeval (S M2) p - aeval (S N_const_2) p = - (aeval (S N_const_2) p - aeval (S M2) p) := by ring
    have h_sub_norm_eq : ‖aeval (S M2) p - aeval (S N_const_2) p‖ = ‖aeval (S N_const_2) p - aeval (S M2) p‖ := by
      rw [h_sub_eq_symm, norm_neg]
    have h_lt_N_const' : ‖aeval (S M2) p‖ < ‖aeval (S N_const_2) p - aeval (S M2) p‖ := by
      rwa [← h_sub_norm_eq, h_eq_norm_N_const_2]
    have h_add_eq : ‖aeval (S N_const_2) p‖ = ‖aeval (S N_const_2) p - aeval (S M2) p‖ := by
      have h_sum : aeval (S N_const_2) p = (aeval (S N_const_2) p - aeval (S M2) p) + aeval (S M2) p := by ring
      have h_norm_eq : ‖aeval (S N_const_2) p‖ = ‖(aeval (S N_const_2) p - aeval (S M2) p) + aeval (S M2) p‖ := congrArg norm h_sum
      have h_norm_sum : ‖(aeval (S N_const_2) p - aeval (S M2) p) + aeval (S M2) p‖ = ‖aeval (S N_const_2) p - aeval (S M2) p‖ := by
        exact norm_add_eq_left_of_norm_lt h_lt_N_const'
      exact h_norm_eq.trans h_norm_sum
    rw [h_add_eq, ← h_sub_norm_eq, h_eq_norm_N_const_2]

  have h_diff_lt : ∀ m ≥ N_const_1, ‖aeval (S (m + 1)) p - aeval (S m) p‖ < (3 : ℝ) ^ V_0 := by
    intro m hm
    have hm_ge_base : m ≥ N_base := by dsimp [N_const_1, N_nonempty] at hm; omega
    rw [h_diff_eq m hm_ge_base]
    have h_deriv_pos : (3 : ℝ) ^ V_deriv > 0 := by positivity
    have h_mul_lt : ‖(m.factorial : Padic 3)‖ * (3 : ℝ) ^ V_deriv < (3 : ℝ) ^ (V_0 - V_deriv) * (3 : ℝ) ^ V_deriv := by
      apply mul_lt_mul_of_pos_right _ h_deriv_pos
      have h_eq_norm : (3 : ℝ) ^ (V_0 - V_deriv) = ‖(N_nonempty.factorial : Padic 3)‖ := by
        rw [hN_val] at h_norm_N_nonempty
        have h_deriv_pos : (3 : ℝ) ^ V_deriv > 0 := by positivity
        have h2 : (3 : ℝ) ^ V_0 = (3 : ℝ) ^ (V_0 - V_deriv) * (3 : ℝ) ^ V_deriv := by
          rw [← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_add (by norm_num)]
          congr 1
          push_cast
          ring
        rw [h2] at h_norm_N_nonempty
        rw [mul_comm] at h_norm_N_nonempty
        exact (mul_right_inj' (ne_of_gt h_deriv_pos)).mp h_norm_N_nonempty
      rw [h_eq_norm]
      have h_le : ‖(m.factorial : Padic 3)‖ ≤ ‖((N_nonempty + 1).factorial : Padic 3)‖ := norm_factorial_mono (by dsimp [N_const_1] at hm; omega)
      have h_lt := norm_factorial_lt_of_dvd_succ N_nonempty h_dvd_nonempty
      exact lt_of_le_of_lt h_le h_lt
    have h_mul_eq : (3 : ℝ) ^ (V_0 - V_deriv) * (3 : ℝ) ^ V_deriv = (3 : ℝ) ^ V_0 := by
      rw [← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    rw [h_mul_eq] at h_mul_lt
    rw [mul_comm] at h_mul_lt
    exact h_mul_lt

  have h_const : ∀ n ≥ N_const_1, ‖aeval (S n) p‖ = ‖aeval (S N_const_1) p‖ := by
    intro n hn
    apply norm_eq_of_diff_lt (by positivity) h_diff_lt N_const_1 (le_refl _) n hn (by rw [h_norm_N_const_1]; exact h_deriv_pos_N_const_1)

  have h_norm_N_const_eq := h_const N_const_2 (by dsimp [N_const_2, N_const_1]; omega)
  rw [h_norm_N_const_2, h_norm_N_const_1] at h_norm_N_const_eq
  have h_deriv_pos : (3 : ℝ) ^ V_deriv > 0 := by positivity
  have h_fac_eq := (mul_right_inj' (ne_of_gt h_deriv_pos)).mp h_norm_N_const_eq

  have h_fac_lt : ‖(N_const_2.factorial : Padic 3)‖ < ‖(N_const_1.factorial : Padic 3)‖ := by
    have h_le : ‖(N_const_2.factorial : Padic 3)‖ ≤ ‖((N_const_1 + 1).factorial : Padic 3)‖ := norm_factorial_mono (by dsimp [N_const_2]; omega)
    have h_lt := norm_factorial_lt_of_dvd_succ N_const_1 hn_const_1_dvd
    exact lt_of_le_of_lt h_le h_lt

  rw [h_fac_eq] at h_fac_lt
  exact lt_irrefl _ h_fac_lt

lemma eventually_constant_norm (p : ℚ[X]) (hp : p ≠ 0) :
  ∃ V : ℤ, ∃ N : ℕ, ∀ n ≥ N, ‖(aeval (S n) p : Padic 3)‖ = (3 : ℝ) ^ V := by
  have h_root : aeval xi_3 p ≠ 0 := by
    intro h_contra
    have h_alg : IsAlgebraic ℚ xi_3 := ⟨p, hp, h_contra⟩
    exact oeis_341685_conjecture_0 h_alg
  exact eventually_constant_norm_of_ne_zero p h_root
