import FormalConjectures.Util.ProblemImports

open Nat BigOperators Filter Topology Algebra Polynomial

noncomputable def S (n : ℕ) : Padic 3 :=
  (Finset.range n).sum (fun k : ℕ => (Nat.factorial k : Padic 3))

noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

lemma tendsto_S : Tendsto S atTop (nhds xi_3) := by
  have h_sum : HasSum (fun k : ℕ => (Nat.factorial k : Padic 3)) xi_3 := by
    exact (tsum_hasSum (fun k : ℕ => (Nat.factorial k : Padic 3))).hasSum
  exact h_sum

lemma S_succ (n : ℕ) : S (n + 1) = (n.factorial : Padic 3) + S n := by
  dsimp [S]
  rw [Finset.sum_range_succ]
  ring

lemma S_eq_algebraMap (n : ℕ) : S n = algebraMap ℚ (Padic 3) (∑ k ∈ Finset.range n, (Nat.factorial k : ℚ)) := by
  dsimp [S]
  rw [map_sum]
  congr 1
  ext k
  norm_cast

lemma S_mono : StrictMono (fun n : ℕ => (∑ k ∈ Finset.range n, (Nat.factorial k : ℚ))) := by
  intro n m h
  apply Finset.sum_lt_sum_of_subset
  · exact Finset.range_mono (by omega)
  · intro x hx h_not
    simp
  · use n
    simp only [Finset.mem_range, lt_self_iff_false, not_false_eq_true, Finset.mem_Ico, le_refl,
      true_and, h, and_true]
    positivity

lemma S_injective : Function.Injective S := by
  have h_inj : Function.Injective (algebraMap ℚ (Padic 3)) := FaithfulSMul.algebraMap_injective ℚ (Padic 3)
  intro n m h_eq
  rw [S_eq_algebraMap, S_eq_algebraMap] at h_eq
  have h_eq_ℚ := h_inj h_eq
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
  · have := S_mono h_lt
    linarith
  · have := S_mono h_gt
    linarith

lemma exists_ne_zero_of_injective {K : Type*} [Field K] [DecidableEq K] (p : K[X]) (hp : p ≠ 0) {f : ℕ → K} (hf : Function.Injective f) : ∃ n, p.eval (f n) ≠ 0 := by
  by_contra h_all
  push_neg at h_all
  have h_roots : ∀ n, p.IsRoot (f n) := fun n => h_all n
  have h_finite := p.roots_finite hp
  have h_subset : Set.range f ⊆ {x | p.IsRoot x} := by
    rintro x ⟨n, rfl⟩
    exact h_roots n
  have h_inf : (Set.range f).Infinite := Set.Infinite.mono (fun _ h => h) (Set.infinite_range_of_injective hf)
  have h_finite_subset := h_finite.subset h_subset
  exact h_finite_subset h_inf

lemma exists_S_ne_zero_ge (p : (Padic 3)[X]) (hp : p ≠ 0) (M : ℕ) : ∃ n ≥ M, p.eval (S n) ≠ 0 := by
  let g := fun (n : ℕ) => S (n + M)
  have h_inj : Function.Injective g := by
    intro n m h_eq
    dsimp [g] at h_eq
    have h_eq2 := S_injective h_eq
    omega
  obtain ⟨n, hn⟩ := exists_ne_zero_of_injective p hp h_inj
  use n + M, (by omega), hn

lemma norm_add_eq_left_of_norm_lt {S : Type*} [NormedAddCommGroup S] [IsUltrametricDist S] {x y : S} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  have h_le := IsUltrametricDist.norm_add_le_max x y
  rcases lt_or_eq_of_le h_le with h_lt | h_eq
  · exfalso
    have h_lt' : ‖x + y - y‖ ≤ max ‖x + y‖ ‖-y‖ := IsUltrametricDist.norm_add_le_max (x + y) (-y)
    rw [norm_neg] at h_lt'
    rw [add_sub_cancel] at h_lt'
    have h_max_eq : max ‖x + y‖ ‖y‖ = ‖y‖ := by
      rw [max_eq_right_iff]
      linarith
    rw [h_max_eq] at h_lt'
    linarith
  · have h_max_eq : max ‖x‖ ‖y‖ = ‖x‖ := max_eq_left (le_of_lt h)
    rw [h_max_eq] at h_eq
    exact h_eq

lemma norm_sub_le_of_diff_lt {S : Type*} [NormedAddCommGroup S] [IsUltrametricDist S] {x : ℕ → S} {K : ℕ} {V : ℝ} (hV : V > 0) (h_diff : ∀ n ≥ K, ‖x (n + 1) - x n‖ < V) :
  ∀ m ≥ K, ∀ n ≥ m, ‖x n - x m‖ < V := by
  intro m hm n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [sub_self, _root_.norm_zero]
    exact hV
  | succ k hk ih =>
    have h_eq : x (k + 1) - x m = (x (k + 1) - x k) + (x k - x m) := by ring
    rw [h_eq]
    have h_max := IsUltrametricDist.norm_add_le_max (x (k + 1) - x k) (x k - x m)
    apply lt_of_le_of_lt h_max
    rw [max_lt_iff]
    refine ⟨h_diff k (by omega), ih⟩

lemma norm_eq_of_diff_lt {S : Type*} [NormedAddCommGroup S] [IsUltrametricDist S] {x : ℕ → S} {K : ℕ} {V : ℝ} (hV : V > 0) (h_diff : ∀ n ≥ K, ‖x (n + 1) - x n‖ < V) :
  ∀ m ≥ K, ∀ n ≥ m, ‖x n‖ ≥ V → ‖x n‖ = ‖x m‖ := by
  intro m hm n hn h_ge
  have h_sub := norm_sub_le_of_diff_lt hV h_diff m hm n hn
  have h_eq : x n = x m + (x n - x m) := by ring
  have h_eq_norm : ‖x n‖ = ‖x m + (x n - x m)‖ := congrArg norm h_eq
  have h_lt : ‖x n - x m‖ < ‖x n‖ := lt_of_lt_of_le h_sub h_ge
  have h_sub_eq_symm : x n - x m = - (x m - x n) := by ring
  have h_norm_symm : ‖x n - x m‖ = ‖x m - x n‖ := by rw [h_sub_eq_symm, norm_neg]
  rw [h_norm_symm] at h_lt
  have h_decomp : x m = x n + (x m - x n) := by ring
  have h_norm_decomp : ‖x m‖ = ‖x n + (x m - x n)‖ := congrArg norm h_decomp
  rw [norm_add_eq_left_of_norm_lt h_lt] at h_norm_decomp
  exact h_norm_decomp.symm

lemma norm_add_sum_eq_first {S : Type*} [NormedAddCommGroup S] [IsUltrametricDist S] {A : S} {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → S) (h : ∀ i ∈ s, ‖f i‖ < ‖A‖) : ‖A + ∑ i ∈ s, f i‖ = ‖A‖ := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty, add_zero]
  | insert hi ih =>
    rw [Finset.sum_insert hi]
    have h_eq : A + (f hi + ∑ x ∈ s, f x) = (A + ∑ x ∈ s, f x) + f hi := by ring
    rw [h_eq]
    have h_lt : ∀ i ∈ s, ‖f i‖ < ‖A‖ := fun i h => h _ (Finset.mem_insert_of_mem h)
    have h_eq2 : ‖A + ∑ x ∈ s, f x‖ = ‖A‖ := ih h_lt
    rw [norm_add_eq_left_of_norm_lt]
    · exact h_eq2
    · rw [h_eq2]
      exact h _ (Finset.mem_insert_self _ _)

lemma taylor_expansion_exact {R : Type*} [CommRing R] (f : R[X]) (r s : R) :
  eval (r + s) f = eval r f + ∑ i ∈ Finset.range f.natDegree, eval r (hasseDeriv (i + 1) f) * s ^ (i + 1) := by
  have h : eval (r + s) f = ∑ i ∈ Finset.range (f.natDegree + 1), eval r (hasseDeriv i f) * s ^ i := by
    rw [eval_eq_sum_hasseDeriv]
  rw [h]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one, hasseDeriv_zero, eval_add]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma hasseDeriv_map_local {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : R[X]) (k : ℕ) :
  hasseDeriv k (p.map f) = (hasseDeriv k p).map f := by
  exact (hasseDeriv_map f p k).symm

lemma taylor_expansion_aeval (p : ℚ[X]) (r s : Padic 3) :
  aeval (r + s) p = aeval r p + ∑ i ∈ Finset.range p.natDegree, aeval r (hasseDeriv (i + 1) p) * s ^ (i + 1) := by
  dsimp [aeval_def]
  have h_eq := taylor_expansion_exact (p.map (algebraMap ℚ (Padic 3))) r s
  rw [eval_map] at h_eq
  · rw [h_eq]
    congr 2
    apply Finset.sum_congr
    · congr 1
      exact (natDegree_map (algebraMap ℚ (Padic 3)) p).symm
    · intro x _
      rw [hasseDeriv_map_local]
      rfl
  · exact p

lemma pow_prime_dvd_factorial_mul_self (p : ℕ) [hp : Fact p.Prime] (r : ℕ) : p ^ r ∣ (p * r).factorial := sorry
lemma pow_prime_dvd_factorial_of_mul_le (p : ℕ) [hp : Fact p.Prime] (r : ℕ) (n : ℕ) (h : p * r ≤ n) : p ^ r ∣ n.factorial := sorry
lemma norm_factorial_le (r : ℕ) (x : ℕ) (h : 3 * r ≤ x) : ‖(x.factorial : Padic 3)‖ ≤ (3 : ℝ) ^ (-(r : ℤ)) := sorry
lemma tendsto_norm_factorial_zero : Tendsto (fun x : ℕ => ‖(x.factorial : Padic 3)‖) atTop (𝓝 0) := sorry
lemma le_max_of_fn (f : ℕ → ℕ) (d : ℕ) {i : ℕ} (hi : i < d) : f i ≤ max_of_fn f d := sorry
lemma pow_le_self_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (i : ℕ) (hi : i ≥ 1) : x ^ i ≤ x := sorry
lemma valuation_eventually_constant_of_deg_zero (p : ℚ[X]) (hp : p ≠ 0) (hdeg : p.natDegree = 0) (S : ℕ → Padic 3) :
  ∃ V : ℤ, ∃ N : ℕ, ∀ n ≥ N, ‖(aeval (S n) p : Padic 3)‖ = (3 : ℝ) ^ V := sorry
lemma antitone_eventually_constant (f : ℕ → ℤ) (hf : ∀ m, f (m + 1) ≤ f m) (b : ℤ) (hb : ∀ m, b ≤ f m) :
  ∃ V, ∃ M_0, ∀ M ≥ M_0, f M = V := sorry
lemma norm_S_le (n : ℕ) : ‖S n‖ ≤ 1 := sorry
lemma lt_three_pow (v : ℕ) : v < 3 ^ v := sorry
lemma zpow_three_ge_self (v : ℤ) : (3 : ℝ) ^ v ≥ v := sorry
lemma exists_int_bound_of_zpow_le (C : ℝ) : ∃ B : ℤ, ∀ v : ℤ, (3 : ℝ) ^ v ≤ C → v ≤ B := sorry
lemma norm_aeval_S_le (p : ℚ[X]) : ∃ C : ℝ, ∀ n : ℕ, ‖aeval (S n) p‖ ≤ C := sorry
lemma exists_max_valuation_ge (p : ℚ[X]) (hp : p ≠ 0) (M : ℕ) :
  ∃ V_max : ℤ, ∃ N_max ≥ M, aeval (S N_max) p ≠ 0 ∧
  (∀ n ≥ M, aeval (S n) p ≠ 0 → - (aeval (S n) p : Padic 3).valuation ≤ V_max) ∧
  - (aeval (S N_max) p : Padic 3).valuation = V_max := sorry

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

  let N_const := 3 * N_nonempty + 2
  have hn_const_ge_base : N_const ≥ N_base := by dsimp [N_const]; omega
  have hn_const_ge_nonempty : N_const ≥ N_nonempty + 1 := by dsimp [N_const]; omega
  have hn_const_dvd : 3 ∣ N_const + 1 := by
    use N_nonempty + 1
    dsimp [N_const]
    ring

  have h_deriv_pos_N_const : (3 : ℝ) ^ V_deriv * ‖(N_const.factorial : Padic 3)‖ > 0 := by
    have : (3 : ℝ) ^ V_deriv > 0 := by positivity
    have : ‖(N_const.factorial : Padic 3)‖ > 0 := norm_pos_iff.mpr (by exact_mod_cast Nat.factorial_ne_zero N_const)
    positivity
  obtain ⟨M_const, hM_const⟩ := Metric.tendsto_atTop.mp h_lim_norm ((3 : ℝ) ^ V_deriv * ‖(N_const.factorial : Padic 3)‖) h_deriv_pos_N_const
  let M2 := max (N_const + 1) M_const
  have hM2_ge : M2 ≥ N_const + 1 := le_max_left _ _
  have h_M2_val : ‖aeval (S M2) p‖ < (3 : ℝ) ^ V_deriv * ‖(N_const.factorial : Padic 3)‖ := by
    have h_val := hM_const M2 (le_max_right _ _)
    rw [_root_.dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h_val
    exact h_val

  have h_eq_norm_N_const := norm_sub_eq_first p V_deriv N_base h_diff_eq hn_const_ge_base hn_const_dvd M2 hM2_ge

  have h_norm_N_const : ‖aeval (S N_const) p‖ = (3 : ℝ) ^ V_deriv * ‖(N_const.factorial : Padic 3)‖ := by
    have h_sub_eq_symm : aeval (S M2) p - aeval (S N_const) p = - (aeval (S N_const) p - aeval (S M2) p) := by ring
    have h_sub_norm_eq : ‖aeval (S M2) p - aeval (S N_const) p‖ = ‖aeval (S N_const) p - aeval (S M2) p‖ := by
      rw [h_sub_eq_symm, norm_neg]
    have h_lt_N_const' : ‖aeval (S M2) p‖ < ‖aeval (S N_const) p - aeval (S M2) p‖ := by
      rwa [← h_sub_norm_eq, h_eq_norm_N_const]
    have h_add_eq : ‖aeval (S N_const) p‖ = ‖aeval (S N_const) p - aeval (S M2) p‖ := by
      have h_sum : aeval (S N_const) p = (aeval (S N_const) p - aeval (S M2) p) + aeval (S M2) p := by ring
      have h_norm_eq : ‖aeval (S N_const) p‖ = ‖(aeval (S N_const) p - aeval (S M2) p) + aeval (S M2) p‖ := congrArg norm h_sum
      have h_norm_sum : ‖(aeval (S N_const) p - aeval (S M2) p) + aeval (S M2) p‖ = ‖aeval (S N_const) p - aeval (S M2) p‖ := by
        exact norm_add_eq_left_of_norm_lt h_lt_N_const'
      exact h_norm_eq.trans h_norm_sum
    rw [h_add_eq, ← h_sub_norm_eq, h_eq_norm_N_const]

  have h_diff_lt : ∀ m ≥ N_nonempty, ‖aeval (S (m + 1)) p - aeval (S m) p‖ < (3 : ℝ) ^ V_0 := by
    intro m hm
    have hm_ge_base : m ≥ N_base := by dsimp [N_nonempty] at hm; omega
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
      have h_le : ‖(m.factorial : Padic 3)‖ ≤ ‖((N_nonempty + 1).factorial : Padic 3)‖ := norm_factorial_mono (by omega)
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

  have h_const : ∀ n ≥ N_nonempty, ‖aeval (S n) p‖ = ‖aeval (S N_nonempty) p‖ := by
    intro n hn
    apply norm_eq_of_diff_lt (by positivity) h_diff_lt N_nonempty (le_refl _) n hn (by rw [hN_val]; positivity)

  have h_norm_N_const_eq := h_const N_const (by dsimp [N_const]; omega)
  rw [h_norm_N_const, h_norm_N_nonempty] at h_norm_N_const_eq
  have h_deriv_pos : (3 : ℝ) ^ V_deriv > 0 := by positivity
  have h_fac_eq := (mul_right_inj' (ne_of_gt h_deriv_pos)).mp h_norm_N_const_eq

  have h_fac_lt : ‖(N_const.factorial : Padic 3)‖ < ‖(N_nonempty.factorial : Padic 3)‖ := by
    have h_le : ‖(N_const.factorial : Padic 3)‖ ≤ ‖((N_nonempty + 1).factorial : Padic 3)‖ := norm_factorial_mono (by dsimp [N_const]; omega)
    have h_lt := norm_factorial_lt_of_dvd_succ N_nonempty h_dvd_nonempty
    exact lt_of_le_of_lt h_le h_lt

  rw [h_fac_eq] at h_fac_lt
  exact lt_irrefl _ h_fac_lt

