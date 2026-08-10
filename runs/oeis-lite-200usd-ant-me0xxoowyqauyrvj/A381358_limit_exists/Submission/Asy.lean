import FormalConjectures.Util.ProblemImports

open scoped BigOperators NNReal
open Filter Topology

namespace Asy

-- Activate the L∞ operator norm (sup over rows of L1 norm) on square matrices.
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing

noncomputable def Amat : Matrix (Fin 7) (Fin 7) ℝ :=
  !![3,-3,1,0,0,0,1; 1,0,0,0,0,0,0; 0,1,0,0,0,0,0; 0,0,1,0,0,0,0; 0,0,0,1,0,0,0; 0,0,0,0,1,0,0; 0,0,0,0,0,1,0]

noncomputable def NN (L : ℕ → ℝ) (k : ℕ) : Matrix (Fin 7) (Fin 7) ℝ :=
  Matrix.of (fun i j => L (k + (6 - i.val) + j.val))

-- test: norm_mul_le works
example (X Y : Matrix (Fin 7) (Fin 7) ℝ) : ‖X * Y‖ ≤ ‖X‖ * ‖Y‖ := norm_mul_le X Y

example : ‖(1 : Matrix (Fin 7) (Fin 7) ℝ)‖ = 1 := norm_one

set_option maxHeartbeats 4000000 in
theorem AN_step (L : ℕ → ℝ)
    (hrec : ∀ k, 4 ≤ k → L (k+7) = 3 * L (k+6) - 3 * L (k+5) + L (k+4) + L k)
    (k : ℕ) (hk : 4 ≤ k) :
    Amat * NN L k = NN L (k+1) := by
  ext i j
  fin_cases i
  · -- row 0
    fin_cases j <;>
    · simp only [Amat, NN, Matrix.mul_apply, Fin.sum_univ_seven, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
        Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val', Fin.isValue,
        zero_mul, one_mul, add_zero, zero_add, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, Nat.reduceSub]
      norm_num
      simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero]
      first
      | (have h := hrec (k+0) (by omega); simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at h; linarith [h])
      | (have h := hrec (k+1) (by omega); simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at h; linarith [h])
      | (have h := hrec (k+2) (by omega); simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at h; linarith [h])
      | (have h := hrec (k+3) (by omega); simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at h; linarith [h])
      | (have h := hrec (k+4) (by omega); simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at h; linarith [h])
      | (have h := hrec (k+5) (by omega); simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at h; linarith [h])
      | (have h := hrec (k+6) (by omega); simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at h; linarith [h])
  · show (Amat * NN L k) (1:Fin 7) j = NN L (k+1) (1:Fin 7) j
    simp only [Amat, NN, Matrix.mul_apply, Fin.sum_univ_seven, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val', Fin.isValue,
      zero_mul, one_mul, add_zero, zero_add, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, Nat.reduceSub]
  · show (Amat * NN L k) (2:Fin 7) j = NN L (k+1) (2:Fin 7) j
    simp only [Amat, NN, Matrix.mul_apply, Fin.sum_univ_seven, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val', Fin.isValue,
      zero_mul, one_mul, add_zero, zero_add, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, Nat.reduceSub]
    congr 1
  · show (Amat * NN L k) (3:Fin 7) j = NN L (k+1) (3:Fin 7) j
    simp only [Amat, NN, Matrix.mul_apply, Fin.sum_univ_seven, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val', Fin.isValue,
      zero_mul, one_mul, add_zero, zero_add, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, Nat.reduceSub]
    congr 1
  · show (Amat * NN L k) (4:Fin 7) j = NN L (k+1) (4:Fin 7) j
    simp only [Amat, NN, Matrix.mul_apply, Fin.sum_univ_seven, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val', Fin.isValue,
      zero_mul, one_mul, add_zero, zero_add, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, Nat.reduceSub]
    congr 1
  · show (Amat * NN L k) (5:Fin 7) j = NN L (k+1) (5:Fin 7) j
    simp only [Amat, NN, Matrix.mul_apply, Fin.sum_univ_seven, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val', Fin.isValue,
      zero_mul, one_mul, add_zero, zero_add, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, Nat.reduceSub]
    congr 1
  · show (Amat * NN L k) (6:Fin 7) j = NN L (k+1) (6:Fin 7) j
    simp only [Amat, NN, Matrix.mul_apply, Fin.sum_univ_seven, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val', Fin.isValue,
      zero_mul, one_mul, add_zero, zero_add, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, Nat.reduceSub]
    congr 1

/-! ### Norm helper lemmas for the L∞ operator norm -/

theorem nnentry_le (A : Matrix (Fin 7) (Fin 7) ℝ) (i j : Fin 7) : ‖A i j‖₊ ≤ ‖A‖₊ := by
  rw [Matrix.linfty_opNNNorm_def]
  calc ‖A i j‖₊ ≤ ∑ j', ‖A i j'‖₊ :=
        Finset.single_le_sum (f := fun j' => ‖A i j'‖₊) (fun _ _ => zero_le _) (Finset.mem_univ j)
    _ ≤ _ := Finset.le_sup (f := fun i => ∑ j', ‖A i j'‖₊) (Finset.mem_univ i)

theorem entry_le (A : Matrix (Fin 7) (Fin 7) ℝ) (i j : Fin 7) : |A i j| ≤ ‖A‖ := by
  have h1 : ‖A i j‖ ≤ ‖A‖ := by exact_mod_cast nnentry_le A i j
  rwa [Real.norm_eq_abs] at h1

theorem nn_le_of_abs_le (x b : ℝ) (h : |x| ≤ b) : ‖x‖₊ ≤ b.toNNReal := by
  rw [← Real.norm_eq_abs] at h
  have : ‖x‖₊ ≤ (b.toNNReal : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_trans (norm_nonneg _) h)]
    exact h
  exact this

theorem linftyOp_le (A : Matrix (Fin 7) (Fin 7) ℝ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ i j, |A i j| ≤ b) : ‖A‖ ≤ 7 * b := by
  have key : ‖A‖₊ ≤ 7 * b.toNNReal := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i _
    calc (∑ j, ‖A i j‖₊) ≤ ∑ _j : Fin 7, b.toNNReal :=
            Finset.sum_le_sum (fun j _ => nn_le_of_abs_le _ _ (h i j))
      _ = 7 * b.toNNReal := by rw [Finset.sum_const]; simp
  have h2 : ‖A‖ ≤ ((7 * b.toNNReal : ℝ≥0) : ℝ) := by exact_mod_cast key
  rwa [NNReal.coe_mul, Real.coe_toNNReal _ hb] at h2

/-! ### Powers of `Amat` and the matrix recurrence -/

theorem AN_pow (L : ℕ → ℝ)
    (hrec : ∀ k, 4 ≤ k → L (k+7) = 3 * L (k+6) - 3 * L (k+5) + L (k+4) + L k)
    (m : ℕ) : Amat ^ m * NN L 5 = NN L (5 + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, ih, AN_step L hrec (5+m) (by omega)]
    congr 1

theorem Apow_eq (L : ℕ → ℝ)
    (hrec : ∀ k, 4 ≤ k → L (k+7) = 3 * L (k+6) - 3 * L (k+5) + L (k+4) + L k)
    (C : Matrix (Fin 7) (Fin 7) ℝ) (hC : NN L 5 * C = 1) (m : ℕ) :
    Amat ^ m = NN L (5 + m) * C := by
  have h := AN_pow L hrec m
  calc Amat ^ m = Amat ^ m * (NN L 5 * C) := by rw [hC, mul_one]
    _ = (Amat ^ m * NN L 5) * C := by rw [mul_assoc]
    _ = NN L (5 + m) * C := by rw [h]

/-! ### L-based norm bounds -/

theorem NN_entry00 (L : ℕ → ℝ) (k : ℕ) : NN L k 0 0 = L (k + 6) := by
  simp [NN]

theorem NN_norm_le (L : ℕ → ℝ) (hLnn : ∀ n, 0 ≤ L n) (hmono : Monotone L) (k : ℕ) :
    ‖NN L k‖ ≤ 7 * L (k + 12) := by
  apply linftyOp_le _ _ (hLnn _)
  intro i j
  have hb : k + (6 - i.val) + j.val ≤ k + 12 := by
    have := i.isLt; have := j.isLt; omega
  rw [NN, Matrix.of_apply, abs_of_nonneg (hLnn _)]
  exact hmono hb

theorem NN_ne_zero (L : ℕ → ℝ) (hpos : 0 < L (k + 6)) : NN L k ≠ 0 := by
  intro hz
  have : NN L k 0 0 = 0 := by rw [hz]; rfl
  rw [NN_entry00] at this
  linarith

theorem normpow_pos (L : ℕ → ℝ)
    (hrec : ∀ k, 4 ≤ k → L (k+7) = 3 * L (k+6) - 3 * L (k+5) + L (k+4) + L k)
    (hmono : Monotone L) (hpos : 0 < L 11) (m : ℕ) : 0 < ‖Amat ^ m‖ := by
  rw [norm_pos_iff]
  intro hz
  have h := AN_pow L hrec m
  rw [hz, zero_mul] at h
  have hne : NN L (5 + m) ≠ 0 := by
    apply NN_ne_zero
    have : 0 < L 11 := hpos
    have : (11 : ℕ) ≤ 5 + m + 6 := by omega
    calc (0:ℝ) < L 11 := hpos
      _ ≤ L (5 + m + 6) := hmono this
  exact hne h.symm

theorem normpow_lb (L : ℕ → ℝ) (hLnn : ∀ n, 0 ≤ L n)
    (hrec : ∀ k, 4 ≤ k → L (k+7) = 3 * L (k+6) - 3 * L (k+5) + L (k+4) + L k)
    (n : ℕ) : L (n + 11) ≤ ‖Amat ^ n‖ * ‖NN L 5‖ := by
  have h := AN_pow L hrec n
  have h1 : L (5 + n + 6) ≤ ‖NN L (5 + n)‖ := by
    rw [← NN_entry00 L (5 + n)]
    have h2 := entry_le (NN L (5 + n)) 0 0
    rwa [abs_of_nonneg (by rw [NN_entry00]; exact hLnn _)] at h2
  have h3 : ‖NN L (5 + n)‖ ≤ ‖Amat ^ n‖ * ‖NN L 5‖ := by
    rw [← h]; exact norm_mul_le _ _
  have he : 5 + n + 6 = n + 11 := by omega
  rw [he] at h1
  linarith

theorem normpow_ub (L : ℕ → ℝ) (hLnn : ∀ n, 0 ≤ L n) (hmono : Monotone L)
    (hrec : ∀ k, 4 ≤ k → L (k+7) = 3 * L (k+6) - 3 * L (k+5) + L (k+4) + L k)
    (C : Matrix (Fin 7) (Fin 7) ℝ) (hC : NN L 5 * C = 1) (n : ℕ) :
    ‖Amat ^ n‖ ≤ 7 * L (n + 17) * ‖C‖ := by
  rw [Apow_eq L hrec C hC n]
  calc ‖NN L (5 + n) * C‖ ≤ ‖NN L (5 + n)‖ * ‖C‖ := norm_mul_le _ _
    _ ≤ 7 * L ((5 + n) + 12) * ‖C‖ := by
        apply mul_le_mul_of_nonneg_right (NN_norm_le L hLnn hmono (5 + n)) (norm_nonneg _)
    _ = 7 * L (n + 17) * ‖C‖ := by rw [show (5 + n) + 12 = n + 17 from by omega]

theorem L_ub (L : ℕ → ℝ) (hLnn : ∀ n, 0 ≤ L n)
    (hrec : ∀ k, 4 ≤ k → L (k+7) = 3 * L (k+6) - 3 * L (k+5) + L (k+4) + L k)
    (n : ℕ) (hn : 11 ≤ n) : L n ≤ ‖Amat ^ (n - 11)‖ * ‖NN L 5‖ := by
  have h := normpow_lb L hLnn hrec (n - 11)
  rwa [show (n - 11) + 11 = n from by omega] at h

/-! ### Shift/limit helpers -/

theorem shift_nat_atTop (d : ℕ) : Tendsto (fun n => n - d) atTop atTop :=
  Filter.tendsto_atTop.2 (fun N => eventually_atTop.2 ⟨N+d, fun n hn => by omega⟩)

theorem shift_tendsto (c : ℕ → ℝ) (γ B : ℝ) (d : ℕ)
    (hc : Tendsto (fun n => c n / n) atTop (𝓝 γ)) :
    Tendsto (fun n => (c (n - d) + B) / n) atTop (𝓝 γ) := by
  have hB : Tendsto (fun n : ℕ => B / (n:ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat B
  have ha : Tendsto (fun n => c (n - d) / (↑(n - d) : ℝ)) atTop (𝓝 γ) := hc.comp (shift_nat_atTop d)
  have hb : Tendsto (fun n : ℕ => (↑(n - d) : ℝ) / (n:ℝ)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ => 1 - (d:ℝ) / (n:ℝ)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (d:ℝ))
    rw [sub_zero] at h0
    refine h0.congr' ?_
    filter_upwards [eventually_ge_atTop (d+1)] with n hn
    have hle : d ≤ n := by omega
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    rw [Nat.cast_sub hle]
    field_simp
  have hprod : Tendsto (fun n => (c (n - d) / (↑(n - d):ℝ)) * ((↑(n - d):ℝ) / (n:ℝ))) atTop (𝓝 (γ * 1)) :=
    ha.mul hb
  rw [mul_one] at hprod
  have hsum := hprod.add hB
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (d+1)] with n hn
  have hnd : (↑(n - d):ℝ) ≠ 0 := by
    have : 0 < n - d := by omega
    positivity
  field_simp

/-! ### The growth-rate limit -/

theorem loglim (L : ℕ → ℝ) (hLnn : ∀ n, 0 ≤ L n)
    (hrec : ∀ k, 4 ≤ k → L (k+7) = 3 * L (k+6) - 3 * L (k+5) + L (k+4) + L k)
    (hmono : Monotone L) (hpos : 0 < L 11)
    (C : Matrix (Fin 7) (Fin 7) ℝ) (hC : NN L 5 * C = 1) :
    ∃ γ : ℝ, Tendsto (fun n => Real.log (L n) / n) atTop (𝓝 γ) := by
  set c : ℕ → ℝ := fun k => Real.log ‖Amat ^ k‖ with hc_def
  have hnp : ∀ m, 0 < ‖Amat ^ m‖ := normpow_pos L hrec hmono hpos
  -- positivity of the two constant matrices
  have hNN5_pos : 0 < ‖NN L 5‖ := by
    have : 0 < L 11 := hpos
    have h2 : L (5 + 6) ≤ ‖NN L 5‖ := by
      rw [← NN_entry00 L 5]
      have h3 := entry_le (NN L 5) 0 0
      rwa [abs_of_nonneg (by rw [NN_entry00]; exact hLnn _)] at h3
    have : (11:ℕ) = 5 + 6 := by norm_num
    rw [this] at hpos; linarith
  have hC_pos : 0 < ‖C‖ := by
    rw [norm_pos_iff]
    rintro rfl
    rw [mul_zero] at hC
    exact (one_ne_zero hC.symm)
  -- subadditivity
  have hsub : Subadditive c := by
    intro m n
    show Real.log ‖Amat ^ (m+n)‖ ≤ Real.log ‖Amat ^ m‖ + Real.log ‖Amat ^ n‖
    rw [pow_add, ← Real.log_mul (ne_of_gt (hnp m)) (ne_of_gt (hnp n))]
    apply Real.log_le_log
    · rw [← pow_add]; exact hnp _
    · exact norm_mul_le _ _
  -- lower bound on c n : ‖Amat^n‖ ≥ L 11 / ‖NN L 5‖
  set P : ℝ := L 11 / ‖NN L 5‖ with hP_def
  have hP_pos : 0 < P := div_pos hpos hNN5_pos
  have hcn_lb : ∀ n, Real.log P ≤ c n := by
    intro n
    apply Real.log_le_log hP_pos
    rw [hP_def, div_le_iff₀ hNN5_pos]
    calc L 11 ≤ L (n + 11) := hmono (by omega)
      _ ≤ ‖Amat ^ n‖ * ‖NN L 5‖ := normpow_lb L hLnn hrec n
  -- BddBelow
  have hbb : BddBelow (Set.range fun n => c n / n) := by
    refine ⟨min 0 (Real.log P), ?_⟩
    rintro x ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with h0 | hn1
    · subst h0; simp only [Nat.cast_zero, div_zero]; exact min_le_left _ _
    · have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
      have hge : Real.log P ≤ c n := hcn_lb n
      rcases le_total 0 (Real.log P) with hlp | hlp
      · have : (0:ℝ) ≤ c n / n := div_nonneg (le_trans hlp hge) (le_of_lt hnpos)
        exact le_trans (min_le_left _ _) this
      · have hmin : min 0 (Real.log P) = Real.log P := min_eq_right hlp
        rw [hmin]
        rw [le_div_iff₀ hnpos]
        have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn1
        nlinarith [hge, hlp, h1, mul_nonneg (neg_nonneg.2 hlp) (by linarith : (0:ℝ) ≤ (n:ℝ) - 1)]
  obtain ⟨γ, hγ⟩ : ∃ γ, Tendsto (fun n => c n / n) atTop (𝓝 γ) :=
    ⟨hsub.lim, hsub.tendsto_lim hbb⟩
  refine ⟨γ, ?_⟩
  -- squeeze
  have hupper : Tendsto (fun n => (c (n - 11) + Real.log ‖NN L 5‖) / n) atTop (𝓝 γ) :=
    shift_tendsto c γ (Real.log ‖NN L 5‖) 11 hγ
  have hlower : Tendsto (fun n => (c (n - 17) + (-(Real.log 7 + Real.log ‖C‖))) / n) atTop (𝓝 γ) :=
    shift_tendsto c γ (-(Real.log 7 + Real.log ‖C‖)) 17 hγ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · -- lower : (c(n-17) - (log7+log‖C‖))/n ≤ log L n / n
    filter_upwards [eventually_ge_atTop 17] with n hn
    have hLpos : 0 < L n := lt_of_lt_of_le hpos (hmono (by omega))
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    -- ‖Amat^(n-17)‖ ≤ 7 * L n * ‖C‖
    have hub := normpow_ub L hLnn hmono hrec C hC (n - 17)
    rw [show (n - 17) + 17 = n from by omega] at hub
    have hpos7 : (0:ℝ) < 7 * L n * ‖C‖ := by positivity
    have hlog : c (n - 17) ≤ Real.log 7 + Real.log (L n) + Real.log ‖C‖ := by
      have := Real.log_le_log (hnp (n - 17)) hub
      rw [Real.log_mul (by positivity) (ne_of_gt hC_pos),
          Real.log_mul (by norm_num) (ne_of_gt hLpos)] at this
      linarith
    rw [div_le_div_iff_of_pos_right hnpos]
    linarith
  · -- upper : log L n / n ≤ (c(n-11) + log‖NN L5‖)/n
    filter_upwards [eventually_ge_atTop 17] with n hn
    have hLpos : 0 < L n := lt_of_lt_of_le hpos (hmono (by omega))
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hub := L_ub L hLnn hrec n (by omega)
    have hlog : Real.log (L n) ≤ c (n - 11) + Real.log ‖NN L 5‖ := by
      have := Real.log_le_log hLpos hub
      rwa [Real.log_mul (ne_of_gt (hnp (n-11))) (ne_of_gt hNN5_pos)] at this
    rw [div_le_div_iff_of_pos_right hnpos]
    linarith

/-! ### From log-limit to rpow-limit, and the row-sum sandwich -/

theorem lognat_div_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (n:ℝ) / (n:ℝ)) atTop (𝓝 0) := by
  have h := Real.isLittleO_log_id_atTop
  have h2 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using h.tendsto_div_nhds_zero
  exact h2.comp tendsto_natCast_atTop_atTop

theorem rpow_tendsto_of_loglim (f : ℕ → ℝ) (γ : ℝ)
    (hpos : ∀ᶠ n in atTop, 0 < f n)
    (hlog : Tendsto (fun n => Real.log (f n) / n) atTop (𝓝 γ)) :
    Tendsto (fun n => (f n) ^ ((n:ℝ)⁻¹)) atTop (𝓝 (Real.exp γ)) := by
  have hexp : Tendsto (fun n => Real.exp (Real.log (f n) / n)) atTop (𝓝 (Real.exp γ)) :=
    (Real.continuous_exp.tendsto γ).comp hlog
  refine hexp.congr' ?_
  filter_upwards [hpos] with n hfn
  rw [Real.rpow_def_of_pos hfn, div_eq_mul_inv]

theorem S_loglim (L S : ℕ → ℝ) (γ : ℝ) (N : ℕ)
    (hL : Tendsto (fun n => Real.log (L n) / n) atTop (𝓝 γ))
    (hLpos : ∀ n, N ≤ n → 0 < L (n-1))
    (hlb : ∀ n, N ≤ n → L (n-1) ≤ S n)
    (hub : ∀ n, N ≤ n → S n ≤ (n:ℝ) * L (n-1)) :
    Tendsto (fun n => Real.log (S n) / n) atTop (𝓝 γ) := by
  have hlow : Tendsto (fun n => (Real.log (L (n-1)) + 0) / n) atTop (𝓝 γ) :=
    shift_tendsto (fun k => Real.log (L k)) γ 0 1 hL
  have hup : Tendsto (fun n : ℕ => (Real.log (n:ℝ) + Real.log (L (n-1))) / (n:ℝ)) atTop (𝓝 γ) := by
    have e : (fun n:ℕ => (Real.log (n:ℝ) + Real.log (L (n-1)))/(n:ℝ))
           = fun n : ℕ => Real.log (n:ℝ) / (n:ℝ) + (Real.log (L (n-1)) + 0)/(n:ℝ) := by
      funext n; rw [add_zero]; ring
    rw [e]
    have := (lognat_div_tendsto_zero).add hlow
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hNn : N ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
    have hLp : 0 < L (n-1) := hLpos n hNn
    rw [add_zero, div_le_div_iff_of_pos_right hnpos]
    exact Real.log_le_log hLp (hlb n hNn)
  · filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hNn : N ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
    have hLp : 0 < L (n-1) := hLpos n hNn
    have hSp : 0 < S n := lt_of_lt_of_le hLp (hlb n hNn)
    rw [div_le_div_iff_of_pos_right hnpos]
    have h2 := Real.log_le_log hSp (hub n hNn)
    rwa [Real.log_mul (by exact_mod_cast (by omega : (0:ℕ) < n).ne') (ne_of_gt hLp)] at h2

/-! ### Top-level engine -/

theorem main_engine (L S : ℕ → ℝ)
    (hLnn : ∀ n, 0 ≤ L n)
    (hrec : ∀ k, 4 ≤ k → L (k+7) = 3 * L (k+6) - 3 * L (k+5) + L (k+4) + L k)
    (hmono : Monotone L) (hpos : 0 < L 11)
    (C : Matrix (Fin 7) (Fin 7) ℝ) (hC : NN L 5 * C = 1)
    (N : ℕ)
    (hlb : ∀ n, N ≤ n → L (n-1) ≤ S n)
    (hub : ∀ n, N ≤ n → S n ≤ (n:ℝ) * L (n-1))
    (hSpos : ∀ᶠ n in atTop, 0 < S n) :
    ∃ ρ : ℝ, Tendsto (fun n => (S n) ^ ((n:ℝ)⁻¹)) atTop (𝓝 ρ) := by
  obtain ⟨γ, hγ⟩ := loglim L hLnn hrec hmono hpos C hC
  have hLpos1 : ∀ n, max N 12 ≤ n → 0 < L (n-1) := fun n hn =>
    lt_of_lt_of_le hpos (hmono (by omega))
  have hS := S_loglim L S γ (max N 12) hγ hLpos1
       (fun n hn => hlb n (le_trans (le_max_left _ _) hn))
       (fun n hn => hub n (le_trans (le_max_left _ _) hn))
  exact ⟨Real.exp γ, rpow_tendsto_of_loglim S γ hSpos hS⟩

end Asy
