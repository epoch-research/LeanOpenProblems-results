import Submission.HarmonicGapSkew

/-! Uniform signed harmonic cancellation with an arbitrary positive gap
cutoff. The proof localizes the finite Hilbert inequality to adjacent
blocks. It does not transfer the result to a fixed gap or to samples
restricted by divisibility. -/

namespace Erdos371.HarmonicGap
open Finset Filter
open scoped Topology

noncomputable def gapTerm (a b : ℕ → ℝ) (H i j : ℕ) : ℝ :=
  if i < j ∧ j-i ≤ H then (a i*b j-b i*a j)/((j : ℝ)-i) else 0

noncomputable def truncatedSkew (a b : ℕ → ℝ) (H N : ℕ) : ℝ :=
  ∑ i ∈ range N, ∑ j ∈ range N, gapTerm a b H i j

lemma determinant_abs_le_two (a b : ℕ → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) (i j : ℕ) :
    |a i*b j-b i*a j| ≤ 2 := by
  have h1 : |a i*b j| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (ha i) (hb j) (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have h2 : |b i*a j| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (hb i) (ha j) (abs_nonneg _) (by norm_num)).trans (by norm_num)
  exact (abs_sub _ _).trans (by linarith)

noncomputable def leftMask (M H i : ℕ) : ℝ :=
  if i < M ∧ M ≤ i+H then 1 else 0

noncomputable def rightMask (M i : ℕ) : ℝ := if M ≤ i then 1 else 0

lemma leftMask_energy (M H : ℕ) :
    (∑ i ∈ range (M+H), (leftMask M H i)^2) ≤ (H : ℝ) := by
  have hcard : ((range (M+H)).filter (fun i => i < M ∧ M ≤ i+H)).card ≤ H := by
    have hs : (range (M+H)).filter (fun i => i < M ∧ M ≤ i+H) ⊆ Ico (M-H) M := by
      intro i hi
      obtain ⟨_, hi, hm⟩ := mem_filter.mp hi
      exact mem_Ico.mpr ⟨by omega, hi⟩
    have h := card_le_card hs
    rw [Nat.card_Ico] at h
    omega
  have he : (∑ i ∈ range (M+H), (leftMask M H i)^2) =
      (((range (M+H)).filter (fun i => i < M ∧ M ≤ i+H)).card : ℝ) := by
    simp [leftMask, ite_pow]
  rw [he]
  exact_mod_cast hcard

lemma rightMask_energy (M H : ℕ) :
    (∑ i ∈ range (M+H), (rightMask M i)^2) = (H : ℝ) := by
  have hs : (range (M+H)).filter (fun i => M ≤ i) = Ico M (M+H) := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    tauto
  simp only [rightMask, ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0), ← sum_filter]
  simp [hs]

lemma mask_hilbert_bound (M H : ℕ) :
    |hilbertSum (leftMask M H) (rightMask M) (M+H)| ≤ Real.pi*H := by
  have h := hilbertSum_energy_bound (leftMask M H) (rightMask M) (M+H)
  rw [rightMask_energy] at h
  have hm := mul_le_mul_of_nonneg_left (leftMask_energy M H)
    (by positivity : 0 ≤ Real.pi/2)
  nlinarith

lemma mask_kernel_nonneg (M H i j : ℕ) :
    0 ≤ leftMask M H i * rightMask M j / ((j : ℝ)-i) := by
  unfold leftMask rightMask
  split_ifs with hi hj
  · have hd : (0 : ℝ) < (j : ℝ)-i := by
      exact sub_pos.mpr (by exact_mod_cast (show i < j by omega))
    positivity
  · simp
  · simp
  · simp

lemma cross_term_bound (a b : ℕ → ℝ) (M H i j : ℕ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) :
    |if i < M ∧ M ≤ j then gapTerm a b H i j else 0| ≤
      2*(leftMask M H i * rightMask M j / ((j : ℝ)-i)) := by
  by_cases hc : i < M ∧ M ≤ j
  · rw [if_pos hc]
    by_cases hh : j-i ≤ H
    · have hij : i < j := by omega
      have hm : M ≤ i+H := by omega
      have hd : (0 : ℝ) < (j : ℝ)-i := sub_pos.mpr (by exact_mod_cast hij)
      rw [gapTerm, if_pos ⟨hij,hh⟩, leftMask, rightMask,
        if_pos ⟨hc.1,hm⟩, if_pos hc.2, one_mul, abs_div, abs_of_pos hd]
      have h := div_le_div_of_nonneg_right (determinant_abs_le_two a b ha hb i j) hd.le
      simpa only [mul_one_div] using h
    · rw [gapTerm, if_neg (by tauto), abs_zero]
      exact mul_nonneg (by norm_num) (mask_kernel_nonneg M H i j)
  · rw [if_neg hc, abs_zero]
    exact mul_nonneg (by norm_num) (mask_kernel_nonneg M H i j)

noncomputable def crossSkew (a b : ℕ → ℝ) (M H : ℕ) : ℝ :=
  ∑ i ∈ range (M+H), ∑ j ∈ range (M+H),
    if i < M ∧ M ≤ j then gapTerm a b H i j else 0

lemma crossSkew_bound (a b : ℕ → ℝ) (M H : ℕ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) :
    |crossSkew a b M H| ≤ 2*Real.pi*H := by
  calc
    _ ≤ ∑ i ∈ range (M+H), ∑ j ∈ range (M+H),
        |if i < M ∧ M ≤ j then gapTerm a b H i j else 0| := by
      unfold crossSkew
      exact (abs_sum_le_sum_abs _ _).trans
        (sum_le_sum fun i _ => abs_sum_le_sum_abs _ _)
    _ ≤ 2*hilbertSum (leftMask M H) (rightMask M) (M+H) := by
      simp only [hilbertSum, mul_sum]
      exact sum_le_sum fun i _ => sum_le_sum fun j _ => cross_term_bound a b M H i j ha hb
    _ ≤ 2*|hilbertSum (leftMask M H) (rightMask M) (M+H)| := by
      exact mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (mask_hilbert_bound M H) (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith

lemma gapTerm_shift (a b : ℕ → ℝ) (M H i j : ℕ) :
    gapTerm a b H (M+i) (M+j) =
      gapTerm (fun n => a (M+n)) (fun n => b (M+n)) H i j := by
  unfold gapTerm
  simp only [Nat.add_lt_add_iff_left, Nat.add_sub_add_left, Nat.cast_add,
    add_sub_add_left_eq_sub]

lemma truncatedSkew_self (a b : ℕ → ℝ) (H : ℕ) :
    truncatedSkew a b H H = harmonicSkew a b H := by
  unfold truncatedSkew harmonicSkew
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  have hgap : j-i ≤ H := (Nat.sub_le j i).trans (mem_range.mp hj).le
  simp only [gapTerm, hgap, and_true]

lemma crossSkew_eq_blocks (a b : ℕ → ℝ) (M H : ℕ) :
    crossSkew a b M H =
      ∑ i ∈ range M, ∑ j ∈ range H, gapTerm a b H i (M+j) := by
  unfold crossSkew
  rw [sum_range_add]
  have hn (i : ℕ) : ¬ M+i < M := by omega
  simp only [hn, false_and, if_false, sum_const_zero, add_zero]
  apply sum_congr rfl
  intro i hi
  have hiM : i < M := mem_range.mp hi
  rw [sum_range_add]
  have hz : (∑ j ∈ range M, if i < M ∧ M ≤ j then gapTerm a b H i j else 0) = 0 := by
    apply sum_eq_zero
    intro j hj
    have hjM := mem_range.mp hj
    rw [if_neg (by omega)]
  rw [hz, zero_add]
  apply sum_congr rfl
  intro j hj
  rw [if_pos ⟨hiM, by omega⟩]

lemma truncatedSkew_add_block (a b : ℕ → ℝ) (M H : ℕ) :
    truncatedSkew a b H (M+H) = truncatedSkew a b H M +
      harmonicSkew (fun n => a (M+n)) (fun n => b (M+n)) H + crossSkew a b M H := by
  rw [truncatedSkew, sum_range_add]
  simp_rw [sum_range_add]
  simp only [sum_add_distrib]
  have hz : (∑ i ∈ range H, ∑ j ∈ range M, gapTerm a b H (M+i) j) = 0 := by
    apply sum_eq_zero
    intro i hi
    apply sum_eq_zero
    intro j hj
    have hjM := mem_range.mp hj
    rw [gapTerm, if_neg (by omega)]
  have hu : (∑ i ∈ range H, ∑ j ∈ range H, gapTerm a b H (M+i) (M+j)) =
      harmonicSkew (fun n => a (M+n)) (fun n => b (M+n)) H := by
    simp_rw [gapTerm_shift]
    exact truncatedSkew_self _ _ H
  rw [hz, zero_add, hu, ← crossSkew_eq_blocks]
  change (truncatedSkew a b H M + crossSkew a b M H) + _ = _
  ring

/-- Signed localization on a union of equal-length blocks. -/
theorem truncatedSkew_multiple_bound (a b : ℕ → ℝ) (K H : ℕ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) :
    |truncatedSkew a b H (K*H)| ≤ 3*Real.pi*(K*H : ℕ) := by
  induction K with
  | zero => simp [truncatedSkew]
  | succ K ih =>
    rw [Nat.succ_mul, truncatedSkew_add_block]
    have h1 := harmonicSkew_bounded (fun n => a (K*H+n)) (fun n => b (K*H+n)) H
      (fun i _ => ha _) (fun i _ => hb _)
    have h2 := crossSkew_bound a b (K*H) H ha hb
    have ht := (abs_add_le (truncatedSkew a b H (K*H) +
      harmonicSkew (fun n => a (K*H+n)) (fun n => b (K*H+n)) H)
      (crossSkew a b (K*H) H)).trans
      (add_le_add (abs_add_le _ _) le_rfl)
    push_cast at ih ⊢
    nlinarith

noncomputable def zeroPad (a : ℕ → ℝ) (N i : ℕ) : ℝ := if i < N then a i else 0

lemma zeroPad_abs_le_one (a : ℕ → ℝ) (N : ℕ) (ha : ∀ i, |a i| ≤ 1) (i : ℕ) :
    |zeroPad a N i| ≤ 1 := by
  unfold zeroPad
  split_ifs
  · exact ha i
  · norm_num

lemma gapTerm_zeroPad (a b : ℕ → ℝ) (N H i j : ℕ) :
    gapTerm (zeroPad a N) (zeroPad b N) H i j =
      if i < N ∧ j < N then gapTerm a b H i j else 0 := by
  by_cases hi : i < N <;> by_cases hj : j < N <;>
    simp [gapTerm, zeroPad, hi, hj]

lemma truncatedSkew_zeroPad (a b : ℕ → ℝ) (H N M : ℕ) (hNM : N ≤ M) :
    truncatedSkew (zeroPad a N) (zeroPad b N) H M = truncatedSkew a b H N := by
  have hs : (range M).filter (fun i => i < N) = range N := by
    ext i
    simp only [mem_filter, mem_range]
    omega
  unfold truncatedSkew
  simp_rw [gapTerm_zeroPad, ite_and, sum_ite_irrel, sum_const_zero, ← sum_filter, hs]

lemma truncatedSkew_padded_bound (a b : ℕ → ℝ) (H N : ℕ) (hH : 0 < H)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) :
    |truncatedSkew a b H N| ≤ 3*Real.pi*((N : ℝ)+H) := by
  let K := N/H+1
  have hNM : N ≤ K*H := by
    dsimp [K]
    have hm := Nat.mod_lt N hH
    have he := Nat.mod_add_div N H
    nlinarith
  have hMN : K*H ≤ N+H := by
    dsimp [K]
    have hm := Nat.div_mul_le_self N H
    nlinarith
  rw [← truncatedSkew_zeroPad a b H N (K*H) hNM]
  have hbnd := truncatedSkew_multiple_bound (zeroPad a N) (zeroPad b N) K H
    (zeroPad_abs_le_one a N ha) (zeroPad_abs_le_one b N hb)
  apply hbnd.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 3*Real.pi)
  exact_mod_cast hMN

lemma truncatedSkew_eq_harmonic_of_le (a b : ℕ → ℝ) (N H : ℕ) (hNH : N ≤ H) :
    truncatedSkew a b H N = harmonicSkew a b N := by
  unfold truncatedSkew harmonicSkew
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  have hgap : j-i ≤ H := (Nat.sub_le j i).trans ((mem_range.mp hj).le.trans hNH)
  simp only [gapTerm, hgap, and_true]

lemma truncatedSkew_zero_gap (a b : ℕ → ℝ) (N : ℕ) : truncatedSkew a b 0 N = 0 := by
  unfold truncatedSkew
  apply sum_eq_zero
  intro i hi
  apply sum_eq_zero
  intro j hj
  rw [gapTerm, if_neg (by omega)]

/-- A bound uniform in both the endpoint and the gap cutoff. In particular,
the cutoff can grow arbitrarily slowly compared with the endpoint. -/
theorem truncatedSkew_bound (a b : ℕ → ℝ) (H N : ℕ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) :
    |truncatedSkew a b H N| ≤ 6*Real.pi*N := by
  by_cases hH : H = 0
  · subst H
    rw [truncatedSkew_zero_gap, abs_zero]
    positivity
  by_cases hHN : H ≤ N
  · have h := truncatedSkew_padded_bound a b H N (by omega) ha hb
    have hh : (H : ℝ) ≤ N := by exact_mod_cast hHN
    have hm := mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ 3*Real.pi)
    nlinarith
  · rw [truncatedSkew_eq_harmonic_of_le a b N H (by omega)]
    have h := harmonicSkew_bounded a b N (fun i _ => ha i) (fun i _ => hb i)
    have h0 : 0 ≤ Real.pi*(N : ℝ) := by positivity
    nlinarith

noncomputable def smoothTruncatedHarmonicSkew (B C H N : ℕ) : ℝ :=
  truncatedSkew (fun n => smoothIndicator B (n+1))
    (fun n => smoothIndicator C (n+1)) H N

/-- This estimate concerns the actual smooth-number indicators, but averages
over all positive gaps at most H, with reciprocal-gap weights. -/
theorem smoothTruncatedHarmonicSkew_bound (B C H N : ℕ) :
    |smoothTruncatedHarmonicSkew B C H N| ≤ 6*Real.pi*N := by
  apply truncatedSkew_bound
  · intro i; unfold smoothIndicator; split_ifs <;> norm_num
  · intro i; unfold smoothIndicator; split_ifs <;> norm_num

lemma smoothTruncatedHarmonicSkew_normalized_bound (B C H N : ℕ)
    (hH : 1 < H) (hN : 0 < N) :
    |smoothTruncatedHarmonicSkew B C H N/((N : ℝ)*Real.log H)| ≤ 6*Real.pi/Real.log H := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log H := Real.log_pos (by exact_mod_cast hH)
  rw [abs_div, abs_of_pos (mul_pos hN0 hlog)]
  apply (div_le_iff₀ (mul_pos hN0 hlog)).mpr
  have he : 6*Real.pi/Real.log H*((N : ℝ)*Real.log H) = 6*Real.pi*N := by field_simp
  rw [he]
  exact smoothTruncatedHarmonicSkew_bound B C H N

/-- All three cutoffs may move with N. Only the gap cutoff must tend to
infinity. This gives no cancellation at any individual fixed gap. -/
theorem smoothTruncatedHarmonicSkew_tendsto (B C H : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) :
    Tendsto (fun N => smoothTruncatedHarmonicSkew (B N) (C N) (H N) N /
      ((N : ℝ)*Real.log (H N))) atTop (nhds 0) := by
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hH)
  have h := hl.inv_tendsto_atTop.const_mul (6*Real.pi)
  simp only [mul_zero] at h
  apply squeeze_zero_norm' _ h
  filter_upwards [hH.eventually_gt_atTop 1, eventually_gt_atTop (0 : ℕ)] with N hHN hN
  simpa only [Real.norm_eq_abs, div_eq_mul_inv, Pi.inv_apply] using
    smoothTruncatedHarmonicSkew_normalized_bound (B N) (C N) (H N) N hHN hN

#print axioms truncatedSkew_bound
#print axioms smoothTruncatedHarmonicSkew_tendsto

end Erdos371.HarmonicGap
