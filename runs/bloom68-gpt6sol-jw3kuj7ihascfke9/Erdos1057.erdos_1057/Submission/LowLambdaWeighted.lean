import Submission.HighLambda

/-!
# A weighted bound for small Carmichael-function values

A balanced decomposition `n = a * b` places both squarefree blocks below
`B = ⌈X^(2/3)⌉`. Orient it so that `b ≤ a`; above a threshold `D`, this
forces `D < a²`. The chosen divisor also satisfies `gcd(a, λ(a)) = 1`.
For each such block, write `λ(n) = λ(a) * k`; the two congruences
`a ∣ n` and `λ(n) ∣ n - 1` place `n` in one CRT class modulo `a * λ(a) * k`.
The sum over `k` is bounded by a harmonic sum, and the `+1` in each CRT
count contributes at most `H * B`.

This is an auxiliary upper bound, not a claim about the unrestricted counting problem.
-/

namespace Erdos1057

/-- Carmichael numbers up to `X` with Carmichael function at most `H`. -/
def lowLambdaCarmichaels (X H : ℕ) : Set ℕ :=
  {n | IsCarmichael n ∧ n ≤ X ∧ ArithmeticFunction.Carmichael n ≤ H}

/-- Admissible larger blocks for the weighted bound. Carmichael divisors `a`
are coprime to `λ(a)`; choosing `b ≤ a` gives `D < n = a * b ≤ a²`, and
in particular `a > √D`. -/
noncomputable def lowLambdaWeightedBlocks (X H D : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (highLambdaBlockCutoff X)).filter (fun a =>
    Squarefree a ∧ a.Coprime (ArithmeticFunction.Carmichael a) ∧ D < a * a ∧
      ArithmeticFunction.Carmichael a ≤ H)

/-- The weighted block sum `∑ 1 / (a * λ(a))`, with the exact cutoff and filter. -/
noncomputable def lowLambdaWeight (X H D : ℕ) : ℝ :=
  ∑ a ∈ lowLambdaWeightedBlocks X H D,
    (1 : ℝ) / ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ))

private theorem carmichael_pos_of_pos {a : ℕ} (ha : 0 < a) :
    0 < ArithmeticFunction.Carmichael a :=
  Nat.pos_of_dvd_of_pos (ArithmeticFunction.carmichael_dvd_totient a)
    (Nat.totient_pos.mpr ha)

private theorem residue_card_le (X M r : ℕ) (hM : 0 < M) :
    ((Finset.range (X + 1)).filter (fun n => n ≡ r [MOD M])).card ≤ X / M + 1 := by
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card (X + 1) hM r,
    Nat.succ_div]
  split_ifs with hd hr <;> try omega

/-- One simultaneous pair of congruences costs at most `X / (a * L) + 1`. -/
private theorem crt_fiber_card_le (X a L : ℕ) (ha : 0 < a) (hL : 0 < L)
    (hcop : a.Coprime L) :
    ((Finset.range (X + 1)).filter (fun n =>
      n ≡ 0 [MOD a] ∧ n ≡ 1 [MOD L])).card ≤ X / (a * L) + 1 := by
  classical
  let r : ℕ := (Nat.chineseRemainder hcop 0 1).val
  have hsub :
      (Finset.range (X + 1)).filter (fun n => n ≡ 0 [MOD a] ∧ n ≡ 1 [MOD L]) ⊆
        (Finset.range (X + 1)).filter (fun n => n ≡ r [MOD a * L]) := by
    intro n hn
    obtain ⟨hnX, hn0, hn1⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr
      ⟨hnX, Nat.chineseRemainder_modEq_unique hcop hn0 hn1⟩
  exact (Finset.card_le_card hsub).trans
    (residue_card_le X (a * L) r (Nat.mul_pos ha hL))

/-- The harmonic sum to a cutoff `K ≤ H` is at most `1 + log H`. -/
private theorem harmonic_Icc_le_log (H K : ℕ) (hK : K ≤ H) :
    (∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ)) ≤
      1 + Real.log (H : ℝ) := by
  have hsum : (∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ)) =
      (harmonic K : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp only [Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [hsum]
  have hlog : Real.log (K : ℝ) ≤ Real.log (H : ℝ) := by
    by_cases hK0 : K = 0
    · simpa only [hK0, Nat.cast_zero, Real.log_zero] using Real.log_natCast_nonneg H
    · exact Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hK0))
        (by exact_mod_cast hK)
  exact (harmonic_le_one_add_log K).trans (by linarith)

/-- A restricted reduction: the large-`n` term only uses squarefree larger
blocks `a` with `D < a²`, `gcd(a, λ(a)) = 1`, and weight `1 / (a * λ(a))`. -/
theorem lowLambdaCarmichaels_card_le_weighted (X H D : ℕ)
    (hX : 1 ≤ X) (hH : 1 ≤ H) :
    ((lowLambdaCarmichaels X H).ncard : ℝ) ≤
      (D : ℝ) + (X : ℝ) * (1 + Real.log (H : ℝ)) * lowLambdaWeight X H D +
        (H : ℝ) * (highLambdaBlockCutoff X : ℝ) := by
  classical
  let B : ℕ := highLambdaBlockCutoff X
  let choices : Finset ℕ := lowLambdaWeightedBlocks X H D
  let levels : ℕ → Finset ℕ := fun a =>
    (Finset.Icc 1 (H / ArithmeticFunction.Carmichael a)).filter
      (fun k => a.Coprime (ArithmeticFunction.Carmichael a * k))
  let fibers : ℕ → ℕ → Finset ℕ := fun a k =>
    (Finset.range (X + 1)).filter (fun n =>
      n ≡ 0 [MOD a] ∧ n ≡ 1 [MOD ArithmeticFunction.Carmichael a * k])
  have hcover : lowLambdaCarmichaels X H ⊆
      (((Finset.Icc 1 D) ∪
        choices.biUnion (fun a => (levels a).biUnion (fibers a)) : Finset ℕ) : Set ℕ) := by
    intro n hn
    obtain ⟨hnC, hnX, hnH⟩ := hn
    have hn1 : 1 ≤ n := by
      have hn' := (hnC 1 (by omega) (by simp)).2.2
      omega
    by_cases hnD : n ≤ D
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_Icc.mpr ⟨hn1, hnD⟩))
    · obtain ⟨a, b, ha, hb, hsa, _, _, hnfac, haB, hbB, hba⟩ :
          ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Squarefree a ∧ Squarefree b ∧ a.Coprime b ∧
            n = a * b ∧ a ≤ B ∧ b ≤ B ∧ b ≤ a := by
        obtain ⟨a₀, b₀, ha₀, hb₀, hsa₀, hsb₀, hcop₀, hnfac₀, haB₀, hbB₀⟩ :=
          isCarmichael_hasBalancedBlocks hnC hnX
        by_cases horder : b₀ ≤ a₀
        · exact ⟨a₀, b₀, ha₀, hb₀, hsa₀, hsb₀, hcop₀, hnfac₀, haB₀, hbB₀, horder⟩
        · exact ⟨b₀, a₀, hb₀, ha₀, hsb₀, hsa₀, hcop₀.symm,
            hnfac₀.trans (Nat.mul_comm a₀ b₀), hbB₀, haB₀, by omega⟩
      have hadiv : a ∣ n := hnfac ▸ dvd_mul_right a b
      let d : ℕ := ArithmeticFunction.Carmichael a
      let L : ℕ := ArithmeticFunction.Carmichael n
      have hdpos : 0 < d := carmichael_pos_of_pos ha
      have hLpos : 0 < L := carmichael_pos_of_pos (by omega : 0 < n)
      have hdvd : d ∣ L := ArithmeticFunction.carmichael_dvd hadiv
      have hdH : d ≤ H := (Nat.le_of_dvd hLpos hdvd).trans hnH
      have hD : D < a * a := by
        calc
          D < n := by omega
          _ = a * b := hnfac
          _ ≤ a * a := Nat.mul_le_mul_left a hba
      have haChoice : a ∈ choices := by
        change a ∈ (Finset.Icc 1 B).filter (fun a =>
          Squarefree a ∧ a.Coprime (ArithmeticFunction.Carmichael a) ∧
            D < a * a ∧ ArithmeticFunction.Carmichael a ≤ H)
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha, haB⟩, hsa,
          isCarmichael_coprime_divisor_lambda hnC hadiv, hD, hdH⟩
      let k : ℕ := L / d
      have hkpos : 0 < k := Nat.div_pos (Nat.le_of_dvd hLpos hdvd) hdpos
      have hkH : k ≤ H / d := Nat.div_le_div_right hnH
      have hdk : d * k = L := by
        calc
          d * k = k * d := Nat.mul_comm _ _
          _ = L := Nat.div_mul_cancel hdvd
      have hnmod1 : n ≡ 1 [MOD d * k] := by
        rw [hdk]
        exact ((Nat.modEq_iff_dvd' hn1).mpr
          (isCarmichael_lambda_dvd_sub_one hnC)).symm
      have hcop : a.Coprime (d * k) := by
        have hmod : a * b ≡ 1 [MOD d * k] := hnfac ▸ hnmod1
        exact Nat.coprime_of_mul_modEq_one b hmod
      have hkLevel : k ∈ levels a := by
        change k ∈ (Finset.Icc 1 (H / d)).filter (fun k => a.Coprime (d * k))
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hkpos, hkH⟩, hcop⟩
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨a, haChoice, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨k, hkLevel, ?_⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), Nat.modEq_zero_iff_dvd.mpr hadiv, hnmod1⟩
  have hcard : (lowLambdaCarmichaels X H).ncard ≤
      (Finset.Icc 1 D).card + ∑ a ∈ choices, ∑ k ∈ levels a, (fibers a k).card := by
    calc
      _ ≤ ((Finset.Icc 1 D) ∪
          choices.biUnion (fun a => (levels a).biUnion (fibers a))).card := by
        simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hcover
      _ ≤ (Finset.Icc 1 D).card +
          (choices.biUnion (fun a => (levels a).biUnion (fibers a))).card :=
        Finset.card_union_le _ _
      _ ≤ (Finset.Icc 1 D).card +
          ∑ a ∈ choices, ((levels a).biUnion (fibers a)).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
      _ ≤ (Finset.Icc 1 D).card +
          ∑ a ∈ choices, ∑ k ∈ levels a, (fibers a k).card := by
        apply Nat.add_le_add_left
        apply Finset.sum_le_sum
        intro a ha
        exact Finset.card_biUnion_le
  have hchoices : choices ⊆ Finset.Icc 1 B := Finset.filter_subset _ _
  have hcardChoices : choices.card ≤ B := by
    exact (Finset.card_le_card hchoices).trans (by simp [Nat.card_Icc])
  have hinner (a : ℕ) (ha : a ∈ choices) :
      (∑ k ∈ levels a, ((fibers a k).card : ℝ)) ≤
        (X : ℝ) * (1 + Real.log (H : ℝ)) *
          ((1 : ℝ) / ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ))) +
          (H : ℝ) := by
    have ha0 : 0 < a :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
    have hd0 : 0 < ArithmeticFunction.Carmichael a := carmichael_pos_of_pos ha0
    have hlevels : levels a ⊆ Finset.Icc 1 (H / ArithmeticFunction.Carmichael a) :=
      Finset.filter_subset _ _
    have hlevelCard : (levels a).card ≤ H := by
      calc
        (levels a).card ≤ (Finset.Icc 1 (H / ArithmeticFunction.Carmichael a)).card :=
          Finset.card_le_card hlevels
        _ ≤ H / ArithmeticFunction.Carmichael a := by simp [Nat.card_Icc]
        _ ≤ H := Nat.div_le_self _ _
    have hbulk :
        (∑ k ∈ levels a,
          (X : ℝ) / ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ) * (k : ℝ))) ≤
          (X : ℝ) * (1 + Real.log (H : ℝ)) *
            ((1 : ℝ) / ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ))) := by
      calc
        _ ≤ ∑ k ∈ Finset.Icc 1 (H / ArithmeticFunction.Carmichael a),
              (X : ℝ) /
                ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ) * (k : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hlevels (by intros; positivity)
        _ = ((X : ℝ) * ((1 : ℝ) /
                ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ)))) *
              ∑ k ∈ Finset.Icc 1 (H / ArithmeticFunction.Carmichael a),
                (1 : ℝ) / (k : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
        _ ≤ ((X : ℝ) * ((1 : ℝ) /
                ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ)))) *
              (1 + Real.log (H : ℝ)) := by
          apply mul_le_mul_of_nonneg_left
            (harmonic_Icc_le_log H (H / ArithmeticFunction.Carmichael a)
              (Nat.div_le_self _ _))
          positivity
        _ = _ := by ring
    have hfiber (k : ℕ) (hk : k ∈ levels a) :
        ((fibers a k).card : ℝ) ≤
          (X : ℝ) / ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ) * (k : ℝ)) + 1 := by
      have hk0 : 0 < k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
      have hcop : a.Coprime (ArithmeticFunction.Carmichael a * k) :=
        (Finset.mem_filter.mp hk).2
      have hf := crt_fiber_card_le X a (ArithmeticFunction.Carmichael a * k)
        ha0 (Nat.mul_pos hd0 hk0) hcop
      calc
        _ ≤ ((X / (a * (ArithmeticFunction.Carmichael a * k)) + 1 : ℕ) : ℝ) := by
          exact_mod_cast hf
        _ ≤ (X : ℝ) /
            ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ) * (k : ℝ)) + 1 := by
          simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, mul_assoc] using
            (add_le_add_left (Nat.cast_div_le (α := ℝ)
              (m := X) (n := a * (ArithmeticFunction.Carmichael a * k))) 1)
    calc
      _ ≤ ∑ k ∈ levels a,
          ((X : ℝ) /
            ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ) * (k : ℝ)) + 1) :=
        Finset.sum_le_sum hfiber
      _ = (∑ k ∈ levels a,
          (X : ℝ) /
            ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ) * (k : ℝ))) +
            ((levels a).card : ℝ) := by
        rw [Finset.sum_add_distrib]
        simp
      _ ≤ (X : ℝ) * (1 + Real.log (H : ℝ)) *
            ((1 : ℝ) / ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ))) +
            (H : ℝ) :=
        add_le_add hbulk (by exact_mod_cast hlevelCard)
  have hsum :
      ((∑ a ∈ choices, ∑ k ∈ levels a, (fibers a k).card : ℕ) : ℝ) ≤
        (X : ℝ) * (1 + Real.log (H : ℝ)) * lowLambdaWeight X H D +
          (H : ℝ) * (B : ℝ) := by
    simp only [Nat.cast_sum]
    calc
      (∑ a ∈ choices, ∑ k ∈ levels a, ((fibers a k).card : ℝ)) ≤
          ∑ a ∈ choices,
            ((X : ℝ) * (1 + Real.log (H : ℝ)) *
              ((1 : ℝ) / ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ))) +
              (H : ℝ)) := Finset.sum_le_sum hinner
      _ = (X : ℝ) * (1 + Real.log (H : ℝ)) * lowLambdaWeight X H D +
          (choices.card : ℝ) * (H : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rfl
      _ ≤ (X : ℝ) * (1 + Real.log (H : ℝ)) * lowLambdaWeight X H D +
          (H : ℝ) * (B : ℝ) := by
        have hcr : (choices.card : ℝ) ≤ (B : ℝ) := by exact_mod_cast hcardChoices
        have hr : (0 : ℝ) ≤ H :=
          le_trans (by norm_num : (0 : ℝ) ≤ 1) (by exact_mod_cast hH)
        nlinarith [mul_le_mul_of_nonneg_right hcr hr]
  have hsmall : (Finset.Icc 1 D).card ≤ D := by simp [Nat.card_Icc]
  calc
    ((lowLambdaCarmichaels X H).ncard : ℝ) ≤
        (((Finset.Icc 1 D).card +
          ∑ a ∈ choices, ∑ k ∈ levels a, (fibers a k).card : ℕ) : ℝ) := by
      exact_mod_cast hcard
    _ ≤ (D : ℝ) +
        ((∑ a ∈ choices, ∑ k ∈ levels a, (fibers a k).card : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hsmall _
    _ ≤ (D : ℝ) +
        ((X : ℝ) * (1 + Real.log (H : ℝ)) * lowLambdaWeight X H D +
          (H : ℝ) * (B : ℝ)) := add_le_add (le_refl (D : ℝ)) hsum
    _ = _ := by ring

end Erdos1057

#print axioms Erdos1057.lowLambdaCarmichaels_card_le_weighted
