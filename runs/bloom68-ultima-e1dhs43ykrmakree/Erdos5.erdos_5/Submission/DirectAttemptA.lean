import FormalConjecturesUtil

/-!
# Direct attempt A: a finite-correlation certificate for actual adjacent prime gaps

This file does not import `Spec.lean` or `Progress.lean`.  In particular, it uses
neither of the unproved assertions in `Spec.lean`.

The unconditional part is an exact odd Bonferroni identity.  A positive finite
alternating sum really forces an *adjacent* pair, not merely two primes.
`FiniteCorrelationPositivity` below is an explicitly unproved arithmetic
hypothesis, not an axiom or a claimed theorem.
-/

open Filter Real Set Finset
open scoped Topology

namespace DirectAttemptA

/-- Odd partial inclusion-exclusion for the number `m` of intervening primes. -/
def bonferroni (r m : ℕ) : ℤ :=
  ∑ k ∈ range (2 * r + 2), (-1 : ℤ) ^ k * (m.choose k : ℤ)

theorem bonferroni_zero (r : ℕ) : bonferroni r 0 = 1 := by
  unfold bonferroni
  rw [show 2 * r + 2 = (2 * r + 1) + 1 by omega, sum_range_succ']
  simp

theorem bonferroni_succ (r m : ℕ) :
    bonferroni r (m + 1) = -(m.choose (2 * r + 1) : ℤ) := by
  unfold bonferroni
  rw [show 2 * r + 2 = (2 * r + 1) + 1 by omega,
    Int.alternating_sum_range_choose_eq_choose]
  simp [pow_add, pow_mul]

theorem bonferroni_le_indicator (r m : ℕ) :
    bonferroni r m ≤ if m = 0 then (1 : ℤ) else 0 := by
  cases m with
  | zero => simp [bonferroni_zero]
  | succ m => simp [bonferroni_succ]

/-- A factorial moment counts choices of `k` interior prime indices. -/
def factorialMoment (s : Finset (ℕ × ℕ)) (k : ℕ) : ℤ :=
  ∑ ij ∈ s, ((ij.2 - ij.1 - 1).choose k : ℤ)

/-- The certificate uses correlations of orders 2 through `2*r+3`. -/
def alternatingMoment (s : Finset (ℕ × ℕ)) (r : ℕ) : ℤ :=
  ∑ k ∈ range (2 * r + 2), (-1 : ℤ) ^ k * factorialMoment s k

theorem alternatingMoment_eq_sum (s : Finset (ℕ × ℕ)) (r : ℕ) :
    alternatingMoment s r = ∑ ij ∈ s, bonferroni r (ij.2 - ij.1 - 1) := by
  unfold alternatingMoment factorialMoment bonferroni
  simp_rw [mul_sum]
  exact sum_comm

/-- This is a counting inequality for actual consecutive indices. -/
theorem alternatingMoment_le_adjacent_card (s : Finset (ℕ × ℕ)) (r : ℕ)
    (hs : ∀ ij ∈ s, ij.1 < ij.2) :
    alternatingMoment s r ≤ ((s.filter (fun ij => ij.2 = ij.1 + 1)).card : ℤ) := by
  classical
  rw [alternatingMoment_eq_sum, natCast_card_filter]
  apply sum_le_sum
  intro ij hij
  have heq : ij.2 - ij.1 - 1 = 0 ↔ ij.2 = ij.1 + 1 := by
    have := hs ij hij
    omega
  simpa only [heq] using bonferroni_le_indicator r (ij.2 - ij.1 - 1)

/-- The exact loss consists only of pairs with many intervening prime indices. -/
theorem alternatingMoment_exact (s : Finset (ℕ × ℕ)) (r : ℕ)
    (hs : ∀ ij ∈ s, ij.1 < ij.2) :
    alternatingMoment s r =
      ((s.filter (fun ij => ij.2 = ij.1 + 1)).card : ℤ) -
        ∑ ij ∈ s.filter (fun ij => ij.1 + 1 < ij.2),
          ((ij.2 - ij.1 - 2).choose (2 * r + 1) : ℤ) := by
  classical
  rw [alternatingMoment_eq_sum, natCast_card_filter, sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro ij hij
  have hi := hs ij hij
  by_cases h : ij.2 = ij.1 + 1
  · simp [h, bonferroni_zero]
  · have hgt : ij.1 + 1 < ij.2 := by omega
    have hsub : ij.2 - ij.1 - 1 = (ij.2 - ij.1 - 2) + 1 := by omega
    simp [h, hgt, hsub, bonferroni_succ]

theorem exists_adjacent_of_positive (s : Finset (ℕ × ℕ)) (r : ℕ)
    (hs : ∀ ij ∈ s, ij.1 < ij.2) (hpos : 0 < alternatingMoment s r) :
    ∃ ij ∈ s, ij.2 = ij.1 + 1 := by
  have hcard : 0 < (s.filter (fun ij => ij.2 = ij.1 + 1)).card := by
    exact_mod_cast lt_of_lt_of_le hpos (alternatingMoment_le_adjacent_card s r hs)
  obtain ⟨ij, hij⟩ := card_pos.mp hcard
  exact ⟨ij, (mem_filter.mp hij).1, (mem_filter.mp hij).2⟩

/-- The same prime and indexing convention as in `Spec.lean`. -/
noncomputable def prime (i : ℕ) : ℕ := Nat.nth Nat.Prime i

noncomputable def normalizedGap (i : ℕ) : ℝ := primeGap i / log i

/-- All endpoint pairs in a dyadic *index* window with the prescribed distance.
The denominator is `log i`, exactly as in the target, not `log (prime i)`. -/
noncomputable def windowPairs (N : ℕ) (a b : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc N (2 * N)).product (Finset.Icc N (2 * N))).filter fun ij =>
    ij.1 < ij.2 ∧ a * log ij.1 < (prime ij.2 - prime ij.1 : ℕ) ∧
      (prime ij.2 - prime ij.1 : ℕ) < b * log ij.1

theorem windowPairs_ordered (N : ℕ) (a b : ℝ) :
    ∀ ij ∈ windowPairs N a b, ij.1 < ij.2 := by
  intro ij hij
  exact (mem_filter.mp hij).2.1

theorem positive_certificate_gives_actual_gap (N r : ℕ) (a b : ℝ)
    (hN : 2 ≤ N) (hpos : 0 < alternatingMoment (windowPairs N a b) r) :
    ∃ i : ℕ, N ≤ i ∧ i < 2 * N ∧ a < normalizedGap i ∧ normalizedGap i < b := by
  obtain ⟨⟨i, j⟩, hij, hadj⟩ := exists_adjacent_of_positive
    (windowPairs N a b) r (windowPairs_ordered N a b) hpos
  have hmem := mem_filter.mp hij
  have hi := mem_Icc.mp (mem_product.mp hmem.1).1
  have hj := mem_Icc.mp (mem_product.mp hmem.1).2
  have hlo := hmem.2.2.1
  have hhi := hmem.2.2.2
  dsimp at hadj hi hj hlo hhi
  subst j
  have hlog : 0 < log (i : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < i))
  refine ⟨i, hi.1, by omega, ?_, ?_⟩
  · exact (lt_div_iff₀ hlog).mpr hlo
  · exact (div_lt_iff₀ hlog).mpr hhi

/-- The substantive missing arithmetic estimate for this route.
The correlation order may depend on the target interval, but not on the scale.
No claim that this property holds for primes is made here. -/
def FiniteCorrelationPositivity : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → ∃ r : ℕ, ∀ K : ℕ,
    ∃ N : ℕ, max K 2 ≤ N ∧ 0 < alternatingMoment (windowPairs N a b) r

/-- A fully verified conditional reduction to precisely the target normalization. -/
theorem finiteCorrelationPositivity_implies_target (h : FiniteCorrelationPositivity) :
    ∀ C : ℝ, 0 ≤ C → ∃ n : ℕ → ℕ,
      StrictMono n ∧ Tendsto (fun i => normalizedGap (n i)) atTop (𝓝 C) := by
  intro C hC
  apply TopologicalSpace.FirstCountableTopology.tendsto_subseq (u := normalizedGap)
  rw [Metric.nhds_basis_ball.mapClusterPt_iff_frequently]
  simp only [Metric.mem_ball, Real.dist_eq, frequently_atTop]
  intro ε hε K
  let a : ℝ := max (C - ε / 2) (ε / 4)
  let b : ℝ := C + ε / 2
  have ha : 0 < a := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hab : a < b := max_lt (by dsimp [b]; linarith) (by dsimp [b]; linarith)
  obtain ⟨r, hr⟩ := h a b ha hab
  obtain ⟨N, hN, hpos⟩ := hr K
  obtain ⟨i, hi, _, hlo, hhi⟩ := positive_certificate_gives_actual_gap N r a b
    ((le_max_right K 2).trans hN) hpos
  refine ⟨i, (le_max_left K 2).trans (hN.trans hi), abs_lt.mpr ⟨?_, ?_⟩⟩
  · have hCa : C - ε / 2 ≤ a := le_max_left _ _
    linarith
  · dsimp [b] at hhi
    linarith

/-- Candidate factorial-moment main terms.  This definition asserts no arithmetic
asymptotic for the prime correlations. -/
noncomputable def momentMain (a b : ℝ) (k : ℕ) : ℝ :=
  (b ^ (k + 1) - a ^ (k + 1)) / ((k + 1).factorial : ℝ)

noncomputable def alternatingMain (a b : ℝ) (r : ℕ) : ℝ :=
  ∑ k ∈ range (2 * r + 2), (-1 : ℝ) ^ k * momentMain a b k

theorem signed_main_eq_shifted_exp (a b : ℝ) (k : ℕ) :
    (-1 : ℝ) ^ k * momentMain a b k =
      (-a) ^ (k + 1) / ((k + 1).factorial : ℝ) -
        (-b) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
  simp only [momentMain, neg_pow a, neg_pow b, pow_succ]
  ring

/-- The analytic main terms, if available arithmetically, give a positive
fixed-degree certificate for every interval, not just for small gap sizes. -/
theorem alternatingMain_tendsto (a b : ℝ) :
    Tendsto (alternatingMain a b) atTop (𝓝 (exp (-a) - exp (-b))) := by
  have ha : HasSum (fun k : ℕ => (-a) ^ k / (k.factorial : ℝ)) (exp (-a)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (-a)
  have hb : HasSum (fun k : ℕ => (-b) ^ k / (k.factorial : ℝ)) (exp (-b)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (-b)
  have hs : HasSum
      (fun k : ℕ => (-a) ^ (k + 1) / ((k + 1).factorial : ℝ) -
        (-b) ^ (k + 1) / ((k + 1).factorial : ℝ)) (exp (-a) - exp (-b)) := by
    simpa using (hasSum_nat_add_iff' 1).mpr (ha.sub hb)
  have ht : Tendsto (fun r : ℕ => 2 * r + 2) atTop atTop := by
    exact tendsto_atTop_mono (fun r : ℕ => by dsimp; omega) tendsto_id
  change Tendsto (fun r => ∑ k ∈ range (2 * r + 2),
    (-1 : ℝ) ^ k * momentMain a b k) atTop _
  simp_rw [signed_main_eq_shifted_exp]
  exact hs.tendsto_sum_nat.comp ht

theorem exists_positive_alternatingMain (a b : ℝ) (hab : a < b) :
    ∃ r : ℕ, 0 < alternatingMain a b r := by
  have hpos : 0 < exp (-a) - exp (-b) := sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  exact ((alternatingMain_tendsto a b).eventually (eventually_gt_nhds hpos)).exists

/-- The lowest-order pair-minus-triple argument cannot even give a positive
candidate main term for intervals lying above 1. -/
theorem alternatingMain_zero (a b : ℝ) :
    alternatingMain a b 0 = (b - a) * (1 - (a + b) / 2) := by
  norm_num [alternatingMain, momentMain, sum_range_succ]
  ring

theorem lowest_order_main_negative {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) :
    alternatingMain a b 0 < 0 := by
  rw [alternatingMain_zero]
  exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

/-- An exact arithmetic check of the analytic certificate, not sampled prime data.
For this interval, orders 2 through 5 would suffice if their total normalized
factorial-moment error were less than `37/3000`. -/
theorem concrete_main_positive :
    alternatingMain (7 / 5) (8 / 5) 1 = 37 / 3000 := by
  norm_num [alternatingMain, momentMain, sum_range_succ]

/-- The total absolute error in finitely many normalized factorial moments. -/
noncomputable def momentError (N r : ℕ) (a b : ℝ) : ℝ :=
  ∑ k ∈ range (2 * r + 2),
    |(factorialMoment (windowPairs N a b) k : ℝ) / (N : ℝ) - momentMain a b k|

/-- A quantitative, finite-dimensional arithmetic approximation suffices.
Crucially, the error estimate is a hypothesis here; it has NOT been proved for primes. -/
theorem moment_error_gives_positive_certificate (N r : ℕ) (a b : ℝ)
    (hN : 0 < N) (herr : momentError N r a b < alternatingMain a b r) :
    0 < alternatingMoment (windowPairs N a b) r := by
  have hdiff :
      |(alternatingMoment (windowPairs N a b) r : ℝ) / (N : ℝ) -
        alternatingMain a b r| ≤ momentError N r a b := by
    have heq :
        (alternatingMoment (windowPairs N a b) r : ℝ) / (N : ℝ) -
          alternatingMain a b r =
        ∑ k ∈ range (2 * r + 2), (-1 : ℝ) ^ k *
          ((factorialMoment (windowPairs N a b) k : ℝ) / (N : ℝ) - momentMain a b k) := by
      simp only [alternatingMoment, alternatingMain, Int.cast_sum, Int.cast_mul,
        Int.cast_pow, Int.cast_neg, Int.cast_one, sum_div, ← sum_sub_distrib]
      apply sum_congr rfl
      intro k hk
      ring
    rw [heq]
    calc
      _ ≤ ∑ k ∈ range (2 * r + 2), |(-1 : ℝ) ^ k *
          ((factorialMoment (windowPairs N a b) k : ℝ) / (N : ℝ) - momentMain a b k)| :=
        abs_sum_le_sum_abs _ _
      _ = momentError N r a b := by simp [momentError, abs_mul, abs_pow]
  have hquot : 0 < (alternatingMoment (windowPairs N a b) r : ℝ) / (N : ℝ) := by
    have := neg_abs_le ((alternatingMoment (windowPairs N a b) r : ℝ) / (N : ℝ) -
      alternatingMain a b r)
    linarith
  have hreal : 0 < (alternatingMoment (windowPairs N a b) r : ℝ) :=
    (div_pos_iff_of_pos_right (by exact_mod_cast hN)).mp hquot
  exact_mod_cast hreal

/-- A single explicitly quantified finite-moment estimate would complete this
route.  The premise is the remaining arithmetic problem, not an established fact. -/
theorem finite_moment_error_implies_target
    (h : ∀ a b : ℝ, 0 < a → a < b → ∃ r : ℕ, ∀ K : ℕ,
      ∃ N : ℕ, max K 2 ≤ N ∧ momentError N r a b < alternatingMain a b r) :
    ∀ C : ℝ, 0 ≤ C → ∃ n : ℕ → ℕ,
      StrictMono n ∧ Tendsto (fun i => normalizedGap (n i)) atTop (𝓝 C) := by
  apply finiteCorrelationPositivity_implies_target
  intro a b ha hab
  obtain ⟨r, hr⟩ := h a b ha hab
  refine ⟨r, fun K => ?_⟩
  obtain ⟨N, hN, herr⟩ := hr K
  exact ⟨N, hN, moment_error_gives_positive_certificate N r a b
    (by have := (le_max_right K 2).trans hN; omega) herr⟩

/-- A countermodel to the purely structural unspecified-pair inference.
This is NOT claimed to be the actual prime-gap limit set. -/
def holeSet : Set ℝ := {t : ℝ | 0 ≤ t ∧ (t ≤ 1 ∨ 2 ≤ t)}

theorem three_differences_hit_holeSet {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    y - x ∈ holeSet ∨ z - y ∈ holeSet ∨ z - x ∈ holeSet := by
  by_cases h₁ : y - x ≤ 1
  · exact Or.inl ⟨by linarith, Or.inl h₁⟩
  by_cases h₂ : z - y ≤ 1
  · exact Or.inr (Or.inl ⟨by linarith, Or.inl h₂⟩)
  · exact Or.inr (Or.inr ⟨by linarith, Or.inr (by linarith)⟩)

theorem holeSet_closed : IsClosed holeSet := by
  exact isClosed_Ici.inter (isClosed_Iic.union isClosed_Ici)

theorem holeSet_omits_interval : (3 / 2 : ℝ) ∉ holeSet := by
  norm_num [holeSet]

#print axioms alternatingMoment_exact
#print axioms alternatingMoment_le_adjacent_card
#print axioms positive_certificate_gives_actual_gap
#print axioms finiteCorrelationPositivity_implies_target
#print axioms alternatingMain_tendsto
#print axioms exists_positive_alternatingMain
#print axioms lowest_order_main_negative
#print axioms concrete_main_positive
#print axioms moment_error_gives_positive_certificate
#print axioms finite_moment_error_implies_target
#print axioms three_differences_hit_holeSet
#print axioms holeSet_closed
#print axioms holeSet_omits_interval

end DirectAttemptA
