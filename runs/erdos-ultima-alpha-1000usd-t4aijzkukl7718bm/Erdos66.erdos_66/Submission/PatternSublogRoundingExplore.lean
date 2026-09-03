import Submission.PurePatternBracketRoundingExplore
import Submission.MatchingNaturalPatternExplore
import Submission.BernoulliCostSelectionExplore

/-! A single upper-tail selection across all natural targets. Vanishing
log-normalized exponential means imply a sublogarithmic Boolean output,
with exact prefix brackets and no selections at zero-probability sites. -/
namespace Erdos66PatternSublogRounding
open Filter Erdos66NaturalPositivePattern Erdos66PurePatternBracketRounding
  Erdos66MatchingNaturalPattern Erdos66SummableTailBudget Erdos66BernoulliCostSelection
  Erdos66FiniteBernoulli Erdos66ClampedPrefixContinuation
open scoped Classical Topology
set_option maxHeartbeats 4000000

noncomputable def forbidZero (p : ℕ → ℝ) (i : ℕ) : Pattern where
  Term := Unit
  terms := {()}
  coeff := fun _ ↦ if p i=0 then 2 else 0
  support := fun _ ↦ {i}
  nonneg := by intro _ _; split_ifs <;> norm_num

lemma forbidZero_eval (p : ℕ → ℝ) (i : ℕ) : (forbidZero p i).eval p=0 := by
  simp only [forbidZero,Pattern.eval,Finset.sum_singleton,Finset.prod_singleton]
  split_ifs with hi <;> simp [hi]

lemma forbidZero_value (p : ℕ → ℝ) (i : ℕ) (hi : p i=0) (f : ℕ → Bool) :
    (forbidZero p i).value f=2*bit (f i) := by
  simp only [Pattern.value,Pattern.eval,forbidZero,hi,if_true,Finset.sum_singleton,Finset.prod_singleton]

/-- This theorem is conditional on the exponential-mean estimate. In
applications, proving that estimate for the actual sparse insertion profile
is a separate mathematical obligation. -/
theorem exists_supported_sublog_rounding
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (P : ℕ → ℕ → Pattern) (X : ℕ → (ℕ → Bool) → ℝ)
    (hX : ∀ n f, 0 ≤ X n f) (μ : ℕ → ℝ) (K : ℕ → ℝ)
    (hμ : Tendsto (fun n : ℕ ↦ μ n/Real.log ((n : ℝ)+2)) atTop (𝓝 0))
    (hmean : ∀ j n, (P j n).eval p ≤ Real.exp (K j*μ n))
    (hvalue : ∀ (j n : ℕ) f, Real.exp (((j : ℝ)+1)*X n f) ≤ (P j n).value f) :
    ∃ A : Set ℕ, (∀ L, PrefixBrackets p A L) ∧
      (∀ i∈A, p i≠0) ∧
      Tendsto (fun n : ℕ ↦ X n (fun i ↦ decide (i∈A))/Real.log ((n : ℝ)+2)) atTop (𝓝 0) := by
  let ell (n : ℕ) := Real.log ((n : ℝ)+2)
  have hell (n : ℕ) : 0<ell n := Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  let g (n : ℕ) := 1/((n : ℝ)+2)^(3 : ℝ)
  have hg : Summable g := by
    have hh := (Real.summable_one_div_nat_add_rpow 2 3).mpr (by norm_num)
    simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (↑(_ : ℕ) : ℝ)+2)] using hh
  have hge (n : ℕ) : Real.exp (-3*ell n)=g n := by
    dsimp only [g,ell]
    rw [Real.rpow_def_of_pos (by positivity),one_div,←Real.exp_neg]
    congr 1
    ring
  have hN (j : ℕ) : ∃ N : ℕ,
      (∀ n≥N, Real.exp (-4*ell n)*(P j n).eval p ≤ g n) ∧
      (∀ S : Finset ℕ, (∀ n∈S, N ≤ n) → (∑ n∈S, g n)<(1/2 : ℝ)^(j+1)/4) := by
    have hh : Tendsto (fun n : ℕ ↦ K j*μ n/ell n) atTop (𝓝 0) := by
      simpa only [mul_zero,mul_div_assoc] using hμ.const_mul (K j)
    obtain ⟨N₁,h₁⟩ := eventually_atTop.mp (hh.eventually_le_const (show (0 : ℝ)<1 by norm_num))
    obtain ⟨N₂,h₂⟩ := exists_tail_budget g hg ((1/2 : ℝ)^(j+1)/4) (by positivity)
    refine ⟨max N₁ N₂,?_,?_⟩
    · intro n hn
      have hh := (div_le_one (hell n)).mp (h₁ n ((le_max_left _ _).trans hn))
      calc
        _ ≤ Real.exp (-4*ell n)*Real.exp (K j*μ n) :=
          mul_le_mul_of_nonneg_left (hmean j n) (Real.exp_pos _).le
        _ ≤ Real.exp (-3*ell n) := by rw [←Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
        _ = _ := hge n
    · intro S hS
      exact h₂ S (fun n hn ↦ (le_max_right _ _).trans (hS n hn))
  choose N hNb hNs using hN
  let Q : ℕ × ℕ → Pattern := fun x ↦ match x.1 with
    | 0 => forbidZero p x.2
    | j+1 => if N j ≤ x.2 then scalePattern (Real.exp (-4*ell x.2)) (Real.exp_pos _).le (P j x.2)
        else zeroPattern
  have hrow (j B : ℕ) : (∑ n∈Finset.range B, (Q (j,n)).eval p) ≤ (1/2 : ℝ)^j/4 := by
    cases j with
    | zero => simp only [Q,forbidZero_eval,Finset.sum_const_zero]; positivity
    | succ j =>
      have hh : (∑ n∈Finset.range B, (Q (j+1,n)).eval p) ≤
          ∑ n∈(Finset.range B).filter (fun n ↦ N j ≤ n), g n := by
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro n _
        by_cases hn : N j ≤ n
        · simpa only [Q,if_pos hn,scalePattern_eval] using hNb j n hn
        · simp only [Q,if_neg hn,zeroPattern_eval,le_refl]
      exact hh.trans (hNs j _ (fun n hn ↦ (Finset.mem_filter.mp hn).2)).le
  have hQ (S : Finset (ℕ × ℕ)) : (∑ x∈S, (Q x).eval p) ≤ 1 := by
    let B := S.sup (fun x ↦ max x.1 x.2)+1
    have hs : S ⊆ (Finset.range B) ×ˢ (Finset.range B) := by
      intro x hx
      have hh := Finset.le_sup (f := fun x : ℕ × ℕ ↦ max x.1 x.2) hx
      dsimp only at hh
      have h1 := le_max_left x.1 x.2
      have h2 := le_max_right x.1 x.2
      apply Finset.mem_product.mpr
      constructor <;> apply Finset.mem_range.mpr <;> dsimp only [B] <;> omega
    have hh := Finset.sum_le_sum_of_subset_of_nonneg hs (fun x _ _ ↦ (Q x).eval_nonneg p (fun i ↦ (hp i).1))
    rw [Finset.sum_product] at hh
    have hh' := Finset.sum_le_sum (fun j (_hj : j∈Finset.range B) ↦ hrow j B)
    have hb : (∑ j∈Finset.range B, (1/2 : ℝ)^j/4) ≤ 1/2 :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ ↦ by positivity)).trans (row_budget B)
    exact (hh.trans (hh'.trans hb)).trans (by norm_num)
  obtain ⟨A,hbr,hpat⟩ := exists_indexed_pattern_rounding p hp Q hQ
  refine ⟨A,hbr,?_,?_⟩
  · intro i hi hzero
    have hh := hpat {(0,i)}
    simp only [Finset.sum_singleton,Q,forbidZero_value p i hzero,bit,hi,decide_true,if_true] at hh
    norm_num at hh
  · have hbound (j n : ℕ) (hn : N j ≤ n) :
        X n (fun i ↦ decide (i∈A))/ell n ≤ 4/((j : ℝ)+1) := by
      have hh := hpat {(j+1,n)}
      simp only [Finset.sum_singleton,Q,if_pos hn,scalePattern_value] at hh
      have hval := mul_le_mul_of_nonneg_left (hvalue j n (fun i ↦ decide (i∈A))) (Real.exp_pos (-4*ell n)).le
      rw [←Real.exp_add] at hval
      have he := Real.exp_le_one_iff.mp (hval.trans hh)
      apply (div_le_div_iff₀ (hell n) (by positivity : 0<(j : ℝ)+1)).mpr
      nlinarith only [he]
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hjlim : Tendsto (fun j : ℕ ↦ 4/((j : ℝ)+1)) atTop (𝓝 0) := by
      simpa only [mul_zero,mul_one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 4
    obtain ⟨j,hj⟩ := (hjlim.eventually_lt_const hε).exists
    filter_upwards [eventually_ge_atTop (N j)] with n hn
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (hX n _) (hell n).le)]
    exact (hbound j n hn).trans_lt hj

end Erdos66PatternSublogRounding
