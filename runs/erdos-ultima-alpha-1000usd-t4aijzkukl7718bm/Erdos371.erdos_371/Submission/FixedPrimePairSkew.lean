import Submission.PrimePairReversalObstruction

/-! A single fixed antisymmetric kernel on exact prime values can have biased
natural subsequences. The kernel is not the numerical order comparison.
This does not disprove the Erdős conjecture. -/
namespace Erdos371.FixedPrimePairSkew
open Finset Filter FiniteSieve
open scoped Topology
set_option autoImplicit false

private lemma exists_endpoint (B : ℕ) :
    ∃ N : ℕ, B+2≤N ∧
      2*(((range N).filter fun n => Nat.maxPrimeFac n≤B).card : ℝ)/N≤1/40 ∧
      (1/20 : ℝ)≤((bothAboveSet (ceilPowerCutoff (21/40) N) N).card : ℝ)/N ∧
      2*N≤(ceilPowerCutoff (21/40) N+1)^2 := by
  have hs := ((density_iff_count (fun n => Nat.maxPrimeFac n≤B) 0).mp
    (bounded_maxPrimeFac_hasDensity_zero B)).const_mul 2
  simp only [mul_zero] at hs
  obtain ⟨N,hN,hsmall,hmass,hprod⟩ :=
    ((eventually_ge_atTop (B+2)).and
      ((hs.eventually_le_const (by norm_num : (0 : ℝ)<1/40)).and
        (bothAbove_upperHalf_positive_proportion.and
          ceilPowerCutoff_upperHalf_product_eventually))).exists
  exact ⟨N,hN,by simpa only [mul_div_assoc] using hsmall,hmass,hprod⟩

noncomputable def endpoint (B : ℕ) : ℕ := Classical.choose (exists_endpoint B)

lemma endpoint_spec (B : ℕ) : B+2≤endpoint B ∧
    2*(((range (endpoint B)).filter fun n => Nat.maxPrimeFac n≤B).card : ℝ)/endpoint B≤1/40 ∧
    (1/20 : ℝ)≤((bothAboveSet (ceilPowerCutoff (21/40) (endpoint B)) (endpoint B)).card : ℝ)/endpoint B ∧
    2*endpoint B≤(ceilPowerCutoff (21/40) (endpoint B)+1)^2 :=
  Classical.choose_spec (exists_endpoint B)

noncomputable def band : ℕ → ℕ
  | 0 => 0
  | j+1 => endpoint (band j)+1

lemma band_strictMono : StrictMono band := by
  apply strictMono_nat_of_lt_succ
  intro j
  have := (endpoint_spec (band j)).1
  change band j<endpoint (band j)+1
  omega

lemma band_index_exists (p : ℕ) : ∃ j : ℕ, p≤band (j+1) :=
  ⟨p,(Nat.le_succ p).trans (band_strictMono.le_apply)⟩

noncomputable def bandIndex (p : ℕ) : ℕ := Nat.find (band_index_exists p)

lemma bandIndex_upper (p : ℕ) : p≤band (bandIndex p+1) :=
  Nat.find_spec (band_index_exists p)

lemma bandIndex_eq (j p : ℕ) (hl : band j<p) (hu : p≤band (j+1)) :
    bandIndex p=j := by
  apply le_antisymm
  · exact Nat.find_min' (band_index_exists p) hu
  · by_contra h
    have hj : bandIndex p+1≤j := by omega
    have hh := (bandIndex_upper p).trans (band_strictMono.monotone hj)
    omega

noncomputable def kernel (a b : ℕ) : ℝ :=
  let N := endpoint (band (bandIndex (max a b)))
  primePairAsymmetryTest (ceilPowerCutoff (21/40) N) N a b

lemma kernel_skew (a b : ℕ) : kernel b a = -kernel a b := by
  unfold kernel
  rw [max_comm b a]
  exact primePairAsymmetryTest_skew _ _ a b

lemma kernel_bound (a b : ℕ) : |kernel a b|≤1 :=
  primePairAsymmetryTest_bound _ _ a b

lemma kernel_matches (j a b : ℕ) (hl : band j < max a b)
    (hu : max a b≤endpoint (band j)) :
    kernel a b=primePairAsymmetryTest
      (ceilPowerCutoff (21/40) (endpoint (band j))) (endpoint (band j)) a b := by
  have hidx := bandIndex_eq j (max a b) hl
    (hu.trans (show endpoint (band j)≤band (j+1) by simp only [band]; omega))
  simp only [kernel,hidx]

/-- At the selected endpoint, only labels from older bands can cause an
error. Their natural proportion is small by fixed-prime smooth sparsity. -/
theorem kernel_mean_positive (j : ℕ) :
    (1/40 : ℝ)≤(∑ n∈range (endpoint (band j)),
      kernel (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)))/(endpoint (band j) : ℝ) := by
  classical
  let B := band j
  let N := endpoint B
  let T := primePairAsymmetryTest (ceilPowerCutoff (21/40) N) N
  have hN := (endpoint_spec B).1
  have hsmall := (endpoint_spec B).2.1
  have hmass := (endpoint_spec B).2.2.1
  have hprod := (endpoint_spec B).2.2.2
  have hpt (n : ℕ) (hn : n∈range N) :
      T (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1))-
        2*(if Nat.maxPrimeFac n≤B then (1 : ℝ) else 0) ≤
      kernel (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)) := by
    by_cases hp : Nat.maxPrimeFac n≤B
    · rw [if_pos hp,mul_one]
      have hk := (abs_le.mp (kernel_bound (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)))).1
      have ht := (abs_le.mp (primePairAsymmetryTest_bound (ceilPowerCutoff (21/40) N) N
        (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)))).2
      change T (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1))≤1 at ht
      linarith
    · rw [if_neg hp,mul_zero,sub_zero]
      have hnN := mem_range.mp hn
      have hl : band j < max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)) :=
        (lt_of_not_ge hp).trans_le (le_max_left _ _)
      have hu : max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1))≤endpoint (band j) := by
        have hp := Nat.maxPrimeFac_le (n := n)
        have hq := Nat.maxPrimeFac_le (n := n+1)
        exact max_le (by change _≤N; omega) (by change _≤N; omega)
      rw [kernel_matches j _ _ hl hu]
  have hsum := sum_le_sum hpt
  rw [sum_sub_distrib,← mul_sum,sum_boole] at hsum
  have hNr : (0 : ℝ)<N := by exact_mod_cast (show 0<N by dsimp [N]; omega)
  have hh := div_le_div_of_nonneg_right hsum hNr.le
  rw [sub_div,primePairAsymmetryTest_mean _ N hprod] at hh
  change (1/40 : ℝ)≤(∑ n∈range N, kernel (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)))/(N : ℝ)
  change 2*(((range N).filter fun n => Nat.maxPrimeFac n≤B).card : ℝ)/N≤1/40 at hsmall
  change (1/20 : ℝ)≤((bothAboveSet (ceilPowerCutoff (21/40) N) N).card : ℝ)/N at hmass
  linarith

lemma endpoints_atTop : Tendsto (fun j => endpoint (band j)) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro j
  have h₁ := band_strictMono.le_apply (x := j)
  have h₂ := (endpoint_spec (band j)).1
  dsimp
  omega

theorem kernel_mean_not_zero :
    ¬ Tendsto (fun N : ℕ => (∑ n∈range N,
      kernel (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)))/(N : ℝ)) atTop (𝓝 0) := by
  intro h
  have ht := h.comp endpoints_atTop
  have hb := ge_of_tendsto ht (Eventually.of_forall kernel_mean_positive)
  norm_num at hb

/-- A fixed bounded antisymmetric kernel on exact prime values need not have
zero adjacent natural mean. The numerical-order kernel remains unresolved. -/
theorem exists_fixed_prime_pair_skew_not_zero :
    ∃ C : ℕ → ℕ → ℝ, (∀ a b, C b a = -C a b) ∧ (∀ a b, |C a b|≤1) ∧
      ¬ Tendsto (fun N : ℕ => (∑ n∈range N,
        C (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)))/(N : ℝ)) atTop (𝓝 0) :=
  ⟨kernel,kernel_skew,kernel_bound,kernel_mean_not_zero⟩

#print axioms kernel_mean_positive
#print axioms exists_fixed_prime_pair_skew_not_zero
end Erdos371.FixedPrimePairSkew
