import Submission.LargePrimeSquares

/-! Almost every integer has no prime-power factor larger than its largest
prime factor. The exceptional repeated-prime powers are controlled by square
divisors and the density-zero bounded-largest-prime-factor set. -/
namespace Erdos371
open Finset Filter
open scoped Topology

noncomputable def largeSquareDivisorCount (B N : ℕ) : ℕ := by
  classical
  exact ((range N).filter fun n => ∃ d, B < d ∧ d^2 ∣ n+1).card

lemma largeSquareDivisorCount_bound (B N : ℕ) :
    (largeSquareDivisorCount B N : ℝ) ≤
      N * (∑ d ∈ range (N+1) with B < d, (1 : ℝ)/(d : ℝ)^2) := by
  classical
  have hpoint (n : ℕ) (hn : n ∈ range N) :
      (if ∃ d, B < d ∧ d^2 ∣ n+1 then (1 : ℝ) else 0) ≤
        ∑ d ∈ range (N+1) with B < d, if d^2 ∣ n+1 then (1 : ℝ) else 0 := by
    split_ifs with h
    · obtain ⟨d,hBd,hd⟩ := h
      have hdN : d ≤ N := by
        have h := Nat.le_of_dvd (by omega : 0 < n+1) hd
        have hnN := mem_range.mp hn
        nlinarith
      have hmem : d ∈ (range (N+1)).filter (B < ·) :=
        mem_filter.mpr ⟨mem_range.mpr (by omega),hBd⟩
      have hh := single_le_sum
        (f := fun q => if q^2 ∣ n+1 then (1 : ℝ) else 0)
        (fun q hq => by dsimp only; split_ifs <;> norm_num) hmem
      dsimp only at hh
      rw [if_pos hd] at hh
      exact hh
    · exact sum_nonneg fun d hd => by split_ifs <;> norm_num
  calc
    _ = ∑ n ∈ range N, if ∃ d, B < d ∧ d^2 ∣ n+1 then (1 : ℝ) else 0 := by
      simp [largeSquareDivisorCount]
    _ ≤ ∑ n ∈ range N, ∑ d ∈ range (N+1) with B < d,
        if d^2 ∣ n+1 then (1 : ℝ) else 0 := sum_le_sum hpoint
    _ = ∑ d ∈ range (N+1) with B < d, ((N/d^2 : ℕ) : ℝ) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d hd
      simp [Nat.card_multiples]
    _ ≤ _ := by
      rw [mul_sum]
      apply sum_le_sum
      intro d hd
      convert (Nat.cast_div_le (m := N) (n := d^2) (α := ℝ)) using 1; push_cast; ring

lemma largeSquareDivisorCount_ratio_bound (B N : ℕ) (hN : 0 < N) :
    (largeSquareDivisorCount B N : ℝ)/N ≤
      (∑' d : ℕ, (1 : ℝ)/(d : ℝ)^2) - ∑ d ∈ range (B+1), (1 : ℝ)/(d : ℝ)^2 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h := div_le_div_of_nonneg_right (largeSquareDivisorCount_bound B N) (Nat.cast_nonneg (α := ℝ) N)
  have he : ((N : ℝ)*(∑ d ∈ range (N+1) with B < d, (1 : ℝ)/(d : ℝ)^2))/N =
      ∑ d ∈ range (N+1) with B < d, (1 : ℝ)/(d : ℝ)^2 := by field_simp
  rw [he] at h
  exact h.trans (reciprocal_square_tail_bound B N)

def primePowerOvershoot (n : ℕ) : Prop :=
  ∃ p ∈ n.primeFactors, Nat.maxPrimeFac n < p^n.factorization p

/-- An oversized repeated prime power contains a large square divisor,
unless the largest prime factor itself is bounded. -/
lemma primePowerOvershoot_cover (B n : ℕ) (h : primePowerOvershoot n) :
    Nat.maxPrimeFac n ≤ B^3 ∨ ∃ d, B < d ∧ d^2 ∣ n := by
  obtain ⟨p,hpn,hbig⟩ := h
  obtain ⟨hp,hpd,hn⟩ := Nat.mem_primeFactors.mp hpn
  have hpmax : p ≤ Nat.maxPrimeFac n := Nat.le_maxPrimeFac hn hp hpd
  have hv : 2 ≤ n.factorization p := by
    have hvpos := hp.factorization_pos_of_dvd hn hpd
    by_contra hv
    have he : n.factorization p = 1 := by omega
    simp only [he,pow_one] at hbig
    omega
  let d := p^(n.factorization p/2)
  have hd : d^2 ∣ n := by
    dsimp only [d]
    rw [← pow_mul]
    apply (hp.pow_dvd_iff_le_factorization hn).mpr
    exact Nat.div_mul_le_self _ _
  have hcube : p^n.factorization p ≤ d^3 := by
    dsimp only [d]
    rw [← pow_mul]
    apply Nat.pow_le_pow_right hp.pos
    omega
  by_cases hsmall : Nat.maxPrimeFac n ≤ B^3
  · exact Or.inl hsmall
  · apply Or.inr
    refine ⟨d,?_,hd⟩
    by_contra hBd
    have hdB : d ≤ B := by omega
    have h := Nat.pow_le_pow_left hdB 3
    omega

noncomputable def primePowerOvershootCount (N : ℕ) : ℕ := by
  classical
  exact ((range N).filter fun n => primePowerOvershoot (n+1)).card

lemma primePowerOvershootCount_bound (B N : ℕ) :
    primePowerOvershootCount N ≤
      ((range N).filter fun n => Nat.maxPrimeFac (n+1) ≤ B^3).card + largeSquareDivisorCount B N := by
  classical
  have hsub : ((range N).filter fun n => primePowerOvershoot (n+1)) ⊆
      ((range N).filter fun n => Nat.maxPrimeFac (n+1) ≤ B^3) ∪
        ((range N).filter fun n => ∃ d, B < d ∧ d^2 ∣ n+1) := by
    intro n hn
    obtain ⟨hn,hbad⟩ := mem_filter.mp hn
    rcases primePowerOvershoot_cover B (n+1) hbad with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨hn,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hn,h⟩)
  exact (card_le_card hsub).trans (card_union_le _ _)

lemma fixed_shifted_smooth_count_tendsto (B : ℕ) :
    Tendsto (fun N : ℕ => (((range N).filter fun n => Nat.maxPrimeFac (n+1) ≤ B).card : ℝ)/N)
      atTop (nhds 0) := by
  have ht := (density_iff_count (fun n => Nat.maxPrimeFac n ≤ B) 0).mp
    (bounded_maxPrimeFac_hasDensity_zero B)
  apply squeeze_zero (fun N => by positivity) _ ht
  intro N
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg (α := ℝ) N)
  have he := sum_range_succ' (fun n => if Nat.maxPrimeFac n ≤ B then (1 : ℕ) else 0) N
  rw [sum_range_succ] at he
  simp only [Nat.maxPrimeFac_zero,show 0 ≤ B from Nat.zero_le _,if_true,sum_boole,Nat.cast_id] at he
  apply Nat.cast_le.mpr
  split_ifs at he <;> omega

/-- The shifted exception count has vanishing natural proportion. -/
theorem primePowerOvershootCount_tendsto_zero :
    Tendsto (fun N : ℕ => (primePowerOvershootCount N : ℝ)/N) atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Eventually.of_forall fun N => hε.trans_le (by positivity)
  · intro ε hε
    have hf : Summable (fun d : ℕ => (1 : ℝ)/(d : ℝ)^2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have ht := (hf.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).const_sub
      (∑' d : ℕ, (1 : ℝ)/(d : ℝ)^2)
    simp only [sub_self] at ht
    obtain ⟨B,hB⟩ := (ht.eventually_lt_const (show (0 : ℝ) < ε/2 by positivity)).exists
    have hs := (fixed_shifted_smooth_count_tendsto (B^3)).eventually_lt_const
      (show (0 : ℝ) < ε/2 by positivity)
    filter_upwards [hs,eventually_gt_atTop (0 : ℕ)] with N hs hN
    have hb : (primePowerOvershootCount N : ℝ) ≤
        (((range N).filter fun n => Nat.maxPrimeFac (n+1) ≤ B^3).card : ℝ) +
          largeSquareDivisorCount B N := by exact_mod_cast primePowerOvershootCount_bound B N
    have hb' := div_le_div_of_nonneg_right hb (Nat.cast_nonneg (α := ℝ) N)
    rw [add_div] at hb'
    have hsquare := largeSquareDivisorCount_ratio_bound B N hN
    dsimp only [Function.comp_apply] at hB
    linarith

/-- The exceptional set itself has natural density zero. -/
theorem primePowerOvershoot_hasDensity_zero : {n | primePowerOvershoot n}.HasDensity 0 := by
  classical
  rw [density_iff_count]
  have ht := primePowerOvershootCount_tendsto_zero.add
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  simp only [add_zero] at ht
  apply squeeze_zero (fun N => by positivity) _ ht
  intro N
  have he := sum_range_succ' (fun n => if primePowerOvershoot n then (1 : ℕ) else 0) N
  rw [sum_range_succ] at he
  simp only [sum_boole,Nat.cast_id] at he
  have hc : ((range N).filter primePowerOvershoot).card ≤ primePowerOvershootCount N + 1 := by
    change _ ≤ ((range N).filter fun n => primePowerOvershoot (n+1)).card + 1
    change ((range N).filter primePowerOvershoot).card + (if primePowerOvershoot N then 1 else 0) =
      ((range N).filter fun n => primePowerOvershoot (n+1)).card + (if primePowerOvershoot 0 then 1 else 0) at he
    split_ifs at he <;> omega
  have hr := div_le_div_of_nonneg_right (Nat.cast_le (α := ℝ).mpr hc) (Nat.cast_nonneg (α := ℝ) N)
  simpa only [Nat.cast_add,Nat.cast_one,add_div] using hr

#print axioms primePowerOvershoot_cover
#print axioms primePowerOvershootCount_tendsto_zero
#print axioms primePowerOvershoot_hasDensity_zero
end Erdos371
