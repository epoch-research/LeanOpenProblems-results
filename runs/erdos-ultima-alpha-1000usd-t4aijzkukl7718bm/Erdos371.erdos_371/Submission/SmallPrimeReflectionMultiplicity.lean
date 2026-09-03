import Submission.SmallPrimeReflectionDensity

/-! Density compression rules out using this particular reflection as an
almost-everywhere injective pairing. The result does not rule out other maps. -/
namespace Erdos371
open Finset Filter
open scoped Topology

lemma bounded_fiber_card_le_initial_add_tail (f : ℕ → ℕ) (S : Finset ℕ)
    (C T N : ℕ) (hS : S ⊆ range N)
    (hC : ∀ m, (S.filter fun n => f n = m).card ≤ C) :
    S.card ≤ C*T+((range N).filter fun n => T ≤ f n).card := by
  have hi : (S.filter fun n => f n < T).card ≤ C*T := by
    have he := sum_card_fiberwise_eq_card_filter S (range T) f
    simp only [mem_range] at he
    rw [← he]
    have hh := sum_le_sum (s := range T) (fun m _ => hC m)
    simpa only [sum_const,card_range,smul_eq_mul,Nat.mul_comm] using hh
  have ht : (S.filter fun n => ¬f n < T).card ≤
      ((range N).filter fun n => T ≤ f n).card := by
    apply card_le_card
    intro n hn
    obtain ⟨hn,hf⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hS hn,not_lt.mp hf⟩
  have hp := card_filter_add_card_filter_not (s := S) (fun n => f n < T)
  omega

/-- Any endpoint-dependent subsets on which this map has uniformly bounded
fibers occupy only o(N) of the original interval. -/
theorem smallPrimeReflection_bounded_fiber_subsets_tendsto_zero
    (S : ℕ → Finset ℕ) (C : ℕ)
    (hS : ∀ N, S N ⊆ range N)
    (hC : ∀ N m, ((S N).filter fun n => smallPrimeReflection n = m).card ≤ C) :
    Tendsto (fun N => ((S N).card : ℝ)/N) atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro δ hδ
    exact Eventually.of_forall fun N => hδ.trans_le (by positivity)
  · intro δ hδ
    obtain ⟨K,hK⟩ := exists_nat_gt (max 0 ((2*C : ℝ)/δ))
    have hK0 : 0 < K := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hK)
    have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
    have hbound : (C : ℝ)/K < δ := by
      have hlarge := (lt_of_le_of_lt (le_max_right _ _) hK)
      have hm := (div_lt_iff₀ hδ).mp hlarge
      apply (div_lt_iff₀ hKr).mpr
      nlinarith
    have ht := ((tendsto_one_div_atTop_nhds_zero_nat.const_mul (C : ℝ)).add
      (smallPrimeReflection_large_image_tendsto_zero (1/(K : ℝ)) (by positivity))).const_add
        ((C : ℝ)/K)
    simp only [mul_zero,add_zero] at ht
    filter_upwards [ht.eventually_lt_const hbound,eventually_gt_atTop (0 : ℕ)] with N hN hN0
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
    have hc := bounded_fiber_card_le_initial_add_tail smallPrimeReflection (S N) C
      (N/K+1) N (hS N) (hC N)
    have htail : ((range N).filter fun n => N/K+1 ≤ smallPrimeReflection n).card ≤
        ((range N).filter fun n => (1/(K : ℝ))*N ≤ (smallPrimeReflection n : ℝ)).card := by
      apply card_le_card
      intro n hn
      obtain ⟨hnN,hr⟩ := mem_filter.mp hn
      apply mem_filter.mpr ⟨hnN,?_⟩
      have hd : N < (N/K+1)*K := (Nat.div_lt_iff_lt_mul hK0).mp (by omega)
      have hd' : (N : ℝ) < ((N/K : ℕ)+1)*K := by exact_mod_cast hd
      have hr' : ((N/K : ℕ) : ℝ)+1 ≤ smallPrimeReflection n := by exact_mod_cast hr
      have he : (N : ℝ)/K < (smallPrimeReflection n : ℝ) :=
        ((div_lt_iff₀ hKr).mpr hd').trans_le hr'
      simpa only [one_div_mul_eq_div] using he.le
    have hc' : ((S N).card : ℝ) ≤ C*((N/K : ℕ)+1)+
        (((range N).filter fun n => (1/(K : ℝ))*N ≤ (smallPrimeReflection n : ℝ)).card : ℝ) := by
      exact_mod_cast hc.trans (Nat.add_le_add_left htail _)
    have hd : ((S N).card : ℝ)/N ≤
        (C : ℝ)/K+(C : ℝ)*(1/N)+
          (((range N).filter fun n => (1/(K : ℝ))*N ≤ (smallPrimeReflection n : ℝ)).card : ℝ)/N := by
      apply (div_le_iff₀ hNr).mpr
      have hf : ((N/K : ℕ) : ℝ) ≤ (N : ℝ)/K := Nat.cast_div_le
      have he : ((C : ℝ)/K+(C : ℝ)*(1/N)+
          (((range N).filter fun n => (1/(K : ℝ))*N ≤ (smallPrimeReflection n : ℝ)).card : ℝ)/N)*N =
          C*((N : ℝ)/K+1)+
            (((range N).filter fun n => (1/(K : ℝ))*N ≤ (smallPrimeReflection n : ℝ)).card : ℝ) := by
        field_simp
      rw [he]
      have hm := mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg (α := ℝ) C)
      linarith
    exact hd.trans_lt (by simpa only [add_assoc] using hN)

/-- In particular, discarding a zero-density exceptional set cannot make
this reflection injective on the remaining inputs. -/
theorem smallPrimeReflection_injective_subsets_tendsto_zero
    (S : ℕ → Finset ℕ) (hS : ∀ N, S N ⊆ range N)
    (hinj : ∀ N, Set.InjOn smallPrimeReflection (S N)) :
    Tendsto (fun N => ((S N).card : ℝ)/N) atTop (nhds 0) := by
  apply smallPrimeReflection_bounded_fiber_subsets_tendsto_zero S 1 hS
  intro N m
  apply card_le_one.mpr
  intro a ha b hb
  obtain ⟨ha,he⟩ := mem_filter.mp ha
  obtain ⟨hb,hf⟩ := mem_filter.mp hb
  exact hinj N ha hb (he.trans hf.symm)

/-- There is no uniform finite bound on the sizes of this map's fibers. -/
theorem smallPrimeReflection_no_uniform_fiber_bound :
    ¬ ∃ C : ℕ, ∀ N m,
      ((range N).filter fun n => smallPrimeReflection n = m).card ≤ C := by
  rintro ⟨C,hC⟩
  have ht := smallPrimeReflection_bounded_fiber_subsets_tendsto_zero (fun N => range N) C
    (fun _ => subset_rfl) hC
  have he : ∀ᶠ N : ℕ in atTop, (((range N).card : ℝ)/N) = 1 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hnz : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp [hnz]
  have ht' := ht.congr' he
  have hh : (0 : ℝ) = 1 := tendsto_nhds_unique ht' tendsto_const_nhds
  norm_num at hh

#print axioms smallPrimeReflection_bounded_fiber_subsets_tendsto_zero
#print axioms smallPrimeReflection_injective_subsets_tendsto_zero
#print axioms smallPrimeReflection_no_uniform_fiber_bound
end Erdos371
