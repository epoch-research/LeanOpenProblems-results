import Submission.SparseRowMeanDecayExplore

/-! A probability profile placing total mass one on each of infinitely many
finite candidate rows. Local finiteness is explicit in every prefix formula. -/
namespace Erdos66InfiniteRowProbability
open Erdos66ClampedPrefixContinuation Erdos66Generating Erdos66Counting
open scoped Classical
set_option maxHeartbeats 3600000

noncomputable def rowProb (E : Set ℕ) (S : ℕ → Finset ℕ) (i : ℕ) : ℝ :=
  ∑' d : ℕ, if d∈E ∧ i∈S d then ((S d).card : ℝ)⁻¹ else 0

lemma rowProb_nonneg (E : Set ℕ) (S : ℕ → Finset ℕ) (i : ℕ) : 0 ≤ rowProb E S i := by
  apply tsum_nonneg
  intro d
  split_ifs <;> positivity

lemma rowProb_of_mem (E : Set ℕ) (S : ℕ → Finset ℕ)
    (hdisj : E.PairwiseDisjoint S) (d i : ℕ) (hd : d∈E) (hi : i∈S d) :
    rowProb E S i=((S d).card : ℝ)⁻¹ := by
  unfold rowProb
  rw [tsum_eq_single d]
  · simp [hd,hi]
  · intro e he
    by_cases heE : e∈E
    · have hni : i∉S e := fun hie ↦ Finset.disjoint_left.mp (hdisj hd heE (Ne.symm he)) hi hie
      simp [hni]
    · simp [heE]

lemma rowProb_eq_zero (E : Set ℕ) (S : ℕ → Finset ℕ) (i : ℕ)
    (hi : ∀ d∈E, i∉S d) : rowProb E S i=0 := by
  unfold rowProb
  have hz (d : ℕ) : (if d∈E ∧ i∈S d then ((S d).card : ℝ)⁻¹ else 0)=0 := by
    by_cases hd : d∈E <;> simp [hd,hi d]
  simp only [hz,tsum_zero]

lemma rowProb_support (E : Set ℕ) (S : ℕ → Finset ℕ)
    (hdisj : E.PairwiseDisjoint S) (i : ℕ) :
    rowProb E S i≠0 ↔ ∃ d∈E, i∈S d := by
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    exact h (rowProb_eq_zero E S i hn)
  · rintro ⟨d,hd,hi⟩
    rw [rowProb_of_mem E S hdisj d i hd hi]
    exact inv_ne_zero (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨i,hi⟩))

lemma rowProb_le_one (E : Set ℕ) (S : ℕ → Finset ℕ)
    (hdisj : E.PairwiseDisjoint S) (i : ℕ) : rowProb E S i ≤ 1 := by
  by_cases h : ∃ d∈E, i∈S d
  · obtain ⟨d,hd,hi⟩ := h
    rw [rowProb_of_mem E S hdisj d i hd hi]
    have hc : (1 : ℝ) ≤ (S d).card := by exact_mod_cast (Finset.card_pos.mpr ⟨i,hi⟩)
    exact inv_le_one_of_one_le₀ hc
  · have hz := rowProb_eq_zero E S i (by simpa only [not_exists,not_and] using h)
    rw [hz]
    norm_num

lemma rowProb_eq_sum (E : Set ℕ) (S : ℕ → Finset ℕ) (i K : ℕ)
    (hK : ∀ d∈E, i∈S d → d<K) :
    rowProb E S i=∑ d∈Finset.range K, if d∈E ∧ i∈S d then ((S d).card : ℝ)⁻¹ else 0 := by
  apply tsum_eq_sum
  intro d hd
  have hd' : ¬ d<K := by simpa only [Finset.mem_range] using hd
  by_cases h : d∈E ∧ i∈S d
  · exact False.elim (hd' (hK d h.1 h.2))
  · simp [h]

lemma mass_rowProb_eq (E : Set ℕ) (S : ℕ → Finset ℕ) (N K : ℕ)
    (hK : ∀ d∈E, ∀ i∈S d, i<N → d<K) :
    mass (rowProb E S) N=
      ∑ d∈Finset.range K, if d∈E then (((S d∩Finset.range N).card : ℝ)/(S d).card) else 0 := by
  unfold mass
  calc
    _ = ∑ i∈Finset.range N, ∑ d∈Finset.range K,
        if d∈E ∧ i∈S d then ((S d).card : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact rowProb_eq_sum E S i K (fun d hd hdi ↦ hK d hd i hdi (Finset.mem_range.mp hi))
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d∈E
      · simp only [hd,true_and,if_true]
        rw [←Finset.sum_filter]
        have he : (Finset.range N).filter (fun i ↦ i∈S d)=S d∩Finset.range N := by
          ext i
          simp [and_comm]
        rw [he]
        simp only [Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv]
      · simp [hd]

lemma mass_rowProb_le_count (E : Set ℕ) (S : ℕ → Finset ℕ) (N K : ℕ)
    (hK : ∀ d∈E, ∀ i∈S d, i<N → d<K) :
    mass (rowProb E S) N ≤ count E K := by
  rw [mass_rowProb_eq E S N K hK]
  have he : (count E K : ℝ)=∑ d∈Finset.range K, if d∈E then (1 : ℝ) else 0 := by
    rw [←Erdos66BracketOrderedExchange.mass_indicator_eq_count]
    rfl
  rw [he]
  apply Finset.sum_le_sum
  intro d _
  by_cases hd : d∈E
  · simp only [hd,if_true]
    by_cases hc : (S d).card=0
    · simp [hc]
    · have hpos : (0 : ℝ)<(S d).card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hc)
      exact (div_le_one hpos).mpr (by exact_mod_cast Finset.card_le_card Finset.inter_subset_left)
  · simp [hd]

lemma mass_rowProb_boundary (E : Set ℕ) (S : ℕ → Finset ℕ) (N k : ℕ)
    (hne : ∀ d∈E, (S d).Nonempty)
    (hbefore : ∀ d∈E, d<k → ∀ i∈S d, i<N)
    (hafter : ∀ d∈E, k ≤ d → ∀ i∈S d, N ≤ i) :
    mass (rowProb E S) N=(count E k : ℝ) := by
  have hK : ∀ d∈E, ∀ i∈S d, i<N → d<k := by
    intro d hd i hi hiN
    by_contra hn
    have hh := hafter d hd (by omega) i hi
    omega
  rw [mass_rowProb_eq E S N k hK]
  have he : (count E k : ℝ)=∑ d∈Finset.range k, if d∈E then (1 : ℝ) else 0 := by
    rw [←Erdos66BracketOrderedExchange.mass_indicator_eq_count]
    rfl
  rw [he]
  apply Finset.sum_congr rfl
  intro d hd'
  by_cases hd : d∈E
  · have hsub : S d ⊆ Finset.range N := fun i hi ↦ Finset.mem_range.mpr
      (hbefore d hd (Finset.mem_range.mp hd') i hi)
    rw [if_pos hd,if_pos hd,Finset.inter_eq_left.mpr hsub]
    exact div_self (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (hne d hd)))
  · simp [hd]

end Erdos66InfiniteRowProbability
