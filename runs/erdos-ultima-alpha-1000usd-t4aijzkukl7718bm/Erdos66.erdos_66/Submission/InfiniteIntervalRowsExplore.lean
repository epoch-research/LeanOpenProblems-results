import Submission.InfiniteRowProbabilityExplore

/-! Infinite ordered interval rows: quantitative central covers and exact
one-point-per-row consequences of prefix-bracket rounding. -/
namespace Erdos66InfiniteIntervalRows
open Filter Erdos66InfiniteRowProbability Erdos66SparseRowMeanDecay
  Erdos66Fractional Erdos66Generating Erdos66Counting Erdos66ClampedPrefixContinuation
  Erdos66BracketOrderedExchange Erdos66ReflectionRoundingPatch Erdos66BracketRankMove
open scoped Classical Topology
set_option maxHeartbeats 3800000

lemma candidates_pairwise_disjoint (E : Set ℕ) (S : ℕ → Finset ℕ) (L U : ℕ → ℕ)
    (hsub : ∀ d∈E, S d ⊆ Finset.Ico (L d) (U d))
    (hdisj : E.PairwiseDisjoint (fun d ↦ Finset.Ico (L d) (U d))) :
    E.PairwiseDisjoint S := by
  intro d hd e he hde
  exact (hdisj hd he hde).mono (hsub d hd) (hsub e he)

lemma interval_rowProb_profile (E : Set ℕ) (S : ℕ → Finset ℕ) (L U : ℕ → ℕ)
    (hsub : ∀ d∈E, S d ⊆ Finset.Ico (L d) (U d))
    (hdisj : E.PairwiseDisjoint (fun d ↦ Finset.Ico (L d) (U d)))
    (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ d∈E, ∀ i∈Finset.Ico (L d) (U d), ((S d).card : ℝ)⁻¹ ≤ C*profile i) :
    ∀ i, rowProb E S i ≤ C*profile i := by
  intro i
  by_cases hi : ∃ d∈E, i∈S d
  · obtain ⟨d,hd,hi⟩ := hi
    rw [rowProb_of_mem E S (candidates_pairwise_disjoint E S L U hsub hdisj) d i hd hi]
    exact hw d hd i (hsub d hd hi)
  · have hz := rowProb_eq_zero E S i (by simpa only [not_exists,not_and] using hi)
    rw [hz]
    exact mul_nonneg hC (profile_nonneg i)

lemma interval_rowProb_prefix (E : Set ℕ) (S : ℕ → Finset ℕ) (L U : ℕ → ℕ)
    (hsub : ∀ d∈E, S d ⊆ Finset.Ico (L d) (U d))
    (hloc : ∀ d∈E, ∀ i∈Finset.Ico (L d) (U d), d ≤ 2*i) (n : ℕ) :
    mass (rowProb E S) (n+1) ≤ count E (2*(n+1)+1) := by
  apply mass_rowProb_le_count
  intro d hd i hi hin
  have hh := hloc d hd i (hsub d hd hi)
  omega

lemma interval_rowProb_central_rows (E : Set ℕ) (S : ℕ → Finset ℕ) (L U : ℕ → ℕ)
    (hsub : ∀ d∈E, S d ⊆ Finset.Ico (L d) (U d))
    (hloc : ∀ d∈E, ∀ i∈Finset.Ico (L d) (U d), d ≤ 2*i)
    (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ d∈E, ∀ i∈Finset.Ico (L d) (U d), ((S d).card : ℝ)⁻¹ ≤ C*profile i)
    (hfill : ∀ d∈E, ((S d).card : ℝ)⁻¹*(U d-L d : ℕ) ≤ 2)
    (n m : ℕ) (hm : 2*m ≤ n+1) :
    HasCentralRows (rowProb E S) n m C (count E (2*(n+1)+1)) := by
  let K := 2*(n+1)+1
  let a (d : ℕ) := max m (L d)
  let b (d : ℕ) := min (n+1-m) (U d)
  let c (d : ℕ) : ℝ := ((S d).card : ℝ)⁻¹
  let J := (Finset.range K).filter (fun d ↦ d∈E ∧ a d<b d)
  have hJ (d : ℕ) (hd : d∈J) : d<K ∧ d∈E ∧ a d<b d := by
    simpa only [J,Finset.mem_filter,Finset.mem_range] using hd
  have hc (d : ℕ) : 0 ≤ c d := by dsimp only [c]; positivity
  have hab (d : ℕ) (hd : d∈J) : m ≤ a d ∧ a d ≤ b d ∧ b d ≤ n+1-m :=
    ⟨le_max_left _ _,(hJ d hd).2.2.le,min_le_left _ _⟩
  have hcard : J.card ≤ count E K := by
    apply Finset.card_le_card
    intro d hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hJ d hd).1,(hJ d hd).2.1⟩
  refine ⟨J,a,b,c,fun d _ ↦ hc d,hab,?_,?_,?_⟩
  · intro i hi
    have hi' := Finset.mem_Ico.mp hi
    rw [rowProb_eq_sum E S i K (by
      intro d hd hdi
      have hh := hloc d hd i (hsub d hd hdi)
      dsimp only [K]
      omega)]
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro d _
    by_cases hdi : d∈E ∧ i∈S d
    · have hir := Finset.mem_Ico.mp (hsub d hdi.1 hdi.2)
      have hia : a d ≤ i := max_le hi'.1 hir.1
      have hib : i<b d := lt_min hi'.2 hir.2
      have hdab : a d<b d := lt_of_le_of_lt hia hib
      simp only [hdi,if_true,show d∈E ∧ a d<b d from ⟨hdi.1,hdab⟩,
        Finset.mem_Ico,hia,hib,and_self,if_true,c,le_refl]
    · rw [if_neg hdi]
      split_ifs <;> first | exact le_rfl | exact hc d
  · have hb (d : ℕ) (hd : d∈J) : c d*(b d-a d : ℕ) ≤ 2 := by
      have hlen : b d-a d ≤ U d-L d := by
        have h1 := min_le_right (n+1-m) (U d)
        have h2 := le_max_right m (L d)
        dsimp only [a,b]
        omega
      exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hlen) (hc d)).trans (hfill d (hJ d hd).2.1)
    have hh := Finset.sum_le_sum (fun d hd ↦ hb d hd)
    simp only [Finset.sum_const,nsmul_eq_mul] at hh
    have hcard' : (J.card : ℝ) ≤ count E K := by exact_mod_cast hcard
    nlinarith
  · have hb (d : ℕ) (hd : d∈J) : c d ≤ C*profile m := by
      have hh := hJ d hd
      have haL : L d ≤ a d := le_max_right _ _
      have haU : a d<U d := hh.2.2.trans_le (min_le_right _ _)
      exact (hw d hh.2.1 (a d) (Finset.mem_Ico.mpr ⟨haL,haU⟩)).trans
        (mul_le_mul_of_nonneg_left (profile_antitone (le_max_left _ _)) hC)
    have hh := Finset.sum_le_sum (fun d hd ↦ hb d hd)
    simp only [Finset.sum_const,nsmul_eq_mul] at hh
    have hcard' : (J.card : ℝ) ≤ count E K := by exact_mod_cast hcard
    have hh' := mul_le_mul_of_nonneg_right hcard' (mul_nonneg hC (profile_nonneg m))
    nlinarith only [hh,hh']

lemma brackets_at_integer_mass (q : ℕ → ℝ) (F : Set ℕ)
    (hbr : ∀ L, PrefixBrackets q F L) (N k : ℕ) (hm : mass q N=(k : ℝ)) :
    mass (indicator F) N=(k : ℝ) := by
  have hh := hbr N N le_rfl
  rw [hm] at hh
  norm_num only [Int.floor_natCast,Int.ceil_natCast,Int.cast_natCast] at hh
  exact le_antisymm hh.2 hh.1

lemma interval_rowProb_exactly_one (E : Set ℕ) (S : ℕ → Finset ℕ) (L U : ℕ → ℕ)
    (hne : ∀ d∈E, (S d).Nonempty)
    (hsub : ∀ d∈E, S d ⊆ Finset.Ico (L d) (U d))
    (hord : ∀ d∈E, ∀ e∈E, d<e → U d ≤ L e)
    (F : Set ℕ) (hbr : ∀ N, PrefixBrackets (rowProb E S) F N) (d : ℕ) (hd : d∈E) :
    (intervalPart F (L d) (U d)).card=1 := by
  have hlu : L d<U d := by
    obtain ⟨i,hi⟩ := hne d hd
    exact lt_of_le_of_lt (Finset.mem_Ico.mp (hsub d hd hi)).1 (Finset.mem_Ico.mp (hsub d hd hi)).2
  have hlo : mass (rowProb E S) (L d)=(count E d : ℝ) := by
    apply mass_rowProb_boundary E S (L d) d hne
    · intro e he hed i hi
      exact (Finset.mem_Ico.mp (hsub e he hi)).2.trans_le (hord e he d hd hed)
    · intro e he hde i hi
      rcases lt_or_eq_of_le hde with hde | rfl
      · exact (hlu.le.trans (hord d hd e he hde)).trans (Finset.mem_Ico.mp (hsub e he hi)).1
      · exact (Finset.mem_Ico.mp (hsub d he hi)).1
  have hhi : mass (rowProb E S) (U d)=(count E (d+1) : ℝ) := by
    apply mass_rowProb_boundary E S (U d) (d+1) hne
    · intro e he hed i hi
      have hed' : e ≤ d := by omega
      rcases lt_or_eq_of_le hed' with hed' | rfl
      · exact ((Finset.mem_Ico.mp (hsub e he hi)).2.trans_le (hord e he d hd hed')).trans hlu
      · exact (Finset.mem_Ico.mp (hsub e he hi)).2
    · intro e he hde i hi
      exact (hord d hd e he (by omega)).trans (Finset.mem_Ico.mp (hsub e he hi)).1
  have hFlo := brackets_at_integer_mass _ F hbr (L d) (count E d) hlo
  have hFhi := brackets_at_integer_mass _ F hbr (U d) (count E (d+1)) hhi
  have hcount : ((intervalPart F (L d) (U d)).card : ℝ)=
      mass (indicator F) (U d)-mass (indicator F) (L d) := by
    rw [show mass (indicator F) (U d)-mass (indicator F) (L d)=
      ∑ i∈Finset.Ico (L d) (U d), indicator F i from (Finset.sum_Ico_eq_sub _ hlu.le).symm]
    simp [intervalPart,indicator]
  rw [hFlo,hFhi,count_succ,if_pos hd] at hcount
  have hh : ((intervalPart F (L d) (U d)).card : ℝ)=1 := by push_cast at hcount; linarith
  exact_mod_cast hh

end Erdos66InfiniteIntervalRows
