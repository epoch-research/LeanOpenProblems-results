import Submission.BalancedCoreDyadic
import Submission.SparseVoidBound

/-! Arithmetic cases of the two-valued count hypothesis. These extend the
full-period result to neighboring lengths, but keep the large-tail restriction. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling

def TwoValuedCoreCount (P : Finset ℕ) (m : ℕ) : Prop :=
  ∃ s : ℕ, ∀ r : Phase P, (populationSurvivors (range m) P r).card = s ∨
    (populationSurvivors (range m) P r).card = s+1

lemma singleton_population_card (p m : ℕ) (r : Phase ({p} : Finset ℕ)) :
    residueHits m p (r ⟨p,mem_singleton_self p⟩)+
      (populationSurvivors (range m) {p} r).card = m := by
  have he (x : ℕ) : (∀ q : ({p} : Finset ℕ), x % q.val ≠ (r q).val) ↔
      x % p ≠ (r ⟨p,mem_singleton_self p⟩).val := by
    constructor
    · intro h
      exact h ⟨p,mem_singleton_self p⟩
    · intro h q
      have hq : q = ⟨p,mem_singleton_self p⟩ := Subtype.ext (mem_singleton.mp q.property)
      rw [hq]
      exact h
  unfold populationSurvivors residueHits
  simp_rw [he]
  exact (card_filter_add_card_filter_not _).trans (card_range m)

/-- A single residue-class deletion always leaves one of two consecutive counts. -/
theorem singleton_two_valued (p : ℕ) (hp : p.Prime) (m : ℕ) :
    TwoValuedCoreCount {p} m := by
  by_cases hm : m = 0
  · subst m
    exact ⟨0,fun r => Or.inl (by simp [populationSurvivors])⟩
  · refine ⟨m-(m/p+1),fun r => ?_⟩
    have hf : m/p+1 ≤ m := by
      have hh := Nat.div_lt_self (by omega : 0 < m) hp.one_lt
      omega
    have hh := singleton_population_card p m r
    rw [residueHits_eq m p hp.pos] at hh
    split_ifs at hh <;> omega

lemma full_period_constant_count (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m : ℕ) (hm : (∏ p ∈ P, p) ∣ m) :
    ∃ s : ℕ, ∀ r : Phase P, (populationSurvivors (range m) P r).card = s := by
  let r0 : Phase P := fun p => ⟨0,(hP p.val p.property).pos⟩
  refine ⟨(populationSurvivors (range m) P r0).card,fun r => ?_⟩
  have hh : ((populationSurvivors (range m) P r).card : ℝ) =
      ((populationSurvivors (range m) P r0).card : ℝ) := by
    simp only [populationSurvivors_card]
    change intervalCount P m r = intervalCount P m r0
    rw [full_period_count P hP m hm,full_period_count P hP m hm]
  exact_mod_cast hh

lemma core_count_succ (P : Finset ℕ) (m : ℕ) (r : Phase P) :
    (populationSurvivors (range (m+1)) P r).card = (populationSurvivors (range m) P r).card ∨
      (populationSurvivors (range (m+1)) P r).card = (populationSurvivors (range m) P r).card+1 := by
  have hh : ((populationSurvivors (range (m+1)) P r).card : ℝ) =
      ((populationSurvivors (range m) P r).card : ℝ)+point P m r := by
    simp only [populationSurvivors_card]
    exact sum_range_succ _ _
  rw [point_eq_avoidance_indicator] at hh
  split_ifs at hh with ha
  · right
    exact_mod_cast hh
  · left
    rw [add_zero] at hh
    exact_mod_cast hh

/-- One position beyond any full-period length has two-valued core counts. -/
theorem full_period_succ_two_valued (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m : ℕ) (hm : (∏ p ∈ P, p) ∣ m) : TwoValuedCoreCount P (m+1) := by
  obtain ⟨s,hs⟩ := full_period_constant_count P hP m hm
  refine ⟨s,fun r => ?_⟩
  simpa only [hs r] using core_count_succ P m r

/-- One position before any positive full-period length has two-valued counts. -/
theorem full_period_pred_two_valued (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m : ℕ) (hm : (∏ p ∈ P, p) ∣ m+1) : TwoValuedCoreCount P m := by
  obtain ⟨s,hs⟩ := full_period_constant_count P hP (m+1) hm
  have hs0 : 0 < s := by
    let r0 : Phase P := fun p => ⟨0,(hP p.val p.property).pos⟩
    have hp : (0 : ℝ) < (s : ℝ) := by
      rw [← hs r0,populationSurvivors_card,← intervalCount,full_period_count P hP (m+1) hm]
      exact mul_pos (by positivity) (density_pos P hP)
    exact_mod_cast hp
  refine ⟨s-1,fun r => ?_⟩
  have hh := core_count_succ P m r
  rw [hs r] at hh
  omega

/-- Loss-free doubling, specialized to an arbitrary singleton core. -/
theorem singleton_core_void_double_le (p : ℕ) (hp : p.Prime) (R : Finset ℕ)
    (hR : ∀ q ∈ R, q.Prime) (hpR : p ∉ R) (m : ℕ) (hlarge : ∀ q ∈ R, 2*m ≤ q) :
    coveredFraction ({p} ∪ R) (2*m) ≤ coveredFraction ({p} ∪ R) m^2 := by
  obtain ⟨s,hs⟩ := singleton_two_valued p hp m
  exact balanced_void_double_le {p} R m s (by simpa) hR
    (by simpa using hpR) hlarge hs

#print axioms singleton_two_valued
#print axioms full_period_succ_two_valued
#print axioms full_period_pred_two_valued
#print axioms singleton_core_void_double_le
end Erdos970.OneHitLogConcavity
