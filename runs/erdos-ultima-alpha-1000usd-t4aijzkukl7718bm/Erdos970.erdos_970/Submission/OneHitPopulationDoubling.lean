import Submission.OneHitLogConcavity
import Submission.OneHitMoments
import Submission.PhaseUnionBennett

/-! Negative dependence of complete coverage for disjoint populations when
all moduli can hit at most one position. A constant-count core transfers this
to a restricted dyadic void inequality. No unrestricted doubling is asserted. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling

lemma phaseMean_div (P : Finset ℕ) (f : Phase P → ℝ) (c : ℝ) :
    phaseMean P (fun r => f r/c) = phaseMean P f/c := by
  unfold phaseMean
  rw [← sum_div]
  ring

lemma insert_cover_erase_iff (S P : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (hS : S ⊆ range p) (r : Phase P) (a : Fin p) :
    (∀ x ∈ S, ∃ q : ↥(insert p P), x % q.val = (extendPhase P p r a q).val) ↔
      (∀ x ∈ S.erase a.val, ∃ q : P, x % q.val = (r q).val) := by
  constructor
  · intro h x hx
    have hxS := (mem_erase.mp hx).2
    obtain ⟨q,hq⟩ := h x hxS
    by_cases hqp : q.val = p
    · have he : q = ⟨p, mem_insert_self _ _⟩ := Subtype.ext hqp
      subst q
      rw [extendPhase_new, Nat.mod_eq_of_lt (mem_range.mp (hS hxS))] at hq
      exact ((mem_erase.mp hx).1 hq).elim
    · have hqP : q.val ∈ P := (mem_insert.mp q.property).resolve_left hqp
      refine ⟨⟨q.val,hqP⟩, ?_⟩
      simpa only [extendPhase_old P p hp r a ⟨q.val,hqP⟩] using hq
  · intro h x hx
    by_cases hxa : x = a.val
    · refine ⟨⟨p,mem_insert_self _ _⟩, ?_⟩
      rw [extendPhase_new, hxa, Nat.mod_eq_of_lt a.isLt]
    · obtain ⟨q,hq⟩ := h x (mem_erase.mpr ⟨hxa,hx⟩)
      refine ⟨⟨q.val,mem_insert_of_mem q.property⟩,?_⟩
      simpa only [extendPhase_old P p hp r a q] using hq

/-- The occupancy recurrence is exactly the actual independent-residue
probability, not independent thinning of the positions. -/
theorem population_eq_occupancy (ps : List ℕ) (hnd : ps.Nodup)
    (m : ℕ) (hp : ∀ p ∈ ps, 0 < p ∧ m ≤ p)
    (S : Finset ℕ) (hS : S ⊆ range m) :
    populationCoveredFraction S ps.toFinset = occupancy ps S.card := by
  induction ps generalizing S with
  | nil =>
    simp [populationCoveredFraction,phaseMean,occupancy, ← eq_empty_iff_forall_notMem]
  | cons p ps ih =>
    obtain ⟨hnot,hnd'⟩ := List.nodup_cons.mp hnd
    have hp0 := (hp p (by simp)).1
    have hmp := (hp p (by simp)).2
    have hp' : ∀ q ∈ ps, 0 < q ∧ m ≤ q := fun q hq => hp q (by simp [hq])
    have hnot' : p ∉ ps.toFinset := by simpa using hnot
    have hSp : S ⊆ range p := hS.trans (range_mono hmp)
    have he (a : Fin p) : populationCoveredFraction (S.erase a.val) ps.toFinset =
        occupancy ps (S.erase a.val).card :=
      ih hnd' hp' (S.erase a.val) ((erase_subset _ _).trans hS)
    rw [List.toFinset_cons, populationCoveredFraction, phaseMean_insert _ _ hnot']
    simp_rw [insert_cover_erase_iff S ps.toFinset p hnot' hSp]
    rw [phaseMean_div,phaseMean_sum]
    change (∑ a : Fin p, populationCoveredFraction (S.erase a.val) ps.toFinset) / p = _
    simp_rw [he]
    rw [Fin.sum_univ_eq_sum_range (fun a => occupancy ps (S.erase a).card)]
    rw [OneHitMoments.sum_erase_card S p hSp]
    rfl

lemma population_eq_finset_occupancy (P S : Finset ℕ) (m : ℕ)
    (hp : ∀ p ∈ P, 0 < p ∧ m ≤ p) (hS : S ⊆ range m) :
    populationCoveredFraction S P = occupancy P.toList S.card := by
  simpa using population_eq_occupancy P.toList P.nodup_toList m
    (fun p hp' => hp p (by simpa using hp')) S hS

/-- Complete coverage of disjoint populations is negatively correlated in
the one-hit regime. Moduli need not be prime, but must be large enough. -/
theorem disjoint_population_coverage (P S T : Finset ℕ) (m : ℕ)
    (hp : ∀ p ∈ P, 0 < p ∧ m ≤ p)
    (hS : S ⊆ range m) (hT : T ⊆ range m) (hdis : Disjoint S T) :
    populationCoveredFraction (S ∪ T) P ≤
      populationCoveredFraction S P * populationCoveredFraction T P := by
  rw [population_eq_finset_occupancy P (S ∪ T) m hp (union_subset hS hT),
    population_eq_finset_occupancy P S m hp hS,
    population_eq_finset_occupancy P T m hp hT, card_union_of_disjoint hdis]
  apply occupancy_submultiplicative
  intro p hp'
  have hpm := hp p (by simpa using hp')
  refine ⟨hpm.1, ?_⟩
  have hh := card_le_card (union_subset hS hT)
  rw [card_union_of_disjoint hdis, card_range] at hh
  exact hh.trans hpm.2

lemma population_empty_iff (S P : Finset ℕ) (r : Phase P) :
    populationSurvivors S P r = ∅ ↔ ∀ x ∈ S, ∃ p : P, x % p.val = (r p).val := by
  simp [populationSurvivors,filter_eq_empty_iff,not_forall]

lemma population_cover_union (S P R : Finset ℕ) (hdis : Disjoint P R) :
    populationCoveredFraction S (P ∪ R) =
      phaseMean P (fun r => populationCoveredFraction (populationSurvivors S P r) R) := by
  unfold populationCoveredFraction
  simp_rw [← population_empty_iff]
  rw [phaseMean_union P R hdis]
  simp_rw [populationSurvivors_union S P R hdis]

lemma void_eq_population (P : Finset ℕ) (m : ℕ) :
    coveredFraction P m = populationCoveredFraction (range m) P := by
  unfold coveredFraction populationCoveredFraction
  congr 1
  funext r
  have he : intervalCount P m r = 0 ↔
      ∀ x ∈ range m, ∃ p : P, x % p.val = (r p).val := by
    constructor
    · intro h x hx
      exact cover_of_count_zero P m r h x (mem_range.mp hx)
    · intro h
      exact count_zero_of_cover P m r (fun x hx => h x (mem_range.mpr hx))
  simp only [he]

lemma void_constant_core (P R : Finset ℕ) (m s : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hdis : Disjoint P R)
    (hR : ∀ p ∈ R, 0 < p ∧ m ≤ p)
    (hc : ∀ r : Phase P, (populationSurvivors (range m) P r).card = s) :
    coveredFraction (P ∪ R) m = occupancy R.toList s := by
  rw [void_eq_population, population_cover_union _ _ _ hdis]
  have he (r : Phase P) : populationCoveredFraction (populationSurvivors (range m) P r) R =
      occupancy R.toList s := by
    rw [population_eq_finset_occupancy R (populationSurvivors (range m) P r) m hR
      (show populationSurvivors (range m) P r ⊆ range m from filter_subset _ _),hc]
  simp_rw [he]
  exact phaseMean_const P hP _

/-- A genuine, but restricted, dyadic void theorem. The constant-count core
assumptions are explicit; they are not asserted for an arbitrary interval. -/
theorem constant_core_doubling (P R : Finset ℕ) (m s : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hdis : Disjoint P R)
    (hR : ∀ p ∈ R, 0 < p ∧ 2*m ≤ p)
    (hs : s ≤ m)
    (hc : ∀ r : Phase P, (populationSurvivors (range m) P r).card = s)
    (hc2 : ∀ r : Phase P, (populationSurvivors (range (2*m)) P r).card = 2*s) :
    coveredFraction (P ∪ R) (2*m) ≤ coveredFraction (P ∪ R) m ^ 2 := by
  rw [void_constant_core P R (2*m) (2*s) hP hdis hR hc2,
    void_constant_core P R m s hP hdis (fun p hp => ⟨(hR p hp).1,by have := (hR p hp).2; omega⟩) hc,
    show 2*s = s+s by omega, pow_two]
  apply occupancy_submultiplicative
  intro p hp
  have hh := hR p (by simpa using hp)
  exact ⟨hh.1,by omega⟩

lemma full_period_variance_zero (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m : ℕ) (hm : (∏ p ∈ P, p) ∣ m) : countVariance P m = 0 := by
  rw [countVariance_expansion P hP]
  apply sum_eq_zero
  intro Q hQ
  have hd : (∏ p ∈ Q, p) ∣ m :=
    (Finset.prod_dvd_prod_of_subset Q P id (mem_powerset.mp hQ)).trans hm
  simp [residueDefect, Nat.mod_eq_zero_of_dvd hd]

lemma full_period_count (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m : ℕ) (hm : (∏ p ∈ P, p) ∣ m) (r : Phase P) :
    intervalCount P m r = (m : ℝ)*density P := by
  have hv := full_period_variance_zero P hP m hm
  have hden : (∏ p : P, (p.val : ℝ)) ≠ 0 := prod_ne_zero_iff.mpr
    (fun p _ => by exact_mod_cast (hP p.val p.property).ne_zero)
  unfold countVariance phaseMean at hv
  have hs := (div_eq_zero_iff.mp hv).resolve_right hden
  have hh := single_le_sum (s := (univ : Finset (Phase P)))
    (f := fun t => (intervalCount P m t-(m : ℝ)*density P)^2)
    (fun t _ => sq_nonneg _) (mem_univ r)
  rw [hs] at hh
  nlinarith only [hh]

/-- Actual prime-phase void doubling for a full-period core and a one-hit
 tail. The full-period and large-tail premises are essential restrictions. -/
theorem full_period_core_doubling (P R : Finset ℕ) (m : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hdis : Disjoint P R)
    (hm : (∏ p ∈ P, p) ∣ m)
    (hR : ∀ p ∈ R, 0 < p ∧ 2*m ≤ p) :
    coveredFraction (P ∪ R) (2*m) ≤ coveredFraction (P ∪ R) m ^ 2 := by
  let r0 : Phase P := fun p => ⟨0, (hP p.val p.property).pos⟩
  let s := (populationSurvivors (range m) P r0).card
  have hsR : (s : ℝ) = (m : ℝ)*density P := by
    rw [show (s : ℝ) = intervalCount P m r0 from populationSurvivors_card _ _ _]
    exact full_period_count P hP m hm r0
  have hs : s ≤ m := (card_le_card (show populationSurvivors (range m) P r0 ⊆ range m
    from filter_subset _ _)).trans_eq (card_range m)
  apply constant_core_doubling P R m s hP hdis hR hs
  · intro r
    have hh : ((populationSurvivors (range m) P r).card : ℝ) = (s : ℝ) := by
      rw [populationSurvivors_card, ← intervalCount, full_period_count P hP m hm, hsR]
    exact_mod_cast hh
  · intro r
    have hh : ((populationSurvivors (range (2*m)) P r).card : ℝ) = ((2*s : ℕ) : ℝ) := by
      rw [populationSurvivors_card, ← intervalCount,
        full_period_count P hP (2*m) (dvd_mul_of_dvd_right hm 2)]
      push_cast
      rw [hsR]
      ring
    exact_mod_cast hh

#print axioms full_period_core_doubling
#print axioms population_eq_occupancy
#print axioms disjoint_population_coverage
#print axioms constant_core_doubling
end Erdos970.OneHitLogConcavity
