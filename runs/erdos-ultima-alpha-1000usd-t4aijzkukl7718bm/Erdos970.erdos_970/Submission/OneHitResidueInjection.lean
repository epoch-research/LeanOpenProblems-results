import Submission.OneHitCoreCorrelation

/-! One-hit occupancy and negative dependence only need injectivity of each
residue map on the actual population. The moduli need not exceed its span.
This keeps a genuine positional hypothesis rather than treating repeated hits
as independent. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling

lemma residue_image_subset (S : Finset ℕ) (p : ℕ) (hp : 0 < p) :
    S.image (fun x => x % p) ⊆ range p := by
  intro a ha
  obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
  exact mem_range.mpr (Nat.mod_lt x hp)

lemma card_le_modulus_of_residue_injective (S : Finset ℕ) (p : ℕ) (hp : 0 < p)
    (hinj : Set.InjOn (fun x => x % p) S) : S.card ≤ p := by
  have hh := card_le_card (residue_image_subset S p hp)
  rwa [card_image_of_injOn hinj,card_range] at hh

lemma residue_image_filter_avoid (S : Finset ℕ) (p a : ℕ) :
    (S.filter (fun x => x % p ≠ a)).image (fun x => x % p) =
      (S.image (fun x => x % p)).erase a := by
  ext b
  simp only [mem_image,mem_filter,mem_erase]
  constructor
  · rintro ⟨x,⟨hx,hxa⟩,rfl⟩
    exact ⟨hxa,⟨x,hx,rfl⟩⟩
  · rintro ⟨hba,x,hx,hxb⟩
    refine ⟨x,⟨hx,?_⟩,hxb⟩
    rwa [hxb]

lemma residue_filter_avoid_card (S : Finset ℕ) (p a : ℕ)
    (hinj : Set.InjOn (fun x => x % p) S) :
    (S.filter (fun x => x % p ≠ a)).card =
      ((S.image (fun x => x % p)).erase a).card := by
  rw [← residue_image_filter_avoid,card_image_of_injOn (hinj.mono (filter_subset _ _))]

/-- Exact one-hit update over arbitrary, residue-separated positions. -/
lemma sum_avoid_card_of_injective (S : Finset ℕ) (p : ℕ) (hp : 0 < p)
    (hinj : Set.InjOn (fun x => x % p) S) (f : ℕ → ℝ) :
    (∑ a : Fin p, f (S.filter (fun x => x % p ≠ a.val)).card) =
      ((p : ℝ)-S.card)*f S.card+(S.card : ℝ)*f (S.card-1) := by
  simp_rw [residue_filter_avoid_card S p _ hinj]
  rw [Fin.sum_univ_eq_sum_range (fun a => f ((S.image (fun x => x % p)).erase a).card)]
  rw [OneHitMoments.sum_erase_card _ p (residue_image_subset S p hp) f,
    card_image_of_injOn hinj]

lemma insert_cover_filter_iff (S P : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (r : Phase P) (a : Fin p) :
    (∀ x ∈ S, ∃ q : ↥(insert p P), x % q.val = (extendPhase P p r a q).val) ↔
      (∀ x ∈ S.filter (fun x => x % p ≠ a.val), ∃ q : P, x % q.val = (r q).val) := by
  constructor
  · intro hh x hx
    obtain ⟨q,hq⟩ := hh x (mem_filter.mp hx).1
    by_cases hqp : q.val = p
    · have he : q = ⟨p,mem_insert_self _ _⟩ := Subtype.ext hqp
      subst q
      rw [extendPhase_new] at hq
      exact ((mem_filter.mp hx).2 hq).elim
    · have hqP : q.val ∈ P := (mem_insert.mp q.property).resolve_left hqp
      refine ⟨⟨q.val,hqP⟩,?_⟩
      simpa only [extendPhase_old P p hp r a ⟨q.val,hqP⟩] using hq
  · intro hh x hx
    by_cases hxa : x % p = a.val
    · refine ⟨⟨p,mem_insert_self _ _⟩,?_⟩
      simpa only [extendPhase_new] using hxa
    · obtain ⟨q,hq⟩ := hh x (mem_filter.mpr ⟨hx,hxa⟩)
      refine ⟨⟨q.val,mem_insert_of_mem q.property⟩,?_⟩
      simpa only [extendPhase_old P p hp r a q] using hq

/-- The full independent-residue probability depends only on population size
whenever every selected modulus is injective on that population. -/
theorem population_eq_occupancy_of_injective (ps : List ℕ) (hnd : ps.Nodup)
    (hp : ∀ p ∈ ps, 0 < p) (S : Finset ℕ)
    (hinj : ∀ p ∈ ps, Set.InjOn (fun x => x % p) S) :
    populationCoveredFraction S ps.toFinset = occupancy ps S.card := by
  induction ps generalizing S with
  | nil => simp [populationCoveredFraction,phaseMean,occupancy,← eq_empty_iff_forall_notMem]
  | cons p ps ih =>
    obtain ⟨hnot,hnd'⟩ := List.nodup_cons.mp hnd
    have hp0 := hp p (by simp)
    have hp' : ∀ q ∈ ps, 0 < q := fun q hq => hp q (by simp [hq])
    have hnot' : p ∉ ps.toFinset := by simpa using hnot
    have he (a : Fin p) :
        populationCoveredFraction (S.filter (fun x => x % p ≠ a.val)) ps.toFinset =
          occupancy ps (S.filter (fun x => x % p ≠ a.val)).card :=
      ih hnd' hp' _ (fun q hq => (hinj q (by simp [hq])).mono (filter_subset _ _))
    rw [List.toFinset_cons,populationCoveredFraction,phaseMean_insert _ _ hnot']
    simp_rw [insert_cover_filter_iff S ps.toFinset p hnot']
    rw [phaseMean_div,phaseMean_sum]
    change (∑ a : Fin p, populationCoveredFraction
      (S.filter (fun x => x % p ≠ a.val)) ps.toFinset)/p = _
    simp_rw [he]
    rw [sum_avoid_card_of_injective S p hp0 (hinj p (by simp))]
    rfl

lemma population_eq_finset_occupancy_of_injective (R S : Finset ℕ)
    (hR : ∀ p ∈ R, 0 < p) (hinj : ∀ p ∈ R, Set.InjOn (fun x => x % p) S) :
    populationCoveredFraction S R = occupancy R.toList S.card := by
  simpa using population_eq_occupancy_of_injective R.toList R.nodup_toList
    (fun p hp => hR p (by simpa using hp)) S (fun p hp => hinj p (by simpa using hp))

/-- Negative dependence for separated populations, with no span bound on the
moduli. Injectivity is required on the UNION, not on the two sets separately. -/
theorem disjoint_population_coverage_of_injective (R S T : Finset ℕ)
    (hR : ∀ p ∈ R, 0 < p) (hST : Disjoint S T)
    (hinj : ∀ p ∈ R, Set.InjOn (fun x => x % p) (↑(S ∪ T) : Set ℕ)) :
    populationCoveredFraction (S ∪ T) R ≤
      populationCoveredFraction S R*populationCoveredFraction T R := by
  rw [population_eq_finset_occupancy_of_injective R (S ∪ T) hR hinj,
    population_eq_finset_occupancy_of_injective R S hR
      (fun p hp => (hinj p hp).mono subset_union_left),
    population_eq_finset_occupancy_of_injective R T hR
      (fun p hp => (hinj p hp).mono subset_union_right),card_union_of_disjoint hST]
  apply occupancy_submultiplicative
  intro p hp
  have hpR : p ∈ R := by simpa using hp
  refine ⟨hR p hpR,?_⟩
  have hh := card_le_modulus_of_residue_injective (S ∪ T) p (hR p hpR) (hinj p hpR)
  rwa [card_union_of_disjoint hST] at hh

/-- Conditional injection on the actual core survivors suffices. No uniform
injection assertion about arbitrary prime cores is hidden in this statement. -/
theorem coreCoverWeight_union_le_of_injective (P R S T : Finset ℕ)
    (hR : ∀ p ∈ R, 0 < p) (hST : Disjoint S T) (r : Phase P)
    (hinj : ∀ p ∈ R, Set.InjOn (fun x => x % p) (populationSurvivors (S ∪ T) P r)) :
    coreCoverWeight P R (S ∪ T) r ≤ coreCoverWeight P R S r*coreCoverWeight P R T r := by
  unfold coreCoverWeight
  rw [populationSurvivors_union_population] at hinj ⊢
  exact disjoint_population_coverage_of_injective R _ _ hR
    (hST.mono (filter_subset _ _) (filter_subset _ _)) hinj

#print axioms population_eq_occupancy_of_injective
#print axioms disjoint_population_coverage_of_injective
#print axioms coreCoverWeight_union_le_of_injective
end Erdos970.OneHitLogConcavity
