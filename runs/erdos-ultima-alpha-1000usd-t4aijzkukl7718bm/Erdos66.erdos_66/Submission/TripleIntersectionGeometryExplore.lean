import Submission.FiniteBernoulliExplore
import Submission.BoundedConflictExplore

/-! Fixed-sum triple intersections have uniformly bounded coordinate
incidence and conflict degree. All three coordinates are required distinct. -/
namespace Erdos66TripleIntersectionGeometry
open Erdos66FiniteBernoulli
open scoped Classical
set_option maxHeartbeats 2200000

abbrev Triple (L : ℕ) := Fin (L+1) × Fin (L+1) × Fin (L+1)

def coords {L : ℕ} (e : Triple L) : Finset (Fin (L+1)) := {e.1,e.2.1,e.2.2}

noncomputable def triples (L N n z : ℕ) : Finset (Triple L) :=
  Finset.univ.filter (fun e ↦ N ≤ e.1.val ∧ N ≤ e.2.1.val ∧
    e.1.val+e.2.1.val=n ∧ e.1.val+e.2.2.val=z ∧
    e.1 ≠ e.2.1 ∧ e.1 ≠ e.2.2 ∧ e.2.1 ≠ e.2.2)

lemma mem_triples {L N n z : ℕ} {e : Triple L} : e ∈ triples L N n z ↔
    N ≤ e.1.val ∧ N ≤ e.2.1.val ∧ e.1.val+e.2.1.val=n ∧ e.1.val+e.2.2.val=z ∧
      e.1 ≠ e.2.1 ∧ e.1 ≠ e.2.2 ∧ e.2.1 ≠ e.2.2 := by simp only [triples,Finset.mem_filter,Finset.mem_univ,true_and]

lemma coords_nonempty {L : ℕ} (e : Triple L) : (coords e).Nonempty := by
  exact ⟨e.1,by simp [coords]⟩

lemma coords_card_le {L : ℕ} (e : Triple L) : (coords e).card ≤ 3 := Finset.card_le_three

lemma coords_card {L N n z : ℕ} {e : Triple L} (he : e∈triples L N n z) : (coords e).card=3 := by
  obtain ⟨_,_,_,_,h1,h2,h3⟩ := mem_triples.mp he
  simp [coords,h1,h2,h3]

lemma first_injective {L N n z : ℕ} :
    Set.InjOn (fun e : Triple L ↦ e.1.val) (triples L N n z : Set (Triple L)) := by
  intro e he f hf h
  obtain ⟨_,_,he1,he2,_⟩ := mem_triples.mp he
  obtain ⟨_,_,hf1,hf2,_⟩ := mem_triples.mp hf
  dsimp only at h
  exact Prod.ext (Fin.ext h) (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))

lemma third_injective {L N n z : ℕ} :
    Set.InjOn (fun e : Triple L ↦ e.2.2.val) (triples L N n z : Set (Triple L)) := by
  intro e he f hf h
  obtain ⟨_,_,he1,he2,_⟩ := mem_triples.mp he
  obtain ⟨_,_,hf1,hf2,_⟩ := mem_triples.mp hf
  dsimp only at h
  exact Prod.ext (Fin.ext (by omega)) (Prod.ext (Fin.ext (by omega)) (Fin.ext h))

lemma triples_card_le (L N n z : ℕ) : (triples L N n z).card ≤ n+1 := by
  have hh : (triples L N n z).card ≤ (Finset.range (n+1)).card := by
    apply Finset.card_le_card_of_injOn (fun e : Triple L ↦ e.1.val)
    · intro e he
      have hh := (mem_triples.mp he).2.2.1
      change e.1.val ∈ Finset.range (n+1)
      exact Finset.mem_range.mpr (by omega)
    · exact first_injective
  simpa only [Finset.card_range] using hh

lemma incident_card (L N n z : ℕ) (i : Fin (L+1)) :
    ((triples L N n z).filter (fun e ↦ i ∈ coords e)).card ≤ 3 := by
  have hh : ((triples L N n z).filter (fun e ↦ i ∈ coords e)).card ≤
      ({i.val,n-i.val,z-i.val} : Finset ℕ).card := by
    apply Finset.card_le_card_of_injOn (fun e : Triple L ↦ e.1.val)
    · intro e he
      obtain ⟨he,hi⟩ := Finset.mem_filter.mp he
      obtain ⟨_,_,hn,hz,_⟩ := mem_triples.mp he
      simp only [coords,Finset.mem_insert,Finset.mem_singleton] at hi
      change e.1.val ∈ ({i.val,n-i.val,z-i.val} : Finset ℕ)
      simp only [Finset.mem_insert,Finset.mem_singleton]
      rcases hi with hi | hi | hi
      · exact Or.inl (congrArg Fin.val hi).symm
      · have hv := congrArg Fin.val hi
        exact Or.inr (Or.inl (by omega))
      · have hv := congrArg Fin.val hi
        exact Or.inr (Or.inr (by omega))
    · exact first_injective.mono (Finset.filter_subset _ _)
  exact hh.trans Finset.card_le_three

lemma conflict_card (L N n z : ℕ) (e : Triple L) :
    ((triples L N n z).filter (fun f ↦ ¬ Disjoint (coords e) (coords f))).card ≤ 9 := by
  have hsub : (triples L N n z).filter (fun f ↦ ¬ Disjoint (coords e) (coords f)) ⊆
      (coords e).biUnion (fun i ↦ (triples L N n z).filter (fun f ↦ i∈coords f)) := by
    intro f hf
    obtain ⟨hf,hd⟩ := Finset.mem_filter.mp hf
    obtain ⟨i,hi,hif⟩ := Finset.not_disjoint_iff.mp hd
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hf,hif⟩⟩
  have hh := Finset.card_le_card hsub
  have hb := Finset.card_biUnion_le_card_mul (coords e)
    (fun i ↦ (triples L N n z).filter (fun f ↦ i∈coords f)) 3 (fun i hi ↦ incident_card L N n z i)
  have hc := coords_card_le e
  omega

lemma triple_monomial_mean {L N n z : ℕ} {e : Triple L} (he : e∈triples L N n z)
    (p : Fin (L+1) → ℝ) : (∏ i∈coords e, p i) = p e.1*p e.2.1*p e.2.2 := by
  obtain ⟨_,_,_,_,h1,h2,h3⟩ := mem_triples.mp he
  simp [coords,h1,h2,h3,mul_assoc]

end Erdos66TripleIntersectionGeometry
