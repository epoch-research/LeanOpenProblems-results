import Submission.SerialMinimum

/-! Transport finite circuit decompositions along an injective coordinate map. -/
open scoped Classical
namespace Erdos184Serial
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
variable {E F : Type*} [DecidableEq E] [DecidableEq F]
variable {C : Code E} {B : Code F} (f : E ↪ F)
variable (hv : ∀ s, C.valid s ↔ B.valid (s.map f))
include hv

lemma circuit_map_iff (s : Finset E) : Circuit B (s.map f) ↔ Circuit C s := by
  constructor
  · intro hc
    refine ⟨(hv s).mpr hc.1,Finset.map_nonempty.mp hc.2.1,?_⟩
    intro t hts ht htne
    apply Finset.map_injective f
    exact hc.2.2 _ (Finset.map_subset_map.mpr hts) ((hv t).mp ht) (Finset.map_nonempty.mpr htne)
  · intro hc
    refine ⟨(hv s).mp hc.1,Finset.map_nonempty.mpr hc.2.1,?_⟩
    intro t hts ht htne
    obtain ⟨u,hus,rfl⟩ := Finset.subset_map_iff.mp hts
    have he := hc.2.2 u hus ((hv u).mpr ht) (Finset.map_nonempty.mp htne)
    rw [he]

lemma map_partition_exists {s : Finset E} {P : Finset (Finset E)}
    (hP : Partition C s P) : ∃ D, Partition B (s.map f) D ∧ D.card = P.card := by
  let a : P → Finset F := fun i => i.val.map f
  have ha : ∀ i, Circuit B (a i) := fun i => (circuit_map_iff f hv i.val).mpr (hP.1 i.val i.property)
  have hc (y : F) : (∑ i, if y ∈ a i then (1 : ℝ) else 0) = if y ∈ s.map f then 1 else 0 := by
    by_cases hy : ∃ x, f x = y
    · obtain ⟨x,rfl⟩ := hy
      simpa only [a,Finset.mem_map'] using hP.coverReal x
    · have hn : ∀ t : Finset E, y ∉ t.map f := by
        intro t ht
        obtain ⟨x,_,hx⟩ := Finset.mem_map.mp ht
        exact hy ⟨x,hx⟩
      simp only [a,if_neg (hn _),Finset.sum_const_zero]
  obtain ⟨D,hD,hcard⟩ := partition_of_coverReal B (s.map f) a ha hc
  exact ⟨D,hD,by simpa only [Fintype.card_coe] using hcard⟩

lemma unmap_partition_exists {s : Finset E} {P : Finset (Finset F)}
    (hP : Partition B (s.map f) P) : ∃ D, Partition C s D ∧ D.card = P.card := by
  have hex : ∀ i : P, ∃ a : Finset E, i.val = a.map f := by
    intro i
    obtain ⟨a,_,he⟩ := Finset.subset_map_iff.mp (hP.piece_subset i.property)
    exact ⟨a,he⟩
  choose a he using hex
  have ha : ∀ i, Circuit C (a i) := by
    intro i
    apply (circuit_map_iff f hv (a i)).mp
    rw [← he i]
    exact hP.1 i.val i.property
  have hc (x : E) : (∑ i, if x ∈ a i then (1 : ℝ) else 0) = if x ∈ s then 1 else 0 := by
    have h := hP.coverReal (f x)
    simp_rw [he,Finset.mem_map'] at h
    exact h
  obtain ⟨D,hD,hcard⟩ := partition_of_coverReal C s a ha hc
  exact ⟨D,hD,by simpa only [Fintype.card_coe] using hcard⟩

lemma hasNumber_map_iff (s : Finset E) (k : ℕ) :
    HasNumber B (s.map f) k ↔ HasNumber C s k := by
  constructor
  · rintro ⟨⟨P,hP,hPk⟩,hlo⟩
    obtain ⟨D,hD,hcard⟩ := unmap_partition_exists f hv hP
    refine ⟨⟨D,hD,hcard.trans hPk⟩,?_⟩
    intro A hA
    obtain ⟨Q,hQ,hcardQ⟩ := map_partition_exists f hv hA
    have h := hlo Q hQ
    omega
  · rintro ⟨⟨P,hP,hPk⟩,hlo⟩
    obtain ⟨D,hD,hcard⟩ := map_partition_exists f hv hP
    refine ⟨⟨D,hD,hcard.trans hPk⟩,?_⟩
    intro A hA
    obtain ⟨Q,hQ,hcardQ⟩ := unmap_partition_exists f hv hA
    have h := hlo Q hQ
    omega

lemma minimalCore_map_iff (s : Finset E) (k : ℕ) :
    MinimalCore B (s.map f) k ↔ MinimalCore C s k := by
  constructor
  · intro hm
    refine ⟨(hasNumber_map_iff f hv s k).mp hm.1,?_⟩
    intro t hts ht
    obtain ⟨P,hP,hcard⟩ := hm.2 (t.map f) (Finset.map_ssubset_map.mpr hts) ((hv t).mp ht)
    obtain ⟨D,hD,hcardD⟩ := unmap_partition_exists f hv hP
    exact ⟨D,hD,by omega⟩
  · intro hm
    refine ⟨(hasNumber_map_iff f hv s k).mpr hm.1,?_⟩
    intro t hts ht
    obtain ⟨u,hus,rfl⟩ := Finset.subset_map_iff.mp hts.1
    have hstrict : u ⊂ s := Finset.map_ssubset_map.mp hts
    obtain ⟨P,hP,hcard⟩ := hm.2 u hstrict ((hv u).mpr ht)
    obtain ⟨D,hD,hcardD⟩ := map_partition_exists f hv hP
    exact ⟨D,hD,by omega⟩

lemma rigid_map_iff (s : Finset E) (k : ℕ) :
    Rigid B (s.map f) k ↔ Rigid C s k := by
  constructor
  · intro hr D hD
    obtain ⟨P,hP,hcard⟩ := map_partition_exists f hv hD
    have h := hr P hP
    omega
  · intro hr D hD
    obtain ⟨P,hP,hcard⟩ := unmap_partition_exists f hv hD
    have h := hr P hP
    omega

#print axioms circuit_map_iff
#print axioms hasNumber_map_iff
#print axioms minimalCore_map_iff
#print axioms rigid_map_iff
end Erdos184Serial
