import FormalConjecturesUtil

/-! Serial gluing of finite circuit systems. This auxiliary module does not
prove an integral bound for graphical minimal cores or settle Erdős 184. -/
open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
namespace Erdos184Serial

structure Code (E : Type*) [DecidableEq E] where
  valid : Finset E → Prop
  empty : valid ∅
  diff : ∀ {s t}, valid s → valid t → t ⊆ s → valid (s \ t)

variable {E F : Type*} [DecidableEq E] [DecidableEq F]

def Circuit (C : Code E) (s : Finset E) : Prop :=
  C.valid s ∧ s.Nonempty ∧ ∀ t ⊆ s, C.valid t → t.Nonempty → t = s

def Partition (C : Code E) (s : Finset E) (D : Finset (Finset E)) : Prop :=
  (∀ a ∈ D, Circuit C a) ∧
  Set.PairwiseDisjoint (D : Set (Finset E)) (fun a => a) ∧
  D.biUnion id = s

def Rigid (C : Code E) (s : Finset E) (k : ℕ) : Prop :=
  ∀ D, Partition C s D → D.card = k

def serial (C : Code E) (B : Code F) (p : E) (q : F) : Code (E ⊕ F) where
  valid s := C.valid s.toLeft ∧ B.valid s.toRight ∧ (p ∈ s.toLeft ↔ q ∈ s.toRight)
  empty := by
    change C.valid ∅ ∧ B.valid ∅ ∧ (p ∈ (∅ : Finset E) ↔ q ∈ (∅ : Finset F))
    exact ⟨C.empty,B.empty,by simp⟩
  diff := by
    intro s t hs ht hts
    rw [Finset.toLeft_sdiff,Finset.toRight_sdiff]
    refine ⟨C.diff hs.1 ht.1 (Finset.toLeft_subset_toLeft hts),
      B.diff hs.2.1 ht.2.1 (Finset.toRight_subset_toRight hts),?_⟩
    simp only [Finset.mem_sdiff]
    exact and_congr hs.2.2 (not_congr ht.2.2)

lemma serial_valid_left {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset E} (hs : C.valid s) (hp : p ∉ s) :
    (serial C B p q).valid (s.disjSum ∅) := by
  change C.valid (s.disjSum ∅).toLeft ∧ B.valid (s.disjSum ∅).toRight ∧ _
  simpa only [Finset.toLeft_disjSum,Finset.toRight_disjSum,Finset.notMem_empty,
    iff_false] using And.intro hs (And.intro B.empty hp)

lemma serial_valid_right {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset F} (hs : B.valid s) (hp : q ∉ s) :
    (serial C B p q).valid ((∅ : Finset E).disjSum s) := by
  change C.valid ((∅ : Finset E).disjSum s).toLeft ∧ B.valid ((∅ : Finset E).disjSum s).toRight ∧ _
  simpa only [Finset.toLeft_disjSum,Finset.toRight_disjSum,Finset.notMem_empty,
    false_iff] using And.intro C.empty (And.intro hs hp)

lemma circuit_left {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset (E ⊕ F)} (hs : Circuit (serial C B p q) s)
    (hne : s.toLeft.Nonempty) : Circuit C s.toLeft := by
  refine ⟨hs.1.1,hne,?_⟩
  intro t hts ht htne
  by_cases hp : p ∈ t
  · by_contra htsne
    have hdiff : (s.toLeft \ t).Nonempty := Finset.sdiff_nonempty.mpr (fun h => htsne (Finset.Subset.antisymm hts h))
    have hval : (serial C B p q).valid ((s.toLeft \ t).disjSum ∅) :=
      serial_valid_left (C.diff hs.1.1 ht hts) (by simp [hp])
    have hsub : (s.toLeft \ t).disjSum (∅ : Finset F) ⊆ s :=
      Finset.disjSum_subset.mpr ⟨Finset.sdiff_subset,Finset.empty_subset _⟩
    have hne' : ((s.toLeft \ t).disjSum (∅ : Finset F)).Nonempty := by
      obtain ⟨x,hx⟩ := hdiff
      exact ⟨Sum.inl x,by simpa using hx⟩
    have heq := hs.2.2 _ hsub hval hne'
    have he := congrArg Finset.toLeft heq
    simp only [Finset.toLeft_disjSum] at he
    have hps : p ∈ s.toLeft := hts hp
    rw [← he] at hps
    exact (Finset.mem_sdiff.mp hps).2 hp
  · have hval : (serial C B p q).valid (t.disjSum ∅) := serial_valid_left ht hp
    have hsub : t.disjSum (∅ : Finset F) ⊆ s :=
      Finset.disjSum_subset.mpr ⟨hts,Finset.empty_subset _⟩
    have hne' : (t.disjSum (∅ : Finset F)).Nonempty := by
      obtain ⟨x,hx⟩ := htne
      exact ⟨Sum.inl x,by simpa using hx⟩
    simpa only [Finset.toLeft_disjSum] using congrArg Finset.toLeft (hs.2.2 _ hsub hval hne')

lemma circuit_right {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset (E ⊕ F)} (hs : Circuit (serial C B p q) s)
    (hne : s.toRight.Nonempty) : Circuit B s.toRight := by
  refine ⟨hs.1.2.1,hne,?_⟩
  intro t hts ht htne
  by_cases hp : q ∈ t
  · by_contra htsne
    have hdiff : (s.toRight \ t).Nonempty := Finset.sdiff_nonempty.mpr (fun h => htsne (Finset.Subset.antisymm hts h))
    have hval : (serial C B p q).valid ((∅ : Finset E).disjSum (s.toRight \ t)) :=
      serial_valid_right (B.diff hs.1.2.1 ht hts) (by simp [hp])
    have hsub : (∅ : Finset E).disjSum (s.toRight \ t) ⊆ s :=
      Finset.disjSum_subset.mpr ⟨Finset.empty_subset _,Finset.sdiff_subset⟩
    have hne' : ((∅ : Finset E).disjSum (s.toRight \ t)).Nonempty := by
      obtain ⟨x,hx⟩ := hdiff
      exact ⟨Sum.inr x,by simpa using hx⟩
    have heq := hs.2.2 _ hsub hval hne'
    have he := congrArg Finset.toRight heq
    simp only [Finset.toRight_disjSum] at he
    have hps : q ∈ s.toRight := hts hp
    rw [← he] at hps
    exact (Finset.mem_sdiff.mp hps).2 hp
  · have hval : (serial C B p q).valid ((∅ : Finset E).disjSum t) := serial_valid_right ht hp
    have hsub : (∅ : Finset E).disjSum t ⊆ s :=
      Finset.disjSum_subset.mpr ⟨Finset.empty_subset _,hts⟩
    have hne' : ((∅ : Finset E).disjSum t).Nonempty := by
      obtain ⟨x,hx⟩ := htne
      exact ⟨Sum.inr x,by simpa using hx⟩
    simpa only [Finset.toRight_disjSum] using congrArg Finset.toRight (hs.2.2 _ hsub hval hne')

lemma circuit_cross_iff {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset (E ⊕ F)} (hs : Circuit (serial C B p q) s) :
    s.toLeft.Nonempty ∧ s.toRight.Nonempty ↔ p ∈ s.toLeft := by
  constructor
  · rintro ⟨hl,hr⟩
    by_contra hp
    have hval := serial_valid_left (B := B) (q := q) hs.1.1 hp
    have hsub : s.toLeft.disjSum (∅ : Finset F) ⊆ s :=
      Finset.disjSum_subset.mpr ⟨Finset.Subset.refl _,Finset.empty_subset _⟩
    obtain ⟨x,hx⟩ := hl
    have heq := hs.2.2 _ hsub hval ⟨Sum.inl x,by simpa using hx⟩
    have he := congrArg Finset.toRight heq
    simp only [Finset.toRight_disjSum] at he
    exact hr.ne_empty he.symm
  · intro hp
    exact ⟨⟨p,hp⟩,⟨q,hs.1.2.2.mp hp⟩⟩

lemma nonempty_projection {s : Finset (E ⊕ F)} (hs : s.Nonempty) :
    s.toLeft.Nonempty ∨ s.toRight.Nonempty := by
  obtain ⟨x,hx⟩ := hs
  cases x with
  | inl x => exact Or.inl ⟨x,Finset.mem_toLeft.mpr hx⟩
  | inr x => exact Or.inr ⟨x,Finset.mem_toRight.mpr hx⟩

#print axioms circuit_left
#print axioms circuit_right
#print axioms circuit_cross_iff


def leftParts (D : Finset (Finset (E ⊕ F))) : Finset (Finset E) :=
  (D.filter (fun a => a.toLeft.Nonempty)).image Finset.toLeft

def rightParts (D : Finset (Finset (E ⊕ F))) : Finset (Finset F) :=
  (D.filter (fun a => a.toRight.Nonempty)).image Finset.toRight

lemma partition_left {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset (E ⊕ F)} {D : Finset (Finset (E ⊕ F))}
    (hD : Partition (serial C B p q) s D) : Partition C s.toLeft (leftParts D) := by
  refine ⟨?_,?_,?_⟩
  · intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    exact circuit_left (hD.1 b (Finset.mem_filter.mp hb).1) (Finset.mem_filter.mp hb).2
  · intro a ha b hb hne
    obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Finset.disjoint_left.mp (hD.2.1 (Finset.mem_filter.mp ha').1
      (Finset.mem_filter.mp hb').1 (fun h => hne (congrArg Finset.toLeft h)))
      (Finset.mem_toLeft.mp hx) (Finset.mem_toLeft.mp hy)
  · ext x
    simp only [Finset.mem_biUnion,id_eq,leftParts,Finset.mem_image,Finset.mem_filter,
      Finset.mem_toLeft]
    constructor
    · rintro ⟨a,⟨b,⟨hb,hbne⟩,rfl⟩,hx⟩
      rw [← hD.2.2]
      exact Finset.mem_biUnion.mpr ⟨b,hb,Finset.mem_toLeft.mp hx⟩
    · intro hx
      rw [← hD.2.2] at hx
      obtain ⟨b,hb,hx⟩ := Finset.mem_biUnion.mp hx
      exact ⟨b.toLeft,⟨b,⟨hb,⟨x,Finset.mem_toLeft.mpr hx⟩⟩,rfl⟩,Finset.mem_toLeft.mpr hx⟩

lemma partition_right {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset (E ⊕ F)} {D : Finset (Finset (E ⊕ F))}
    (hD : Partition (serial C B p q) s D) : Partition B s.toRight (rightParts D) := by
  refine ⟨?_,?_,?_⟩
  · intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    exact circuit_right (hD.1 b (Finset.mem_filter.mp hb).1) (Finset.mem_filter.mp hb).2
  · intro a ha b hb hne
    obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Finset.disjoint_left.mp (hD.2.1 (Finset.mem_filter.mp ha').1
      (Finset.mem_filter.mp hb').1 (fun h => hne (congrArg Finset.toRight h)))
      (Finset.mem_toRight.mp hx) (Finset.mem_toRight.mp hy)
  · ext x
    simp only [Finset.mem_biUnion,id_eq,rightParts,Finset.mem_image,Finset.mem_filter,
      Finset.mem_toRight]
    constructor
    · rintro ⟨a,⟨b,⟨hb,hbne⟩,rfl⟩,hx⟩
      rw [← hD.2.2]
      exact Finset.mem_biUnion.mpr ⟨b,hb,Finset.mem_toRight.mp hx⟩
    · intro hx
      rw [← hD.2.2] at hx
      obtain ⟨b,hb,hx⟩ := Finset.mem_biUnion.mp hx
      exact ⟨b.toRight,⟨b,⟨hb,⟨x,Finset.mem_toRight.mpr hx⟩⟩,rfl⟩,Finset.mem_toRight.mpr hx⟩

lemma leftParts_card {D : Finset (Finset (E ⊕ F))}
    (hd : Set.PairwiseDisjoint (D : Set (Finset (E ⊕ F))) (fun a => a)) :
    (leftParts D).card = (D.filter fun a => a.toLeft.Nonempty).card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb he
  by_contra hn
  obtain ⟨x,hx⟩ := (Finset.mem_filter.mp ha).2
  have hy : x ∈ b.toLeft := he ▸ hx
  exact Finset.disjoint_left.mp (hd (Finset.mem_filter.mp ha).1
    (Finset.mem_filter.mp hb).1 hn) (Finset.mem_toLeft.mp hx) (Finset.mem_toLeft.mp hy)

lemma rightParts_card {D : Finset (Finset (E ⊕ F))}
    (hd : Set.PairwiseDisjoint (D : Set (Finset (E ⊕ F))) (fun a => a)) :
    (rightParts D).card = (D.filter fun a => a.toRight.Nonempty).card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb he
  by_contra hn
  obtain ⟨x,hx⟩ := (Finset.mem_filter.mp ha).2
  have hy : x ∈ b.toRight := he ▸ hx
  exact Finset.disjoint_left.mp (hd (Finset.mem_filter.mp ha).1
    (Finset.mem_filter.mp hb).1 hn) (Finset.mem_toRight.mp hx) (Finset.mem_toRight.mp hy)

/-- Exactly one circuit crosses a used serial interface. -/
lemma unique_cross {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset (E ⊕ F)} {D : Finset (Finset (E ⊕ F))}
    (hD : Partition (serial C B p q) s D) (hp : p ∈ s.toLeft) :
    ∃ a ∈ D, (D.filter fun b => b.toLeft.Nonempty ∧ b.toRight.Nonempty) = {a} := by
  have hps : Sum.inl p ∈ s := Finset.mem_toLeft.mp hp
  rw [← hD.2.2] at hps
  obtain ⟨a,ha,hpa⟩ := Finset.mem_biUnion.mp hps
  refine ⟨a,ha,?_⟩
  ext b
  simp only [Finset.mem_filter,Finset.mem_singleton]
  constructor
  · rintro ⟨hb,hcross⟩
    have hpb := Finset.mem_toLeft.mp ((circuit_cross_iff (hD.1 b hb)).mp hcross)
    by_contra hn
    exact Finset.disjoint_left.mp (hD.2.1 hb ha hn) hpb hpa
  · rintro rfl
    exact ⟨ha,(circuit_cross_iff (hD.1 _ ha)).mpr (Finset.mem_toLeft.mpr hpa)⟩

lemma projected_card_sum {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset (E ⊕ F)} {D : Finset (Finset (E ⊕ F))}
    (hD : Partition (serial C B p q) s D) (hp : p ∈ s.toLeft) :
    (leftParts D).card + (rightParts D).card = D.card + 1 := by
  let L := D.filter fun a => a.toLeft.Nonempty
  let R := D.filter fun a => a.toRight.Nonempty
  have hu : L ∪ R = D := by
    ext a
    simp only [L,R,Finset.mem_union,Finset.mem_filter]
    constructor
    · tauto
    · intro ha
      rcases nonempty_projection (hD.1 a ha).2.1 with hl | hr
      · exact Or.inl ⟨ha,hl⟩
      · exact Or.inr ⟨ha,hr⟩
  have hi : L ∩ R = D.filter (fun a => a.toLeft.Nonempty ∧ a.toRight.Nonempty) := by
    ext a
    simp only [L,R,Finset.mem_inter,Finset.mem_filter]
    tauto
  obtain ⟨a,ha,he⟩ := unique_cross hD hp
  have hc := Finset.card_union_add_card_inter L R
  rw [hu,hi,he,Finset.card_singleton] at hc
  rw [leftParts_card hD.2.1,rightParts_card hD.2.1]
  exact hc.symm

/-- Serial gluing preserves rigidity and adds partition counts minus one.
The ports remain as two tied coordinates; this is not unrestricted matroid two-sum. -/
lemma serial_rigid {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset (E ⊕ F)} {k l : ℕ}
    (hC : Rigid C s.toLeft k) (hB : Rigid B s.toRight l) (hp : p ∈ s.toLeft) :
    Rigid (serial C B p q) s (k + l - 1) := by
  intro D hD
  have hc := projected_card_sum hD hp
  rw [hC _ (partition_left hD),hB _ (partition_right hD)] at hc
  omega

#print axioms serial_rigid


lemma exists_circuit_subset (C : Code E) {s : Finset E}
    (hs : C.valid s) (hne : s.Nonempty) : ∃ a ⊆ s, Circuit C a := by
  classical
  let T := s.powerset.filter (fun a => C.valid a ∧ a.Nonempty)
  have hT : s ∈ T := by simp [T,hs,hne]
  obtain ⟨a,ha,hmin⟩ := Finset.exists_min_image T Finset.card ⟨s,hT⟩
  have has := Finset.mem_powerset.mp (Finset.mem_filter.mp ha).1
  refine ⟨a,has,(Finset.mem_filter.mp ha).2.1,(Finset.mem_filter.mp ha).2.2,?_⟩
  intro t hta ht htne
  apply Finset.eq_of_subset_of_card_le hta
  apply hmin t
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hta.trans has),ht,htne⟩

lemma Partition.piece_subset {C : Code E} {s : Finset E} {D : Finset (Finset E)}
    (hD : Partition C s D) {a : Finset E} (ha : a ∈ D) : a ⊆ s := by
  intro x hx
  rw [← hD.2.2]
  exact Finset.mem_biUnion.mpr ⟨a,ha,hx⟩

lemma partition_empty (C : Code E) : Partition C ∅ ∅ := by
  refine ⟨by simp,?_,by simp⟩
  intro a ha
  simp at ha

lemma partition_singleton {C : Code E} {a : Finset E} (ha : Circuit C a) :
    Partition C a {a} := by
  refine ⟨?_,?_,by simp⟩
  · intro b hb
    exact Finset.mem_singleton.mp hb ▸ ha
  · intro b hb c hc hne
    have hb' := Finset.mem_singleton.mp hb
    have hc' := Finset.mem_singleton.mp hc
    exact (hne (hb'.trans hc'.symm)).elim

lemma Partition.join {C : Code E} {s t : Finset E} {D A : Finset (Finset E)}
    (hD : Partition C s D) (hA : Partition C t A) (hdis : Disjoint s t) :
    Partition C (s ∪ t) (D ∪ A) ∧ (D ∪ A).card = D.card + A.card := by
  have hc : ∀ d ∈ D, ∀ a ∈ A, Disjoint d a := by
    intro d hd a ha
    exact hdis.mono (hD.piece_subset hd) (hA.piece_subset ha)
  have hDA : Disjoint D A := by
    apply Finset.disjoint_left.mpr
    intro a hd ha
    obtain ⟨x,hx⟩ := (hD.1 a hd).2.1
    exact Finset.disjoint_left.mp (hc a hd a ha) hx hx
  refine ⟨⟨?_,?_,?_⟩,Finset.card_union_of_disjoint hDA⟩
  · intro a ha
    rcases Finset.mem_union.mp ha with hd | he
    · exact hD.1 a hd
    · exact hA.1 a he
  · intro a ha b hb hn
    rcases Finset.mem_union.mp ha with ha | ha <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · exact hD.2.1 ha hb hn
    · exact hc a ha b hb
    · exact (hc b hb a ha).symm
    · exact hA.2.1 ha hb hn
  · rw [Finset.union_biUnion,hD.2.2,hA.2.2]

lemma exists_partition (C : Code E) {s : Finset E} (hs : C.valid s) :
    ∃ D, Partition C s D := by
  classical
  induction s using Finset.strongInductionOn
  rename_i s ih
  by_cases hne : s.Nonempty
  · obtain ⟨a,has,ha⟩ := exists_circuit_subset C hs hne
    obtain ⟨D,hD⟩ := ih (s \ a) (Finset.sdiff_ssubset has ha.2.1) (C.diff hs ha.1 has)
    have hd : Disjoint a (s \ a) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (Finset.mem_sdiff.mp hy).2 hx
    obtain ⟨hpart,_⟩ := (partition_singleton ha).join hD hd
    rw [Finset.union_sdiff_of_subset has] at hpart
    exact ⟨_,hpart⟩
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst s
    exact ⟨∅,partition_empty C⟩

/-- Strict minimality, expressed without choosing a numerical optimum. -/
def Minimal (C : Code E) (s : Finset E) (k : ℕ) : Prop :=
  (∃ D, Partition C s D ∧ D.card = k) ∧
    ∀ t ⊂ s, C.valid t → ∃ D, Partition C t D ∧ D.card < k

lemma rigid_minimal {C : Code E} {s : Finset E} {k : ℕ}
    (hs : C.valid s) (hr : Rigid C s k) : Minimal C s k := by
  obtain ⟨D,hD⟩ := exists_partition C hs
  refine ⟨⟨D,hD,hr D hD⟩,?_⟩
  intro t hts ht
  obtain ⟨A,hA⟩ := exists_partition C ht
  obtain ⟨B,hB⟩ := exists_partition C (C.diff hs ht hts.1)
  have hdis : Disjoint t (s \ t) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 hx
  obtain ⟨hAB,hcard⟩ := hA.join hB hdis
  rw [Finset.union_sdiff_of_subset hts.1] at hAB
  have hk := hr _ hAB
  have hBne : B.Nonempty := by
    by_contra hn
    have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hcov := hB.2.2
    simp only [he,Finset.biUnion_empty] at hcov
    have hsub : s ⊆ t := Finset.sdiff_eq_empty_iff_subset.mp hcov.symm
    exact hts.2 hsub
  have hp := Finset.card_pos.mpr hBne
  refine ⟨A,hA,?_⟩
  omega

lemma serial_minimal {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset (E ⊕ F)} {k l : ℕ}
    (hs : (serial C B p q).valid s)
    (hC : Rigid C s.toLeft k) (hB : Rigid B s.toRight l) (hp : p ∈ s.toLeft) :
    Minimal (serial C B p q) s (k + l - 1) :=
  rigid_minimal hs (serial_rigid hC hB hp)

#print axioms serial_minimal


lemma left_circuit_lift {C : Code E} {B : Code F} {p : E} {q : F}
    {a : Finset E} (ha : Circuit C a) (hp : p ∉ a) :
    Circuit (serial C B p q) (a.disjSum ∅) := by
  refine ⟨serial_valid_left ha.1 hp,?_,?_⟩
  · obtain ⟨x,hx⟩ := ha.2.1
    exact ⟨Sum.inl x,by simpa using hx⟩
  · intro t hta ht htne
    have htR : t.toRight = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro y hy
      have h := hta (Finset.mem_toRight.mp hy)
      simpa using h)
    have htL : t.toLeft ⊆ a := (Finset.subset_disjSum.mp hta).1
    have hn : t.toLeft.Nonempty := (nonempty_projection htne).resolve_right (by simp [htR])
    have he := ha.2.2 t.toLeft htL ht.1 hn
    rw [← t.toLeft_disjSum_toRight,he,htR]

lemma right_circuit_lift {C : Code E} {B : Code F} {p : E} {q : F}
    {a : Finset F} (ha : Circuit B a) (hp : q ∉ a) :
    Circuit (serial C B p q) ((∅ : Finset E).disjSum a) := by
  refine ⟨serial_valid_right ha.1 hp,?_,?_⟩
  · obtain ⟨x,hx⟩ := ha.2.1
    exact ⟨Sum.inr x,by simpa using hx⟩
  · intro t hta ht htne
    have htL : t.toLeft = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro y hy
      have h := hta (Finset.mem_toLeft.mp hy)
      simpa using h)
    have htR : t.toRight ⊆ a := (Finset.subset_disjSum.mp hta).2
    have hn : t.toRight.Nonempty := (nonempty_projection htne).resolve_left (by simp [htL])
    have he := ha.2.2 t.toRight htR ht.2.1 hn
    rw [← t.toLeft_disjSum_toRight,he,htL]

lemma cross_circuit_lift {C : Code E} {B : Code F} {p : E} {q : F}
    {a : Finset E} {b : Finset F} (ha : Circuit C a) (hb : Circuit B b)
    (hp : p ∈ a) (hq : q ∈ b) : Circuit (serial C B p q) (a.disjSum b) := by
  refine ⟨?_,⟨Sum.inl p,by simpa using hp⟩,?_⟩
  · change C.valid (a.disjSum b).toLeft ∧ B.valid (a.disjSum b).toRight ∧ _
    simpa only [Finset.toLeft_disjSum,Finset.toRight_disjSum] using
      And.intro ha.1 (And.intro hb.1 (iff_of_true hp hq))
  · intro t htab ht htne
    obtain ⟨htL,htR⟩ := Finset.subset_disjSum.mp htab
    have hnL : t.toLeft.Nonempty := by
      rcases nonempty_projection htne with hl | hr
      · exact hl
      · have heR := hb.2.2 t.toRight htR ht.2.1 hr
        exact ⟨p,ht.2.2.mpr (heR.symm ▸ hq)⟩
    have heL := ha.2.2 t.toLeft htL ht.1 hnL
    have hnR : t.toRight.Nonempty := ⟨q,ht.2.2.mp (heL.symm ▸ hp)⟩
    have heR := hb.2.2 t.toRight htR ht.2.1 hnR
    rw [← t.toLeft_disjSum_toRight,heL,heR]

#print axioms cross_circuit_lift


section Fractional
variable {I J : Type*} [Fintype I] [Fintype J]

abbrev GlueIndex (a : I → Finset E) (b : J → Finset F) (p : E) (q : F) :=
  {i // p ∉ a i} ⊕ ({j // q ∉ b j} ⊕ ({i // p ∈ a i} × {j // q ∈ b j}))

def gluePiece (a : I → Finset E) (b : J → Finset F) (p : E) (q : F) :
    GlueIndex a b p q → Finset (E ⊕ F)
  | .inl i => (a i).disjSum ∅
  | .inr (.inl j) => (∅ : Finset E).disjSum (b j)
  | .inr (.inr ij) => (a ij.1).disjSum (b ij.2)

def glueWeight (a : I → Finset E) (b : J → Finset F) (p : E) (q : F)
    (x : I → ℝ) (y : J → ℝ) : GlueIndex a b p q → ℝ
  | .inl i => x i
  | .inr (.inl j) => y j
  | .inr (.inr ij) => x ij.1 * y ij.2

lemma gluePiece_circuit {C : Code E} {B : Code F}
    (a : I → Finset E) (b : J → Finset F) (p : E) (q : F)
    (ha : ∀ i, Circuit C (a i)) (hb : ∀ j, Circuit B (b j)) :
    ∀ k, Circuit (serial C B p q) (gluePiece a b p q k) := by
  intro k
  rcases k with i | (j | ij)
  · exact left_circuit_lift (ha i) i.property
  · exact right_circuit_lift (hb j) j.property
  · exact cross_circuit_lift (ha ij.1) (hb ij.2) ij.1.property ij.2.property

lemma sum_subtype_ite (P : I → Prop) [DecidablePred P] (x : I → ℝ) :
    (∑ i : {i // P i}, x i) = ∑ i, if P i then x i else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp) x,Finset.sum_filter]

lemma glueWeight_nonneg (a : I → Finset E) (b : J → Finset F) (p : E) (q : F)
    (x : I → ℝ) (y : J → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j) :
    ∀ k, 0 ≤ glueWeight a b p q x y k := by
  intro k
  rcases k with i | (j | ij)
  · exact hx i
  · exact hy j
  · exact mul_nonneg (hx ij.1) (hy ij.2)

lemma glue_cover (a : I → Finset E) (b : J → Finset F) (p : E) (q : F)
    (x : I → ℝ) (y : J → ℝ) (s : Finset E) (t : Finset F)
    (ha : ∀ e, (∑ i, if e ∈ a i then x i else 0) = if e ∈ s then 1 else 0)
    (hb : ∀ e, (∑ j, if e ∈ b j then y j else 0) = if e ∈ t then 1 else 0)
    (hp : p ∈ s) (hq : q ∈ t) :
    ∀ e, (∑ k, if e ∈ gluePiece a b p q k then glueWeight a b p q x y k else 0) =
      if e ∈ s.disjSum t then 1 else 0 := by
  have hpx : (∑ i : {i // p ∈ a i}, x i) = 1 := by
    rw [sum_subtype_ite,ha,if_pos hp]
  have hqy : (∑ j : {j // q ∈ b j}, y j) = 1 := by
    rw [sum_subtype_ite,hb,if_pos hq]
  intro e
  cases e with
  | inl e =>
    simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,gluePiece,glueWeight,
      Finset.inl_mem_disjSum,Finset.notMem_empty,if_false,Finset.sum_const_zero,zero_add]
    have he : (∑ i : {i // p ∈ a i}, ∑ j : {j // q ∈ b j},
        if e ∈ a i then x i * y j else 0) =
        ∑ i : {i // p ∈ a i}, if e ∈ a i then x i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : e ∈ a i
      · simp only [if_pos hi,← Finset.mul_sum,hqy,mul_one]
      · simp [hi]
    rw [he]
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i => p ∈ a i)
      (fun i => if e ∈ a i then x i else 0)
    rw [add_comm,hsplit,ha]
  | inr e =>
    simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,gluePiece,glueWeight,
      Finset.inr_mem_disjSum,Finset.notMem_empty,if_false,Finset.sum_const_zero,zero_add]
    have he : (∑ i : {i // p ∈ a i}, ∑ j : {j // q ∈ b j},
        if e ∈ b j then x i * y j else 0) =
        ∑ j : {j // q ∈ b j}, if e ∈ b j then y j else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : e ∈ b j
      · simp only [if_pos hj,← Finset.sum_mul,hpx,one_mul]
      · simp [hj]
    rw [he]
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun j => q ∈ b j)
      (fun j => if e ∈ b j then y j else 0)
    rw [add_comm,hsplit,hb]

lemma glue_cost (a : I → Finset E) (b : J → Finset F) (p : E) (q : F)
    (x : I → ℝ) (y : J → ℝ)
    (hp : (∑ i : {i // p ∈ a i}, x i) = 1)
    (hq : (∑ j : {j // q ∈ b j}, y j) = 1) :
    (∑ k, glueWeight a b p q x y k) = (∑ i, x i) + (∑ j, y j) - 1 := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,glueWeight]
  rw [← Finset.sum_mul_sum, hp,hq]
  have hx := Fintype.sum_subtype_add_sum_subtype (fun i => p ∈ a i) x
  have hy := Fintype.sum_subtype_add_sum_subtype (fun j => q ∈ b j) y
  rw [hp] at hx
  rw [hq] at hy
  linarith

/-- Assemble the circuit property, nonnegativity, exact coverage, and cost. -/
lemma serial_fractional {C : Code E} {B : Code F}
    (a : I → Finset E) (b : J → Finset F) (p : E) (q : F)
    (x : I → ℝ) (y : J → ℝ) (s : Finset E) (t : Finset F)
    (ha : ∀ i, Circuit C (a i)) (hb : ∀ j, Circuit B (b j))
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j)
    (hcovA : ∀ e, (∑ i, if e ∈ a i then x i else 0) = if e ∈ s then 1 else 0)
    (hcovB : ∀ e, (∑ j, if e ∈ b j then y j else 0) = if e ∈ t then 1 else 0)
    (hp : p ∈ s) (hq : q ∈ t) :
    (∀ k, Circuit (serial C B p q) (gluePiece a b p q k)) ∧
    (∀ k, 0 ≤ glueWeight a b p q x y k) ∧
    (∀ e, (∑ k, if e ∈ gluePiece a b p q k then glueWeight a b p q x y k else 0) =
      if e ∈ s.disjSum t then 1 else 0) ∧
    (∑ k, glueWeight a b p q x y k) = (∑ i, x i) + (∑ j, y j) - 1 := by
  refine ⟨gluePiece_circuit a b p q ha hb,glueWeight_nonneg a b p q x y hx hy,
    glue_cover a b p q x y s t hcovA hcovB hp hq,?_⟩
  apply glue_cost
  · rw [sum_subtype_ite,hcovA,if_pos hp]
  · rw [sum_subtype_ite,hcovB,if_pos hq]

#print axioms glue_cover
#print axioms glue_cost
#print axioms serial_fractional
end Fractional
end Erdos184Serial
