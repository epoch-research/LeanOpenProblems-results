import Submission.SerialCore

/-! Exact optima and strict minimality across a retained two-port serial interface.
This auxiliary cut-reduction result does not settle the graph conjecture. -/
open scoped Classical
namespace Erdos184Serial
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
variable {E F : Type*} [DecidableEq E] [DecidableEq F]

/-- Full-support optimality, including existence of a partition. -/
def HasNumber (C : Code E) (s : Finset E) (k : ℕ) : Prop :=
  (∃ D, Partition C s D ∧ D.card = k) ∧
  ∀ D, Partition C s D → k ≤ D.card

/-- Unlike `Minimal`, this includes the full-support lower bound. -/
def MinimalCore (C : Code E) (s : Finset E) (k : ℕ) : Prop :=
  HasNumber C s k ∧
  ∀ t ⊂ s, C.valid t → ∃ D, Partition C t D ∧ D.card < k

lemma Partition.coverReal {C : Code E} {s : Finset E} {D : Finset (Finset E)}
    (hD : Partition C s D) (e : E) :
    (∑ a : D, if e ∈ a.val then (1 : ℝ) else 0) = if e ∈ s then 1 else 0 := by
  by_cases he : e ∈ s
  · have he' := he
    rw [← hD.2.2] at he'
    obtain ⟨a,ha,hea⟩ := Finset.mem_biUnion.mp he'
    let i : D := ⟨a,ha⟩
    rw [if_pos he]
    calc
      _ = if e ∈ i.val then (1 : ℝ) else 0 := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          have hn : e ∉ j.val := by
            intro hej
            exact Finset.disjoint_left.mp (hD.2.1 j.property ha
              (fun h => hji (Subtype.ext h))) hej hea
          simp [hn]
        · simp
      _ = 1 := if_pos hea
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro a _
    exact if_neg (fun ha => he (hD.piece_subset a.property ha))

lemma partition_of_coverReal {I : Type*} [Fintype I] [DecidableEq I]
    (C : Code E) (s : Finset E) (a : I → Finset E)
    (ha : ∀ i, Circuit C (a i))
    (hc : ∀ e, (∑ i, if e ∈ a i then (1 : ℝ) else 0) = if e ∈ s then 1 else 0) :
    ∃ D, Partition C s D ∧ D.card = Fintype.card I := by
  have hcount (e : E) : (Finset.univ.filter (fun i => e ∈ a i)).card = if e ∈ s then 1 else 0 := by
    have h := hc e
    have hs : (∑ i, if e ∈ a i then (1 : ℝ) else 0) =
        ((Finset.univ.filter (fun i => e ∈ a i)).card : ℝ) := by simp
    rw [hs] at h
    split_ifs at h ⊢ <;> exact_mod_cast h
  have hmem (e : E) : (∃ i, e ∈ a i) ↔ e ∈ s := by
    constructor
    · rintro ⟨i,hi⟩
      have hp : 0 < (Finset.univ.filter (fun i => e ∈ a i)).card :=
        Finset.card_pos.mpr ⟨i,by simp [hi]⟩
      rw [hcount] at hp
      split_ifs at hp with he
      · exact he
      · omega
    · intro he
      have hp : 0 < (Finset.univ.filter (fun i => e ∈ a i)).card := by rw [hcount,if_pos he]; omega
      obtain ⟨i,hi⟩ := Finset.card_pos.mp hp
      exact ⟨i,(Finset.mem_filter.mp hi).2⟩
  have huniq {e : E} {i j : I} (hi : e ∈ a i) (hj : e ∈ a j) : i = j := by
    have he := (hmem e).mp ⟨i,hi⟩
    have hcard : (Finset.univ.filter (fun i => e ∈ a i)).card = 1 := by rw [hcount,if_pos he]
    obtain ⟨k,hk⟩ := Finset.card_eq_one.mp hcard
    have hi' : i ∈ Finset.univ.filter (fun i => e ∈ a i) := by simp [hi]
    have hj' : j ∈ Finset.univ.filter (fun i => e ∈ a i) := by simp [hj]
    rw [hk,Finset.mem_singleton] at hi' hj'
    exact hi'.trans hj'.symm
  have hinj : Function.Injective a := by
    intro i j he
    obtain ⟨e,hi⟩ := (ha i).2.1
    exact huniq hi (he ▸ hi)
  refine ⟨Finset.univ.image a,⟨?_,?_,?_⟩,?_⟩
  · intro b hb
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
    exact ha i
  · intro b hb c hd hn
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hd
    apply Finset.disjoint_left.mpr
    intro e hi hj
    exact hn (congrArg a (huniq hi hj))
  · ext e
    simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and,id_eq]
    constructor
    · rintro ⟨b,⟨i,rfl⟩,hi⟩
      exact (hmem e).mp ⟨i,hi⟩
    · intro he
      obtain ⟨i,hi⟩ := (hmem e).mpr he
      exact ⟨a i,⟨i,rfl⟩,hi⟩
  · rw [Finset.card_image_of_injective _ hinj,Finset.card_univ]

lemma serial_partition {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset E} {t : Finset F} {D : Finset (Finset E)} {A : Finset (Finset F)}
    (hD : Partition C s D) (hA : Partition B t A) (hp : p ∈ s) (hq : q ∈ t) :
    ∃ P, Partition (serial C B p q) (s.disjSum t) P ∧ P.card + 1 = D.card + A.card := by
  let a : D → Finset E := Subtype.val
  let b : A → Finset F := Subtype.val
  have hcov := glue_cover a b p q (fun _ => 1) (fun _ => 1) s t hD.coverReal hA.coverReal hp hq
  have hw (i : GlueIndex a b p q) : glueWeight a b p q (fun _ => 1) (fun _ => 1) i = 1 := by
    rcases i with i | i | i <;> simp [glueWeight]
  simp_rw [hw] at hcov
  obtain ⟨P,hP,hcP⟩ := partition_of_coverReal (serial C B p q) (s.disjSum t)
    (gluePiece a b p q) (gluePiece_circuit a b p q (fun i => hD.1 i.val i.property)
      (fun j => hA.1 j.val j.property)) hcov
  have hleft : (∑ i : {i : D // p ∈ a i}, (1 : ℝ)) = 1 := by
    rw [sum_subtype_ite (fun i : D => p ∈ a i) (fun _ => (1 : ℝ))]
    exact (hD.coverReal p).trans (if_pos hp)
  have hright : (∑ i : {i : A // q ∈ b i}, (1 : ℝ)) = 1 := by
    rw [sum_subtype_ite (fun i : A => q ∈ b i) (fun _ => (1 : ℝ))]
    exact (hA.coverReal q).trans (if_pos hq)
  have hc := glue_cost a b p q (fun _ => 1) (fun _ => 1) hleft hright
  simp_rw [hw] at hc
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Fintype.card_coe] at hc
  refine ⟨P,hP,?_⟩
  rw [hcP]
  exact_mod_cast (show (Fintype.card (GlueIndex a b p q) : ℝ) + 1 = D.card + A.card by linarith)

lemma serial_hasNumber {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset E} {t : Finset F} {k l : ℕ}
    (hC : HasNumber C s k) (hB : HasNumber B t l) (hp : p ∈ s) (hq : q ∈ t) :
    HasNumber (serial C B p q) (s.disjSum t) (k + l - 1) := by
  obtain ⟨D,hD,hk⟩ := hC.1
  obtain ⟨A,hA,hl⟩ := hB.1
  obtain ⟨P,hP,hc⟩ := serial_partition hD hA hp hq
  refine ⟨⟨P,hP,by omega⟩,?_⟩
  intro Q hQ
  have hL := hC.2 (leftParts Q) (by simpa only [Finset.toLeft_disjSum] using partition_left hQ)
  have hR := hB.2 (rightParts Q) (by simpa only [Finset.toRight_disjSum] using partition_right hQ)
  have hsum := projected_card_sum hQ (by simpa only [Finset.toLeft_disjSum] using hp)
  omega

#print axioms serial_partition
#print axioms serial_hasNumber

lemma parallel_partition {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset E} {t : Finset F} {D : Finset (Finset E)} {A : Finset (Finset F)}
    (hD : Partition C s D) (hA : Partition B t A) (hp : p ∉ s) (hq : q ∉ t) :
    ∃ P, Partition (serial C B p q) (s.disjSum t) P ∧ P.card = D.card + A.card := by
  let a : D ⊕ A → Finset (E ⊕ F) := Sum.elim
    (fun d => d.val.disjSum ∅) (fun d => (∅ : Finset E).disjSum d.val)
  have hc (i : D ⊕ A) : Circuit (serial C B p q) (a i) := by
    cases i with
    | inl d => exact left_circuit_lift (hD.1 d.val d.property) (fun h => hp (hD.piece_subset d.property h))
    | inr d => exact right_circuit_lift (hA.1 d.val d.property) (fun h => hq (hA.piece_subset d.property h))
  have hcov (e : E ⊕ F) : (∑ i, if e ∈ a i then (1 : ℝ) else 0) = if e ∈ s.disjSum t then 1 else 0 := by
    cases e with
    | inl e =>
      simp only [Fintype.sum_sum_type,a,Sum.elim_inl,Sum.elim_inr,Finset.inl_mem_disjSum,
        Finset.notMem_empty,if_false,Finset.sum_const_zero,add_zero]
      exact hD.coverReal e
    | inr e =>
      simp only [Fintype.sum_sum_type,a,Sum.elim_inl,Sum.elim_inr,Finset.inr_mem_disjSum,
        Finset.notMem_empty,if_false,Finset.sum_const_zero,zero_add]
      exact hA.coverReal e
  obtain ⟨P,hP,hcP⟩ := partition_of_coverReal (serial C B p q) (s.disjSum t) a hc hcov
  exact ⟨P,hP,by simpa only [Fintype.card_sum,Fintype.card_coe] using hcP⟩

lemma projected_card_sum_unused {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset (E ⊕ F)} {D : Finset (Finset (E ⊕ F))}
    (hD : Partition (serial C B p q) s D) (hp : p ∉ s.toLeft) :
    (leftParts D).card + (rightParts D).card = D.card := by
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
  have hi : L ∩ R = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨hl,hr⟩ := Finset.mem_inter.mp ha
    obtain ⟨ha,hL⟩ := Finset.mem_filter.mp hl
    have hR := (Finset.mem_filter.mp hr).2
    have hpa := (circuit_cross_iff (hD.1 a ha)).mp ⟨hL,hR⟩
    exact hp (Finset.toLeft_subset_toLeft (hD.piece_subset ha) hpa)
  have hc := Finset.card_union_add_card_inter L R
  rw [hu,hi,Finset.card_empty,add_zero] at hc
  rw [leftParts_card hD.2.1,rightParts_card hD.2.1]
  exact hc.symm

lemma parallel_hasNumber {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset E} {t : Finset F} {k l : ℕ}
    (hC : HasNumber C s k) (hB : HasNumber B t l) (hp : p ∉ s) (hq : q ∉ t) :
    HasNumber (serial C B p q) (s.disjSum t) (k + l) := by
  obtain ⟨D,hD,hk⟩ := hC.1
  obtain ⟨A,hA,hl⟩ := hB.1
  obtain ⟨P,hP,hc⟩ := parallel_partition hD hA hp hq
  refine ⟨⟨P,hP,by omega⟩,?_⟩
  intro Q hQ
  have hL := hC.2 (leftParts Q) (by simpa only [Finset.toLeft_disjSum] using partition_left hQ)
  have hR := hB.2 (rightParts Q) (by simpa only [Finset.toRight_disjSum] using partition_right hQ)
  have hsum := projected_card_sum_unused hQ (by simpa only [Finset.toLeft_disjSum] using hp)
  omega

lemma HasNumber.pos {C : Code E} {s : Finset E} {k : ℕ}
    (hC : HasNumber C s k) (hs : s.Nonempty) : 0 < k := by
  obtain ⟨D,hD,hk⟩ := hC.1
  have hne : D.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hs0 := hD.2.2
    simp only [he,Finset.biUnion_empty] at hs0
    exact hs.ne_empty hs0.symm
  have hp := Finset.card_pos.mpr hne
  omega

lemma MinimalCore.partition_le {C : Code E} {s : Finset E} {k : ℕ}
    (hC : MinimalCore C s k) {t : Finset E} (hts : t ⊆ s) (ht : C.valid t) :
    ∃ D, Partition C t D ∧ D.card ≤ k ∧ (t ≠ s → D.card < k) := by
  by_cases he : t = s
  · subst t
    obtain ⟨D,hD,hk⟩ := hC.1.1
    exact ⟨D,hD,hk.le,fun h => (h rfl).elim⟩
  · obtain ⟨D,hD,hk⟩ := hC.2 t (Finset.ssubset_iff_subset_ne.mpr ⟨hts,he⟩) ht
    exact ⟨D,hD,hk.le,fun _ => hk⟩

/-- Minimal inputs need not be rigid: strict support minimality still glues. -/
lemma serial_minimalCore {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset E} {t : Finset F} {k l : ℕ}
    (hC : MinimalCore C s k) (hB : MinimalCore B t l) (hp : p ∈ s) (hq : q ∈ t) :
    MinimalCore (serial C B p q) (s.disjSum t) (k + l - 1) := by
  refine ⟨serial_hasNumber hC.1 hB.1 hp hq,?_⟩
  intro u hus hu
  obtain ⟨hLs,hRt⟩ := Finset.subset_disjSum.mp hus.1
  obtain ⟨D,hD,hDle,hDlt⟩ := hC.partition_le hLs hu.1
  obtain ⟨A,hA,hAle,hAlt⟩ := hB.partition_le hRt hu.2.1
  have hne : u.toLeft ≠ s ∨ u.toRight ≠ t := by
    by_contra hn
    push_neg at hn
    have he : u = s.disjSum t := by rw [← u.toLeft_disjSum_toRight,hn.1,hn.2]
    exact hus.2 he.ge
  by_cases hpU : p ∈ u.toLeft
  · obtain ⟨P,hP,hcard⟩ := serial_partition hD hA hpU (hu.2.2.mp hpU)
    rw [Finset.toLeft_disjSum_toRight] at hP
    refine ⟨P,hP,?_⟩
    rcases hne with hn | hn
    · have hlt := hDlt hn
      omega
    · have hlt := hAlt hn
      omega
  · have hqU : q ∉ u.toRight := fun h => hpU (hu.2.2.mpr h)
    obtain ⟨P,hP,hcard⟩ := parallel_partition hD hA hpU hqU
    rw [Finset.toLeft_disjSum_toRight] at hP
    have hltD := hDlt (fun h => hpU (h.symm ▸ hp))
    have hltA := hAlt (fun h => hqU (h.symm ▸ hq))
    exact ⟨P,hP,by omega⟩

#print axioms serial_minimalCore
#print axioms parallel_hasNumber

lemma Partition.erase {C : Code E} {s : Finset E} {D : Finset (Finset E)}
    (hD : Partition C s D) {a : Finset E} (ha : a ∈ D) :
    Partition C (s \ a) (D.erase a) := by
  refine ⟨fun b hb => hD.1 b (Finset.mem_of_mem_erase hb),?_,?_⟩
  · intro b hb c hc hne
    exact hD.2.1 (Finset.mem_of_mem_erase hb) (Finset.mem_of_mem_erase hc) hne
  · ext e
    simp only [Finset.mem_biUnion,id_eq,Finset.mem_erase,Finset.mem_sdiff]
    constructor
    · rintro ⟨b,⟨hne,hb⟩,he⟩
      exact ⟨hD.piece_subset hb he,fun hea => Finset.disjoint_left.mp (hD.2.1 hb ha hne) he hea⟩
    · rintro ⟨hes,hnea⟩
      rw [← hD.2.2] at hes
      obtain ⟨b,hb,heb⟩ := Finset.mem_biUnion.mp hes
      exact ⟨b,⟨fun he => hnea (he ▸ heb),hb⟩,heb⟩

lemma HasNumber.erase_of_optimal {C : Code E} {s : Finset E} {k : ℕ}
    (hC : HasNumber C s k) {D : Finset (Finset E)} (hD : Partition C s D)
    (hk : D.card = k) {a : Finset E} (ha : a ∈ D) : HasNumber C (s \ a) (k - 1) := by
  refine ⟨⟨D.erase a,hD.erase ha,by simp [Finset.card_erase_of_mem ha,hk]⟩,?_⟩
  intro A hA
  have hdis : Disjoint a (s \ a) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 hx
  obtain ⟨hP,hcard⟩ := (partition_singleton (hD.1 a ha)).join hA hdis
  rw [Finset.union_sdiff_of_subset (hD.piece_subset ha)] at hP
  have hle := hC.2 _ hP
  simp only [Finset.card_singleton] at hcard
  omega

lemma serial_minimalCore_left {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset E} {t : Finset F} {k l : ℕ}
    (ht : B.valid t) (hC : HasNumber C s k) (hB : HasNumber B t l)
    (_hp : p ∈ s) (hq : q ∈ t)
    (hmin : MinimalCore (serial C B p q) (s.disjSum t) (k + l - 1)) :
    MinimalCore C s k := by
  refine ⟨hC,?_⟩
  intro u hus hu
  by_cases hpu : p ∈ u
  · have hval : (serial C B p q).valid (u.disjSum t) := by
      change C.valid (u.disjSum t).toLeft ∧ B.valid (u.disjSum t).toRight ∧ _
      simpa only [Finset.toLeft_disjSum,Finset.toRight_disjSum] using
        And.intro hu (And.intro ht (iff_of_true hpu hq))
    obtain ⟨P,hP,hcard⟩ := hmin.2 (u.disjSum t)
      (Finset.disjSum_ssubset_disjSum_of_ssubset_of_subset hus (Finset.Subset.refl _)) hval
    have hL : Partition C u (leftParts P) := by
      simpa only [Finset.toLeft_disjSum] using partition_left hP
    have hR : Partition B t (rightParts P) := by
      simpa only [Finset.toRight_disjSum] using partition_right hP
    have hsum := projected_card_sum hP (by simpa only [Finset.toLeft_disjSum] using hpu)
    have hlow := hB.2 _ hR
    exact ⟨leftParts P,hL,by omega⟩
  · obtain ⟨A,hA,hAl⟩ := hB.1
    have hqt := hq
    rw [← hA.2.2] at hqt
    obtain ⟨a,ha,hqa⟩ := Finset.mem_biUnion.mp hqt
    have hrest := hB.erase_of_optimal hA hAl ha
    have hqrest : q ∉ t \ a := fun h => (Finset.mem_sdiff.mp h).2 hqa
    have hval : (serial C B p q).valid (u.disjSum (t \ a)) := by
      change C.valid (u.disjSum (t \ a)).toLeft ∧ B.valid (u.disjSum (t \ a)).toRight ∧ _
      simpa only [Finset.toLeft_disjSum,Finset.toRight_disjSum] using
        And.intro hu (And.intro (B.diff ht (hA.1 a ha).1 (hA.piece_subset ha)) (iff_of_false hpu hqrest))
    obtain ⟨P,hP,hcard⟩ := hmin.2 (u.disjSum (t \ a))
      (Finset.disjSum_ssubset_disjSum_of_ssubset_of_subset hus Finset.sdiff_subset) hval
    have hL : Partition C u (leftParts P) := by
      simpa only [Finset.toLeft_disjSum] using partition_left hP
    have hR : Partition B (t \ a) (rightParts P) := by
      simpa only [Finset.toRight_disjSum] using partition_right hP
    have hsum := projected_card_sum_unused hP (by simpa only [Finset.toLeft_disjSum] using hpu)
    have hlow := hrest.2 _ hR
    have hlpos := hB.pos ⟨q,hq⟩
    exact ⟨leftParts P,hL,by omega⟩

lemma serial_minimalCore_right {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset E} {t : Finset F} {k l : ℕ}
    (hs : C.valid s) (hC : HasNumber C s k) (hB : HasNumber B t l)
    (hp : p ∈ s) (_hq : q ∈ t)
    (hmin : MinimalCore (serial C B p q) (s.disjSum t) (k + l - 1)) :
    MinimalCore B t l := by
  refine ⟨hB,?_⟩
  intro u hut hu
  by_cases hqu : q ∈ u
  · have hval : (serial C B p q).valid (s.disjSum u) := by
      change C.valid (s.disjSum u).toLeft ∧ B.valid (s.disjSum u).toRight ∧ _
      simpa only [Finset.toLeft_disjSum,Finset.toRight_disjSum] using
        And.intro hs (And.intro hu (iff_of_true hp hqu))
    obtain ⟨P,hP,hcard⟩ := hmin.2 (s.disjSum u)
      (Finset.disjSum_ssubset_disjSum_of_subset_of_ssubset (Finset.Subset.refl _) hut) hval
    have hL : Partition C s (leftParts P) := by
      simpa only [Finset.toLeft_disjSum] using partition_left hP
    have hR : Partition B u (rightParts P) := by
      simpa only [Finset.toRight_disjSum] using partition_right hP
    have hsum := projected_card_sum hP (by simpa only [Finset.toLeft_disjSum] using hp)
    have hlow := hC.2 _ hL
    exact ⟨rightParts P,hR,by omega⟩
  · obtain ⟨D,hD,hDk⟩ := hC.1
    have hps := hp
    rw [← hD.2.2] at hps
    obtain ⟨a,ha,hpa⟩ := Finset.mem_biUnion.mp hps
    have hrest := hC.erase_of_optimal hD hDk ha
    have hprest : p ∉ s \ a := fun h => (Finset.mem_sdiff.mp h).2 hpa
    have hval : (serial C B p q).valid ((s \ a).disjSum u) := by
      change C.valid ((s \ a).disjSum u).toLeft ∧ B.valid ((s \ a).disjSum u).toRight ∧ _
      simpa only [Finset.toLeft_disjSum,Finset.toRight_disjSum] using
        And.intro (C.diff hs (hD.1 a ha).1 (hD.piece_subset ha)) (And.intro hu (iff_of_false hprest hqu))
    obtain ⟨P,hP,hcard⟩ := hmin.2 ((s \ a).disjSum u)
      (Finset.disjSum_ssubset_disjSum_of_subset_of_ssubset Finset.sdiff_subset hut) hval
    have hL : Partition C (s \ a) (leftParts P) := by
      simpa only [Finset.toLeft_disjSum] using partition_left hP
    have hR : Partition B u (rightParts P) := by
      simpa only [Finset.toRight_disjSum] using partition_right hP
    have hsum := projected_card_sum_unused hP (by simpa only [Finset.toLeft_disjSum] using hprest)
    have hlow := hrest.2 _ hL
    have hkpos := hC.pos ⟨p,hp⟩
    exact ⟨rightParts P,hR,by omega⟩

/-- Exact decomposition of strict minimality at a used serial interface. -/
lemma serial_minimalCore_iff {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset E} {t : Finset F} {k l : ℕ}
    (hs : C.valid s) (ht : B.valid t) (hC : HasNumber C s k) (hB : HasNumber B t l)
    (hp : p ∈ s) (hq : q ∈ t) :
    MinimalCore (serial C B p q) (s.disjSum t) (k + l - 1) ↔
      MinimalCore C s k ∧ MinimalCore B t l := by
  constructor
  · intro h
    exact ⟨serial_minimalCore_left ht hC hB hp hq h,serial_minimalCore_right hs hC hB hp hq h⟩
  · rintro ⟨hC,hB⟩
    exact serial_minimalCore hC hB hp hq

lemma serial_rigid_iff {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset E} {t : Finset F} {k l : ℕ}
    (hC : HasNumber C s k) (hB : HasNumber B t l) (hp : p ∈ s) (hq : q ∈ t) :
    Rigid (serial C B p q) (s.disjSum t) (k + l - 1) ↔ Rigid C s k ∧ Rigid B t l := by
  constructor
  · intro h
    have hkpos := hC.pos ⟨p,hp⟩
    have hlpos := hB.pos ⟨q,hq⟩
    constructor
    · intro D hD
      obtain ⟨A,hA,hAl⟩ := hB.1
      obtain ⟨P,hP,hcard⟩ := serial_partition hD hA hp hq
      have he := h P hP
      omega
    · intro A hA
      obtain ⟨D,hD,hDk⟩ := hC.1
      obtain ⟨P,hP,hcard⟩ := serial_partition hD hA hp hq
      have he := h P hP
      omega
  · rintro ⟨hC,hB⟩
    apply serial_rigid
    · simpa only [Finset.toLeft_disjSum] using hC
    · simpa only [Finset.toRight_disjSum] using hB
    · simpa only [Finset.toLeft_disjSum] using hp

/-- A nonrigid minimal serial core has a nonrigid minimal factor. -/
lemma nonrigid_minimal_serial_factor {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset E} {t : Finset F} {k l : ℕ}
    (hs : C.valid s) (ht : B.valid t) (hC : HasNumber C s k) (hB : HasNumber B t l)
    (hp : p ∈ s) (hq : q ∈ t)
    (hmin : MinimalCore (serial C B p q) (s.disjSum t) (k + l - 1))
    (hn : ¬ Rigid (serial C B p q) (s.disjSum t) (k + l - 1)) :
    (MinimalCore C s k ∧ ¬ Rigid C s k) ∨ (MinimalCore B t l ∧ ¬ Rigid B t l) := by
  obtain ⟨hmC,hmB⟩ := (serial_minimalCore_iff hs ht hC hB hp hq).mp hmin
  by_cases hrC : Rigid C s k
  · exact Or.inr ⟨hmB,fun hrB => hn ((serial_rigid_iff hC hB hp hq).mpr ⟨hrC,hrB⟩)⟩
  · exact Or.inl ⟨hmC,hrC⟩

#print axioms serial_minimalCore_iff
#print axioms serial_rigid_iff
#print axioms nonrigid_minimal_serial_factor

lemma exists_hasNumber (C : Code E) {s : Finset E} (hs : C.valid s) :
    ∃ k, HasNumber C s k := by
  have hex : ∃ k, ∃ D, Partition C s D ∧ D.card = k := by
    obtain ⟨D,hD⟩ := exists_partition C hs
    exact ⟨D.card,D,hD,rfl⟩
  refine ⟨Nat.find hex,Nat.find_spec hex,?_⟩
  intro D hD
  exact Nat.find_min' hex ⟨D,hD,rfl⟩

lemma HasNumber.unique {C : Code E} {s : Finset E} {k l : ℕ}
    (hk : HasNumber C s k) (hl : HasNumber C s l) : k = l := by
  obtain ⟨D,hD,hDk⟩ := hk.1
  obtain ⟨A,hA,hAl⟩ := hl.1
  have h1 := hk.2 _ hA
  have h2 := hl.2 _ hD
  omega

lemma minimalCore_of_rigid {C : Code E} {s : Finset E} {k : ℕ}
    (hs : C.valid s) (hr : Rigid C s k) : MinimalCore C s k := by
  have hmin := rigid_minimal hs hr
  exact ⟨⟨hmin.1,fun D hD => (hr D hD).ge⟩,hmin.2⟩

/-- The factor reduction with local optimum counts chosen internally. -/
lemma nonrigid_serial_factor {C : Code E} {B : Code F} {p : E} {q : F}
    {s : Finset E} {t : Finset F} {N : ℕ}
    (hs : C.valid s) (ht : B.valid t) (hp : p ∈ s) (hq : q ∈ t)
    (hmin : MinimalCore (serial C B p q) (s.disjSum t) N)
    (hn : ¬ Rigid (serial C B p q) (s.disjSum t) N) :
    ∃ k l, HasNumber C s k ∧ HasNumber B t l ∧ k + l = N + 1 ∧
      ((MinimalCore C s k ∧ ¬ Rigid C s k) ∨ (MinimalCore B t l ∧ ¬ Rigid B t l)) := by
  obtain ⟨k,hk⟩ := exists_hasNumber C hs
  obtain ⟨l,hl⟩ := exists_hasNumber B ht
  have he : N = k + l - 1 := hmin.1.unique (serial_hasNumber hk hl hp hq)
  have hkp := hk.pos ⟨p,hp⟩
  have hlp := hl.pos ⟨q,hq⟩
  refine ⟨k,l,hk,hl,by omega,?_⟩
  rw [he] at hmin hn
  exact nonrigid_minimal_serial_factor hs ht hk hl hp hq hmin hn

#print axioms nonrigid_serial_factor
end Erdos184Serial
