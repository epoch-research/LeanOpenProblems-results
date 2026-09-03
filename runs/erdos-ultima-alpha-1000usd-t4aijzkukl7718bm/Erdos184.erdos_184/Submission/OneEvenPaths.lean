import Submission.EndpointDefectStep
import Submission.CoveredPathParity

/-! Full simple-path partitions with one even-degree vertex.  This is a path
result, not a cycle-and-single-edge decomposition bound. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths.OneEven
open OccurrenceFan
set_option maxHeartbeats 1600000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A full endpoint list, with one missing vertex recorded separately. -/
def Missing (L : List (Piece G)) (z : V) : Prop :=
  (endpoints L ++ [z]).Nodup ∧ ∀ v, v ∈ endpoints L ++ [z]

def Admissible (L : List (Piece G)) : Prop :=
  (edgeList L).Nodup ∧ ∃ z, Missing L z

def Maximal (L : List (Piece G)) : Prop :=
  Admissible L ∧ ∀ M : List (Piece G), Admissible M →
    (edgeList M).length ≤ (edgeList L).length

lemma Missing.not_mem {L : List (Piece G)} {z : V} (hz : Missing L z) :
    z ∉ endpoints L := by
  intro h
  exact hz.1.disjoint h (by simp)

lemma Missing.mem_iff {L : List (Piece G)} {z v : V} (hz : Missing L z) :
    v ∈ endpoints L ↔ v ≠ z := by
  constructor
  · intro h he
    exact hz.not_mem (he ▸ h)
  · intro h
    have hv := hz.2 v
    simpa only [List.mem_append,List.mem_singleton,h,or_false] using hv

lemma Missing.perm {L M : List (Piece G)} {z w : V} (hz : Missing L z)
    (hp : (endpoints M ++ [w]).Perm (endpoints L ++ [z])) : Missing M w :=
  ⟨hp.nodup_iff.mpr hz.1,fun v => hp.mem_iff.mpr (hz.2 v)⟩

lemma exists_maximal_of_admissible (L : List (Piece G)) (hL : Admissible L) :
    ∃ M : List (Piece G), Maximal M := by
  let P : ℕ → Prop := fun k => ∃ M : List (Piece G),
    Admissible M ∧ (edgeList M).length = k
  have hp : P (edgeList L).length := ⟨L,hL,rfl⟩
  obtain ⟨M,hM,hm⟩ := Nat.findGreatest_spec (edgeList_length_le hL.1) hp
  refine ⟨M,hM,?_⟩
  intro N hN
  rw [hm]
  exact Nat.le_findGreatest (edgeList_length_le hN.1) ⟨N,hN,rfl⟩

/-- The uniquely missing endpoint has no unused incident edge in a maximum. -/
lemma Maximal.no_unused_at_missing {L : List (Piece G)} (hL : Maximal L)
    {z : V} (hz : Missing L z) {a : V} :
    ¬ (G \ coveredGraph L).Adj z a := by
  intro ha
  rcases edge_step hL.1.1 ha with ⟨M,hn,he,hv⟩ | ⟨t,M,ht,hzt,hn,hlen,hv⟩
  · have hM : Admissible M := ⟨hn,a,hz.perm hv⟩
    have hle := hL.2 M hM
    have hl := he.length_eq
    simp only [List.length_append,List.length_singleton] at hl
    omega
  · have ht' : t = z := by
      by_contra hne
      exact ht (hz.mem_iff.mpr hne)
    exact hzt.ne ht'.symm

lemma Maximal.missing_even {L : List (Piece G)} (hL : Maximal L)
    {z : V} (hz : Missing L z) : Even (Nat.card (G.neighborSet z)) := by
  have hpar := coveredGraph_degree_mod_two L hL.1.1 z
  have hc : (endpoints L).count z = 0 := List.count_eq_zero.mpr hz.not_mem
  rw [hc] at hpar
  have hd := degree_sdiff_add G (coveredGraph L) (coveredGraph_le L) z
  have hzero : (G \ coveredGraph L).degree z = 0 :=
    (SimpleGraph.degree_eq_zero_iff_notMem_support _ _).mpr (by
      rintro ⟨a,ha⟩
      exact hL.no_unused_at_missing hz ha)
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hzero hpar
  rw [Nat.even_iff]
  omega

lemma missing_alternatives {L M : List (Piece G)} {z a x t : V}
    (hz : Missing L z)
    (hd : (endpoints M ++ [x]).Perm (endpoints L ++ [a]))
    (ht : t ∉ endpoints M) : t = x ∨ t = z := by
  by_cases htz : t = z
  · exact Or.inr htz
  · have hm := hd.mem_iff.mpr (List.mem_append_left [a] (hz.mem_iff.mpr htz))
    exact Or.inl (by simpa only [List.mem_append,ht,false_or,List.mem_singleton] using hm)

lemma close_missing {L N : List (Piece G)} {z x t : V}
    (hz : Missing L z) (hn : (edgeList N).Nodup)
    (hp : (endpoints N ++ [x]).Perm (endpoints L ++ [t]))
    (ht : t = x ∨ t = z) : Admissible N := by
  rcases ht with rfl | rfl
  · have he : (endpoints N).Perm (endpoints L) := (List.perm_append_right_iff _).mp hp
    exact ⟨hn,z,hz.perm (he.append_right [z])⟩
  · exact ⟨hn,x,hz.perm hp⟩

lemma no_defect_trail {L : List (Piece G)} (hL : Maximal L) {z a x : V}
    (hz : Missing L z) (P : G.Walk a x) (hP : P.IsTrail)
    (M : List (Piece G)) (hn : (edgeList M).Nodup)
    (hmore : (edgeList L).length < (edgeList M).length)
    (hd : (endpoints M ++ [x]).Perm (endpoints L ++ [a]))
    (hdis : (edgeList M).Disjoint P.edges) : False := by
  induction P generalizing M with
  | nil =>
    exact (Nat.not_lt_of_ge (hL.2 M (close_missing hz hn hd (Or.inl rfl)))) hmore
  | @cons a b x hab P ih =>
    have hunused : (G \ coveredGraph M).Adj b a := by
      refine ⟨hab.symm,?_⟩
      intro hc
      apply hdis ((coveredGraph_adj M b a).mp hc)
      simp [Sym2.eq_swap]
    rcases edge_step hn hunused with ⟨N,hnN,he,hv⟩ | ⟨t,N,ht,hbt,hnN,hlen,hv⟩
    · have hmoreN : (edgeList L).length < (edgeList N).length := by
        have hl := he.length_eq
        simp only [List.length_append,List.length_singleton] at hl
        omega
      have hdN : (endpoints N ++ [x]).Perm (endpoints L ++ [b]) := by
        apply List.perm_iff_count.mpr
        intro v
        have h₁ := hd.count_eq v
        have h₂ := hv.count_eq v
        simp only [List.count_append,List.count_cons,List.count_nil] at h₁ h₂ ⊢
        omega
      have hdisN : (edgeList N).Disjoint P.edges := by
        intro e heN heP
        rcases List.mem_append.mp (he.mem_iff.mp heN) with hm | hm
        · exact hdis hm (List.mem_cons_of_mem _ heP)
        · have heq : e = s(b,a) := List.mem_singleton.mp hm
          have ht := hP.edges_nodup
          rw [Walk.edges_cons,List.nodup_cons] at ht
          apply ht.1
          simpa only [heq,Sym2.eq_swap] using heP
      exact ih hP.of_cons N hnN hmoreN hdN hdisN
    · have ht' := missing_alternatives hz hd ht
      have hvN : (endpoints N ++ [x]).Perm (endpoints L ++ [t]) := by
        apply List.perm_iff_count.mpr
        intro v
        have h₁ := hd.count_eq v
        have h₂ := hv.count_eq v
        simp only [List.count_append,List.count_cons,List.count_nil] at h₁ h₂ ⊢
        omega
      have hle := hL.2 N (close_missing hz hnN hvN ht')
      omega

/-- No unused cycle survives when the host has just one possible even vertex. -/
lemma Maximal.no_unused_cycle {L : List (Piece G)} (hL : Maximal L)
    {z : V} (hz : Missing L z)
    (hodd : ∀ v, v ≠ z → Odd (Nat.card (G.neighborSet v)))
    {x : V} (D : G.Walk x x) (hD : D.IsCycle)
    (hdis : (edgeList L).Disjoint D.edges) : False := by
  cases D with
  | nil => exact hD.not_nil (by simp)
  | @cons x a x hxa P =>
    have hunused : (G \ coveredGraph L).Adj a x := by
      refine ⟨hxa.symm,?_⟩
      intro hc
      apply hdis ((coveredGraph_adj L a x).mp hc)
      simp [Sym2.eq_swap]
    rcases edge_step hL.1.1 hunused with ⟨M,hn,he,hv⟩ | ⟨t,M,ht,hat,hn,hlen,hv⟩
    · have hmore : (edgeList L).length < (edgeList M).length := by
        have hl := he.length_eq
        simp only [List.length_append,List.length_singleton] at hl
        omega
      have hdisM : (edgeList M).Disjoint P.edges := by
        intro e heM heP
        rcases List.mem_append.mp (he.mem_iff.mp heM) with hm | hm
        · exact hdis hm (List.mem_cons_of_mem _ heP)
        · have heq : e = s(a,x) := List.mem_singleton.mp hm
          have ht := hD.isTrail.edges_nodup
          rw [Walk.edges_cons,List.nodup_cons] at ht
          apply ht.1
          simpa only [heq,Sym2.eq_swap] using heP
      exact no_defect_trail hL hz P hD.isTrail.of_cons M hn hmore hv hdisM
    · have ht' : t = z := by
        by_contra htz
        exact ht (hz.mem_iff.mpr htz)
      subst t
      have hm : Admissible M := ⟨hn,x,hz.perm hv⟩
      have hmmax : Maximal M := ⟨hm,by
        intro N hN
        have h := hL.2 N hN
        omega⟩
      have hmz := hmmax.missing_even (hz.perm hv)
      have hxz : x ≠ z := by
        intro hxz
        subst x
        exact hL.no_unused_at_missing hz hunused.symm
      exact (Nat.not_even_iff_odd.mpr (hodd x hxz)) hmz

lemma Maximal.residual_acyclic {L : List (Piece G)} (hL : Maximal L)
    {z : V} (hz : Missing L z)
    (hodd : ∀ v, v ≠ z → Odd (Nat.card (G.neighborSet v))) :
    (G \ coveredGraph L).IsAcyclic := by
  intro x C hC
  have hle : G \ coveredGraph L ≤ G := sdiff_le
  apply hL.no_unused_cycle hz hodd (C.mapLe hle) (hC.mapLe hle)
  intro e he heD
  have hr := C.edges_subset_edgeSet (by simpa only [Walk.edges_mapLe_eq_edges] using heD)
  rw [SimpleGraph.edgeSet_sdiff] at hr
  exact hr.2 ((coveredGraph_edgeSet L e).mpr he)

lemma exists_initial (z : V) (hz : Even (Nat.card (G.neighborSet z)))
    (hodd : ∀ v, v ≠ z → Odd (Nat.card (G.neighborSet v))) :
    ∃ L : List (Piece G), Admissible L := by
  obtain ⟨L,R,hRG,hRe,hed,hen,hcov,hdis,hterm⟩ := exists_extraction G
  have ht (v : V) : v ∈ endpoints L ↔ v ≠ z := by
    rw [hterm,mem_oddVertices]
    constructor
    · intro hv he
      subst v
      exact (Nat.not_even_iff_odd.mpr hv) hz
    · exact hodd v
  have hzne : z ∉ endpoints L := by rw [ht]; simp
  refine ⟨L,hed,z,hen.append (by simp) ?_,?_⟩
  · intro v hv hzv
    have hvz : v = z := by simpa using hzv
    exact hzne (hvz ▸ hv)
  · intro v
    simp only [List.mem_append,List.mem_singleton,ht]
    exact em (v = z) |>.symm

lemma Missing.path_count {L : List (Piece G)} {z : V} (hz : Missing L z) :
    2 * L.length + 1 = Fintype.card V := by
  have hset : (endpoints L ++ [z]).toFinset = Finset.univ := by
    ext v
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
    exact hz.2 v
  have hc := List.toFinset_card_of_nodup hz.1
  rw [hset,Finset.card_univ,List.length_append,List.length_singleton,endpoints_length] at hc
  exact hc.symm

/-- Every graph with precisely one even-degree vertex has a full simple-path
partition, using each other vertex exactly once as an endpoint. -/
lemma full_partition (z : V) (hz : Even (Nat.card (G.neighborSet z)))
    (hodd : ∀ v, v ≠ z → Odd (Nat.card (G.neighborSet v))) :
    ∃ L : List (Piece G), (edgeList L).Nodup ∧ Missing L z ∧
      (∀ e, e ∈ G.edgeSet ↔ e ∈ edgeList L) ∧
      2 * L.length + 1 = Fintype.card V := by
  obtain ⟨A,hA⟩ := exists_initial z hz hodd
  obtain ⟨L,hL⟩ := exists_maximal_of_admissible A hA
  obtain ⟨w,hw⟩ := hL.1.2
  have hwz : w = z := by
    by_contra h
    exact (Nat.not_even_iff_odd.mpr (hodd w h)) (hL.missing_even hw)
  subst w
  have he : ∀ v, Even ((G \ coveredGraph L).degree v) := by
    intro v
    have hp := coveredGraph_degree_mod_two L hL.1.1 v
    have hd := degree_sdiff_add G (coveredGraph L) (coveredGraph_le L) v
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hp hd ⊢
    rw [Nat.even_iff]
    by_cases hv : v = z
    · subst v
      have hc : (endpoints L).count z = 0 := List.count_eq_zero.mpr hw.not_mem
      rw [hc] at hp
      have h := Nat.even_iff.mp hz
      omega
    · have hc : (endpoints L).count v = 1 :=
        List.count_eq_one_of_mem hw.1.of_append_left (hw.mem_iff.mpr hv)
      rw [hc] at hp
      have h := Nat.odd_iff.mp (hodd v hv)
      omega
  have hbot : G \ coveredGraph L = ⊥ := acyclic_even_eq_bot _ (hL.residual_acyclic hw hodd) (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he)
  have hle : G ≤ coveredGraph L := sdiff_eq_bot_iff.mp hbot
  refine ⟨L,hL.1.1,hw,?_,hw.path_count⟩
  intro e
  exact ⟨fun h => (coveredGraph_edgeSet L e).mp (SimpleGraph.edgeSet_mono hle h),
    edgeList_mem_edgeSet⟩

end Erdos184Work.OddPaths.OneEven
#print axioms Erdos184Work.OddPaths.OneEven.full_partition
