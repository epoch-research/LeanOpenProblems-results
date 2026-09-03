import Submission.MengerMatching

/-!
Extract simple paths from the supported permutation. The first-return segments
between endpoint copies have disjoint internal supports. Nonadjacent endpoints
then also give edge disjointness.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.MengerMatching

section ReturnSegments
variable {I W : Type*} [Fintype I] [Fintype W]

structure ReturnSegment (f : Equiv.Perm (I ⊕ W)) (i : I) where
  length : ℕ
  pos : 0 < length
  last : ∃ j, (f : I ⊕ W → I ⊕ W)^[length] (.inl i) = .inl j
  first : ∀ n, 0 < n → n < length → ∀ j,
    (f : I ⊕ W → I ⊕ W)^[n] (.inl i) ≠ .inl j

lemma exists_return_segment (f : Equiv.Perm (I ⊕ W)) (i : I) :
    Nonempty (ReturnSegment f i) := by
  have hp : (f : I ⊕ W → I ⊕ W)^[orderOf f] (.inl i) = .inl i := by
    rw [← Equiv.Perm.coe_pow,pow_orderOf_eq_one]
    rfl
  have hex : ∃ n : ℕ, 0 < n ∧ ∃ j, (f : I ⊕ W → I ⊕ W)^[n] (.inl i) = .inl j :=
    ⟨orderOf f,orderOf_pos f,i,hp⟩
  refine ⟨⟨Nat.find hex,(Nat.find_spec hex).1,(Nat.find_spec hex).2,?_⟩⟩
  intro n hn hlt j heq
  exact Nat.find_min hex hlt ⟨hn,j,heq⟩

omit [Fintype I] [Fintype W] in
/-- Before their first return to an endpoint copy, permutation segments
cannot meet, even when they start at different endpoint copies. -/
lemma before_return_injective (f : Equiv.Perm (I ⊕ W))
    {i j : I} (p : ReturnSegment f i) (q : ReturnSegment f j)
    {a b : ℕ} (ha : a < p.length) (hb : b < q.length)
    (he : (f : I ⊕ W → I ⊕ W)^[a] (.inl i) =
      (f : I ⊕ W → I ⊕ W)^[b] (.inl j)) : a = b ∧ i = j := by
  have aux {i j : I} (q : ReturnSegment f j) {a b : ℕ}
      (hb : b < q.length) (hab : a ≤ b)
      (he : (f : I ⊕ W → I ⊕ W)^[a] (.inl i) =
        (f : I ⊕ W → I ⊕ W)^[b] (.inl j)) : a = b ∧ i = j := by
    have hh : (Sum.inl i : I ⊕ W) = (f : I ⊕ W → I ⊕ W)^[b-a] (.inl j) := by
      apply f.injective.iterate a
      rw [← Function.iterate_add_apply]
      simpa only [Nat.add_sub_of_le hab] using he
    have heq : a = b := by
      by_contra hn
      exact q.first (b-a) (by omega) (by omega) i hh.symm
    subst b
    simp only [Nat.sub_self,Function.iterate_zero,Function.id_def] at hh
    exact ⟨rfl,Sum.inl.inj hh⟩
  by_cases hab : a ≤ b
  · exact aux q hb hab he
  · obtain ⟨h,h'⟩ := aux p ha (by omega) he.symm
    exact ⟨h.symm,h'.symm⟩

omit [Fintype I] [Fintype W] in
lemma ReturnSegment.internal (f : Equiv.Perm (I ⊕ W)) {i : I}
    (p : ReturnSegment f i) {n : ℕ} (hn : 0 < n) (hlt : n < p.length) :
    ∃ w : W, (f : I ⊕ W → I ⊕ W)^[n] (.inl i) = .inr w := by
  cases h : (f : I ⊕ W → I ⊕ W)^[n] (.inl i) with
  | inl j => exact (p.first n hn hlt j h).elim
  | inr w => exact ⟨w,rfl⟩

end ReturnSegments

section VertexSequences
variable {V : Type*} {G : SimpleGraph V}

/-- A walk specified by its finite sequence of successive vertices. -/
def sequenceWalk (v : ℕ → V) : (n : ℕ) →
    (∀ i, i < n → G.Adj (v i) (v (i+1))) → G.Walk (v 0) (v n)
  | 0, _ => .nil
  | n+1, h => .cons (h 0 (by omega))
      (sequenceWalk (fun i => v (i+1)) n (fun i hi => h (i+1) (by omega)))

lemma sequenceWalk_support (v : ℕ → V) (n : ℕ)
    (h : ∀ i, i < n → G.Adj (v i) (v (i+1))) (x : V) :
    x ∈ (sequenceWalk v n h).support ↔ ∃ i, i ≤ n ∧ x = v i := by
  induction n generalizing v with
  | zero => simp [sequenceWalk]
  | succ n ih =>
    simp only [sequenceWalk,Walk.support_cons,List.mem_cons,ih]
    constructor
    · rintro (hx | ⟨i,hi,hx⟩)
      · exact ⟨0,by omega,hx⟩
      · exact ⟨i+1,by omega,hx⟩
    · rintro ⟨i,hi,hx⟩
      by_cases hz : i = 0
      · exact Or.inl (by simpa only [hz] using hx)
      · exact Or.inr ⟨i-1,by omega,by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using hx⟩

lemma sequenceWalk_isPath (v : ℕ → V) (n : ℕ)
    (h : ∀ i, i < n → G.Adj (v i) (v (i+1)))
    (hi : Set.InjOn v {i | i ≤ n}) : (sequenceWalk v n h).IsPath := by
  induction n generalizing v with
  | zero => simp [sequenceWalk]
  | succ n ih =>
    rw [sequenceWalk,Walk.cons_isPath_iff]
    refine ⟨ih _ _ ?_,?_⟩
    · intro i hi' j hj' he
      change i ≤ n at hi'
      change j ≤ n at hj'
      have hh := hi (by change i+1 ≤ n+1; omega) (by change j+1 ≤ n+1; omega) he
      omega
    · intro hm
      obtain ⟨i,hi',he⟩ := (sequenceWalk_support _ _ _ _).mp hm
      have hh := hi (by change 0 ≤ n+1; omega) (by change i+1 ≤ n+1; omega) he
      omega

end VertexSequences

section GraphPaths
variable {V : Type*} {G : SimpleGraph V} {k : ℕ} {u v : V}

noncomputable def segmentVertex (f : Equiv.Perm (Node k u v)) (i : Fin k) (n : ℕ) : V :=
  if n = 0 then u else target ((f : Node k u v → Node k u v)^[n] (.inl i))

lemma segmentVertex_zero (f : Equiv.Perm (Node k u v)) (i : Fin k) :
    segmentVertex f i 0 = u := by simp [segmentVertex]

lemma segmentVertex_last (f : Equiv.Perm (Node k u v)) {i : Fin k}
    (p : ReturnSegment f i) : segmentVertex f i p.length = v := by
  obtain ⟨j,hj⟩ := p.last
  simp [segmentVertex,ne_of_gt p.pos,hj,target]

lemma segmentVertex_internal (f : Equiv.Perm (Node k u v)) {i : Fin k}
    (p : ReturnSegment f i) {n : ℕ} (hn : 0 < n) (hlt : n < p.length) :
    ∃ w : Internal u v,
      (f : Node k u v → Node k u v)^[n] (.inl i) = .inr w ∧ segmentVertex f i n = w.val := by
  obtain ⟨w,hw⟩ := p.internal f hn hlt
  exact ⟨w,hw,by simp [segmentVertex,ne_of_gt hn,hw,target]⟩

lemma segmentVertex_eq_source_iff (f : Equiv.Perm (Node k u v)) {i : Fin k}
    (p : ReturnSegment f i) (huv : u ≠ v) {n : ℕ} (hn : n ≤ p.length) :
    segmentVertex f i n = u ↔ n = 0 := by
  by_cases hz : n = 0
  · simp [hz,segmentVertex_zero]
  by_cases he : n = p.length
  · rw [he,segmentVertex_last f p]
    exact iff_of_false huv.symm (by omega)
  obtain ⟨w,_,hw⟩ := segmentVertex_internal f p (n := n) (by omega) (by omega)
  rw [hw]
  exact iff_of_false w.property.1 hz

lemma segmentVertex_eq_target_iff (f : Equiv.Perm (Node k u v)) {i : Fin k}
    (p : ReturnSegment f i) (huv : u ≠ v) {n : ℕ} (hn : n ≤ p.length) :
    segmentVertex f i n = v ↔ n = p.length := by
  by_cases he : n = p.length
  · simp [he,segmentVertex_last f p]
  by_cases hz : n = 0
  · rw [hz,segmentVertex_zero]
    exact iff_of_false huv (by omega)
  obtain ⟨w,_,hw⟩ := segmentVertex_internal f p (n := n) (by omega) (by omega)
  rw [hw]
  exact iff_of_false w.property.2 he

lemma segmentVertex_injective (f : Equiv.Perm (Node k u v)) {i : Fin k}
    (p : ReturnSegment f i) (huv : u ≠ v) :
    Set.InjOn (segmentVertex f i) {n | n ≤ p.length} := by
  intro a ha b hb he
  change a ≤ p.length at ha
  change b ≤ p.length at hb
  by_cases ha0 : a = 0
  · have hb0 := (segmentVertex_eq_source_iff f p huv hb).mp
      (by simpa only [ha0,segmentVertex_zero] using he.symm)
    omega
  by_cases hb0 : b = 0
  · have ha0 := (segmentVertex_eq_source_iff f p huv ha).mp
      (by simpa only [hb0,segmentVertex_zero] using he)
    omega
  by_cases hal : a = p.length
  · have hbl := (segmentVertex_eq_target_iff f p huv hb).mp
      (by simpa only [hal,segmentVertex_last f p] using he.symm)
    omega
  by_cases hbl : b = p.length
  · have hal := (segmentVertex_eq_target_iff f p huv ha).mp
      (by simpa only [hbl,segmentVertex_last f p] using he)
    omega
  obtain ⟨x,hx,hxa⟩ := segmentVertex_internal f p (by omega) (by omega : a < p.length)
  obtain ⟨y,hy,hyb⟩ := segmentVertex_internal f p (by omega) (by omega : b < p.length)
  have hxy : x = y := Subtype.ext (by rwa [← hxa,← hyb])
  exact (before_return_injective f p p (by omega) (by omega) (by rw [hx,hy,hxy])).1

lemma segmentVertex_adj (f : Equiv.Perm (Node k u v))
    (hf : ∀ x, Rel G k u v x (f x)) {i : Fin k}
    (p : ReturnSegment f i) (huv : u ≠ v) {n : ℕ} (hn : n < p.length) :
    G.Adj (segmentVertex f i n) (segmentVertex f i (n+1)) := by
  let x := (f : Node k u v → Node k u v)^[n] (.inl i)
  have hs : source x = segmentVertex f i n := by
    by_cases hz : n = 0
    · simp [x,hz,source,segmentVertex_zero]
    · obtain ⟨w,hw,_⟩ := segmentVertex_internal f p (by omega) hn
      simp [x,hw,source,segmentVertex,hz,target]
  have ht : target (f x) = segmentVertex f i (n+1) := by
    simp only [segmentVertex,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false]
    rw [Function.iterate_succ_apply']
  rcases hf x with ⟨w,hx,hfx⟩ | h
  · have he : segmentVertex f i n = segmentVertex f i (n+1) := by
      rw [← hs,← ht,hfx,hx]
      rfl
    have hh := segmentVertex_injective f p huv (by change n ≤ p.length; omega)
      (by change n+1 ≤ p.length; omega) he
    omega
  · simpa only [hs,ht] using h

variable [Fintype V]

/-- The supported matching yields k paths with pairwise disjoint internal
vertices. At this point a direct edge may still be used by several paths. -/
lemma paths_of_supported_permutation (f : Equiv.Perm (Node k u v))
    (hf : ∀ x, Rel G k u v x (f x)) (huv : u ≠ v) :
    ∃ p : Fin k → G.Walk u v,
      (∀ i, (p i).IsPath) ∧
      (∀ i j, i ≠ j → ∀ x, x ∈ (p i).support → x ∈ (p j).support → x = u ∨ x = v) := by
  let d (i : Fin k) : ReturnSegment f i := Classical.choice (exists_return_segment f i)
  let h (i : Fin k) (n : ℕ) (hn : n < (d i).length) := segmentVertex_adj f hf (d i) huv hn
  let p (i : Fin k) : G.Walk u v := (sequenceWalk (segmentVertex f i) (d i).length (h i)).copy
    (segmentVertex_zero f i) (segmentVertex_last f (d i))
  have hp : ∀ i, (p i).IsPath := by
    intro i
    apply (Walk.isPath_copy _ _ _).mpr
    exact sequenceWalk_isPath _ _ _ (segmentVertex_injective f (d i) huv)
  have hsupport (i : Fin k) (x : V) : x ∈ (p i).support ↔
      ∃ n, n ≤ (d i).length ∧ x = segmentVertex f i n := by
    simp only [p,Walk.support_copy,sequenceWalk_support]
  refine ⟨p,hp,?_⟩
  intro i j hij x hxi hxj
  by_contra! hx
  obtain ⟨a,ha,hxa⟩ := (hsupport i x).mp hxi
  obtain ⟨b,hb,hxb⟩ := (hsupport j x).mp hxj
  have ha0 : a ≠ 0 := by
    intro h
    apply hx.1
    simpa only [h,segmentVertex_zero] using hxa
  have hb0 : b ≠ 0 := by
    intro h
    apply hx.1
    simpa only [h,segmentVertex_zero] using hxb
  have hal : a ≠ (d i).length := by
    intro h
    apply hx.2
    simpa only [h,segmentVertex_last f (d i)] using hxa
  have hbl : b ≠ (d j).length := by
    intro h
    apply hx.2
    simpa only [h,segmentVertex_last f (d j)] using hxb
  obtain ⟨z,hz,hza⟩ := segmentVertex_internal f (d i) (by omega) (by omega : a < (d i).length)
  obtain ⟨w,hw,hwb⟩ := segmentVertex_internal f (d j) (by omega) (by omega : b < (d j).length)
  have hzw : z = w := Subtype.ext (by rw [← hza,← hwb,← hxa,← hxb])
  exact hij (before_return_injective f (d i) (d j) (a := a) (b := b) (by omega) (by omega)
    (by rw [hz,hw,hzw])).2

/-- Vertex-disjoint-path existence for nonadjacent endpoints. The nonadjacency
hypothesis prevents repeated use of a direct endpoint edge. -/
theorem exists_internally_disjoint_paths (huv : u ≠ v) (hn : ¬G.Adj u v)
    (hconn : ∀ S : Set V, S.ncard < k → (hu : u ∉ S) → (hv : v ∉ S) →
      (G.induce Sᶜ).Reachable ⟨u,hu⟩ ⟨v,hv⟩) :
    ∃ p : Fin k → G.Walk u v,
      (∀ i, (p i).IsPath) ∧
      (∀ i j, i ≠ j → (p i).edges.Disjoint (p j).edges) ∧
      (∀ i j, i ≠ j → ∀ x, x ∈ (p i).support → x ∈ (p j).support → x = u ∨ x = v) := by
  obtain ⟨f,hf⟩ := exists_supported_permutation G k huv hconn
  obtain ⟨p,hp,hs⟩ := paths_of_supported_permutation f hf huv
  refine ⟨p,hp,?_,hs⟩
  intro i j hij e hei hej
  induction e using Sym2.ind with
  | h x y =>
    have hx := hs i j hij x ((p i).fst_mem_support_of_mem_edges hei)
      ((p j).fst_mem_support_of_mem_edges hej)
    have hy := hs i j hij y ((p i).snd_mem_support_of_mem_edges hei)
      ((p j).snd_mem_support_of_mem_edges hej)
    have hadj := (p i).adj_of_mem_edges hei
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact hadj.ne rfl
    · exact hn hadj
    · exact hn hadj.symm
    · exact hadj.ne rfl

end GraphPaths
end Erdos184.MengerMatching
