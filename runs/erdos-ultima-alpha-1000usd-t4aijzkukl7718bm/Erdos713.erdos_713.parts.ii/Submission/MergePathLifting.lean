import FormalConjecturesUtil
import Submission.VertexMerging
import Submission.TwoPathRootCounting

/-! A path through an identified vertex either lifts to a path, or splits
into two original walks with prescribed endpoints. No extremal-rate transfer
is asserted. -/
open SimpleGraph Finset
namespace Erdos713MergePathLifting
open Erdos713VertexMerging Erdos713TwoPathRootCounting
variable {V : Type*} {G : SimpleGraph V} {u v : V}
set_option maxHeartbeats 2000000

open scoped Classical in
noncomputable def liftMap (u v : V) (b : Bool) (x : {a : V // a ≠ v}) : V :=
  if b then Equiv.swap u v x.val else x.val

lemma liftMap_injective (u v : V) (b : Bool) : Function.Injective (liftMap u v b) := by
  classical
  cases b
  · exact Subtype.val_injective
  · exact (Equiv.swap u v).injective.comp Subtype.val_injective

lemma liftMap_off (u v : V) (b : Bool) (x : {a : V // a ≠ v}) (hx : x.val ≠ u) :
    liftMap u v b x = x.val := by
  classical
  cases b <;> simp [liftMap,Equiv.swap_apply_of_ne_of_ne hx x.property]

lemma liftMap_root (huv : u ≠ v) (b : Bool) :
    liftMap u v b ⟨u,huv⟩ = if b then v else u := by
  classical
  cases b <;> simp [liftMap]

lemma lift_avoiding (hn : ¬ G.Adj u v) (b : Bool)
    {x y : {a : V // a ≠ v}} (p : (merge G u v hn).Walk x y)
    (ha : ∀ z ∈ p.support, z.val ≠ u) :
    ∃ q : G.Walk (liftMap u v b x) (liftMap u v b y),
      q.length = p.length ∧ q.support = p.support.map (liftMap u v b) := by
  classical
  induction p with
  | nil => exact ⟨Walk.nil,rfl,rfl⟩
  | @cons x z y h p ih =>
    have hx : x.val ≠ u := ha x (by simp)
    have hz : z.val ≠ u := ha z (by simp)
    have ht : ∀ a ∈ p.support, a.val ≠ u := fun a h => ha a (by simp [h])
    obtain ⟨q,hq,hqs⟩ := ih ht
    have hg : G.Adj x.val z.val := by
      rcases (merge_adj G u v hn x z).mp h with h | ⟨he,_⟩ | ⟨he,_⟩
      · exact h
      · exact (hx he).elim
      · exact (hz he).elim
    have hg' : G.Adj (liftMap u v b x) (liftMap u v b z) := by
      simpa only [liftMap_off u v b x hx,liftMap_off u v b z hz] using hg
    refine ⟨Walk.cons hg' q,?_,?_⟩
    · simp only [Walk.length_cons,hq]
    · simp only [Walk.support_cons,List.map_cons,hqs]

lemma lift_from_root (huv : u ≠ v) (hn : ¬ G.Adj u v)
    {x : {a : V // a ≠ v}} (hx : x.val ≠ u)
    (p : (merge G u v hn).Walk ⟨u,huv⟩ x) (hp : p.IsPath) :
    ∃ b : Bool, ∃ q : G.Walk (liftMap u v b ⟨u,huv⟩) (liftMap u v b x),
      q.length = p.length ∧ q.support = p.support.map (liftMap u v b) := by
  classical
  cases p with
  | nil => exact (hx rfl).elim
  | @cons _ z x h p =>
    have hparts := (Walk.cons_isPath_iff h p).mp hp
    have ht : ∀ a ∈ p.support, a.val ≠ u := by
      intro a ha he
      apply hparts.2
      have he' : a = ⟨u,huv⟩ := Subtype.ext he
      simpa only [he'] using ha
    have hz : z.val ≠ u := ht z p.start_mem_support
    have hcover : G.Adj u z.val ∨ G.Adj v z.val := by
      rcases (merge_adj G u v hn ⟨u,huv⟩ z).mp h with h | ⟨_,h⟩ | ⟨he,_⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact (hz he).elim
    rcases hcover with hcover | hcover
    · obtain ⟨q,hq,hqs⟩ := lift_avoiding hn false p ht
      refine ⟨false,Walk.cons hcover q,?_,?_⟩
      · simp only [Walk.length_cons,hq]
      · simp only [Walk.support_cons,List.map_cons,hqs]
    · obtain ⟨q,hq,hqs⟩ := lift_avoiding hn true p ht
      have hnew : G.Adj (liftMap u v true ⟨u,huv⟩) (liftMap u v true z) := by
        simpa only [liftMap_root huv,liftMap_off u v true z hz,if_true] using hcover
      refine ⟨true,Walk.cons hnew q,?_,?_⟩
      · simp only [Walk.length_cons,hq]
      · simp only [Walk.support_cons,List.map_cons,hqs]

lemma mem_total_of_walks [Fintype V] {a b c d : V}
    (p : G.Walk a c) (q : G.Walk b d) :
    ((a,b),(c,d)) ∈ totalLengthRoots G (p.length+q.length) := by
  classical
  apply mem_biUnion.mpr
  refine ⟨p.length,by simp,?_⟩
  apply mem_union.mpr
  apply Or.inl
  apply mem_image.mpr
  refine ⟨((a,c),(b,d)),?_,rfl⟩
  apply mem_product.mpr
  constructor
  · exact mem_filter.mpr ⟨mem_univ _,⟨p,rfl⟩⟩
  · apply mem_filter.mpr
    refine ⟨mem_univ _,⟨q,?_⟩⟩
    omega

lemma mem_total_of_walks_alt [Fintype V] {a b c d : V}
    (p : G.Walk a d) (q : G.Walk b c) :
    ((a,b),(c,d)) ∈ totalLengthRoots G (p.length+q.length) := by
  classical
  apply mem_biUnion.mpr
  refine ⟨p.length,by simp,?_⟩
  apply mem_union.mpr
  apply Or.inr
  apply mem_image.mpr
  refine ⟨((a,d),(b,c)),?_,rfl⟩
  apply mem_product.mpr
  constructor
  · exact mem_filter.mpr ⟨mem_univ _,⟨p,rfl⟩⟩
  · apply mem_filter.mpr
    refine ⟨mem_univ _,⟨q,?_⟩⟩
    omega

/-- This is a statement about an actual simple path in a one-pair merger.
If it cannot lift as a path of the same length, its endpoints and the
merged pair are among the two-walk endpoint quadruples counted above. -/
theorem path_lifts_or_two_walks [Fintype V] (huv : u ≠ v) (hn : ¬ G.Adj u v)
    {x y : {a : V // a ≠ v}} (hx : x.val ≠ u) (hy : y.val ≠ u)
    (p : (merge G u v hn).Walk x y) (hp : p.IsPath) :
    (∃ q : G.Walk x.val y.val, q.IsPath ∧ q.length = p.length) ∨
      ((u,v),(x.val,y.val)) ∈ totalLengthRoots G p.length := by
  classical
  let root : {a : V // a ≠ v} := ⟨u,huv⟩
  by_cases hr : root ∈ p.support
  · let p1 := p.takeUntil root hr
    let p2 := p.dropUntil root hr
    have hjoin : p1.append p2 = p := p.take_spec hr
    have hlen : p1.length+p2.length = p.length := by
      simpa only [Walk.length_append] using congrArg Walk.length hjoin
    have hp1 : p1.reverse.IsPath := (hp.takeUntil hr).reverse
    have hp2 : p2.IsPath := hp.dropUntil hr
    obtain ⟨b1,q1,hq1,hs1⟩ := lift_from_root huv hn hx p1.reverse hp1
    obtain ⟨b2,q2,hq2,hs2⟩ := lift_from_root huv hn hy p2 hp2
    by_cases hb : b1 = b2
    · subst b2
      let q := q1.reverse.append q2
      have hs : q.support = p.support.map (liftMap u v b1) := by
        calc
          q.support = (p1.support++p2.support.tail).map (liftMap u v b1) := by
            simp only [q,Walk.support_append,Walk.support_reverse,hs1,hs2]
            simp only [List.map_reverse,List.reverse_reverse,List.map_append,List.map_tail]
          _ = p.support.map (liftMap u v b1) := by rw [← Walk.support_append,hjoin]
      have hqp : q.IsPath := by
        rw [Walk.isPath_def,hs]
        exact hp.support_nodup.map (liftMap_injective u v b1)
      have hql : q.length = p.length := by
        simp only [q,Walk.length_append,Walk.length_reverse,hq1,hq2,Walk.length_reverse]
        exact hlen
      refine Or.inl ⟨q.copy (liftMap_off u v b1 x hx) (liftMap_off u v b1 y hy),?_,?_⟩
      · exact (Walk.isPath_copy _ _ _).mpr hqp
      · simpa only [Walk.length_copy] using hql
    · apply Or.inr
      cases b1 <;> cases b2
      · exact (hb rfl).elim
      · let pA := q1.copy (liftMap_root huv false) (liftMap_off u v false x hx)
        let pB := q2.copy (liftMap_root huv true) (liftMap_off u v true y hy)
        have ht := mem_total_of_walks pA pB
        have hl : pA.length+pB.length = p.length := by
          simp only [pA,pB,Walk.length_copy,hq1,hq2,Walk.length_reverse]
          exact hlen
        simpa only [hl,Bool.false_eq_true,if_false,if_true] using ht
      · let pA := q2.copy (liftMap_root huv false) (liftMap_off u v false y hy)
        let pB := q1.copy (liftMap_root huv true) (liftMap_off u v true x hx)
        have ht := mem_total_of_walks_alt pA pB
        have hl : pA.length+pB.length = p.length := by
          simp only [pA,pB,Walk.length_copy,hq1,hq2,Walk.length_reverse]
          omega
        simpa only [hl,Bool.false_eq_true,if_false,if_true] using ht
      · exact (hb rfl).elim
  · have havoid : ∀ a ∈ p.support, a.val ≠ u := by
      intro a ha he
      apply hr
      have he' : a = root := Subtype.ext he
      simpa only [he'] using ha
    obtain ⟨q,hq,hs⟩ := lift_avoiding hn false p havoid
    apply Or.inl
    refine ⟨q,?_,hq⟩
    rw [Walk.isPath_def,hs]
    exact hp.support_nodup.map (liftMap_injective u v false)

#print axioms lift_from_root
#print axioms path_lifts_or_two_walks
end Erdos713MergePathLifting
