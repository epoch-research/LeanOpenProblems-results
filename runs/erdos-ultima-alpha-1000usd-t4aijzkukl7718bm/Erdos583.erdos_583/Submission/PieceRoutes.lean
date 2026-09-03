import Submission.Work

/-! Expanding finite edge-labelled routes into internally disjoint path pieces. -/
namespace Erdos583PieceRoutesDevelopment
open SimpleGraph Erdos583Work
set_option maxHeartbeats 1800000
universe u v w
variable {A : Type u} {E : Type v} {V : Type w}

def source (s t : E → A) (e : E) (d : Bool) : A := if d then s e else t e
def target (s t : E → A) (e : E) (d : Bool) : A := if d then t e else s e

inductive Route (s t : E → A) : A → A → Type (max u v)
  | nil (a : A) : Route s t a a
  | cons (e : E) (d : Bool) {b : A} (q : Route s t (target s t e d) b) :
      Route s t (source s t e d) b

namespace Route
variable {s t : E → A}

def support {a b : A} : Route s t a b → List A
  | .nil a => [a]
  | .cons e d q => source s t e d :: q.support

def pieces {a b : A} : Route s t a b → List E
  | .nil _ => []
  | .cons e _ q => e :: q.pieces

lemma start_mem {a b : A} (q : Route s t a b) : a ∈ q.support := by
  cases q <;> simp [support]

lemma end_mem {a b : A} (q : Route s t a b) : b ∈ q.support := by
  induction q with
  | nil a => simp [support]
  | cons e d q ih => exact List.mem_cons_of_mem _ ih

lemma piece_ends {a b : A} (q : Route s t a b) {e : E} (he : e ∈ q.pieces) :
    s e ∈ q.support ∧ t e ∈ q.support := by
  induction q with
  | nil a => simp [pieces] at he
  | cons f d q ih =>
    simp only [pieces,List.mem_cons] at he
    rcases he with rfl|he
    · have hh := q.start_mem
      cases d <;> simp_all [support,source,target]
    · obtain ⟨hs,ht⟩ := ih he
      exact ⟨List.mem_cons_of_mem _ hs,List.mem_cons_of_mem _ ht⟩

def compatible [DecidableEq A] (a b : A) : List (E × Bool) → Bool
  | [] => decide (a=b)
  | (e,d) :: l => decide (a=source s t e d) && compatible (target s t e d) b l

lemma of_compatible [DecidableEq A] {a b : A} (l : List (E × Bool))
    (h : compatible (s := s) (t := t) a b l=true) :
    ∃ q : Route s t a b, q.support=a :: l.map (fun ed ↦ target s t ed.1 ed.2) ∧
      q.pieces=l.map Prod.fst := by
  induction l generalizing a with
  | nil =>
    have hab : a=b := by simpa [compatible] using h
    subst b
    exact ⟨.nil a,rfl,rfl⟩
  | cons ed l ih =>
    rcases ed with ⟨e,d⟩
    simp only [compatible,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨q,hqs,hqp⟩ := ih h.2
    rcases h.1 with rfl
    exact ⟨.cons e d q,by simp [support,hqs],by simp [pieces,hqp]⟩

variable {G : SimpleGraph V} (f : A → V) (R : ∀ e, G.Walk (f (s e)) (f (t e)))

def oriented (e : E) (d : Bool) : G.Walk (f (source s t e d)) (f (target s t e d)) :=
  match d with
  | true => R e
  | false => (R e).reverse

def expand {a b : A} : Route s t a b → G.Walk (f a) (f b)
  | .nil _ => .nil
  | .cons e d q => (oriented f R e d).append (expand q)

lemma oriented_support (e : E) (d : Bool) (x : V) :
    x ∈ (oriented f R e d).support ↔ x ∈ (R e).support := by
  cases d <;> simp [oriented]

lemma oriented_edges (e : E) (d : Bool) :
    (oriented f R e d).toSubgraph.edgeSet=(R e).toSubgraph.edgeSet := by
  cases d <;> simp [oriented]

lemma mem_expand_support {a b : A} (q : Route s t a b) {x : V}
    (hx : x ∈ (q.expand f R).support) : x=f b ∨ ∃ e ∈ q.pieces, x ∈ (R e).support := by
  induction q with
  | nil a => exact Or.inl (by simpa [expand] using hx)
  | cons e d q ih =>
    rw [expand,Walk.mem_support_append_iff] at hx
    rcases hx with he|hq
    · exact Or.inr ⟨e,by simp [pieces],(oriented_support f R e d x).mp he⟩
    · rcases ih hq with h|⟨j,hj,hxj⟩
      · exact Or.inl h
      · exact Or.inr ⟨j,List.mem_cons_of_mem _ hj,hxj⟩

lemma expand_core_mem (hf : Function.Injective f)
    (hcore : ∀ e x, f x ∈ (R e).support → x=s e ∨ x=t e)
    {a b x : A} (q : Route s t a b) (hx : f x ∈ (q.expand f R).support) : x ∈ q.support := by
  rcases mem_expand_support f R q hx with he|⟨e,he,hx⟩
  · have hxb := hf he
    exact hxb.symm ▸ q.end_mem
  · rcases hcore e x hx with rfl|rfl
    · exact (q.piece_ends he).1
    · exact (q.piece_ends he).2

lemma expand_isPath (hf : Function.Injective f)
    (hpath : ∀ e, (R e).IsPath)
    (hcore : ∀ e x, f x ∈ (R e).support → x=s e ∨ x=t e)
    (hinter : ∀ e j, e ≠ j → ∀ x ∈ (R e).support, x ∈ (R j).support → ∃ a, x=f a)
    {a b : A} (q : Route s t a b) (hq : q.support.Nodup) : (q.expand f R).IsPath := by
  induction q with
  | nil a => simp [expand]
  | cons e d q ih =>
    obtain ⟨hstart,hn⟩ := List.nodup_cons.mp hq
    have hfirst : (oriented f R e d).IsPath := by cases d <;> simp [oriented,hpath,(hpath e).reverse]
    apply path_append_of_support_intersection hfirst (ih hn)
    intro x hxR hxq
    have hxRe := (oriented_support f R e d x).mp hxR
    have hxe : ∃ a, x=f a := by
      rcases mem_expand_support f R q hxq with hh|⟨j,hj,hxj⟩
      · exact ⟨_,hh⟩
      · have hej : e ≠ j := by
          rintro rfl
          obtain ⟨hs,ht⟩ := q.piece_ends hj
          cases d <;> simp_all [source]
        exact hinter e j hej x hxRe hxj
    obtain ⟨a,hxa⟩ := hxe
    have ha := hcore e a (hxa ▸ hxRe)
    have haq := expand_core_mem f R hf hcore q (hxa ▸ hxq)
    cases d <;> simp only [source,target] at hstart ⊢
    · rcases ha with rfl|rfl
      · exact hxa
      · exact (hstart haq).elim
    · rcases ha with rfl|rfl
      · exact (hstart haq).elim
      · exact hxa

lemma expand_edges {a b : A} (q : Route s t a b) (d : Sym2 V) :
    d ∈ (q.expand f R).toSubgraph.edgeSet ↔ ∃ e ∈ q.pieces, d ∈ (R e).toSubgraph.edgeSet := by
  induction q with
  | nil a => simp [expand,pieces]
  | cons e b q ih =>
    simp only [expand,Walk.toSubgraph_append,Subgraph.edgeSet_sup,Set.mem_union,oriented_edges,
      ih,pieces,List.mem_cons]
    aesop

lemma expand_two_cover (hf : Function.Injective f)
    (hpath : ∀ e, (R e).IsPath)
    (hcore : ∀ e x, f x ∈ (R e).support → x=s e ∨ x=t e)
    (hinter : ∀ e j, e ≠ j → ∀ x ∈ (R e).support, x ∈ (R j).support → ∃ a, x=f a)
    (hdis : ∀ e j, e ≠ j → Disjoint (R e).toSubgraph.edgeSet (R j).toSubgraph.edgeSet)
    {a b c d : A} (p : Route s t a b) (q : Route s t c d)
    (hp : p.support.Nodup) (hq : q.support.Nodup)
    (hsep : p.pieces.Disjoint q.pieces) (hcover : ∀ e, e ∈ p.pieces ∨ e ∈ q.pieces) :
    (p.expand f R).IsPath ∧ (q.expand f R).IsPath ∧
    Disjoint (p.expand f R).toSubgraph.edgeSet (q.expand f R).toSubgraph.edgeSet ∧
    (p.expand f R).toSubgraph.edgeSet ∪ (q.expand f R).toSubgraph.edgeSet = ⋃ e, (R e).toSubgraph.edgeSet := by
  refine ⟨expand_isPath f R hf hpath hcore hinter p hp,expand_isPath f R hf hpath hcore hinter q hq,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨e,he,hxe⟩ := (expand_edges f R p x).mp hx
    obtain ⟨j,hj,hxj⟩ := (expand_edges f R q x).mp hy
    have hej : e ≠ j := fun hh ↦ hsep he (hh.symm ▸ hj)
    exact Set.disjoint_left.mp (hdis e j hej) hxe hxj
  · ext x
    simp only [Set.mem_union,expand_edges,Set.mem_iUnion]
    constructor
    · rintro (⟨e,he,hxe⟩|⟨e,he,hxe⟩) <;> exact ⟨e,hxe⟩
    · rintro ⟨e,he⟩
      exact (hcover e).elim (fun h ↦ Or.inl ⟨e,h,he⟩) (fun h ↦ Or.inr ⟨e,h,he⟩)

end Route
end Erdos583PieceRoutesDevelopment
