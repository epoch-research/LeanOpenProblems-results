import Submission.MengerPaths

/-! Adding a terminal-set apex and extracting paths back in the original graph. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.FanPaths
variable {V : Type*}

/-- A new vertex joined precisely to S. -/
def cone (G : SimpleGraph V) (S : Set V) : SimpleGraph (Option V) where
  Adj
    | some u, some v => G.Adj u v
    | none, some v => v ∈ S
    | some v, none => v ∈ S
    | none, none => False
  symm := by intro x y h; cases x <;> cases y <;> first | exact h | exact h.symm
  loopless := by intro x; cases x; exact id; exact G.loopless _

def someEmbedding (G : SimpleGraph V) (S : Set V) : G ↪g cone G S where
  toFun := Option.some
  inj' := Option.some_injective V
  map_rel_iff' := Iff.rfl

def pullbackHom (G : SimpleGraph V) (S : Set V) (a : V) :
    (cone G S).induce (Set.range (Option.some : V → Option V)) →g G where
  toFun x := x.val.getD a
  map_rel' := by
    rintro ⟨x,hx⟩ ⟨y,hy⟩ h
    obtain ⟨u,rfl⟩ := hx
    obtain ⟨v,rfl⟩ := hy
    exact h

lemma pullbackHom_injective (G : SimpleGraph V) (S : Set V) (a : V) :
    Function.Injective (pullbackHom G S a) := by
  rintro ⟨x,hx⟩ ⟨y,hy⟩ h
  obtain ⟨u,rfl⟩ := hx
  obtain ⟨v,rfl⟩ := hy
  exact Subtype.ext (congrArg Option.some h)

/-- A path avoiding the apex is a path in G, with the same old vertices. -/
lemma pullback_path {G : SimpleGraph V} {S : Set V} {a b : V}
    (p : (cone G S).Walk (some a) (some b)) (hp : p.IsPath) (hn : none ∉ p.support) :
    ∃ q : G.Walk a b, q.IsPath ∧ ∀ x, x ∈ q.support ↔ some x ∈ p.support := by
  have hs : ∀ x ∈ p.support, x ∈ Set.range (Option.some : V → Option V) := by
    intro x hx
    cases x with
    | none => exact (hn hx).elim
    | some x => exact ⟨x,rfl⟩
  let r := p.induce (Set.range (Option.some : V → Option V)) hs
  have hr : r.IsPath := by
    apply Walk.IsPath.of_map (f := (Embedding.induce _).toHom)
    simpa only [r,Walk.map_induce] using hp
  let q : G.Walk a b := r.map (pullbackHom G S a)
  refine ⟨q,Walk.map_isPath_of_injective (pullbackHom_injective G S a) hr,?_⟩
  intro x
  simp only [q,r,Walk.support_map,List.mem_map,Walk.support_induce,List.mem_attachWith]
  constructor
  · rintro ⟨⟨y,hy⟩,hyp,hx⟩
    obtain ⟨z,rfl⟩ := hy
    have hzx : z = x := hx
    simpa only [hzx] using hyp
  · intro hx
    exact ⟨⟨some x,⟨x,rfl⟩⟩,hx,rfl⟩

/-- Remove the final apex edge from a simple old-vertex-to-apex path. -/
lemma path_to_apex {G : SimpleGraph V} {S : Set V} {a : V}
    (p : (cone G S).Walk (some a) none) (hp : p.IsPath) :
    ∃ b ∈ S, ∃ q : G.Walk a b, q.IsPath ∧
      ∀ x, x ∈ q.support → some x ∈ p.support := by
  obtain ⟨w,hw,r,heq⟩ := Walk.exists_eq_cons_of_ne (by simp : (none : Option V) ≠ some a) p.reverse
  cases w with
  | none => exact hw.elim
  | some b =>
    have hb : b ∈ S := hw
    have hpath := hp.reverse
    rw [heq,Walk.cons_isPath_iff] at hpath
    obtain ⟨q,hq,hqs⟩ := pullback_path r hpath.1 hpath.2
    refine ⟨b,hb,q.reverse,hq.reverse,?_⟩
    intro x hx
    have hxq : x ∈ q.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hx
    have hxr := (hqs x).mp hxq
    have hxp : some x ∈ p.reverse.support := by
      rw [heq]
      exact r.support_subset_support_cons hw hxr
    simpa only [Walk.support_reverse,List.mem_reverse] using hxp

/-- A prefix of a simple path stops at its first vertex in S. -/
lemma first_hit_path {G : SimpleGraph V} (S : Set V) {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) (hb : b ∈ S) :
    ∃ w ∈ S, ∃ q : G.Walk a w, q.IsPath ∧ q.support ⊆ p.support ∧
      ∀ x, x ∈ q.support → x ∈ S → x = w := by
  induction p with
  | nil =>
    exact ⟨_,hb,.nil,Walk.IsPath.nil,(fun _ hx => hx),by intro x hx _; simpa using hx⟩
  | @cons a b c hab p ih =>
    by_cases ha : a ∈ S
    · refine ⟨a,ha,.nil,Walk.IsPath.nil,?_,?_⟩
      · intro x hx
        have hx' : x = a := by simpa using hx
        exact hx' ▸ (Walk.cons hab p).start_mem_support
      · intro x hx _
        simpa using hx
    · have hparts := (Walk.cons_isPath_iff hab p).mp hp
      obtain ⟨w,hw,q,hq,hsub,hfirst⟩ := ih hparts.1 hb
      refine ⟨w,hw,Walk.cons hab q,hq.cons (fun hx => hparts.2 (hsub hx)),?_,?_⟩
      · intro x hx
        simp only [Walk.support_cons,List.mem_cons] at hx ⊢
        exact hx.imp_right (fun h => hsub h)
      · intro x hx hxS
        simp only [Walk.support_cons,List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact (ha hxS).elim
        · exact hfirst x hx hxS

end Erdos184.FanPaths
