import Submission.UniformLayerRegularization

/-! Affine padding introduces no new two-vertex shared links. This controls
a structural source of one-selected-vertex common-neighbor witnesses in a
mixed restart. No stochastic profile estimate is assumed or concluded. -/
namespace Erdos773.RegularizationSharedLinks
open Finset UniformLayerRegularization
set_option maxHeartbeats 2500000
noncomputable section

section Definition
variable {β : Type*} [Fintype β] [DecidableEq β]

def links (H : Finset (Finset β)) (x y : β) : Finset (Finset β) :=
  univ.filter (fun A => A.card=2 ∧ x∉A ∧ y∉A ∧ insert x A∈H ∧ insert y A∈H)

def count (H : Finset (Finset β)) (x y : β) : ℕ := (links H x y).card

lemma mem_links {H : Finset (Finset β)} {x y : β} {A : Finset β} :
    A∈links H x y ↔ A.card=2 ∧ x∉A ∧ y∉A ∧ insert x A∈H ∧ insert y A∈H := by
  simp [links]

omit [Fintype β] in
lemma insert_inter {A : Finset β} {x y : β} (hxy : x≠y) :
    insert x A∩insert y A=A := by
  ext a
  simp only [mem_inter,mem_insert]
  constructor
  · rintro ⟨h,h'⟩
    rcases h with rfl | h
    · exact h'.resolve_left hxy
    · exact h
  · intro h
    exact ⟨Or.inr h,Or.inr h⟩

omit [Fintype β] in
lemma insert_distinct {A : Finset β} {x y : β} (hxy : x≠y) (hx : x∉A) :
    insert x A≠insert y A := by
  intro he
  have hm : x∈insert y A := he ▸ mem_insert_self x A
  exact (mem_insert.mp hm).elim hxy hx
end Definition

section Copies
variable {α ρ F : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] [Field F] [Fintype F] [DecidableEq F]

/-- Any distinct edges with at least two common vertices lie together in
one old copy. All new/new and old/new overlaps have size at most one. -/
lemma overlap_rigid (H : Finset (Finset α)) (h : ρ → F) (hh : Function.Injective h)
    (S : α → Finset F) {e f : Finset (Vertex α ρ F)}
    (he : e∈regularized H h S) (hf : f∈regularized H h S)
    (hne : e≠f) (hi : 1<(e∩f).card) :
    ∃ a∈H, ∃ b∈H, ∃ c : Copy ρ F, e=copyEdge a c ∧ f=copyEdge b c := by
  rcases mem_union.mp he with he | he <;> rcases mem_union.mp hf with hf | hf
  · obtain ⟨a,ha,c,rfl⟩ := mem_oldEdges.mp he
    obtain ⟨b,hb,d,rfl⟩ := mem_oldEdges.mp hf
    have hcd : c=d := by
      by_contra hcd
      rw [copy_inter_distinct a b c d hcd,card_empty] at hi
      omega
    exact ⟨a,ha,b,hb,c,rfl,by rw [hcd]⟩
  · obtain ⟨a,ha,c,rfl⟩ := mem_oldEdges.mp he
    obtain ⟨b,s,hs,t,rfl⟩ := mem_newEdges.mp hf
    exact (not_lt_of_ge (copy_line_inter_card a c h b s t) hi).elim
  · obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
    obtain ⟨b,hb,c,rfl⟩ := mem_oldEdges.mp hf
    rw [inter_comm] at hi
    exact (not_lt_of_ge (copy_line_inter_card b c h a s t) hi).elim
  · obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
    obtain ⟨b,u,hu,v,rfl⟩ := mem_newEdges.mp hf
    exact (not_lt_of_ge (line_inter_card h hh a b s t u v hne) hi).elim

/-- A shared link forces its endpoints, and the whole link, into a common
copy coordinate. -/
lemma link_coordinates (H : Finset (Finset α)) (h : ρ → F) (hh : Function.Injective h)
    (S : α → Finset F) {x y : Vertex α ρ F} (hxy : x≠y)
    {A : Finset (Vertex α ρ F)} (hA : A∈links (regularized H h S) x y) :
    x.2=y.2 ∧ ∀ z∈A, z.2=x.2 := by
  obtain ⟨hcard,hx,hy,he,hf⟩ := mem_links.mp hA
  obtain ⟨a,ha,b,hb,c,he,hf⟩ := overlap_rigid H h hh S he hf
    (insert_distinct hxy hx) (by rw [insert_inter hxy,hcard]; decide)
  have hxc : x.2=c := (mem_copyEdge.mp (he ▸ mem_insert_self x A)).2
  have hyc : y.2=c := (mem_copyEdge.mp (hf ▸ mem_insert_self y A)).2
  exact ⟨hxc.trans hyc.symm,fun z hz =>
    ((mem_copyEdge.mp (he ▸ mem_insert_of_mem hz)).2).trans hxc.symm⟩

/-- Projecting a shared link gives a genuine old link. -/
lemma project_link (H : Finset (Finset α)) (h : ρ → F) (hh : Function.Injective h)
    (S : α → Finset F) {x y : Vertex α ρ F} (hxy : x≠y)
    {A : Finset (Vertex α ρ F)} (hA : A∈links (regularized H h S) x y) :
    A.image Prod.fst∈links H x.1 y.1 := by
  have hc := link_coordinates H h hh S hxy hA
  obtain ⟨hcard,hx,hy,he,hf⟩ := mem_links.mp hA
  obtain ⟨a,ha,b,hb,c,he,hf⟩ := overlap_rigid H h hh S he hf
    (insert_distinct hxy hx) (by rw [insert_inter hxy,hcard]; decide)
  have hinj : Set.InjOn (Prod.fst : Vertex α ρ F → α) (A:Set (Vertex α ρ F)) := by
    intro z hz w hw he
    exact Prod.ext he ((hc.2 z hz).trans (hc.2 w hw).symm)
  have hc' : (A.image Prod.fst).card=2 := (card_image_iff.mpr hinj).trans hcard
  have hx' : x.1∉A.image Prod.fst := by
    intro hx'
    obtain ⟨z,hz,hzx⟩ := mem_image.mp hx'
    have hez : z=x := Prod.ext hzx (hc.2 z hz)
    exact hx (hez ▸ hz)
  have hy' : y.1∉A.image Prod.fst := by
    intro hy'
    obtain ⟨z,hz,hzy⟩ := mem_image.mp hy'
    have hez : z=y := Prod.ext hzy ((hc.2 z hz).trans hc.1)
    exact hy (hez ▸ hz)
  have project (a : Finset α) (c : Copy ρ F) : (copyEdge a c).image Prod.fst=a := by
    simp only [copyEdge,image_image]
    exact image_id
  have hpa := congrArg (fun e : Finset (Vertex α ρ F) => e.image Prod.fst) he
  have hpb := congrArg (fun e : Finset (Vertex α ρ F) => e.image Prod.fst) hf
  dsimp only at hpa hpb
  rw [image_insert,project] at hpa hpb
  exact mem_links.mpr ⟨hc',hx',hy',hpa.symm ▸ ha,hpb.symm ▸ hb⟩

/-- Shared-link bounds are preserved, with no additive deterioration. -/
theorem count_bound (H : Finset (Finset α)) (h : ρ → F) (hh : Function.Injective h)
    (S : α → Finset F) (B : ℕ) (hB : ∀ a b, a≠b → count H a b≤B)
    (x y : Vertex α ρ F) (hxy : x≠y) : count (regularized H h S) x y≤B := by
  by_cases hc : x.2=y.2
  · have hab : x.1≠y.1 := fun he => hxy (Prod.ext he hc)
    apply (show count (regularized H h S) x y≤count H x.1 y.1 from ?_).trans (hB _ _ hab)
    apply card_le_card_of_injOn (fun A : Finset (Vertex α ρ F) => A.image Prod.fst)
    · exact fun A hA => project_link H h hh S hxy hA
    · intro A hA B hB he
      dsimp only at he
      have hAc := (link_coordinates H h hh S hxy hA).2
      have hBc := (link_coordinates H h hh S hxy hB).2
      ext z
      constructor
      · intro hz
        have hz' : z.1∈B.image Prod.fst := he ▸ mem_image_of_mem Prod.fst hz
        obtain ⟨w,hw,hwz⟩ := mem_image.mp hz'
        have hwz' : w=z := Prod.ext hwz ((hBc w hw).trans (hAc z hz).symm)
        exact hwz' ▸ hw
      · intro hz
        have hz' : z.1∈A.image Prod.fst := he.symm ▸ mem_image_of_mem Prod.fst hz
        obtain ⟨w,hw,hwz⟩ := mem_image.mp hz'
        have hwz' : w=z := Prod.ext hwz ((hAc w hw).trans (hBc z hz).symm)
        exact hwz' ▸ hw
  · have he : links (regularized H h S) x y=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro A hA
      exact hc (link_coordinates H h hh S hxy hA).1
    simp [count,he]
end Copies

#print axioms overlap_rigid
#print axioms link_coordinates
#print axioms project_link
#print axioms count_bound
end
end Erdos773.RegularizationSharedLinks
