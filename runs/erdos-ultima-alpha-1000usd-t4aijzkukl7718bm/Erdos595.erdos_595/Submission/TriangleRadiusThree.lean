import Submission.TriangleComponentProduct

/-!
A sharp local threshold: in a K4-free graph, edges at triangle-sharing
radius at most three from one edge have a three-piece triangle-free cover.
The earlier TriangleRadius construction has radius four and contains arbitrary
K4-free graphs, so this local bound does not settle Erdős 595.
-/

open SimpleGraph Set
namespace Erdos595TriangleRadiusThree
open Erdos595Work Erdos595BadEdge Erdos595TriangleComponentProduct

variable {V : Type*} (G : SimpleGraph V)

/-- Waiting or moving between two edges of one triangle. -/
def Near (e f : Edge G) : Prop := e = f ∨ Step G e f

def RadiusThree (e f : Edge G) : Prop :=
  ∃ e₁ e₂, Near G e e₁ ∧ Near G e₁ e₂ ∧ Near G e₂ f

lemma first_hits {a b : V} (hab : G.Adj a b) {e : Edge G}
    (h : Near G ⟨s(a,b),hab⟩ e) : a ∈ e.val ∨ b ∈ e.val := by
  rcases h with rfl | ⟨x,y,z,hxy,hxz,hyz,he,hf⟩
  · exact Or.inl (Sym2.mem_mk_left _ _)
  · have ha : a = x ∨ a = y := Sym2.mem_iff.mp (he ▸ Sym2.mem_mk_left a b)
    have hb : b = x ∨ b = y := Sym2.mem_iff.mp (he ▸ Sym2.mem_mk_right a b)
    have he' : (a = x ∧ b = y) ∨ (a = y ∧ b = x) := Sym2.eq_iff.mp he
    rw [hf]
    rcases he' with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl (Sym2.mem_mk_left _ _)
    · exact Or.inr (Sym2.mem_mk_left _ _)

lemma near_from_incident {r : V} {e f : Edge G}
    (hr : r ∈ e.val) (h : Near G e f) :
    ∀ v ∈ f.val, v = r ∨ G.Adj r v := by
  rcases h with rfl | ⟨x,y,z,hxy,hxz,hyz,he,hf⟩
  · obtain ⟨⟨x,y⟩,he⟩ := Quot.exists_rep e.val
    change s(x,y) = e.val at he
    have hxy : G.Adj x y := by simpa only [← he] using e.property
    rw [← he] at hr ⊢
    rcases Sym2.mem_iff.mp hr with rfl | rfl
    · intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr hxy
    · intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact Or.inr hxy.symm
      · exact Or.inl rfl
  · rw [he] at hr
    rw [hf]
    rcases Sym2.mem_iff.mp hr with rfl | rfl
    · intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr hxz
    · intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact Or.inr hxy.symm
      · exact Or.inr hyz

lemma second_inside {a b : V} (hab : G.Adj a b) {e₁ e₂ : Edge G}
    (h₁ : Near G ⟨s(a,b),hab⟩ e₁) (h₂ : Near G e₁ e₂) :
    ∀ v ∈ e₂.val, G.Adj a v ∨ G.Adj b v := by
  rcases first_hits G hab h₁ with ha | hb
  · intro v hv
    rcases near_from_incident G ha h₂ v hv with rfl | hadj
    · exact Or.inr hab.symm
    · exact Or.inl hadj
  · intro v hv
    rcases near_from_incident G hb h₂ v hv with rfl | hadj
    · exact Or.inl hab
    · exact Or.inr hadj

lemma near_shared {e f : Edge G} (h : Near G e f) :
    ∃ v, v ∈ e.val ∧ v ∈ f.val := by
  rcases h with rfl | ⟨x,y,z,hxy,hxz,hyz,he,hf⟩
  · obtain ⟨⟨x,y⟩,he⟩ := Quot.exists_rep e.val
    change s(x,y) = e.val at he
    exact ⟨x,he ▸ Sym2.mem_mk_left _ _,he ▸ Sym2.mem_mk_left _ _⟩
  · exact ⟨x,he ▸ Sym2.mem_mk_left _ _,hf ▸ Sym2.mem_mk_left _ _⟩

/-- Radius three cannot reach an edge with both endpoints outside the two
root neighborhoods. This combinatorial fact does not need K4-freeness. -/
theorem radius_three_touches {a b x y : V} (hab : G.Adj a b) (hxy : G.Adj x y)
    (h : RadiusThree G ⟨s(a,b),hab⟩ ⟨s(x,y),hxy⟩) :
    (G.Adj a x ∨ G.Adj b x) ∨ (G.Adj a y ∨ G.Adj b y) := by
  obtain ⟨e₁,e₂,h₁,h₂,h₃⟩ := h
  obtain ⟨v,hve,hvf⟩ := near_shared G h₃
  have hv := second_inside G hab h₁ h₂ v hve
  rcases Sym2.mem_iff.mp hvf with rfl | rfl
  · exact Or.inl hv
  · exact Or.inr hv

noncomputable def internal (a b : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧
    ((G.Adj a x ∧ G.Adj a y) ∨ (G.Adj b x ∧ G.Adj b y))
  symm := fun _ _ h => ⟨h.1.symm,h.2.imp And.symm And.symm⟩
  loopless := fun _ h => h.1.ne rfl

lemma internal_triangleFree (hG : G.CliqueFree 4) (a b : V) :
    (internal G a b).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨x,y,z,hxy,hxz,hyz,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  have ha : G.Adj a x → G.Adj a y → G.Adj a z → False := fun hx hy hz =>
    no_adj_common_neighbors hG hxy.1 hxz.1 hyz.1 hx.symm hy.symm hz.symm
  have hb : G.Adj b x → G.Adj b y → G.Adj b z → False := fun hx hy hz =>
    no_adj_common_neighbors hG hxy.1 hxz.1 hyz.1 hx.symm hy.symm hz.symm
  rcases hxy.2 with h₁ | h₁ <;> rcases hxz.2 with h₂ | h₂ <;>
    rcases hyz.2 with h₃ | h₃ <;> aesop

noncomputable def cut (a : V) : SimpleGraph V := by
  classical
  exact G ⊓ (⊤ : SimpleGraph Bool).comap (fun x => decide (G.Adj a x))

lemma cut_triangleFree (a : V) : (cut G a).CliqueFree 3 := by
  classical
  have hc : (cut G a).Colorable 2 :=
    (SimpleGraph.Coloring.mk (G := cut G a) (fun x => decide (G.Adj a x))
      (fun h => h.2)).colorable
  exact hc.cliqueFree (by decide)

/-- Three pieces suffice for ANY K4-free graph whose edges all touch the
union of two neighborhoods. The neighborhoods can be arbitrarily large. -/
theorem three_cover_of_touch (hG : G.CliqueFree 4) (a b : V)
    (ht : ∀ x y, G.Adj x y →
      (G.Adj a x ∨ G.Adj b x) ∨ (G.Adj a y ∨ G.Adj b y)) :
    Erdos595CompleteFilterEdgeCover.CoversWith G 3 := by
  classical
  refine ⟨![internal G a b,cut G a,cut G b],?_,?_⟩
  · intro j
    fin_cases j
    · exact internal_triangleFree G hG a b
    · exact cut_triangleFree G a
    · exact cut_triangleFree G b
  · intro x y hxy
    have htouch := ht x y hxy
    by_cases hax : G.Adj a x
    · by_cases hay : G.Adj a y
      · exact ⟨0,hxy,Or.inl ⟨hax,hay⟩⟩
      · exact ⟨1,by simp [cut,hxy,hax,hay]⟩
    · by_cases hay : G.Adj a y
      · exact ⟨1,by simp [cut,hxy,hax,hay]⟩
      · by_cases hbx : G.Adj b x
        · by_cases hby : G.Adj b y
          · exact ⟨0,hxy,Or.inr ⟨hbx,hby⟩⟩
          · exact ⟨2,by simp [cut,hxy,hbx,hby]⟩
        · have hby : G.Adj b y := by tauto
          exact ⟨2,by simp [cut,hxy,hbx,hby]⟩

/-- In particular, global triangle-sharing radius at most three implies a
FINITE cover. Radius four, unlike radius three, is universal for K4-free graphs. -/
theorem radius_three_finite_cover (hG : G.CliqueFree 4) {a b : V} (hab : G.Adj a b)
    (hr : ∀ x y (hxy : G.Adj x y),
      RadiusThree G ⟨s(a,b),hab⟩ ⟨s(x,y),hxy⟩) :
    Erdos595CompleteFilterEdgeCover.CoversWith G 3 :=
  three_cover_of_touch G hG a b (fun x y hxy => radius_three_touches G hab hxy (hr x y hxy))

#print axioms radius_three_touches
#print axioms three_cover_of_touch
#print axioms radius_three_finite_cover
end Erdos595TriangleRadiusThree
