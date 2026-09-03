import Submission.UniformLayerRegularization
import Submission.PolynomialSidonSlopes

/-! Common-neighbor control for regularizing an already mixed residual
hypergraph. Its graph layer is preserved by higher-rank regularization;
Sidon slopes bound the extra common neighbors in rank two. -/
namespace Erdos773.RegularizationCommonNeighbors
open Finset UniformLayerRegularization
set_option maxHeartbeats 2500000
noncomputable section
attribute [local instance] Classical.propDecidable

section Graph
variable {β : Type*} [Fintype β] [DecidableEq β]

def Adj (H : Finset (Finset β)) (x y : β) : Prop := x≠y ∧ ({x,y}:Finset β)∈H

def both (H K : Finset (Finset β)) (x y : β) : Finset β :=
  univ.filter (fun z => Adj H x z ∧ Adj K y z)

def common (H : Finset (Finset β)) (x y : β) : ℕ := (both H H x y).card

lemma mem_both {H K : Finset (Finset β)} {x y z : β} :
    z∈both H K x y ↔ Adj H x z ∧ Adj K y z := by simp [both]

omit [Fintype β] in
lemma adj_union (H K : Finset (Finset β)) (x y : β) :
    Adj (H∪K) x y ↔ Adj H x y ∨ Adj K x y := by simp [Adj,and_or_left]

lemma both_swap (H K : Finset (Finset β)) (x y : β) : both H K x y=both K H y x := by
  ext z
  simp only [mem_both,and_comm]

lemma common_union (H K : Finset (Finset β)) (x y : β) :
    common (H∪K) x y ≤ common H x y+(both H K x y).card+
      (both K H x y).card+common K x y := by
  have he : both (H∪K) (H∪K) x y=
      (both H H x y∪both H K x y)∪(both K H x y∪both K K x y) := by
    ext z
    simp only [mem_both,mem_union,adj_union]
    tauto
  unfold common
  rw [he]
  have h1 := card_union_le (both H H x y∪both H K x y) (both K H x y∪both K K x y)
  have h2 := card_union_le (both H H x y) (both H K x y)
  have h3 := card_union_le (both K H x y) (both K K x y)
  omega
end Graph

section Copies
variable {α ρ F : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] [Nontrivial ρ]
  [Field F] [Fintype F] [DecidableEq F]

omit [Fintype α] [Field F] [Nontrivial ρ] in
lemma old_adj (H : Finset (Finset α)) (x y : Vertex α ρ F) :
    Adj (oldEdges H) x y ↔ x.2=y.2 ∧ Adj H x.1 y.1 := by
  constructor
  · rintro ⟨hne,he⟩
    obtain ⟨f,hf,c,hfc⟩ := mem_oldEdges.mp he
    have hx : x∈copyEdge f c := by rw [hfc]; simp
    have hy : y∈copyEdge f c := by rw [hfc]; simp
    have hxc := (mem_copyEdge.mp hx).2
    have hyc := (mem_copyEdge.mp hy).2
    have hxy := hxc.trans hyc.symm
    have hab : x.1≠y.1 := fun h => hne (Prod.ext h hxy)
    have hec : copyEdge ({x.1,y.1}:Finset α) c=({x,y}:Finset (Vertex α ρ F)) := by
      simp only [copyEdge,image_insert,image_singleton]
      have hx' : (x.1,c)=x := by rw [← hxc]
      have hy' : (y.1,c)=y := by rw [← hyc]
      rw [hx',hy']
    have hfe := copyEdge_injective c (hfc.trans hec.symm)
    exact ⟨hxy,hab,by rwa [← hfe]⟩
  · rintro ⟨hxy,hab,hpair⟩
    refine ⟨fun h => hab (congrArg Prod.fst h),mem_oldEdges.mpr ⟨_,hpair,x.2,?_⟩⟩
    simp only [copyEdge,image_insert,image_singleton,Prod.mk.eta]
    rw [hxy]

omit [Nontrivial ρ] in
lemma new_adj_witness (h : ρ → F) (S : α → Finset F) {x y : Vertex α ρ F}
    (hxy : Adj (newEdges h S) x y) :
    ∃ a s, s∈S a ∧ ∃ t, x∈line h a s t ∧ y∈line h a s t := by
  obtain ⟨a,s,hs,t,he⟩ := mem_newEdges.mp hxy.2
  exact ⟨a,s,hs,t,by rw [he]; simp,by rw [he]; simp⟩

omit [Nontrivial ρ] in
lemma new_adj_label (h : ρ → F) (S : α → Finset F) {x y : Vertex α ρ F}
    (hxy : Adj (newEdges h S) x y) : x.1=y.1 := by
  obtain ⟨a,s,hs,t,hx,hy⟩ := new_adj_witness h S hxy
  exact (mem_line.mp hx).1.trans (mem_line.mp hy).1.symm

omit [Nontrivial ρ] in
lemma new_adj_row (h : ρ → F) (S : α → Finset F) {x y : Vertex α ρ F}
    (hxy : Adj (newEdges h S) x y) : x.2.1≠y.2.1 := by
  obtain ⟨a,s,hs,t,hx,hy⟩ := new_adj_witness h S hxy
  obtain ⟨hxa,hx⟩ := mem_line.mp hx
  obtain ⟨hya,hy⟩ := mem_line.mp hy
  intro he
  apply hxy.1
  refine Prod.ext (hxa.trans hya.symm) (Prod.ext he ?_)
  rw [hx,hy,he]

omit [Field F] in
lemma old_common_bound (H : Finset (Finset α)) (C : ℕ)
    (hC : ∀ a b, a≠b → common H a b≤C) (x y : Vertex α ρ F) (hxy : x≠y) :
    common (oldEdges H) x y≤C := by
  by_cases hc : x.2=y.2
  · have hab : x.1≠y.1 := fun h => hxy (Prod.ext h hc)
    have hb : (both (oldEdges H) (oldEdges H) x y).card≤(both H H x.1 y.1).card := by
      apply card_le_card_of_injOn Prod.fst
      · intro z hz
        obtain ⟨hx,hy⟩ := mem_both.mp hz
        exact mem_both.mpr ⟨((old_adj H x z).mp hx).2,((old_adj H y z).mp hy).2⟩
      · intro z hz w hw he
        have hzc := ((old_adj H x z).mp (mem_both.mp hz).1).1
        have hwc := ((old_adj H x w).mp (mem_both.mp hw).1).1
        exact Prod.ext he (hzc.symm.trans hwc)
    exact hb.trans (hC _ _ hab)
  · have he : both (oldEdges H) (oldEdges H) x y=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hx,hy⟩ := mem_both.mp hz
      exact hc (((old_adj H x z).mp hx).1.trans ((old_adj H y z).mp hy).1.symm)
    simp only [common,he,card_empty,Nat.zero_le]

/-- An old-edge/new-edge common neighbor is determined by one original
label and one copy coordinate, so there is at most one. -/
lemma mixed_common_bound (H : Finset (Finset α)) (h : ρ → F) (S : α → Finset F)
    (x y : Vertex α ρ F) : (both (oldEdges H) (newEdges h S) x y).card≤1 := by
  apply card_le_one.mpr
  intro z hz w hw
  obtain ⟨hxz,hyz⟩ := mem_both.mp hz
  obtain ⟨hxw,hyw⟩ := mem_both.mp hw
  have hzc := ((old_adj H x z).mp hxz).1
  have hwc := ((old_adj H x w).mp hxw).1
  have hza := new_adj_label h S hyz
  have hwa := new_adj_label h S hyw
  exact Prod.ext (hza.symm.trans hwa) (hzc.symm.trans hwc)

omit [Nontrivial ρ] in
lemma adj_regularized_other (H : Finset (Finset α)) (h : ρ → F) (S : α → Finset F)
    (hρ : Fintype.card ρ≠2) (x y : Vertex α ρ F) :
    Adj (regularized H h S) x y ↔ Adj (oldEdges H) x y := by
  rw [regularized,adj_union]
  have hn : ¬Adj (newEdges h S) x y := by
    rintro ⟨hne,he⟩
    obtain ⟨a,s,hs,t,hline⟩ := mem_newEdges.mp he
    have hh := congrArg Finset.card hline
    rw [line_card,card_pair hne] at hh
    exact hρ hh
  simp only [hn,or_false]

/-- Adding only higher-rank constraints leaves the graph layer unchanged
inside each old copy. -/
lemma higher_common_bound (H : Finset (Finset α)) (h : ρ → F) (S : α → Finset F)
    (hρ : Fintype.card ρ≠2) (C : ℕ) (hC : ∀ a b, a≠b → common H a b≤C)
    (x y : Vertex α ρ F) (hxy : x≠y) : common (regularized H h S) x y≤C := by
  have he : both (regularized H h S) (regularized H h S) x y=
      both (oldEdges H) (oldEdges H) x y := by
    ext z
    simp only [mem_both,adj_regularized_other H h S hρ]
  unfold common
  rw [he]
  exact old_common_bound H C hC x y hxy
end Copies

section TwoRows
variable {α F : Type*} [Fintype α] [DecidableEq α]
  [Field F] [Fintype F] [DecidableEq F]

lemma two_eq_of_ne (a b c : Fin 2) (hac : a≠c) (hbc : b≠c) : a=b := by
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have ha' : a.val≠c.val := fun h => hac (Fin.ext h)
  have hb' : b.val≠c.val := fun h => hbc (Fin.ext h)
  omega

/-- Sidon slope labels forbid a four-cycle entirely among newly added
rank-two edges. This controls common neighbors, not just pair codegrees. -/
lemma new_common_bound (h : Fin 2 → F) (hh : Function.Injective h)
    (S : α → Finset F) (T : Finset F) (hST : ∀ a, S a⊆T) (hT : IsSidon (T:Set F))
    (x y : Vertex α (Fin 2) F) (hxy : x≠y) : common (newEdges h S) x y≤1 := by
  apply card_le_one.mpr
  intro z hz w hw
  obtain ⟨hxz,hyz⟩ := mem_both.mp hz
  obtain ⟨hxw,hyw⟩ := mem_both.mp hw
  have hrowxy : x.2.1=y.2.1 := two_eq_of_ne _ _ _ (new_adj_row h S hxz) (new_adj_row h S hyz)
  have hrowzw : z.2.1=w.2.1 := two_eq_of_ne _ _ _ (new_adj_row h S hxz).symm (new_adj_row h S hxw).symm
  obtain ⟨a,s,hs,t,hx,hz⟩ := new_adj_witness h S hxz
  obtain ⟨b,u,hu,v,hy,hz'⟩ := new_adj_witness h S hyz
  obtain ⟨c,s',hs',t',hx',hw⟩ := new_adj_witness h S hxw
  obtain ⟨d,u',hu',v',hy',hw'⟩ := new_adj_witness h S hyw
  obtain ⟨hxa,hx⟩ := mem_line.mp hx
  obtain ⟨hza,hz⟩ := mem_line.mp hz
  obtain ⟨hyb,hy⟩ := mem_line.mp hy
  obtain ⟨hzb,hz'⟩ := mem_line.mp hz'
  obtain ⟨hxc,hx'⟩ := mem_line.mp hx'
  obtain ⟨hwc,hw⟩ := mem_line.mp hw
  obtain ⟨hyd,hy'⟩ := mem_line.mp hy'
  obtain ⟨hwd,hw'⟩ := mem_line.mp hw'
  have hxa' : x.1=y.1 := hxa.trans (hza.symm.trans (hzb.trans hyb.symm))
  have hvxy : x.2.2≠y.2.2 := fun he => hxy (Prod.ext hxa' (Prod.ext hrowxy he))
  have hdelta : h z.2.1-h x.2.1≠0 :=
    sub_ne_zero.mpr (fun he => (new_adj_row h S hxz).symm (hh he))
  have hslope : (s-u)*(h z.2.1-h x.2.1)=(s'-u')*(h z.2.1-h x.2.1) := by
    rw [← hrowxy] at hy hy'
    rw [← hrowzw] at hw hw'
    linear_combination -hz+hx+hz'-hy+hw-hx'-hw'+hy'
  have he : s-u=s'-u' := mul_right_cancel₀ hdelta hslope
  have hsu : s≠u := by
    intro he
    rw [← hrowxy] at hy
    have ht : t=v := by rw [he] at hz; linear_combination hz'-hz
    apply hvxy
    rw [hx,hy,he,ht]
  have hss := PolynomialSidonSlopes.difference_unique hT
    (hST a hs) (hST b hu) (hST c hs') (hST d hu') hsu he
  have htt : t=t' := by rw [hss.1] at hx; linear_combination hx'-hx
  refine Prod.ext (hza.trans (hxa.symm.trans (hxc.trans hwc.symm))) (Prod.ext hrowzw ?_)
  rw [hz,hw,htt,hss.1,hrowzw]

/-- The graph common-neighbor cap grows by at most three. The original
constraints are all retained, and no density-transfer assertion is needed
for this local structural estimate. -/
theorem two_common_bound (H : Finset (Finset α)) (h : Fin 2 → F) (hh : Function.Injective h)
    (S : α → Finset F) (T : Finset F) (hST : ∀ a, S a⊆T) (hT : IsSidon (T:Set F))
    (C : ℕ) (hC : ∀ a b, a≠b → common H a b≤C)
    (x y : Vertex α (Fin 2) F) (hxy : x≠y) : common (regularized H h S) x y≤C+3 := by
  have h1 := common_union (oldEdges H) (newEdges h S) x y
  have h2 := old_common_bound H C hC x y hxy
  have h3 := mixed_common_bound H h S x y
  have h4 := mixed_common_bound H h S y x
  rw [both_swap] at h4
  have h5 := new_common_bound h hh S T hST hT x y hxy
  change common (oldEdges H∪newEdges h S) x y≤C+3
  omega
end TwoRows

#print axioms old_common_bound
#print axioms higher_common_bound
#print axioms new_common_bound
#print axioms two_common_bound
end
end Erdos773.RegularizationCommonNeighbors
