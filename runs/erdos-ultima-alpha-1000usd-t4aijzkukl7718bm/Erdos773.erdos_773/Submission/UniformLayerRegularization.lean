import Submission.FourUniformRegularization

/-!
A finite regularization construction. Copies of a hypergraph are supplemented
by affine-line edges between copies of the same original vertex. The added
edges have pair codegree at most one. This is preparatory work, not an
independent-set lower bound or a proof of Erdős 773.
-/
namespace Erdos773.UniformLayerRegularization
open Finset HypergraphDegreeTrim
open FourUniformRegularization (pairDegree)
set_option maxHeartbeats 1500000
noncomputable section
variable {α ρ F : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] [Nontrivial ρ]
  [Field F] [Fintype F] [DecidableEq F]

abbrev Copy (ρ F : Type*) := ρ × F
abbrev Vertex (α ρ F : Type*) := α × Copy ρ F

def copyEdge (e : Finset α) (c : Copy ρ F) : Finset (Vertex α ρ F) :=
  e.image (fun a => (a,c))

omit [Fintype α] [Field F] [Fintype F] [Fintype ρ] [Nontrivial ρ] in
lemma mem_copyEdge {e : Finset α} {c : Copy ρ F} {x : Vertex α ρ F} :
    x ∈ copyEdge e c ↔ x.1 ∈ e ∧ x.2 = c := by
  rcases x with ⟨a,b⟩
  simp [copyEdge,eq_comm]

omit [Fintype α] [Field F] [Fintype F] [Fintype ρ] [Nontrivial ρ] in
lemma copyEdge_injective (c : Copy ρ F) :
    Function.Injective (fun e : Finset α => copyEdge e c) := by
  intro e f he
  ext a
  have hh := congrArg (fun t : Finset (Vertex α ρ F) => (a,c) ∈ t) he
  simpa only [mem_copyEdge,and_true] using hh.to_iff

omit [Fintype α] [Field F] [Fintype F] [Fintype ρ] [Nontrivial ρ] in
lemma copyEdge_card (e : Finset α) (c : Copy ρ F) : (copyEdge e c).card = e.card :=
  card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)

def line (h : ρ → F) (a : α) (s t : F) : Finset (Vertex α ρ F) :=
  univ.image (fun i => (a,(i,t+s*h i)))

omit [Fintype α] [Fintype F] [Nontrivial ρ] in
lemma mem_line {h : ρ → F} {a : α} {s t : F} {x : Vertex α ρ F} :
    x ∈ line h a s t ↔ x.1 = a ∧ x.2.2 = t+s*h x.2.1 := by
  rcases x with ⟨a',i,y⟩
  simp [line,eq_comm]

omit [Fintype α] [Fintype F] [Nontrivial ρ] in
lemma line_card (h : ρ → F) (a : α) (s t : F) :
    (line h a s t).card = Fintype.card ρ := by
  rw [line,card_image_of_injective _ (fun i j he => congrArg (fun x => x.2.1) he)]
  simp

omit [Fintype α] [Fintype F] in
lemma line_parameters {h : ρ → F} (hh : Function.Injective h)
    {a b : α} {s t u v : F} (he : line h a s t = line h b u v) :
    a = b ∧ s = u ∧ t = v := by
  obtain ⟨i,j,hij⟩ := exists_pair_ne ρ
  have h0 : (a,(i,t+s*h i)) ∈ line h b u v := by
    rw [← he]
    exact mem_line.mpr ⟨rfl,rfl⟩
  have h1 : (a,(j,t+s*h j)) ∈ line h b u v := by
    rw [← he]
    exact mem_line.mpr ⟨rfl,rfl⟩
  obtain ⟨hab,h0⟩ := mem_line.mp h0
  have h1 := (mem_line.mp h1).2
  have hne : h i - h j ≠ 0 := sub_ne_zero.mpr (fun he => by
    have := hh he
    exact hij this)
  have hmul : (s-u)*(h i-h j) = 0 := by linear_combination h0-h1
  have hsu := (mul_eq_zero.mp hmul).resolve_right hne
  have hsu : s = u := sub_eq_zero.mp hsu
  refine ⟨hab,hsu,?_⟩
  rw [hsu] at h0
  exact add_right_cancel h0

omit [Fintype α] [Fintype F] [Nontrivial ρ] in
lemma line_pair_unique {h : ρ → F} (hh : Function.Injective h)
    {x y : Vertex α ρ F} (hxy : x ≠ y)
    {a b : α} {s t u v : F}
    (hx : x ∈ line h a s t) (hy : y ∈ line h a s t)
    (hx' : x ∈ line h b u v) (hy' : y ∈ line h b u v) :
    line h a s t = line h b u v := by
  obtain ⟨hxa,hx⟩ := mem_line.mp hx
  obtain ⟨hya,hy⟩ := mem_line.mp hy
  obtain ⟨hxb,hx'⟩ := mem_line.mp hx'
  obtain ⟨hyb,hy'⟩ := mem_line.mp hy'
  have hij : x.2.1 ≠ y.2.1 := by
    intro he
    apply hxy
    apply Prod.ext (hxa.trans hya.symm)
    apply Prod.ext he
    rw [hx,hy,he]
  have hne : h x.2.1-h y.2.1 ≠ 0 := sub_ne_zero.mpr (fun he => hij (hh he))
  have hmul : (s-u)*(h x.2.1-h y.2.1)=0 := by
    linear_combination hx'-hx-hy'+hy
  have hsu : s=u := sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hne)
  have htv : t=v := by rw [hsu] at hx; linear_combination hx'-hx
  rw [hxa.symm.trans hxb,hsu,htv]

def oldEdges (H : Finset (Finset α)) : Finset (Finset (Vertex α ρ F)) :=
  (H ×ˢ (univ : Finset (Copy ρ F))).image (fun p => copyEdge p.1 p.2)

def newEdges (h : ρ → F) (S : α → Finset F) : Finset (Finset (Vertex α ρ F)) :=
  ((univ : Finset (α × F × F)).filter (fun p => p.2.1 ∈ S p.1)).image
    (fun p => line h p.1 p.2.1 p.2.2)

def regularized (H : Finset (Finset α)) (h : ρ → F) (S : α → Finset F) :=
  oldEdges (F := F) H ∪ newEdges h S

omit [Fintype α] [Field F] [Nontrivial ρ] in
lemma mem_oldEdges {H : Finset (Finset α)} {e : Finset (Vertex α ρ F)} :
    e ∈ oldEdges H ↔ ∃ f ∈ H, ∃ c : Copy ρ F, copyEdge f c = e := by
  simp [oldEdges]

omit [Nontrivial ρ] in
lemma mem_newEdges {h : ρ → F} {S : α → Finset F}
    {e : Finset (Vertex α ρ F)} :
    e ∈ newEdges h S ↔ ∃ a : α, ∃ s ∈ S a, ∃ t : F, line h a s t = e := by
  simp [newEdges]

lemma old_new_disjoint (H : Finset (Finset α)) (h : ρ → F) (S : α → Finset F) :
    Disjoint (oldEdges H) (newEdges h S) := by
  apply disjoint_left.mpr
  intro e he hf
  obtain ⟨f,hf,c,rfl⟩ := mem_oldEdges.mp he
  obtain ⟨a,s,hs,t,he⟩ := mem_newEdges.mp hf
  have hc (i : ρ) : i = c.1 := by
    have hm : (a,(i,t+s*h i)) ∈ copyEdge f c := by
      rw [← he]
      exact mem_line.mpr ⟨rfl,rfl⟩
    exact congrArg Prod.fst (mem_copyEdge.mp hm).2
  obtain ⟨i,j,hij⟩ := exists_pair_ne ρ
  exact hij ((hc i).trans (hc j).symm)

omit [Nontrivial ρ] in
lemma regularized_uniform (H : Finset (Finset α)) (h : ρ → F) (S : α → Finset F)
    (h4 : ∀ e ∈ H, e.card = Fintype.card ρ) :
    ∀ e ∈ regularized H h S, e.card = Fintype.card ρ := by
  intro e he
  rcases mem_union.mp he with he | he
  · obtain ⟨f,hf,c,rfl⟩ := mem_oldEdges.mp he
    rw [copyEdge_card,h4 f hf]
  · obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
    exact line_card h a s t

omit [Fintype α] [Field F] [Nontrivial ρ] in
lemma old_incident (H : Finset (Finset α)) (x : Vertex α ρ F) :
    (oldEdges H).filter (fun e => x ∈ e) =
      (H.filter (fun e => x.1 ∈ e)).image (fun e => copyEdge e x.2) := by
  ext e
  constructor
  · intro he
    obtain ⟨he,hx⟩ := mem_filter.mp he
    obtain ⟨f,hf,c,rfl⟩ := mem_oldEdges.mp he
    obtain ⟨hx',hc⟩ := mem_copyEdge.mp hx
    subst c
    exact mem_image.mpr ⟨f,mem_filter.mpr ⟨hf,hx'⟩,rfl⟩
  · intro he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    obtain ⟨hf,hx⟩ := mem_filter.mp hf
    exact mem_filter.mpr ⟨mem_oldEdges.mpr ⟨f,hf,x.2,rfl⟩,mem_copyEdge.mpr ⟨hx,rfl⟩⟩

omit [Fintype α] [Field F] [Nontrivial ρ] in
lemma old_degree (H : Finset (Finset α)) (x : Vertex α ρ F) :
    degree (oldEdges H) x = degree H x.1 := by
  rw [degree,old_incident,card_image_of_injective _ (copyEdge_injective _)]
  rfl

omit [Nontrivial ρ] in
lemma new_incident (h : ρ → F) (S : α → Finset F) (x : Vertex α ρ F) :
    (newEdges h S).filter (fun e => x ∈ e) =
      (S x.1).image (fun s => line h x.1 s (x.2.2-s*h x.2.1)) := by
  ext e
  constructor
  · intro he
    obtain ⟨he,hx⟩ := mem_filter.mp he
    obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
    obtain ⟨hxa,hx⟩ := mem_line.mp hx
    have ht : t=x.2.2-s*h x.2.1 := by linear_combination -hx
    subst a
    subst t
    exact mem_image.mpr ⟨s,hs,rfl⟩
  · intro he
    obtain ⟨s,hs,rfl⟩ := mem_image.mp he
    exact mem_filter.mpr ⟨mem_newEdges.mpr ⟨x.1,s,hs,_,rfl⟩,
      mem_line.mpr ⟨rfl,by ring⟩⟩

lemma new_degree (h : ρ → F) (hh : Function.Injective h)
    (S : α → Finset F) (x : Vertex α ρ F) :
    degree (newEdges h S) x = (S x.1).card := by
  rw [degree,new_incident,card_image_of_injective]
  intro s t he
  exact (line_parameters hh he).2.1

lemma regularized_degree (H : Finset (Finset α)) (h : ρ → F)
    (hh : Function.Injective h) (S : α → Finset F) (x : Vertex α ρ F) :
    degree (regularized H h S) x = degree H x.1+(S x.1).card := by
  unfold regularized degree
  rw [filter_union,card_union_of_disjoint
    ((old_new_disjoint H h S).mono (filter_subset _ _) (filter_subset _ _))]
  exact congrArg₂ (·+·) (old_degree H x) (new_degree h hh S x)

omit [Fintype α] [Field F] [Nontrivial ρ] in
lemma old_pair_incident (H : Finset (Finset α)) (x y : Vertex α ρ F)
    (hxy : x.2 = y.2) :
    (oldEdges H).filter (fun e => x ∈ e ∧ y ∈ e) =
      (H.filter (fun e => x.1 ∈ e ∧ y.1 ∈ e)).image (fun e => copyEdge e x.2) := by
  ext e
  constructor
  · intro he
    obtain ⟨he,hx,hy⟩ := mem_filter.mp he
    obtain ⟨f,hf,c,rfl⟩ := mem_oldEdges.mp he
    obtain ⟨hx',hc⟩ := mem_copyEdge.mp hx
    have hy' := (mem_copyEdge.mp hy).1
    subst c
    exact mem_image.mpr ⟨f,mem_filter.mpr ⟨hf,hx',hy'⟩,rfl⟩
  · intro he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    obtain ⟨hf,hx,hy⟩ := mem_filter.mp hf
    exact mem_filter.mpr ⟨mem_oldEdges.mpr ⟨f,hf,x.2,rfl⟩,
      mem_copyEdge.mpr ⟨hx,rfl⟩,mem_copyEdge.mpr ⟨hy,hxy.symm⟩⟩

omit [Fintype α] [Field F] [Nontrivial ρ] in
lemma old_pair_degree (H : Finset (Finset α)) (x y : Vertex α ρ F)
    (hxy : x.2 = y.2) :
    pairDegree (oldEdges H) x y = pairDegree H x.1 y.1 := by
  rw [pairDegree,old_pair_incident H x y hxy,
    card_image_of_injective _ (copyEdge_injective _)]
  rfl

omit [Fintype α] [Field F] [Nontrivial ρ] in
lemma old_pair_empty (H : Finset (Finset α)) (x y : Vertex α ρ F)
    (hxy : x.2 ≠ y.2) :
    (oldEdges H).filter (fun e => x ∈ e ∧ y ∈ e) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hx,hy⟩ := mem_filter.mp he
  obtain ⟨f,hf,c,rfl⟩ := mem_oldEdges.mp he
  exact hxy ((mem_copyEdge.mp hx).2.trans (mem_copyEdge.mp hy).2.symm)

omit [Nontrivial ρ] in
lemma new_pair_empty (h : ρ → F) (S : α → Finset F) (x y : Vertex α ρ F)
    (hxy : x.1 ≠ y.1) :
    (newEdges h S).filter (fun e => x ∈ e ∧ y ∈ e) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hx,hy⟩ := mem_filter.mp he
  obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
  exact hxy ((mem_line.mp hx).1.trans (mem_line.mp hy).1.symm)

omit [Nontrivial ρ] in
lemma new_pair_degree (h : ρ → F) (hh : Function.Injective h)
    (S : α → Finset F) (x y : Vertex α ρ F) (hxy : x ≠ y) :
    pairDegree (newEdges h S) x y ≤ 1 := by
  apply card_le_one.mpr
  intro e he f hf
  obtain ⟨he,hx,hy⟩ := mem_filter.mp he
  obtain ⟨hf,hx',hy'⟩ := mem_filter.mp hf
  obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
  obtain ⟨b,u,hu,v,rfl⟩ := mem_newEdges.mp hf
  exact line_pair_unique hh hxy hx hy hx' hy'

omit [Nontrivial ρ] in
/-- No pair-codegree loss, provided the old bound is at least one. -/
theorem regularized_pair_degree (H : Finset (Finset α)) (h : ρ → F)
    (hh : Function.Injective h) (S : α → Finset F) (K : ℕ) (hK : 1 ≤ K)
    (hcode : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K) :
    ∀ x y : Vertex α ρ F, x ≠ y → pairDegree (regularized H h S) x y ≤ K := by
  intro x y hxy
  by_cases hc : x.2 = y.2
  · have ha : x.1 ≠ y.1 := fun he => hxy (Prod.ext he hc)
    unfold pairDegree regularized
    rw [filter_union,new_pair_empty h S x y ha,union_empty]
    exact (old_pair_degree H x y hc).trans_le (hcode _ _ ha)
  · unfold pairDegree regularized
    rw [filter_union,old_pair_empty H x y hc,empty_union]
    exact (new_pair_degree h hh S x y hxy).trans hK

omit [Fintype α] [Field F] [Fintype F] [Fintype ρ] [Nontrivial ρ] in
lemma copy_inter_same (e f : Finset α) (c : Copy ρ F) :
    copyEdge e c ∩ copyEdge f c = copyEdge (e ∩ f) c := by
  ext x
  simp only [mem_inter,mem_copyEdge]
  tauto

omit [Fintype α] [Field F] [Fintype F] [Fintype ρ] [Nontrivial ρ] in
lemma copy_inter_distinct (e f : Finset α) (c d : Copy ρ F) (hcd : c ≠ d) :
    copyEdge e c ∩ copyEdge f d = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hx,hy⟩ := mem_inter.mp hx
  exact hcd ((mem_copyEdge.mp hx).2.symm.trans (mem_copyEdge.mp hy).2)

omit [Fintype α] [Fintype F] [Nontrivial ρ] in
lemma copy_line_inter_card (e : Finset α) (c : Copy ρ F)
    (h : ρ → F) (a : α) (s t : F) :
    (copyEdge e c ∩ line h a s t).card ≤ 1 := by
  apply card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxc,hxl⟩ := mem_inter.mp hx
  obtain ⟨hyc,hyl⟩ := mem_inter.mp hy
  exact Prod.ext ((mem_line.mp hxl).1.trans (mem_line.mp hyl).1.symm)
    ((mem_copyEdge.mp hxc).2.trans (mem_copyEdge.mp hyc).2.symm)

omit [Fintype α] [Fintype F] [Nontrivial ρ] in
lemma line_inter_card (h : ρ → F) (hh : Function.Injective h)
    (a b : α) (s t u v : F) (hne : line h a s t ≠ line h b u v) :
    (line h a s t ∩ line h b u v).card ≤ 1 := by
  apply card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  obtain ⟨hx,hx'⟩ := mem_inter.mp hx
  obtain ⟨hy,hy'⟩ := mem_inter.mp hy
  exact hne (line_pair_unique hh hxy hx hy hx' hy')

omit [Nontrivial ρ] in
/-- Edge-intersection bounds at least one are preserved as well. In particular,
    distinct edges with three common vertices cannot be newly introduced. -/
theorem regularized_intersections (H : Finset (Finset α)) (h : ρ → F)
    (hh : Function.Injective h) (S : α → Finset F) (k : ℕ) (hk : 1 ≤ k)
    (hinter : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ k) :
    ∀ e ∈ regularized H h S, ∀ f ∈ regularized H h S,
      e ≠ f → (e ∩ f).card ≤ k := by
  intro e he f hf hne
  rcases mem_union.mp he with he | he <;> rcases mem_union.mp hf with hf | hf
  · obtain ⟨a,ha,c,rfl⟩ := mem_oldEdges.mp he
    obtain ⟨b,hb,d,rfl⟩ := mem_oldEdges.mp hf
    by_cases hcd : c = d
    · subst d
      have hab : a ≠ b := fun he => hne (congrArg (fun t => copyEdge t c) he)
      rw [copy_inter_same,copyEdge_card]
      exact hinter a ha b hb hab
    · rw [copy_inter_distinct a b c d hcd]
      simp
  · obtain ⟨a,ha,c,rfl⟩ := mem_oldEdges.mp he
    obtain ⟨b,s,hs,t,rfl⟩ := mem_newEdges.mp hf
    exact (copy_line_inter_card a c h b s t).trans hk
  · obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
    obtain ⟨b,hb,c,rfl⟩ := mem_oldEdges.mp hf
    rw [inter_comm]
    exact (copy_line_inter_card b c h a s t).trans hk
  · obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
    obtain ⟨b,u,hu,v,rfl⟩ := mem_newEdges.mp hf
    exact (line_inter_card h hh a b s t u v hne).trans hk

/-- Original vertices retained in one fixed copy. -/
def slice (B : Finset (Vertex α ρ F)) (c : Copy ρ F) : Finset α :=
  univ.filter (fun a => (a,c) ∈ B)

omit [Field F] [Nontrivial ρ] in
lemma sum_slice_card (B : Finset (Vertex α ρ F)) :
    ∑ c : Copy ρ F, (slice B c).card = B.card := by
  simp only [slice,card_filter]
  rw [sum_comm,← Fintype.sum_prod_type (fun p : Vertex α ρ F => if p ∈ B then (1:ℕ) else 0)]
  simp

/-- Averaging independent sets back to the original hypergraph incurs exactly
    the number-of-copies factor, not an additional density loss. -/
theorem independent_slice (H : Finset (Finset α)) (h : ρ → F)
    (S : α → Finset F) (B : Finset (Vertex α ρ F))
    (hB : ∀ e ∈ regularized H h S, ¬e ⊆ B) :
    ∃ A : Finset α, (∀ e ∈ H, ¬e ⊆ A) ∧
      B.card ≤ (Fintype.card ρ * Fintype.card F) * A.card := by
  obtain ⟨c,hc,hmax⟩ := exists_max_image (univ : Finset (Copy ρ F))
    (fun c => (slice B c).card) univ_nonempty
  refine ⟨slice B c,?_,?_⟩
  · intro e he hsub
    apply hB (copyEdge e c) (mem_union_left _ (mem_oldEdges.mpr ⟨e,he,c,rfl⟩))
    intro x hx
    obtain ⟨hx',hcopy⟩ := mem_copyEdge.mp hx
    have hmem := (mem_filter.mp (hsub hx')).2
    simpa only [← hcopy,Prod.mk.eta] using hmem
  · calc
      B.card = ∑ d : Copy ρ F, (slice B d).card := (sum_slice_card B).symm
      _ ≤ ∑ _d : Copy ρ F, (slice B c).card := sum_le_sum (fun d hd => hmax d hd)
      _ = _ := by simp [Copy,Fintype.card_prod]

omit [DecidableEq α] [Field F] [DecidableEq F] [DecidableEq ρ] [Nontrivial ρ] in
lemma vertex_card : Fintype.card (Vertex α ρ F) = (Fintype.card ρ*Fintype.card F)*Fintype.card α := by
  simp only [Vertex,Copy,Fintype.card_prod]
  ring

/-- A real-valued lower bound on the independent-set density transfers
    unchanged from the regularization to the original graph. -/
theorem independent_density_transfer (H : Finset (Finset α)) (h : ρ → F)
    (S : α → Finset F) (B : Finset (Vertex α ρ F))
    (hB : ∀ e ∈ regularized H h S, ¬e ⊆ B) (δ : ℝ)
    (hδ : δ * Fintype.card (Vertex α ρ F) ≤ B.card) :
    ∃ A : Finset α, (∀ e ∈ H, ¬e ⊆ A) ∧ δ * Fintype.card α ≤ A.card := by
  obtain ⟨A,hA,hcard⟩ := independent_slice H h S B hB
  refine ⟨A,hA,?_⟩
  have hp : (0:ℝ) < (Fintype.card ρ:ℝ)*(Fintype.card F:ℝ) := by
    have hn : 0 < Fintype.card F := Fintype.card_pos
    have hr : 0 < Fintype.card ρ := Fintype.card_pos
    positivity
  have hc : (B.card:ℝ) ≤ ((Fintype.card ρ:ℝ)*(Fintype.card F:ℝ))*A.card := by exact_mod_cast hcard
  rw [vertex_card] at hδ
  push_cast at hδ
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith only [hδ,hc]

omit [Fintype α] [Field F] [DecidableEq F] in
lemma exists_slopes (H : Finset (Finset α)) (D : ℕ)
    (hD : D ≤ Fintype.card F) :
    ∃ S : α → Finset F, ∀ a : α, (S a).card = D-degree H a := by
  have hs (a : α) : ∃ s : Finset F, s.card = D-degree H a := by
    obtain ⟨s,hs,hcard⟩ := exists_subset_card_eq
      (show D-degree H a ≤ (univ : Finset F).card by simpa using (Nat.sub_le D _).trans hD)
    exact ⟨s,hcard⟩
  choose S hS using hs
  exact ⟨S,hS⟩


/-- The original constraints of one specified size. -/
def layer {β : Type*} [DecidableEq β] (H : Finset (Finset β)) (k : ℕ) : Finset (Finset β) :=
  H.filter (fun e => e.card=k)

omit [Fintype α] [Nontrivial ρ] [Field F] in
lemma layer_old (H : Finset (Finset α)) (k : ℕ) :
    layer (oldEdges (ρ := ρ) (F := F) H) k=oldEdges (layer H k) := by
  ext e
  simp only [layer,mem_filter,mem_oldEdges]
  constructor
  · rintro ⟨⟨f,hf,c,rfl⟩,hc⟩
    exact ⟨f,⟨hf,by simpa only [copyEdge_card] using hc⟩,c,rfl⟩
  · rintro ⟨f,⟨hf,hfc⟩,c,rfl⟩
    exact ⟨⟨f,hf,c,rfl⟩,by simpa only [copyEdge_card] using hfc⟩

omit [Nontrivial ρ] in
lemma layer_new_same (h : ρ → F) (S : α → Finset F) :
    layer (newEdges h S) (Fintype.card ρ)=newEdges h S := by
  apply filter_eq_self.mpr
  intro e he
  obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
  exact line_card h a s t

omit [Nontrivial ρ] in
lemma layer_new_other (h : ρ → F) (S : α → Finset F) {k : ℕ} (hk : k≠Fintype.card ρ) :
    layer (newEdges h S) k=∅ := by
  apply filter_eq_empty_iff.mpr
  intro e he hc
  obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
  exact hk (hc.symm.trans (line_card h a s t))

lemma layer_union {β : Type*} [DecidableEq β] (H G : Finset (Finset β)) (k : ℕ) :
    layer (H∪G) k=layer H k∪layer G k := filter_union _ _ _

omit [Nontrivial ρ] in
/-- Only the selected rank is changed. All the other degree layers are
copied exactly, including already-shortened constraints. -/
lemma degree_layer_other (H : Finset (Finset α)) (h : ρ → F) (S : α → Finset F)
    {k : ℕ} (hk : k≠Fintype.card ρ) (x : Vertex α ρ F) :
    degree (layer (regularized H h S) k) x=degree (layer H k) x.1 := by
  rw [regularized,layer_union,layer_old,layer_new_other h S hk,union_empty,old_degree]

lemma degree_layer_same (H : Finset (Finset α)) (h : ρ → F) (hh : Function.Injective h)
    (S : α → Finset F) (x : Vertex α ρ F) :
    degree (layer (regularized H h S) (Fintype.card ρ)) x=
      degree (layer H (Fintype.card ρ)) x.1+(S x.1).card := by
  rw [regularized,layer_union,layer_old,layer_new_same]
  exact regularized_degree (layer H (Fintype.card ρ)) h hh S x

omit [Nontrivial ρ] in
lemma rank_range (H : Finset (Finset α)) (h : ρ → F) (S : α → Finset F)
    (hH : ∀ e ∈ H, 2≤e.card ∧ e.card≤4)
    (hρ : 2≤Fintype.card ρ ∧ Fintype.card ρ≤4) :
    ∀ e ∈ regularized H h S, 2≤e.card ∧ e.card≤4 := by
  intro e he
  rcases mem_union.mp he with he | he
  · obtain ⟨f,hf,c,rfl⟩ := mem_oldEdges.mp he
    simpa only [copyEdge_card] using hH f hf
  · obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
    simpa only [line_card] using hρ

omit [Fintype α] [Field F] [Fintype F] [DecidableEq F] in
/-- An arbitrary large enough slope reservoir can fill every degree deficit;
using a Sidon reservoir will additionally control graph common neighbors. -/
lemma exists_slopes_subset (H : Finset (Finset α)) (D : ℕ) (T : Finset F) (hT : D≤T.card) :
    ∃ S : α → Finset F, (∀ a, S a⊆T) ∧ (∀ a, (S a).card=D-degree H a) := by
  have hs (a : α) : ∃ s ⊆ T, s.card=D-degree H a :=
    exists_subset_card_eq ((Nat.sub_le D _).trans hT)
  choose S hS hcard using hs
  exact ⟨S,hS,hcard⟩

#print axioms regularized_pair_degree
#print axioms regularized_intersections
#print axioms independent_density_transfer
#print axioms degree_layer_other
#print axioms degree_layer_same
#print axioms exists_slopes_subset

end
end Erdos773.UniformLayerRegularization
