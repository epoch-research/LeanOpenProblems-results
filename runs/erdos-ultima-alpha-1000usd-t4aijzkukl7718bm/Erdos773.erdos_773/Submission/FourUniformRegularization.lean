import Submission.HypergraphDegreeTrim

/-!
A finite regularization construction. Copies of a hypergraph are supplemented
by affine-line edges between copies of the same original vertex. The added
edges have pair codegree at most one. This is preparatory work, not an
independent-set lower bound or a proof of Erdős 773.
-/
namespace Erdos773.FourUniformRegularization
open Finset HypergraphDegreeTrim
set_option maxHeartbeats 1500000
noncomputable section
variable {α F : Type*} [Fintype α] [DecidableEq α]
  [Field F] [Fintype F] [DecidableEq F]

abbrev Copy (F : Type*) := Fin 4 × F
abbrev Vertex (α F : Type*) := α × Copy F

def copyEdge (e : Finset α) (c : Copy F) : Finset (Vertex α F) :=
  e.image (fun a => (a,c))

omit [Fintype α] [Field F] [Fintype F] in
lemma mem_copyEdge {e : Finset α} {c : Copy F} {x : Vertex α F} :
    x ∈ copyEdge e c ↔ x.1 ∈ e ∧ x.2 = c := by
  rcases x with ⟨a,b⟩
  simp [copyEdge,eq_comm]

omit [Fintype α] [Field F] [Fintype F] in
lemma copyEdge_injective (c : Copy F) :
    Function.Injective (fun e : Finset α => copyEdge e c) := by
  intro e f he
  ext a
  have hh := congrArg (fun t : Finset (Vertex α F) => (a,c) ∈ t) he
  simpa only [mem_copyEdge,and_true] using hh.to_iff

omit [Fintype α] [Field F] [Fintype F] in
lemma copyEdge_card (e : Finset α) (c : Copy F) : (copyEdge e c).card = e.card :=
  card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)

def line (h : Fin 4 → F) (a : α) (s t : F) : Finset (Vertex α F) :=
  univ.image (fun i => (a,(i,t+s*h i)))

omit [Fintype α] [Fintype F] in
lemma mem_line {h : Fin 4 → F} {a : α} {s t : F} {x : Vertex α F} :
    x ∈ line h a s t ↔ x.1 = a ∧ x.2.2 = t+s*h x.2.1 := by
  rcases x with ⟨a',i,y⟩
  simp [line,eq_comm]

omit [Fintype α] [Fintype F] in
lemma line_card (h : Fin 4 → F) (a : α) (s t : F) :
    (line h a s t).card = 4 := by
  rw [line,card_image_of_injective _ (fun i j he => congrArg (fun x => x.2.1) he)]
  simp

omit [Fintype α] [Fintype F] in
lemma line_parameters {h : Fin 4 → F} (hh : Function.Injective h)
    {a b : α} {s t u v : F} (he : line h a s t = line h b u v) :
    a = b ∧ s = u ∧ t = v := by
  have h0 : (a,((0 : Fin 4),t+s*h 0)) ∈ line h b u v := by
    rw [← he]
    exact mem_line.mpr ⟨rfl,rfl⟩
  have h1 : (a,((1 : Fin 4),t+s*h 1)) ∈ line h b u v := by
    rw [← he]
    exact mem_line.mpr ⟨rfl,rfl⟩
  obtain ⟨hab,h0⟩ := mem_line.mp h0
  have h1 := (mem_line.mp h1).2
  have hne : h 0 - h 1 ≠ 0 := sub_ne_zero.mpr (fun he => by
    have := hh he
    exact (by decide : (0 : Fin 4) ≠ 1) this)
  have hmul : (s-u)*(h 0-h 1) = 0 := by linear_combination h0-h1
  have hsu := (mul_eq_zero.mp hmul).resolve_right hne
  have hsu : s = u := sub_eq_zero.mp hsu
  refine ⟨hab,hsu,?_⟩
  rw [hsu] at h0
  exact add_right_cancel h0

omit [Fintype α] [Fintype F] in
lemma line_pair_unique {h : Fin 4 → F} (hh : Function.Injective h)
    {x y : Vertex α F} (hxy : x ≠ y)
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

def oldEdges (H : Finset (Finset α)) : Finset (Finset (Vertex α F)) :=
  (H ×ˢ (univ : Finset (Copy F))).image (fun p => copyEdge p.1 p.2)

def newEdges (h : Fin 4 → F) (S : α → Finset F) : Finset (Finset (Vertex α F)) :=
  ((univ : Finset (α × F × F)).filter (fun p => p.2.1 ∈ S p.1)).image
    (fun p => line h p.1 p.2.1 p.2.2)

def regularized (H : Finset (Finset α)) (h : Fin 4 → F) (S : α → Finset F) :=
  oldEdges (F := F) H ∪ newEdges h S

omit [Fintype α] [Field F] in
lemma mem_oldEdges {H : Finset (Finset α)} {e : Finset (Vertex α F)} :
    e ∈ oldEdges H ↔ ∃ f ∈ H, ∃ c : Copy F, copyEdge f c = e := by
  simp [oldEdges]

lemma mem_newEdges {h : Fin 4 → F} {S : α → Finset F}
    {e : Finset (Vertex α F)} :
    e ∈ newEdges h S ↔ ∃ a : α, ∃ s ∈ S a, ∃ t : F, line h a s t = e := by
  simp [newEdges]

lemma old_new_disjoint (H : Finset (Finset α)) (h : Fin 4 → F) (S : α → Finset F) :
    Disjoint (oldEdges H) (newEdges h S) := by
  apply disjoint_left.mpr
  intro e he hf
  obtain ⟨f,hf,c,rfl⟩ := mem_oldEdges.mp he
  obtain ⟨a,s,hs,t,he⟩ := mem_newEdges.mp hf
  have hc (i : Fin 4) : i = c.1 := by
    have hm : (a,(i,t+s*h i)) ∈ copyEdge f c := by
      rw [← he]
      exact mem_line.mpr ⟨rfl,rfl⟩
    exact congrArg Prod.fst (mem_copyEdge.mp hm).2
  exact (by decide : (0 : Fin 4) ≠ 1) ((hc 0).trans (hc 1).symm)

lemma regularized_uniform (H : Finset (Finset α)) (h : Fin 4 → F) (S : α → Finset F)
    (h4 : ∀ e ∈ H, e.card = 4) :
    ∀ e ∈ regularized H h S, e.card = 4 := by
  intro e he
  rcases mem_union.mp he with he | he
  · obtain ⟨f,hf,c,rfl⟩ := mem_oldEdges.mp he
    rw [copyEdge_card,h4 f hf]
  · obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
    exact line_card h a s t

omit [Fintype α] [Field F] in
lemma old_incident (H : Finset (Finset α)) (x : Vertex α F) :
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

omit [Fintype α] [Field F] in
lemma old_degree (H : Finset (Finset α)) (x : Vertex α F) :
    degree (oldEdges H) x = degree H x.1 := by
  rw [degree,old_incident,card_image_of_injective _ (copyEdge_injective _)]
  rfl

lemma new_incident (h : Fin 4 → F) (S : α → Finset F) (x : Vertex α F) :
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

lemma new_degree (h : Fin 4 → F) (hh : Function.Injective h)
    (S : α → Finset F) (x : Vertex α F) :
    degree (newEdges h S) x = (S x.1).card := by
  rw [degree,new_incident,card_image_of_injective]
  intro s t he
  exact (line_parameters hh he).2.1

lemma regularized_degree (H : Finset (Finset α)) (h : Fin 4 → F)
    (hh : Function.Injective h) (S : α → Finset F) (x : Vertex α F) :
    degree (regularized H h S) x = degree H x.1+(S x.1).card := by
  unfold regularized degree
  rw [filter_union,card_union_of_disjoint
    ((old_new_disjoint H h S).mono (filter_subset _ _) (filter_subset _ _))]
  exact congrArg₂ (·+·) (old_degree H x) (new_degree h hh S x)

def pairDegree {β : Type*} [DecidableEq β] (H : Finset (Finset β)) (x y : β) : ℕ :=
  (H.filter (fun e => x ∈ e ∧ y ∈ e)).card

omit [Fintype α] [Field F] in
lemma old_pair_incident (H : Finset (Finset α)) (x y : Vertex α F)
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

omit [Fintype α] [Field F] in
lemma old_pair_degree (H : Finset (Finset α)) (x y : Vertex α F)
    (hxy : x.2 = y.2) :
    pairDegree (oldEdges H) x y = pairDegree H x.1 y.1 := by
  rw [pairDegree,old_pair_incident H x y hxy,
    card_image_of_injective _ (copyEdge_injective _)]
  rfl

omit [Fintype α] [Field F] in
lemma old_pair_empty (H : Finset (Finset α)) (x y : Vertex α F)
    (hxy : x.2 ≠ y.2) :
    (oldEdges H).filter (fun e => x ∈ e ∧ y ∈ e) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hx,hy⟩ := mem_filter.mp he
  obtain ⟨f,hf,c,rfl⟩ := mem_oldEdges.mp he
  exact hxy ((mem_copyEdge.mp hx).2.trans (mem_copyEdge.mp hy).2.symm)

lemma new_pair_empty (h : Fin 4 → F) (S : α → Finset F) (x y : Vertex α F)
    (hxy : x.1 ≠ y.1) :
    (newEdges h S).filter (fun e => x ∈ e ∧ y ∈ e) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hx,hy⟩ := mem_filter.mp he
  obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
  exact hxy ((mem_line.mp hx).1.trans (mem_line.mp hy).1.symm)

lemma new_pair_degree (h : Fin 4 → F) (hh : Function.Injective h)
    (S : α → Finset F) (x y : Vertex α F) (hxy : x ≠ y) :
    pairDegree (newEdges h S) x y ≤ 1 := by
  apply card_le_one.mpr
  intro e he f hf
  obtain ⟨he,hx,hy⟩ := mem_filter.mp he
  obtain ⟨hf,hx',hy'⟩ := mem_filter.mp hf
  obtain ⟨a,s,hs,t,rfl⟩ := mem_newEdges.mp he
  obtain ⟨b,u,hu,v,rfl⟩ := mem_newEdges.mp hf
  exact line_pair_unique hh hxy hx hy hx' hy'

/-- No pair-codegree loss, provided the old bound is at least one. -/
theorem regularized_pair_degree (H : Finset (Finset α)) (h : Fin 4 → F)
    (hh : Function.Injective h) (S : α → Finset F) (K : ℕ) (hK : 1 ≤ K)
    (hcode : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K) :
    ∀ x y : Vertex α F, x ≠ y → pairDegree (regularized H h S) x y ≤ K := by
  intro x y hxy
  by_cases hc : x.2 = y.2
  · have ha : x.1 ≠ y.1 := fun he => hxy (Prod.ext he hc)
    unfold pairDegree regularized
    rw [filter_union,new_pair_empty h S x y ha,union_empty]
    exact (old_pair_degree H x y hc).trans_le (hcode _ _ ha)
  · unfold pairDegree regularized
    rw [filter_union,old_pair_empty H x y hc,empty_union]
    exact (new_pair_degree h hh S x y hxy).trans hK

omit [Fintype α] [Field F] [Fintype F] in
lemma copy_inter_same (e f : Finset α) (c : Copy F) :
    copyEdge e c ∩ copyEdge f c = copyEdge (e ∩ f) c := by
  ext x
  simp only [mem_inter,mem_copyEdge]
  tauto

omit [Fintype α] [Field F] [Fintype F] in
lemma copy_inter_distinct (e f : Finset α) (c d : Copy F) (hcd : c ≠ d) :
    copyEdge e c ∩ copyEdge f d = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hx,hy⟩ := mem_inter.mp hx
  exact hcd ((mem_copyEdge.mp hx).2.symm.trans (mem_copyEdge.mp hy).2)

omit [Fintype α] [Fintype F] in
lemma copy_line_inter_card (e : Finset α) (c : Copy F)
    (h : Fin 4 → F) (a : α) (s t : F) :
    (copyEdge e c ∩ line h a s t).card ≤ 1 := by
  apply card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxc,hxl⟩ := mem_inter.mp hx
  obtain ⟨hyc,hyl⟩ := mem_inter.mp hy
  exact Prod.ext ((mem_line.mp hxl).1.trans (mem_line.mp hyl).1.symm)
    ((mem_copyEdge.mp hxc).2.trans (mem_copyEdge.mp hyc).2.symm)

omit [Fintype α] [Fintype F] in
lemma line_inter_card (h : Fin 4 → F) (hh : Function.Injective h)
    (a b : α) (s t u v : F) (hne : line h a s t ≠ line h b u v) :
    (line h a s t ∩ line h b u v).card ≤ 1 := by
  apply card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  obtain ⟨hx,hx'⟩ := mem_inter.mp hx
  obtain ⟨hy,hy'⟩ := mem_inter.mp hy
  exact hne (line_pair_unique hh hxy hx hy hx' hy')

/-- Edge-intersection bounds at least one are preserved as well. In particular,
    distinct edges with three common vertices cannot be newly introduced. -/
theorem regularized_intersections (H : Finset (Finset α)) (h : Fin 4 → F)
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
def slice (B : Finset (Vertex α F)) (c : Copy F) : Finset α :=
  univ.filter (fun a => (a,c) ∈ B)

omit [Field F] in
lemma sum_slice_card (B : Finset (Vertex α F)) :
    ∑ c : Copy F, (slice B c).card = B.card := by
  simp only [slice,card_filter]
  rw [sum_comm,← Fintype.sum_prod_type (fun p : Vertex α F => if p ∈ B then (1:ℕ) else 0)]
  simp

/-- Averaging independent sets back to the original hypergraph incurs exactly
    the number-of-copies factor, not an additional density loss. -/
theorem independent_slice (H : Finset (Finset α)) (h : Fin 4 → F)
    (S : α → Finset F) (B : Finset (Vertex α F))
    (hB : ∀ e ∈ regularized H h S, ¬e ⊆ B) :
    ∃ A : Finset α, (∀ e ∈ H, ¬e ⊆ A) ∧
      B.card ≤ (4 * Fintype.card F) * A.card := by
  obtain ⟨c,hc,hmax⟩ := exists_max_image (univ : Finset (Copy F))
    (fun c => (slice B c).card) univ_nonempty
  refine ⟨slice B c,?_,?_⟩
  · intro e he hsub
    apply hB (copyEdge e c) (mem_union_left _ (mem_oldEdges.mpr ⟨e,he,c,rfl⟩))
    intro x hx
    obtain ⟨hx',hcopy⟩ := mem_copyEdge.mp hx
    have hmem := (mem_filter.mp (hsub hx')).2
    simpa only [← hcopy,Prod.mk.eta] using hmem
  · calc
      B.card = ∑ d : Copy F, (slice B d).card := (sum_slice_card B).symm
      _ ≤ ∑ _d : Copy F, (slice B c).card := sum_le_sum (fun d hd => hmax d hd)
      _ = _ := by simp [Copy,Fintype.card_prod]

omit [DecidableEq α] [Field F] [DecidableEq F] in
lemma vertex_card : Fintype.card (Vertex α F) = (4*Fintype.card F)*Fintype.card α := by
  simp only [Vertex,Copy,Fintype.card_prod,Fintype.card_fin]
  ring

/-- A real-valued lower bound on the independent-set density transfers
    unchanged from the regularization to the original graph. -/
theorem independent_density_transfer (H : Finset (Finset α)) (h : Fin 4 → F)
    (S : α → Finset F) (B : Finset (Vertex α F))
    (hB : ∀ e ∈ regularized H h S, ¬e ⊆ B) (ρ : ℝ)
    (hρ : ρ * Fintype.card (Vertex α F) ≤ B.card) :
    ∃ A : Finset α, (∀ e ∈ H, ¬e ⊆ A) ∧ ρ * Fintype.card α ≤ A.card := by
  obtain ⟨A,hA,hcard⟩ := independent_slice H h S B hB
  refine ⟨A,hA,?_⟩
  have hp : (0:ℝ) < 4*(Fintype.card F:ℝ) := by
    have hn : 0 < Fintype.card F := Fintype.card_pos
    positivity
  have hc : (B.card:ℝ) ≤ (4*(Fintype.card F:ℝ))*A.card := by exact_mod_cast hcard
  rw [vertex_card] at hρ
  push_cast at hρ
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith only [hρ,hc]

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

/-- Finite regularization over a field with four distinct row labels. -/
theorem exists_regularization_over_field (H : Finset (Finset α)) (D K : ℕ)
    (h4 : ∀ e ∈ H, e.card = 4) (hdeg : ∀ a : α, degree H a ≤ D)
    (hK : 1 ≤ K) (hcode : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (hD : D ≤ Fintype.card F) (h : Fin 4 → F) (hh : Function.Injective h) :
    ∃ G : Finset (Finset (Vertex α F)),
      (∀ e ∈ G, e.card = 4) ∧
      (∀ x : Vertex α F, degree G x = D) ∧
      (∀ x y : Vertex α F, x ≠ y → pairDegree G x y ≤ K) ∧
      (∀ k : ℕ, 1 ≤ k →
        (∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ k) →
        ∀ e ∈ G, ∀ f ∈ G, e ≠ f → (e ∩ f).card ≤ k) ∧
      (∀ B : Finset (Vertex α F), (∀ e ∈ G, ¬e ⊆ B) →
        ∃ A : Finset α, (∀ e ∈ H, ¬e ⊆ A) ∧
          B.card ≤ (4 * Fintype.card F) * A.card) := by
  obtain ⟨S,hS⟩ := exists_slopes (F := F) H D hD
  refine ⟨regularized H h S,regularized_uniform H h S h4,?_,
    regularized_pair_degree H h hh S K hK hcode,
    regularized_intersections H h hh S,independent_slice H h S⟩
  intro x
  rw [regularized_degree H h hh S x,hS x.1]
  exact Nat.add_sub_of_le (hdeg x.1)

/-- A prime field always supplies the finite regularization. There are exactly
`4*p` copies of the original vertex set, and the codegree bound is preserved. -/
theorem exists_regularization_prime (H : Finset (Finset α)) (D K : ℕ)
    (h4 : ∀ e ∈ H, e.card = 4) (hdeg : ∀ a : α, degree H a ≤ D)
    (hK : 1 ≤ K) (hcode : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K) :
    ∃ p : ℕ, p.Prime ∧ D ≤ p ∧ 3 < p ∧ p ≤ 2*max D 5 ∧
      ∃ G : Finset (Finset (Vertex α (ZMod p))),
        (∀ e ∈ G, e.card = 4) ∧
        (∀ x : Vertex α (ZMod p), degree G x = D) ∧
        (∀ x y : Vertex α (ZMod p), x ≠ y → pairDegree G x y ≤ K) ∧
        (∀ k : ℕ, 1 ≤ k →
          (∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ k) →
          ∀ e ∈ G, ∀ f ∈ G, e ≠ f → (e ∩ f).card ≤ k) ∧
        (∀ B : Finset (Vertex α (ZMod p)), (∀ e ∈ G, ¬e ⊆ B) →
          ∃ A : Finset α, (∀ e ∈ H, ¬e ⊆ A) ∧ B.card ≤ (4*p)*A.card) := by
  obtain ⟨p,hprime,hp,hpupper⟩ := Nat.exists_prime_lt_and_le_two_mul (max D 5) (by omega)
  letI : Fact p.Prime := ⟨hprime⟩
  have hpD : D ≤ p := (le_max_left _ _).trans hp.le
  have hp5 : 5 ≤ p := (le_max_right _ _).trans hp.le
  let h : Fin 4 → ZMod p := fun i => (i.val : ZMod p)
  have hh : Function.Injective h := by
    intro i j hij
    apply Fin.ext
    have he := (ZMod.natCast_eq_natCast_iff' i.val j.val p).mp hij
    simpa only [Nat.mod_eq_of_lt (show i.val < p by omega),
      Nat.mod_eq_of_lt (show j.val < p by omega)] using he
  obtain ⟨G,hG,hreg,hpair,hinter,hext⟩ := exists_regularization_over_field H D K h4 hdeg
    hK hcode (show D ≤ Fintype.card (ZMod p) by simpa using hpD) h hh
  refine ⟨p,hprime,hpD,by omega,hpupper,G,hG,hreg,hpair,hinter,?_⟩
  intro B hB
  simpa only [ZMod.card] using hext B hB

#print axioms independent_density_transfer
#print axioms exists_regularization_prime
#print axioms regularized_intersections
#print axioms regularized_uniform
#print axioms regularized_degree
#print axioms regularized_pair_degree
#print axioms independent_slice
#print axioms exists_regularization_over_field
end
end Erdos773.FourUniformRegularization
