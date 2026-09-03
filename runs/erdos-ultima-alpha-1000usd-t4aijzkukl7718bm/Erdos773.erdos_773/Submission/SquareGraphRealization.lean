import Submission.QuadraticRotationSpecialization
import Submission.GreedyHypergraphState

/-!
Every finite simple graph has a positive-integer square realization as a
residual two-graph. Each graph edge has two private selected vertices, using
the 3-4-5 rotation. All square-pair relations are controlled by the finite
specialization theorem. This gives no quantitative root-height estimate and
is not a settlement of Erdős 773.
-/
namespace Erdos773.SquareGraphRealization
open Finset GreedyHypergraphState QuadraticRotationTrade
set_option maxHeartbeats 2500000
noncomputable section

abbrev Index {n : ℕ} (E : Finset (Edge n)) := {e : Edge n // e ∈ E}
abbrev Vertex {n : ℕ} (E : Finset (Edge n)) := Fin n ⊕ (Index E × Bool)

def embed {n : ℕ} {E : Finset (Edge n)} : Vertex E → Root n
  | .inl a => .core a
  | .inr (e,false) => .plus e.val
  | .inr (e,true) => .minus e.val

lemma embed_injective {n : ℕ} {E : Finset (Edge n)} :
    Function.Injective (embed (E := E)) := by
  classical
  intro u v h
  rcases u with a | ⟨e,c⟩ <;> rcases v with b | ⟨f,d⟩
  · simpa [embed] using h
  · cases d <;> simp [embed] at h
  · cases c <;> simp [embed] at h
  · cases c <;> cases d <;> simp only [embed] at h
    all_goals first
      | cases h
      | have he : e=f := Subtype.ext (Root.plus.inj h); subst f; rfl
      | have he : e=f := Subtype.ext (Root.minus.inj h); subst f; rfl

def edge {n : ℕ} {E : Finset (Edge n)} (e : Index E) : Finset (Vertex E) :=
  {.inl e.val.val.1, .inl e.val.val.2, .inr (e,false), .inr (e,true)}

def H {n : ℕ} (E : Finset (Edge n)) : Finset (Finset (Vertex E)) := by
  classical
  exact univ.image (edge (E := E))

def I {n : ℕ} (E : Finset (Edge n)) : Finset (Vertex E) := univ.image Sum.inr

def cores {n : ℕ} (E : Finset (Edge n)) : Finset (Vertex E) := univ.image Sum.inl

lemma edge_image {n : ℕ} {E : Finset (Edge n)} (e : Index E) :
    (edge e).image embed=QuadraticRotationTrade.support e.val := by
  classical
  simp [edge, QuadraticRotationTrade.support, embed]

lemma edge_card {n : ℕ} {E : Finset (Edge n)} (e : Index E) : (edge e).card=4 := by
  classical
  rw [← card_image_of_injective _ embed_injective, edge_image, support_card]

lemma endpoint_pair_injective {n : ℕ} {e f : Edge n}
    (h : ({e.val.1,e.val.2} : Finset (Fin n))={f.val.1,f.val.2}) : e=f := by
  have hs : ({e.val.1,e.val.2} : Set (Fin n))={f.val.1,f.val.2} := by
    simpa only [coe_insert,coe_singleton] using congrArg (fun s : Finset (Fin n) => (s : Set (Fin n))) h
  rcases Set.pair_eq_pair_iff.mp hs with ⟨h₁,h₂⟩ | hh
  · exact Subtype.ext (Prod.ext h₁ h₂)
  · exact (edge_swap_impossible e f hh).elim

lemma endpoint_inter_bound {n : ℕ} {e f : Edge n} (hne : e ≠ f) :
    (({e.val.1,e.val.2} : Finset (Fin n)) ∩ {f.val.1,f.val.2}).card ≤ 1 := by
  classical
  by_contra hn
  have h₂ : 2 ≤ (({e.val.1,e.val.2} : Finset (Fin n)) ∩ {f.val.1,f.val.2}).card := by omega
  have he : ({e.val.1,e.val.2} : Finset (Fin n)).card=2 := by simp [ne_of_lt e.property]
  have hf : ({f.val.1,f.val.2} : Finset (Fin n)).card=2 := by simp [ne_of_lt f.property]
  have hl := eq_of_subset_of_card_le inter_subset_left (he ▸ h₂)
  have hr := eq_of_subset_of_card_le inter_subset_right (hf ▸ h₂)
  exact hne (endpoint_pair_injective (hl.symm.trans hr))

lemma edge_inter_bound {n : ℕ} {E : Finset (Edge n)} {e f : Index E} (hne : e ≠ f) :
    (edge e ∩ edge f).card ≤ 1 := by
  classical
  have he : e.val ≠ f.val := fun h => hne (Subtype.ext h)
  have hs : edge e ∩ edge f ⊆
      (({e.val.val.1,e.val.val.2} : Finset (Fin n)) ∩ {f.val.val.1,f.val.val.2}).image Sum.inl := by
    intro u hu
    rcases u with a | ⟨g,c⟩
    · obtain ⟨hu,hv⟩ := mem_inter.mp hu
      have h₁ : a=e.val.val.1 ∨ a=e.val.val.2 := by simpa [edge] using hu
      have h₂ : a=f.val.val.1 ∨ a=f.val.val.2 := by simpa [edge] using hv
      exact mem_image.mpr ⟨a,by simp [h₁,h₂],rfl⟩
    · obtain ⟨hu,hv⟩ := mem_inter.mp hu
      have h₁ : g=e := by cases c <;> simpa [edge] using hu
      have h₂ : g=f := by cases c <;> simpa [edge] using hv
      exact (hne (h₁.symm.trans h₂)).elim
  exact (card_le_card hs).trans (card_image_le.trans (endpoint_inter_bound he))

/-- The original square-collision hypergraph is linear as well. -/
theorem linear {n : ℕ} (E : Finset (Edge n)) :
    ∀ e ∈ H E, ∀ f ∈ H E, e ≠ f → (e ∩ f).card ≤ 1 := by
  classical
  intro e he f hf hne
  obtain ⟨i,_,rfl⟩ := mem_image.mp he
  obtain ⟨j,_,rfl⟩ := mem_image.mp hf
  exact edge_inter_bound (fun h => hne (congrArg edge h))

lemma four_uniform {n : ℕ} (E : Finset (Edge n)) : ∀ e ∈ H E, e.card=4 := by
  classical
  intro e he
  obtain ⟨i,_,rfl⟩ := mem_image.mp he
  exact edge_card i

@[simp] lemma label_mem_I {n : ℕ} {E : Finset (Edge n)} (e : Index E) (c : Bool) :
    (Sum.inr (e,c) : Vertex E) ∈ I E := by simp [I]

@[simp] lemma core_notMem_I {n : ℕ} {E : Finset (Edge n)} (a : Fin n) :
    (Sum.inl a : Vertex E) ∉ I E := by simp [I]

lemma edge_residual {n : ℕ} {E : Finset (Edge n)} (e : Index E) :
    edge e \ I E={.inl e.val.val.1, .inl e.val.val.2} := by
  classical
  ext u
  rcases u with a | ⟨f,c⟩ <;> simp [mem_sdiff,edge]

lemma independent {n : ℕ} (E : Finset (Edge n)) : Independent (H E) (I E) := by
  classical
  intro e he hs
  obtain ⟨i,_,rfl⟩ := mem_image.mp he
  exact core_notMem_I i.val.val.1 (hs (by simp [edge]))

lemma label_available {n : ℕ} {E : Finset (Edge n)} {J : Finset (Vertex E)}
    (hJ : J ⊆ I E) {e : Index E} {c : Bool} (hn : Sum.inr (e,c) ∉ J) :
    Sum.inr (e,c) ∈ available (H E) J :=
  mem_available.mpr ⟨hn,(independent E).mono (insert_subset (label_mem_I e c) hJ)⟩

lemma available_eq {n : ℕ} (E : Finset (Edge n)) : available (H E) (I E)=cores E := by
  classical
  ext u
  rcases u with a | ⟨e,c⟩
  · have hc : (Sum.inl a : Vertex E) ∈ cores E := by simp [cores]
    simp only [mem_available,core_notMem_I,not_false_eq_true,true_and,iff_true_intro hc,iff_true]
    intro s hs hsub
    obtain ⟨e,_,rfl⟩ := mem_image.mp hs
    have h₁ := hsub (show Sum.inl e.val.val.1 ∈ edge e by simp [edge])
    have h₂ := hsub (show Sum.inl e.val.val.2 ∈ edge e by simp [edge])
    simp only [mem_insert,Sum.inl.injEq,core_notMem_I,or_false] at h₁ h₂
    exact (ne_of_lt e.val.property) (h₁.trans h₂.symm)
  · simp [mem_available,cores]

lemma plus_mem_embed {n : ℕ} {E : Finset (Edge n)} {s : Finset (Vertex E)} {e : Edge n}
    (h : Root.plus e ∈ s.image embed) : e ∈ E := by
  classical
  obtain ⟨u,_,hu⟩ := mem_image.mp h
  rcases u with a | ⟨f,c⟩
  · simp [embed] at hu
  · cases c with
    | false => have he : f.val=e := Root.plus.inj hu; exact he ▸ f.property
    | true => simp [embed] at hu

lemma support_lift {n : ℕ} {E : Finset (Edge n)} {s : Finset (Vertex E)} {e : Edge n}
    (h : s.image embed=QuadraticRotationTrade.support e) : s ∈ H E := by
  classical
  have he : e ∈ E := plus_mem_embed (by rw [h]; simp [QuadraticRotationTrade.support])
  let i : Index E := ⟨e,he⟩
  have hi : s=edge i := by
    classical
    apply Finset.image_injective embed_injective
    rw [h,edge_image]
  rw [hi]
  exact mem_image.mpr ⟨i,mem_univ _,rfl⟩

/-- The exact four-root square-collision hypergraph on a finite carrier. -/
def squareEdges {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℕ) : Finset (Finset α) :=
  by
    classical
    exact univ.powerset.filter (fun s => s.card=4 ∧ ∃ a b c d, s={a,b,c,d} ∧ f a^2+f b^2=f c^2+f d^2)

lemma relation_support {n : ℕ} {E : Finset (Edge n)} {f : Vertex E → ℕ}
    (hf : ∀ u v w z, f u^2+f v^2=f w^2+f z^2 ↔
      value (embed u)+value (embed v)=value (embed w)+value (embed z))
    {u v w z : Vertex E} (h : f u^2+f v^2=f w^2+f z^2) :
    ((u=w ∧ v=z) ∨ (u=z ∧ v=w)) ∨ {u,v,w,z} ∈ H E := by
  classical
  rcases pair_classification ((hf u v w z).mp h) with hm | ⟨e,he⟩
  · exact Or.inl (hm.imp (fun ⟨h₁,h₂⟩ => ⟨embed_injective h₁,embed_injective h₂⟩)
      (fun ⟨h₁,h₂⟩ => ⟨embed_injective h₁,embed_injective h₂⟩))
  · right
    apply support_lift (e := e)
    simpa only [image_insert,image_singleton] using he

lemma squareEdges_eq {n : ℕ} {E : Finset (Edge n)} {f : Vertex E → ℕ}
    (hf : ∀ u v w z, f u^2+f v^2=f w^2+f z^2 ↔
      value (embed u)+value (embed v)=value (embed w)+value (embed z)) :
    squareEdges f=H E := by
  classical
  ext s
  constructor
  · intro hs
    simp only [squareEdges, mem_filter, mem_powerset, subset_univ, true_and] at hs
    obtain ⟨hc,a,b,c,d,rfl,he⟩ := hs
    rcases relation_support hf he with hm | hh
    · have hsub : ({a,b,c,d} : Finset (Vertex E)) ⊆ {a,b} := by
        rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [insert_subset_iff,singleton_subset_iff]
      have hsmall := (card_le_card hsub).trans (card_le_two (a := a) (b := b))
      omega
    · exact hh
  · intro hs
    obtain ⟨e,_,rfl⟩ := mem_image.mp hs
    simp only [squareEdges,mem_filter,mem_powerset,subset_univ,true_and]
    refine ⟨edge_card e,Sum.inr (e,false),Sum.inr (e,true),
      Sum.inl e.val.val.1,Sum.inl e.val.val.2,?_,?_⟩
    · ext u
      simp only [edge,mem_insert,mem_singleton]
      tauto
    · apply (hf _ _ _ _).mpr
      exact trade e.val

/-- Independence here is exactly Sidonness, including the possible
    three-root obstructions: no such obstruction is silently omitted. -/
lemma sidon_iff_independent {n : ℕ} {E : Finset (Edge n)} {f : Vertex E → ℕ}
    (hinj : Function.Injective f)
    (hf : ∀ u v w z, f u^2+f v^2=f w^2+f z^2 ↔
      value (embed u)+value (embed v)=value (embed w)+value (embed z))
    (J : Finset (Vertex E)) :
    IsSidon (J.image (fun u => f u^2) : Set ℕ) ↔ Independent (H E) J := by
  classical
  constructor
  · intro hS s hs hsub
    obtain ⟨e,_,rfl⟩ := mem_image.mp hs
    have hmem (u : Vertex E) (hu : u ∈ edge e) :
        f u^2 ∈ (J.image (fun v => f v^2) : Set ℕ) := mem_image.mpr ⟨u,hsub hu,rfl⟩
    have heq := (hf (Sum.inr (e,false)) (Sum.inr (e,true))
      (Sum.inl e.val.val.1) (Sum.inl e.val.val.2)).mpr (trade e.val)
    have hh := hS _ (hmem _ (by simp [edge])) _ (hmem _ (by simp [edge]))
      _ (hmem _ (by simp [edge])) _ (hmem _ (by simp [edge])) heq
    rcases hh with ⟨he,_⟩ | ⟨he,_⟩
    all_goals
      have hi := hinj (Nat.pow_left_injective (by decide : (2:ℕ) ≠ 0) he)
      cases hi
  · intro hJ a ha b hb c hc d hd heq
    obtain ⟨u,hu,rfl⟩ := mem_image.mp ha
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hb
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hc
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hd
    rcases relation_support hf heq with hm | hh
    · rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
    · exact (hJ _ hh (by simp [insert_subset_iff,singleton_subset_iff,hu,hv,hw,hz])).elim

lemma selected_sidon {n : ℕ} {E : Finset (Edge n)} {f : Vertex E → ℕ}
    (hf : ∀ u v w z, f u^2+f v^2=f w^2+f z^2 ↔
      value (embed u)+value (embed v)=value (embed w)+value (embed z)) :
    IsSidon ((I E).image (fun u => f u^2) : Set ℕ) := by
  classical
  intro a ha b hb c hc d hd heq
  obtain ⟨u,hu,rfl⟩ := mem_image.mp ha
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hb
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hc
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hd
  rcases relation_support hf heq with hm | hh
  · rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
  · exact ((independent E) _ hh (by simp [insert_subset_iff,singleton_subset_iff,hu,hv,hw,hz])).elim

/-- Every finite graph is realized by actual positive integer squares. The
    selected labels have Sidon squares, and their legal residual graph is
    exactly the prescribed graph on the core vertices. -/
theorem realize (n : ℕ) (E : Finset (Edge n)) :
    ∃ f : Vertex E → ℕ, (∀ u, 0 < f u) ∧ Function.Injective f ∧
      (∀ J, IsSidon (J.image (fun u => f u^2) : Set ℕ) ↔ Independent (H E) J) ∧
      squareEdges f=H E ∧ IsSidon ((I E).image (fun u => f u^2) : Set ℕ) ∧
      available (squareEdges f) (I E)=cores E ∧
      (∀ J ⊆ I E, ∀ u ∈ I E, u ∉ J → u ∈ available (squareEdges f) J) ∧
      (∀ e : Index E, edge e \ I E={.inl e.val.val.1,.inl e.val.val.2}) := by
  classical
  obtain ⟨g,hpos,hinj,hg⟩ := exists_integer_model n
  let f : Vertex E → ℕ := g ∘ embed
  have hf : ∀ u v w z, f u^2+f v^2=f w^2+f z^2 ↔
      value (embed u)+value (embed v)=value (embed w)+value (embed z) :=
    fun u v w z => hg _ _ _ _
  have hs := squareEdges_eq hf
  refine ⟨f,fun u => hpos _,hinj.comp embed_injective,
    sidon_iff_independent (hinj.comp embed_injective) hf,hs,selected_sidon hf,?_,?_,edge_residual⟩
  · rw [hs,available_eq]
  · intro J hJ u hu hn
    obtain ⟨⟨e,c⟩,_,rfl⟩ := mem_image.mp hu
    rw [hs]
    exact label_available hJ hn

#print axioms linear
#print axioms four_uniform
#print axioms independent
#print axioms available_eq
#print axioms relation_support
#print axioms squareEdges_eq
#print axioms sidon_iff_independent
#print axioms selected_sidon
#print axioms realize
end
end Erdos773.SquareGraphRealization
