import Submission.LabelKernelEmbedding

/-! Circuits in the two-copy parallel extension of a labelled graph. -/
namespace Erdos184Work.LabelKernel.Parallel
open Erdos184Serial
set_option maxHeartbeats 1000000
variable {E W : Type*} [DecidableEq E] [DecidableEq W]
variable (src dst : E → W)

def source (j : E × Bool) : W := src j.1
def target (j : E × Bool) : W := dst j.1

def pair (e : E) : Finset (E × Bool) := {(e,false),(e,true)}

lemma pair_valid (e : E) : (code (source src) (target dst)).valid (pair e) := by
  intro w
  by_cases h : src e = w ∨ dst e = w
  · simp [pair,source,target,Finset.filter_insert,Finset.filter_singleton,h]
  · simp [pair,source,target,Finset.filter_insert,Finset.filter_singleton,h]

lemma pair_nonempty (e : E) : (pair e).Nonempty := by simp [pair]

def choiceEmbedding (b : E → Bool) :
    Embedding src dst (source src) (target dst) where
  edge := ⟨fun e => (e,b e),fun _ _ h => congrArg Prod.fst h⟩
  vertex := Function.Embedding.refl W
  endpoints _ := rfl

lemma image_choice {s : Finset (E × Bool)}
    (h : ∀ e, ¬ ((e,false) ∈ s ∧ (e,true) ∈ s)) :
    (s.image Prod.fst).map (choiceEmbedding src dst (fun e => decide ((e,true) ∈ s))).edge = s := by
  ext p
  rcases p with ⟨e,b⟩
  simp only [Finset.mem_map,Finset.mem_image,choiceEmbedding]
  constructor
  · rintro ⟨i,⟨⟨j,c⟩,hj,he⟩,hp⟩
    have hje : j = e := he.trans (congrArg Prod.fst hp)
    subst j
    have hi : i = e := congrArg Prod.fst hp
    subst i
    have hb : decide ((e,true) ∈ s) = b := congrArg Prod.snd hp
    cases b with
    | true => exact of_decide_eq_true hb
    | false =>
      have hn : (e,true) ∉ s := of_decide_eq_false hb
      cases c with
      | false => exact hj
      | true => exact (hn hj).elim
  · intro hp
    refine ⟨e,⟨(e,b),hp,rfl⟩,?_⟩
    change (e,decide ((e,true) ∈ s)) = (e,b)
    refine Prod.ext rfl ?_
    cases b with
    | true => exact decide_eq_true hp
    | false => exact decide_eq_false (fun ht => h e ⟨hp,ht⟩)

lemma circuit_cases {s : Finset (E × Bool)}
    (hs : Circuit (code (source src) (target dst)) s) :
    (∃ e, s = pair e) ∨
      ∃ t : Finset E, ∃ b : E → Bool,
        Circuit (code src dst) t ∧ s = t.map (choiceEmbedding src dst b).edge := by
  classical
  by_cases h : ∃ e, (e,false) ∈ s ∧ (e,true) ∈ s
  · obtain ⟨e,he0,he1⟩ := h
    left
    refine ⟨e,?_⟩
    have hsub : pair e ⊆ s := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact he0
      · have hh := Finset.mem_singleton.mp hx
        exact hh.symm ▸ he1
    exact (hs.2.2 _ hsub (pair_valid src dst e) (pair_nonempty e)).symm
  · right
    have hn : ∀ e, ¬ ((e,false) ∈ s ∧ (e,true) ∈ s) := by simpa using h
    let b : E → Bool := fun e => decide ((e,true) ∈ s)
    have he := image_choice src dst hn
    refine ⟨s.image Prod.fst,b,?_,he.symm⟩
    apply ((choiceEmbedding src dst b).circuit_map_iff _).mp
    rw [he]
    exact hs

lemma sum_choice {M : Type*} [AddCommMonoid M] (w : E → M)
    (t : Finset E) (b : E → Bool) :
    ∑ p ∈ t.map (choiceEmbedding src dst b).edge, w p.1 = ∑ e ∈ t, w e := by
  rw [Finset.sum_map]
  rfl

#print axioms circuit_cases
end Erdos184Work.LabelKernel.Parallel
