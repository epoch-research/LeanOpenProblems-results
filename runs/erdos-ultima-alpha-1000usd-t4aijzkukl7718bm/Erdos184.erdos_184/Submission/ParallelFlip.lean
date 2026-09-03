import Submission.ParallelLabels

/-! Independent permutations of the two copies of each parallel edge. -/
namespace Erdos184Work.LabelKernel.Parallel
open Erdos184Serial
variable {E W : Type*} [DecidableEq E] [DecidableEq W]
variable (src dst : E → W)

def flip (b : E → Bool) :
    Embedding (source src) (target dst) (source src) (target dst) where
  edge := ⟨fun p => (p.1,Bool.xor p.2 (b p.1)),by
    rintro ⟨e,c⟩ ⟨f,d⟩ h
    have he : e = f := congrArg Prod.fst h
    subst f
    have hc : Bool.xor c (b e) = Bool.xor d (b e) := congrArg Prod.snd h
    have hcd : c = d := by cases c <;> cases d <;> cases b e <;> simp_all
    exact congrArg (fun x => (e,x)) hcd⟩
  vertex := Function.Embedding.refl W
  endpoints _ := rfl

lemma flip_surjective (b : E → Bool) : Function.Surjective (flip src dst b).edge := by
  rintro ⟨e,c⟩
  refine ⟨(e,Bool.xor c (b e)),?_⟩
  change (e,Bool.xor (Bool.xor c (b e)) (b e)) = (e,c)
  cases c <;> cases b e <;> rfl

lemma flip_choice (t : Finset E) (b : E → Bool) :
    (t.map (choiceEmbedding src dst (fun _ => false)).edge).map (flip src dst b).edge =
      t.map (choiceEmbedding src dst b).edge := by
  rw [Finset.map_map]
  congr 1
  apply Function.Embedding.ext
  intro e
  change (e,Bool.xor false (b e)) = (e,b e)
  cases b e <;> rfl

lemma flip_univ [Fintype E] (b : E → Bool) :
    Finset.univ.map (flip src dst b).edge = Finset.univ :=
  Finset.map_univ_of_surjective (flip_surjective src dst b)

lemma cofactor_partition [Fintype E] (t : Finset E) (b : E → Bool) (k : ℕ)
    (h : ∃ D, Partition (code (source src) (target dst))
      (Finset.univ \ t.map (choiceEmbedding src dst (fun _ => false)).edge) D ∧ D.card = k) :
    ∃ D, Partition (code (source src) (target dst))
      (Finset.univ \ t.map (choiceEmbedding src dst b).edge) D ∧ D.card = k := by
  obtain ⟨D,hD,hcD⟩ := h
  obtain ⟨A,hA,hcA⟩ := map_partition_exists (flip src dst b).edge (flip src dst b).valid_map hD
  rw [Finset.map_sdiff,flip_univ,flip_choice] at hA
  exact ⟨A,hA,hcA.trans hcD⟩

#print axioms cofactor_partition
end Erdos184Work.LabelKernel.Parallel
