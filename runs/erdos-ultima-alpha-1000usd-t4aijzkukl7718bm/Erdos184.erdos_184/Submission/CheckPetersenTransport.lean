import Submission.DoublePetersenCore
import Submission.LabelKernelRealization
import Submission.PathKernelDifference
open SimpleGraph
open scoped Classical
namespace Erdos184Work.DoublePetersenGraph
open Critical EvenCore Rigidity Erdos184Serial DoublePetersen
abbrev Vertex := DoublePetersen.Vertex ⊕ DoublePetersen.Edge
def graph : SimpleGraph Vertex := LabelKernel.Realization.graph src dst
lemma loopless : ∀ e, src e ≠ dst e := fun e => PetersenBase.src_ne_dst e.1
def family : PathSubstitution.Family DoublePetersen.Edge DoublePetersen.Vertex graph :=
  LabelKernel.Realization.family src dst loopless
lemma valid_eq (s : Finset DoublePetersen.Edge) : family.validLabels s ↔ DoublePetersen.code.valid s := by
  unfold PathSubstitution.Family.validLabels DoublePetersen.code LabelKernel.code LabelKernel.valid
  dsimp [family, LabelKernel.Realization.family]
  apply forall_congr'
  intro w
  apply iff_of_eq
  congr 2
  ext j
  simp

lemma number_iff (s : Finset DoublePetersen.Edge) (k : ℕ) :
    @HasNumber _ (Classical.decEq _) (@LabelKernel.code _ _ (Classical.decEq _) (Classical.decEq _) family.src family.dst) s k ↔
      HasNumber DoublePetersen.code s k := by
  have hE : Classical.decEq DoublePetersen.Edge = (fun a b => instDecidableEqProd a b) := Subsingleton.elim _ _
  have hW : Classical.decEq DoublePetersen.Vertex = instDecidableEqFin 10 := Subsingleton.elim _ _
  rw [hE,hW]
  rfl
end Erdos184Work.DoublePetersenGraph
