import Submission.FlatCanonicalKernel
import Submission.FourSingleContactKernel
open Erdos184Work
open CycleSegments FourSingleContactKernel
namespace CheckFlatCompute
lemma size_eq : FlatCanonicalKernel.size counts = 12 := by decide +kernel
lemma first_edge : (FlatCanonicalKernel.edge counts ⟨0,by rw [size_eq]; decide⟩).1 = 0 := by decide +kernel
lemma source_check : ∀ o : ∀ i : Fin 4, Marked.Order (CanonicalPairLayout.arity counts i),
    FlatCanonicalKernel.src counts marker_bound o ⟨0,by rw [size_eq]; decide⟩ = 2 := by
  decide +kernel
#print axioms source_check
end CheckFlatCompute
