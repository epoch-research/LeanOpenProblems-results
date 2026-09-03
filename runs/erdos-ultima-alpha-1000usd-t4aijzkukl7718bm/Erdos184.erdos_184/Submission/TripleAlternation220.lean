import Submission.KernelMarker
import Submission.LabelCycleCertificates
import Submission.LabelKernelEmbedding

/-! The two local obstructions forcing two pairs of contacts to alternate.
Arbitrary rotations and orientations of all three words are permitted. -/
namespace Erdos184Work.TripleAlternationKernels
open LabelKernel Erdos184Serial
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option Elab.async false

abbrev P4 := Equiv.Perm (Fin 4)
abbrev P3 := Equiv.Perm (Fin 3)
abbrev P2 := Equiv.Perm (Fin 2)

local instance : Fintype P4 := fintypePerm
local instance : Fintype P3 := fintypePerm
local instance : Fintype P2 := fintypePerm

def Alternating (p : P4) : Prop := p.symm 1 = p.symm 0 + 2
instance (p : P4) : Decidable (Alternating p) := inferInstanceAs (Decidable (_ = _))

def start (p : P4) : Fin 4 :=
  if (p 0).val < 2 ∧ (p 1).val < 2 then 0
  else if (p 1).val < 2 ∧ (p 2).val < 2 then 1
  else if (p 2).val < 2 ∧ (p 3).val < 2 then 2 else 3

def vertex4 (p : P4) (i : Fin 4) : Fin 4 := p (start p+i)

def src220 (p : P4) (q r : P2) : Fin 8 → Fin 4 :=
  ![p 0,p 1,p 2,p 3,(![0,1] : Fin 2 → Fin 4) (q 0),![0,1] (q 1),![2,3] (r 0),![2,3] (r 1)]
def dst220 (p : P4) (q r : P2) : Fin 8 → Fin 4 :=
  ![p 1,p 2,p 3,p 0,(![0,1] : Fin 2 → Fin 4) (q 1),![0,1] (q 0),![2,3] (r 1),![2,3] (r 0)]
def edge220 (p : P4) : Fin 8 → Fin 8 :=
  ![Fin.castLE (by decide) (start p),Fin.castLE (by decide) (start p+1),
    Fin.castLE (by decide) (start p+2),Fin.castLE (by decide) (start p+3),4,5,6,7]

lemma valid220 : ∀ (p : P4) (q r : P2), ¬ Alternating p →
    Function.Injective (edge220 p) ∧ Function.Injective (vertex4 p) ∧
      ∀ e, s(vertex4 p (NonAlternate220.src e),vertex4 p (NonAlternate220.dst e)) =
        s(src220 p q r (edge220 p e),dst220 p q r (edge220 p e)) := by decide +kernel

def embedding220 (p : P4) (q r : P2) (hp : ¬ Alternating p) :
    Embedding NonAlternate220.src NonAlternate220.dst (src220 p q r) (dst220 p q r) where
  edge := ⟨edge220 p,(valid220 p q r hp).1⟩
  vertex := ⟨vertex4 p,(valid220 p q r hp).2.1⟩
  endpoints := (valid220 p q r hp).2.2

lemma number220 (p : P4) (q r : P2) (hp : ¬ Alternating p) :
    HasNumber (code (src220 p q r) (dst220 p q r)) Finset.univ 3 := by
  let M := embedding220 p q r hp
  have he : Finset.univ.map M.edge = Finset.univ :=
    Finset.map_univ_of_surjective (Finite.surjective_of_injective M.edge.injective)
  have h := M.hasNumber_map_iff Finset.univ 3
  rw [he] at h
  exact h.mpr NonAlternate220.full_number


#print axioms number220
end Erdos184Work.TripleAlternationKernels
