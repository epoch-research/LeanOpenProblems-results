import Submission.TripleAlternation220

/-! The nonalternating (2,2,1) local kernel has a four-circuit partition,
for every choice of rotations and orientations of its three cyclic words. -/
namespace Erdos184Work.TripleAlternationKernels
open LabelKernel Erdos184Serial
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option Elab.async false
local instance : Fintype P4 := fintypePerm
local instance : Fintype P3 := fintypePerm

-- Adding the one contact between the two peripheral words changes the
-- obstruction from a minimum of three to a partition with four circuits.
def baseSrc221 : Fin 10 → Fin 5 := ![0,1,2,3,0,1,4,2,3,4]
def baseDst221 : Fin 10 → Fin 5 := ![1,2,3,0,1,4,0,3,4,2]
def cycle221a : CycleData (Fin 10) (Fin 5) := ⟨0,![0,4],![0,1]⟩
def cycle221b : CycleData (Fin 10) (Fin 5) := ⟨0,![2,7],![2,3]⟩
def cycle221c : CycleData (Fin 10) (Fin 5) := ⟨1,![1,9,5],![1,2,4]⟩
def cycle221d : CycleData (Fin 10) (Fin 5) := ⟨1,![3,6,8],![3,0,4]⟩
def baseCertificate221 : PartitionData (Fin 10) (Fin 5) :=
  ⟨4,![cycle221a,cycle221b,cycle221c,cycle221d]⟩
lemma base_valid221 : baseCertificate221.Valid baseSrc221 baseDst221 Finset.univ := by decide +kernel

def src221 (p : P4) (q r : P3) : Fin 10 → Fin 5 :=
  ![Fin.castLE (by decide) (p 0),Fin.castLE (by decide) (p 1),
    Fin.castLE (by decide) (p 2),Fin.castLE (by decide) (p 3),
    (![0,1,4] : Fin 3 → Fin 5) (q 0),![0,1,4] (q 1),![0,1,4] (q 2),
    ![2,3,4] (r 0),![2,3,4] (r 1),![2,3,4] (r 2)]
def dst221 (p : P4) (q r : P3) : Fin 10 → Fin 5 :=
  ![Fin.castLE (by decide) (p 1),Fin.castLE (by decide) (p 2),
    Fin.castLE (by decide) (p 3),Fin.castLE (by decide) (p 0),
    (![0,1,4] : Fin 3 → Fin 5) (q 1),![0,1,4] (q 2),![0,1,4] (q 0),
    ![2,3,4] (r 1),![2,3,4] (r 2),![2,3,4] (r 0)]
def vertex5 (p : P4) : Fin 5 → Fin 5 :=
  ![Fin.castLE (by decide) (vertex4 p 0),Fin.castLE (by decide) (vertex4 p 1),
    Fin.castLE (by decide) (vertex4 p 2),Fin.castLE (by decide) (vertex4 p 3),4]
def flip (h : Bool) : Fin 3 → Fin 3 := if h then ![1,0,2] else id

def edge221 (p : P4) (q r : P3) (e : Fin 10) : Fin 10 :=
  if h : e.val < 4 then Fin.castLE (by decide) (start p + ⟨e.val,h⟩)
  else if h' : e.val < 7 then
    ⟨4 + (q.symm (flip (decide (vertex4 p 0 = 1)) (⟨e.val-4,by omega⟩+2)) + 1).val,by omega⟩
  else
    ⟨7 + (r.symm (flip (decide (vertex4 p 2 = 3)) (⟨e.val-7,by omega⟩+2)) + 1).val,by omega⟩

lemma valid221 : ∀ (p : P4) (q r : P3), ¬ Alternating p →
    Function.Injective (edge221 p q r) ∧ Function.Injective (vertex5 p) ∧
      ∀ e, s(vertex5 p (baseSrc221 e),vertex5 p (baseDst221 e)) =
        s(src221 p q r (edge221 p q r e),dst221 p q r (edge221 p q r e)) := by decide +kernel

def embedding221 (p : P4) (q r : P3) (hp : ¬ Alternating p) :
    Embedding baseSrc221 baseDst221 (src221 p q r) (dst221 p q r) where
  edge := ⟨edge221 p q r,(valid221 p q r hp).1⟩
  vertex := ⟨vertex5 p,(valid221 p q r hp).2.1⟩
  endpoints := (valid221 p q r hp).2.2

lemma four221 (p : P4) (q r : P3) (hp : ¬ Alternating p) :
    ∃ D, Partition (code (src221 p q r) (dst221 p q r)) Finset.univ D ∧ D.card = 4 := by
  obtain ⟨D,hD,hcD⟩ := PartitionData.exists_partition base_valid221
  let M := embedding221 p q r hp
  obtain ⟨Q,hQ,hcQ⟩ := map_partition_exists M.edge M.valid_map hD
  have he : Finset.univ.map M.edge = Finset.univ :=
    Finset.map_univ_of_surjective (Finite.surjective_of_injective M.edge.injective)
  rw [he] at hQ
  exact ⟨Q,hQ,hcQ.trans hcD⟩

#print axioms number220
#print axioms four221
end Erdos184Work.TripleAlternationKernels
