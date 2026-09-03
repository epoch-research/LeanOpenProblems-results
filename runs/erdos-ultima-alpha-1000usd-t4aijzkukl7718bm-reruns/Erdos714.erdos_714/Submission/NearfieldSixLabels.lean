import Submission.LabelledSumGraphs

/-!
The concrete degree-six label operation at q=7 and its cubic-subfield label
embedding. The operation is noncommutative, but its left translations are
permutations, so the general exact counts apply. The field-label compatibility
in the transfer theorem is an explicit hypothesis, not a trusted discrete-log
computation. This does not settle Erdős 714.
-/
noncomputable section
open SimpleGraph Classical
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
namespace Erdos714NearfieldSixLabels
abbrev U := ZMod 18
abbrev W := ZMod 144

def qUnit : Wˣ := ⟨7,103,by decide,by decide⟩

def leftPerm (a : W) : Equiv W W :=
  (MulAction.toPerm (qUnit^(a.val%6))).trans (Equiv.addLeft a)

lemma leftPerm_apply (a b : W) : leftPerm a b=a+7^(a.val%6)*b := by
  simp [leftPerm,qUnit,MulAction.toPerm_apply,Units.smul_def,smul_eq_mul]

/-- The retained operation is not ordinary addition on exponent labels. -/
lemma noncommutative : leftPerm 1 2 ≠ leftPerm 2 1 := by decide

/-- Explicit image of the cyclic eighteen-element subfield label group. -/
def label (a : U) : W := 56*(a.val : W)+(if a.val%3=2 then 96 else 0)

lemma label_injective : Function.Injective label := by decide
lemma label_product : ∀ a b : U, label (a+b)=leftPerm (label a) (label b) := by decide

def labelEmbedding : U ↪ W := ⟨label,label_injective⟩

/-- Given the actual compatibility of the two field-label maps, the entire
cubic-subfield graph embeds. No commutativity of the larger label operation
is assumed or inferred. -/
def subfieldCopy {K E : Type*} [Field K] [Field E]
    (ν : Kˣ → U) (μ : Eˣ → W) (f : K →+* E)
    (hν : ∀ z, μ (Units.map f.toMonoidHom z)=label (ν z)) :
    (Erdos714LabelledSums.graph ν Equiv.addLeft).Copy
      (Erdos714LabelledSums.graph μ leftPerm) :=
  Erdos714LabelledSums.subfieldCopy ν Equiv.addLeft μ leftPerm f labelEmbedding
    hν label_product

/-- In particular a biclique in that compatible restriction is a biclique
in the genuine larger model, rather than only in a quotient of its labels. -/
theorem not_free_of_subfield {K E : Type*} [Field K] [Field E]
    {r s : ℕ} (ν : Kˣ → U) (μ : Eˣ → W) (f : K →+* E)
    (hν : ∀ z, μ (Units.map f.toMonoidHom z)=label (ν z))
    (hf : ¬ (completeBipartiteGraph (Fin r) (Fin s)).Free
      (Erdos714LabelledSums.graph ν Equiv.addLeft)) :
    ¬ (completeBipartiteGraph (Fin r) (Fin s)).Free
      (Erdos714LabelledSums.graph μ leftPerm) :=
  Erdos714LabelledSums.not_free_of_subfield ν Equiv.addLeft μ leftPerm f
    labelEmbedding hν label_product hf

/-- Exact degree-six instance counts, for arbitrary field labels μ. -/
theorem vertex_count {E : Type*} [Field E] [Fintype E]
    (hE : Fintype.card E=117649) :
    Fintype.card ((E × W) ⊕ (E × W))=33882912 := by
  simp only [Fintype.card_sum,Fintype.card_prod,hE,ZMod.card]

theorem edge_count {E : Type*} [Field E] [Fintype E]
    (hE : Fintype.card E=117649) (μ : Eˣ → W) :
    (Erdos714LabelledSums.graph μ leftPerm).edgeFinset.card=1993128415488 := by
  rw [Erdos714LabelledSums.edge_count,hE,ZMod.card]

end Erdos714NearfieldSixLabels
#print axioms Erdos714NearfieldSixLabels.leftPerm_apply
#print axioms Erdos714NearfieldSixLabels.noncommutative
#print axioms Erdos714NearfieldSixLabels.label_injective
#print axioms Erdos714NearfieldSixLabels.label_product
#print axioms Erdos714NearfieldSixLabels.subfieldCopy
#print axioms Erdos714NearfieldSixLabels.not_free_of_subfield
#print axioms Erdos714NearfieldSixLabels.vertex_count
#print axioms Erdos714NearfieldSixLabels.edge_count
