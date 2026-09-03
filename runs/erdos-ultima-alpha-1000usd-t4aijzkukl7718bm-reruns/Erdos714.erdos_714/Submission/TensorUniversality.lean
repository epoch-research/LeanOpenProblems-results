import Submission.TensorObstruction
import Submission.AffineThreeSeed

/-!
Unrestricted sparse vertex selections in tensor powers of the affine-three seed
can realize every bipartite graph. The embedding preserves nonedges too. Its
depth is the sum of the two part sizes, not logarithmic in their sizes, and it
provides no new lower bound for the input graph's edge count. Thus unrestricted
sparse tensor selection is a reformulation, not by itself an amplification.
-/

noncomputable section
open Classical SimpleGraph Erdos714Tensor
set_option maxHeartbeats 1000000

namespace Erdos714TensorUniversality

variable {A B X Y K : Type*}

/-- A three-edge, one-nonedge rectangular pattern in the seed relation. -/
structure Frame (S : A → B → Prop) where
  a₀ : A
  a₁ : A
  b₀ : B
  b₁ : B
  h₀₀ : S a₀ b₀
  h₀₁ : S a₀ b₁
  h₁₀ : S a₁ b₀
  h₁₁ : ¬ S a₁ b₁

variable {S : A → B → Prop} (P : Frame S) (R : X → Y → Prop)

lemma Frame.left_ne : P.a₁ ≠ P.a₀ := fun h => P.h₁₁ (h.symm ▸ P.h₀₁)
lemma Frame.right_ne : P.b₁ ≠ P.b₀ := fun h => P.h₁₁ (h.symm ▸ P.h₁₀)

/-- The row's own coordinate is distinguished; extra column coordinates are harmless. -/
def rowWord (x : X) : X ⊕ Y → A
  | .inl i => if x = i then P.a₁ else P.a₀
  | .inr _ => P.a₀

/-- The first coordinates encode the input relation, and the second ensure injectivity. -/
def colWord (y : Y) : X ⊕ Y → B
  | .inl i => if R i y then P.b₀ else P.b₁
  | .inr j => if y = j then P.b₁ else P.b₀

lemma rowWord_injective : Function.Injective (rowWord (X := X) (Y := Y) P) := by
  intro x x' h
  by_contra hne
  have he := congrFun h (.inl x)
  simp [rowWord, Ne.symm hne] at he
  exact P.left_ne he

lemma colWord_injective : Function.Injective (colWord P R) := by
  intro y y' h
  by_contra hne
  have he := congrFun h (.inr y)
  simp [colWord, Ne.symm hne] at he
  exact P.right_ne he

/-- Exact recovery of both edges and nonedges from the coordinatewise seed relation. -/
theorem relation_iff (x : X) (y : Y) :
    (∀ i, S (rowWord P x i) (colWord P R y i)) ↔ R x y := by
  constructor
  · intro h
    by_contra hn
    exact P.h₁₁ (by simpa [rowWord, colWord, hn] using h (.inl x))
  · intro h i
    cases i with
    | inl j =>
      by_cases hx : x = j
      · subst j
        simpa [rowWord, colWord, h] using P.h₁₀
      · by_cases hj : R j y
        · simpa [rowWord, colWord, hx, hj] using P.h₀₀
        · simpa [rowWord, colWord, hx, hj] using P.h₀₁
    | inr j =>
      by_cases hy : y = j
      · simpa [rowWord, colWord, hy] using P.h₀₁
      · simpa [rowWord, colWord, hy] using P.h₀₀

/-- Tensor graphs with an arbitrary coordinate type. -/
def powerGraph (S : A → B → Prop) (K : Type*) : SimpleGraph ((K → A) ⊕ (K → B)) :=
  incidence fun x y => ∀ i, S (x i) (y i)

/-- Every bipartite relation embeds as an induced subgraph of such a tensor graph. -/
def embedding : incidence R ↪g powerGraph S (X ⊕ Y) where
  toFun := Sum.map (rowWord P) (colWord P R)
  inj' := Sum.map_injective.mpr ⟨rowWord_injective P, colWord_injective P R⟩
  map_rel_iff' := by
    intro x y
    cases x <;> cases y
    · rfl
    · exact relation_iff P R _ _
    · exact relation_iff P R _ _
    · rfl

/-- Reindexing coordinates leaves the tensor graph unchanged up to isomorphism. -/
def reindex {L : Type*} (e : K ≃ L) : powerGraph S K ≃g powerGraph S L where
  toEquiv := Equiv.sumCongr (Equiv.arrowCongr e (Equiv.refl A))
    (Equiv.arrowCongr e (Equiv.refl B))
  map_rel_iff' := by
    intro x y
    cases x <;> cases y
    · rfl
    · rename_i f g
      exact (e.symm.surjective.forall (p := fun k => S (f k) (g k))).symm
    · rename_i g f
      exact (e.symm.surjective.forall (p := fun k => S (f k) (g k))).symm
    · rfl

/-- For finite graphs the depth is explicitly the number of input vertices. -/
def finiteEmbedding [Fintype X] [Fintype Y] :
    incidence R ↪g powerGraph S (Fin (Fintype.card (X ⊕ Y))) :=
  (reindex (S := S) (Fintype.equivFin (X ⊕ Y))).toEmbedding.comp (embedding P R)

abbrev TernaryPoint := Erdos714AffineThree.Point (ZMod 3)

/-- The bipartite relation underlying the checked finite affine-three seed. -/
def affineRelation (u v : TernaryPoint) : Prop := u.2 + v.2 = u.1 ⬝ᵥ v.1

/-- Only zero constants and the first coordinate axis are needed for universality. -/
def affineFrame : Frame affineRelation where
  a₀ := (0, 0)
  a₁ := (![1, 0, 0], 0)
  b₀ := (0, 0)
  b₁ := (![1, 0, 0], 0)
  h₀₀ := by simp [affineRelation]
  h₀₁ := by simp [affineRelation]
  h₁₀ := by simp [affineRelation]
  h₁₁ := by simp [affineRelation, dotProduct, Fin.sum_univ_succ]

/-- The universality statement uses the fixed 81-symbol alphabet on each part. -/
def affineEmbedding [Fintype X] [Fintype Y] (R : X → Y → Prop) :
    incidence R ↪g powerGraph affineRelation (Fin (Fintype.card (X ⊕ Y))) :=
  finiteEmbedding affineFrame R

/-- This representation is very sparse; it does not keep a positive ambient fraction. -/
theorem ambient_card (k : ℕ) :
    Fintype.card ((Fin k → TernaryPoint) ⊕ (Fin k → TernaryPoint)) = 2 * 81^k := by
  simp [TernaryPoint, Erdos714AffineThree.Point, two_mul]

end Erdos714TensorUniversality

#print axioms Erdos714TensorUniversality.relation_iff
#print axioms Erdos714TensorUniversality.embedding
#print axioms Erdos714TensorUniversality.finiteEmbedding
#print axioms Erdos714TensorUniversality.affineEmbedding
#print axioms Erdos714TensorUniversality.ambient_card
