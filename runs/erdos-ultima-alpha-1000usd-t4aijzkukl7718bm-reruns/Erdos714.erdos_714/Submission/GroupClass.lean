import FormalConjecturesUtil

/-!
A uniform biclique obstruction for an SL(3) conjugacy-class graph candidate.
This does not settle the balanced Zarankiewicz conjecture.
-/

open SimpleGraph Matrix
open scoped MatrixGroups

namespace Erdos714ClassGraph

variable {Γ : Type*} [Group Γ]

/-- Two copies of a group, joined when the relative element is conjugate to `a`. -/
def graph (a : Γ) : SimpleGraph (Γ ⊕ Γ) where
  Adj x y := match x,y with
    | .inl g, .inr h => ∃ k : Γ, g⁻¹*h = k*a*k⁻¹
    | .inr h, .inl g => ∃ k : Γ, g⁻¹*h = k*a*k⁻¹
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> simp_all
  loopless := by intro x; cases x <;> simp

/-- A matrix identity without inverses is sufficient to certify every edge of a biclique. -/
theorem not_free_of_intertwining (a : Γ) {r : ℕ} (L R : Fin r ↪ Γ)
    (K : Fin r → Fin r → Γ)
    (h : ∀ i j, L i * K i j * a = R j * K i j) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free (graph a) := by
  have hadj (i j : Fin r) : (graph a).Adj (.inl (L i)) (.inr (R j)) := by
    refine ⟨K i j, ?_⟩
    have he := congrArg (fun z : Γ => (L i)⁻¹ * z * (K i j)⁻¹) (h i j)
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using he.symm
  intro hfree
  apply hfree
  refine ⟨⟨⟨L.sumMap R, ?_⟩, (L.sumMap R).injective⟩⟩
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j => simp at hxy
    | inr j => exact hadj i j
  | inr i =>
    cases y with
    | inl j => exact (hadj j i).symm
    | inr j => simp at hxy

/-- Simultaneously translating both sides preserves all relative elements. -/
theorem translated_intertwining (a p : Γ) {X Y : Type*}
    (L : X → Γ) (R : Y → Γ) (K : X → Y → Γ)
    (h : ∀ x y, L x * K x y * a = R y * K x y) :
    ∀ x y, (p*L x) * K x y * a = (p*R y) * K x y := by
  intro x y
  simpa only [mul_assoc] using congrArg (fun z : Γ => p*z) (h x y)

end Erdos714ClassGraph

namespace Erdos714SL3Class

variable {F : Type*} [CommRing F]

/-- A determinant-one companion matrix; its characteristic polynomial is
`X^3-a*X^2+b*X-1`. No reducibility assumption is used in the obstruction. -/
def center (a b : F) : SL(3,F) :=
  ⟨!![0,0,1; 1,0,-b; 0,1,a], by simp [Matrix.det_fin_three]⟩

/-- The left side of the universal grid. -/
def left (x : F) : SL(3,F) :=
  ⟨!![1,0,-x; x,1,-x^2; 0,0,1], by simp [Matrix.det_fin_three]⟩

/-- The right side is a unipotent conjugation of the companion matrix. -/
def right (a b s : F) : SL(3,F) :=
  ⟨!![0,0,1; 1,s,-b+a*s-s^2; 0,1,a-s], by simp [Matrix.det_fin_three]⟩

def conjugator (x s : F) : SL(3,F) :=
  ⟨!![1,0,x; 0,1,s; 0,0,1], by simp [Matrix.det_fin_three]⟩

/-- Every cross pair has exactly the prescribed conjugacy class. -/
theorem intertwining (a b x s : F) :
    left x * conjugator x s * center a b = right a b s * conjugator x s := by
  apply Subtype.ext
  change ((left x : Matrix (Fin 3) (Fin 3) F) * conjugator x s) * center a b =
    (right a b s : Matrix (Fin 3) (Fin 3) F) * conjugator x s
  simp only [left, right, conjugator, center, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

lemma left_injective : Function.Injective (left : F → SL(3,F)) := by
  intro x y h
  have he := congrArg (fun g : SL(3,F) => g 1 0) h
  exact he

lemma right_injective (a b : F) : Function.Injective (right a b) := by
  intro x y h
  have he := congrArg (fun g : SL(3,F) => g 1 1) h
  exact he

/-- A grid of any size at most the field cardinality occurs in the class graph. -/
theorem not_free (a b : F) {r : ℕ} (e : Fin r ↪ F) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free
      (Erdos714ClassGraph.graph (center a b)) := by
  let L : Fin r ↪ SL(3,F) := e.trans ⟨left, left_injective⟩
  let R : Fin r ↪ SL(3,F) := e.trans ⟨right a b, right_injective a b⟩
  apply Erdos714ClassGraph.not_free_of_intertwining (center a b) L R
    (fun i j => conjugator (e i) (e j))
  intro i j
  exact intertwining a b (e i) (e j)

/-- In particular, no irreducible companion class can rescue this SL(3) candidate
once the coefficient field has at least four elements. -/
theorem not_free_four [Fintype F] (a b : F) (hq : 4 ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714ClassGraph.graph (center a b)) := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := F) (by simpa using hq)
  exact not_free a b e

end Erdos714SL3Class

#print axioms Erdos714ClassGraph.not_free_of_intertwining
#print axioms Erdos714SL3Class.intertwining
#print axioms Erdos714SL3Class.not_free_four
