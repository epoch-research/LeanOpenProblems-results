import Submission.ShiftBicliqueTransport
import Submission.ArcShiftCertificateChunked

/-!
Covering criteria for the finite-parameter model of the shift-square right
adjoint. This is auxiliary work, not a solution of Erdős 595.
-/

set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595ShiftCover
open Erdos595MiddleCorner Erdos595ArcAdjoint Erdos595FiniteBiclique
open Erdos595ShiftTransport Erdos595TupleType

variable {A I : Type*} [LinearOrder A]

def Valid (x : I × Fin 3 → A) : Prop :=
  ∀ i, x (i,0) < x (i,1) ∧ x (i,1) < x (i,2)

def decode (x : I × Fin 3 → A) (h : Valid x) : I → Triple A :=
  fun i => ⟨x (i,0),x (i,1),x (i,2),(h i).1,(h i).2⟩

lemma encode_decode (x : I × Fin 3 → A) (h : Valid x) : encode (decode x h) = x := by
  funext p
  obtain ⟨i,j⟩ := p
  fin_cases j <;> rfl

lemma valid_encode (x : I → Triple A) : Valid (encode x) :=
  fun i => ⟨(x i).ab,(x i).bc⟩

lemma decode_encode (x : I → Triple A) : decode (encode x) (valid_encode x) = x := by
  funext i
  rfl

lemma familyAdj_iff_right (x y : I → Triple A) :
    (right (graph A)).Adj (completion (graph A) (range x))
      (completion (graph A) (range y)) ↔ familyAdj x y := by
  simp [right, completion, common, familyAdj, familyCommon, familyDouble, Set.Nonempty]

def codeGraph (I A : Type*) [LinearOrder A] : SimpleGraph (I × Fin 3 → A) where
  Adj x y := ∃ hx : Valid x, ∃ hy : Valid y, familyAdj (decode x hx) (decode y hy)
  symm := by
    rintro x y ⟨hx,hy,h⟩
    exact ⟨hy,hx,h.symm⟩
  loopless := by
    rintro x ⟨hx,hx',h⟩
    obtain ⟨v,hv,hv'⟩ := h.1
    exact (graph A).loopless v (hv v hv')

noncomputable def codeToRight : codeGraph I A →g right (graph A) := by
  classical
  refine { toFun := fun x => completion (graph A) (if h : Valid x then range (decode x h) else ∅)
           map_rel' := ?_ }
  rintro x y ⟨hx,hy,h⟩
  rw [dif_pos hx,dif_pos hy]
  exact (familyAdj_iff_right _ _).mpr h

lemma cliqueFree_four_of_hom {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hH : H.CliqueFree 4) : G.CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have h (i j : Fin 4) (hij : i ≠ j) : H.Adj (f (e i)) (f (e j)) :=
    f.map_adj (e.map_rel_iff.mpr hij)
  exact Erdos595Work.no_adj_common_neighbors hH
    (h 0 1 (by decide)) (h 0 2 (by decide)) (h 1 2 (by decide))
    (h 0 3 (by decide)) (h 1 3 (by decide)) (h 2 3 (by decide))

lemma codeGraph_cliqueFree : (codeGraph I A).CliqueFree 4 :=
  cliqueFree_four_of_hom codeToRight (Erdos595ArcShift.right_shift_cliqueFree A)

section Dense
variable [DenselyOrdered A] [NoMinOrder A] [NoMaxOrder A] [Nonempty A] [Finite I]

lemma codeGraph_invariant : OrderTypeInvariant (codeGraph I A) := by
  intro x y z w htype hxy
  obtain ⟨hx,hy,hxy⟩ := hxy
  obtain ⟨h₀,h₁,h₂,h₃⟩ := pairType_eq_iff.mp htype
  have hz : Valid z := by
    intro i
    constructor
    · simpa only [lt_iff_le_not_ge, ← h₀] using (hx i).1
    · simpa only [lt_iff_le_not_ge, ← h₀] using (hx i).2
  have hw : Valid w := by
    intro i
    constructor
    · simpa only [lt_iff_le_not_ge, ← h₃] using (hy i).1
    · simpa only [lt_iff_le_not_ge, ← h₃] using (hy i).2
  refine ⟨hz,hw,?_⟩
  apply (familyAdj_of_pairType (x := decode x hx) (z := decode y hy)
    (y := decode z hz) (w := decode w hw) ?_).mp hxy
  intro p q
  simp only [encode_decode]
  exact congrFun (congrFun htype p) q |>.to_iff

/-- Every fixed finite family-parameter piece of the right-adjoint
candidate has a countable triangle-free cover. -/
theorem codeGraph_cover : Erdos595Work.IsCountableUnionOfTriangleFree (codeGraph I A) := by
  haveI : Infinite A := NoMaxOrder.infinite
  exact countable_cover _ codeGraph_cliqueFree codeGraph_invariant

private noncomputable def enumerate {V : Type*} (S : Finset V) {n : ℕ}
    (h : S.card = n) : Fin n → V := fun i => (Finset.equivFinOfCardEq h).symm i

private lemma range_enumerate {V : Type*} (S : Finset V) {n : ℕ} (h : S.card = n) :
    range (enumerate S h) = S := by
  ext v
  constructor
  · rintro ⟨i,rfl⟩
    exact ((Finset.equivFinOfCardEq h).symm i).2
  · intro hv
    exact ⟨Finset.equivFinOfCardEq h ⟨v,hv⟩, by simp [enumerate]⟩

/-- Combining the finite-parameter-size pieces gives a cover of the full
finite-subset model. -/
theorem finiteRight_cover :
    Erdos595Work.IsCountableUnionOfTriangleFree (finiteRight (graph A)) := by
  classical
  let e : ℕ → ℕ → Fin 2 := fun n k => if n = k then 1 else 0
  have he : Function.Injective e := by
    intro n m h
    by_contra hnm
    have hh := congrFun h n
    simp [e] at hh
    exact hnm hh.symm
  let f : Finset (Triple A) → ℕ → Fin 2 := fun S => e S.card
  apply Erdos595Work.countable_union_of_vertex_pieces (finiteRight (graph A)) f
  intro i
  by_cases hi : ∃ S, f S = i
  · obtain ⟨S₀,hS₀⟩ := hi
    let n := S₀.card
    let param (S : Finset (Triple A)) : Fin n → Triple A :=
      if h : S.card = n then enumerate S h else enumerate S₀ rfl
    have hr (S : Finset (Triple A)) (h : f S = i) : range (param S) = S := by
      have hc : S.card = n := he (h.trans hS₀.symm)
      simp only [param, dif_pos hc, range_enumerate]
    let g : Erdos595Work.vertexPiece (finiteRight (graph A)) f i →g codeGraph (Fin n) A :=
      { toFun := fun S => encode (param S)
        map_rel' := by
          intro S T h
          refine ⟨valid_encode _,valid_encode _,?_⟩
          simp only [decode_encode]
          apply (familyAdj_iff_right _ _).mp
          rw [hr S h.2.1,hr T h.2.2]
          exact h.1 }
    exact Erdos595Work.countable_union_of_hom g codeGraph_cover
  · have hh : Erdos595Work.vertexPiece (finiteRight (graph A)) f i = ⊥ := by
      ext S T
      change (_ ∧ _ ∧ _) ↔ False
      exact ⟨fun h => hi ⟨S,h.2.1⟩,False.elim⟩
    rw [hh]
    exact ⟨fun _ => ⊥,fun _ => SimpleGraph.cliqueFree_bot (by omega),by simp⟩

/-- The right adjoint of the shift-square graph is countably triangle-free
coverable over every dense nonempty linear order without endpoints. -/
theorem right_shift_cover_dense :
    Erdos595Work.IsCountableUnionOfTriangleFree (right (graph A)) :=
  (cover_iff _ (Erdos595Noetherian.shift_finiteCommonNeighbors A)).mpr finiteRight_cover

end Dense

/-- Functoriality of the biclique right adjoint. -/
def rightMap {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) : right G →g right H where
  toFun p := ⟨(f '' p.1.1,f '' p.1.2),by
    rintro a ⟨x,hx,rfl⟩ b ⟨y,hy,rfl⟩
    exact f.map_adj (p.2 x hx y hy)⟩
  map_rel' := by
    intro p q hpq
    obtain ⟨a,hap,haq⟩ := hpq.1
    obtain ⟨b,hbq,hbp⟩ := hpq.2
    exact ⟨⟨f a,⟨a,hap,rfl⟩,⟨a,haq,rfl⟩⟩,
      ⟨f b,⟨b,hbq,rfl⟩,⟨b,hbp,rfl⟩⟩⟩

def shiftMap {B : Type*} [LinearOrder B] (f : A ↪o B) : graph A →g graph B where
  toFun x := ⟨f x.a,f x.b,f x.c,f.strictMono x.ab,f.strictMono x.bc⟩
  map_rel' := by
    intro x y h
    rcases h with (⟨h₁,h₂⟩ | h) | (⟨h₁,h₂⟩ | h)
    · exact Or.inl (Or.inl ⟨congrArg f h₁,congrArg f h₂⟩)
    · exact Or.inl (Or.inr (congrArg f h))
    · exact Or.inr (Or.inl ⟨congrArg f h₁,congrArg f h₂⟩)
    · exact Or.inr (Or.inr (congrArg f h))

/-- The complete right-adjoint shift-square candidate is countably
triangle-free coverable, at every cardinality and for every linear order. -/
theorem right_shift_cover (A : Type*) [LinearOrder A] :
    Erdos595Work.IsCountableUnionOfTriangleFree (right (graph A)) := by
  classical
  cases isEmpty_or_nonempty A with
  | inl h =>
    letI := h
    apply right_cover_of_rainbow (graph A) (fun _ => (0 : ℕ))
    intro a
    exact isEmptyElim a.a
  | inr h =>
    letI := h
    let D := A ×ₗ ℚ
    letI : DenselyOrdered D := ⟨by
      intro x y hxy
      rcases Prod.Lex.lt_iff.mp hxy with hxy | ⟨he,hxy⟩
      · refine ⟨toLex (x.1,x.2 + 1),?_,?_⟩
        · exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl,by change (x.2 : ℚ) < x.2 + 1; linarith⟩)
        · exact Prod.Lex.lt_iff.mpr (Or.inl hxy)
      · obtain ⟨q,hq,hq'⟩ := exists_between hxy
        exact ⟨toLex (x.1,q),Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl,hq⟩),
          Prod.Lex.lt_iff.mpr (Or.inr ⟨he,hq'⟩)⟩⟩
    letI : NoMinOrder D := ⟨fun x => ⟨toLex (x.1,x.2-1),
      Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl,by change (x.2 : ℚ) - 1 < x.2; linarith⟩)⟩⟩
    letI : NoMaxOrder D := ⟨fun x => ⟨toLex (x.1,x.2+1),
      Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl,by change (x.2 : ℚ) < x.2 + 1; linarith⟩)⟩⟩
    let e : A ↪o D := OrderEmbedding.ofStrictMono (fun a => toLex (a,0))
      (fun _ _ h => Prod.Lex.lt_iff.mpr (Or.inl h))
    exact Erdos595Work.countable_union_of_hom (rightMap (shiftMap e)) right_shift_cover_dense

#print axioms right_shift_cover
#print axioms finiteRight_cover
#print axioms right_shift_cover_dense
#print axioms familyAdj_iff_right
#print axioms codeGraph_cliqueFree
#print axioms codeGraph_invariant
#print axioms codeGraph_cover
end Erdos595ShiftCover
