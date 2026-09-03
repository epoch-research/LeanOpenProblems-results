import Submission.RestrictedTupleCover

/-!
Countable tuple coordinates over a dense linear order. In a full
order-type-invariant K4-free graph, each edge has a finite comparison
witness excluding homogeneous triangles. This is an auxiliary covering
result, not a settlement of Erdős 595.
-/

set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595CountableTupleType
open Erdos595TupleType

variable {A I : Type*} [LinearOrder A]

private def modelLE {R : Type*} [LinearOrder R] (x y : I → A)
    (p q : R × I) : Prop :=
  if p.1 < q.1 then x p.2 ≤ y q.2 else
    if q.1 < p.1 then y p.2 ≤ x q.2 else x p.2 ≤ x q.2

private lemma modelLE_three (x : Fin 3 → I → A)
    (h₁ : pairType (x 0) (x 1) = pairType (x 0) (x 2))
    (h₂ : pairType (x 0) (x 1) = pairType (x 1) (x 2))
    (i j : Fin 3) (a b : I) :
    modelLE (x 0) (x 1) (i,a) (j,b) ↔ x i a ≤ x j b := by
  obtain ⟨h₁₀,h₁₁,h₁₂,h₁₃⟩ := pairType_eq_iff.mp h₁
  obtain ⟨h₂₀,h₂₁,h₂₂,h₂₃⟩ := pairType_eq_iff.mp h₂
  fin_cases i <;> fin_cases j <;> simp only [modelLE]
  · rfl
  · rfl
  · exact h₁₁ a b
  · rfl
  · exact h₂₀ a b
  · exact h₂₁ a b
  · exact h₁₂ a b
  · exact h₂₂ a b
  · exact (h₂₀ a b).trans (h₂₃ a b)

/-- Any three elements of a linear order have the same comparison pattern
as a triple in `Fin 3`, with repetitions retained. -/
private lemma compress_three {R : Type*} [LinearOrder R] (v : Fin 3 → R) :
    ∃ f : Fin 3 → Fin 3, ∀ i j, (f i < f j ↔ v i < v j) := by
  classical
  let S : Finset R := Finset.univ.image v
  have hc : S.card ≤ 3 := (Finset.card_image_le).trans (by simp)
  let e : S ↪o Fin 3 := (S.orderIsoOfFin rfl).symm.toOrderEmbedding.trans
    (Fin.castLEOrderEmb hc)
  let f : Fin 3 → Fin 3 := fun i => e ⟨v i, by simp [S]⟩
  exact ⟨f, fun i j => e.lt_iff_lt⟩

private lemma modelLE_transfer {R T : Type*} [LinearOrder R] [LinearOrder T]
    (x y : I → A) {r s : R} {u v : T} (h₁ : r < s ↔ u < v)
    (h₂ : s < r ↔ v < u) (a b : I) :
    modelLE x y (r,a) (s,b) ↔ modelLE x y (u,a) (v,b) := by
  simp only [modelLE, h₁, h₂]

private lemma modelLE_trans {R : Type*} [LinearOrder R]
    (x : Fin 3 → I → A)
    (h₁ : pairType (x 0) (x 1) = pairType (x 0) (x 2))
    (h₂ : pairType (x 0) (x 1) = pairType (x 1) (x 2)) :
    Transitive (modelLE (R := R) (x 0) (x 1)) := by
  intro p q r hpq hqr
  let v : Fin 3 → R := ![p.1,q.1,r.1]
  obtain ⟨f, hf⟩ := compress_three v
  have ht (i j : Fin 3) (a b : I) :
      modelLE (x 0) (x 1) (v i,a) (v j,b) ↔ x (f i) a ≤ x (f j) b :=
    (modelLE_transfer (x 0) (x 1) (hf i j).symm (hf j i).symm a b).trans
      (modelLE_three x h₁ h₂ (f i) (f j) a b)
  exact (ht 0 2 p.2 r.2).mpr
    (((ht 0 1 p.2 q.2).mp hpq).trans ((ht 1 2 q.2 r.2).mp hqr))


private lemma modelLE_congr {R : Type*} [LinearOrder R]
    {x y z w : I → A} (h : pairType x y = pairType z w) (p q : R × I) :
    modelLE x y p q ↔ modelLE z w p q := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := pairType_eq_iff.mp h
  unfold modelLE
  split_ifs <;> first | exact h₀ _ _ | exact h₁ _ _ | exact h₂ _ _

private lemma realize_countable_preorder {P : Type*} [Countable P]
    [DenselyOrdered A] [Nontrivial A]
    (R : P → P → Prop) (hr : Reflexive R) (ht : Transitive R)
    (hc : ∀ a b, R a b ∨ R b a) :
    ∃ f : P → A, ∀ a b, (R a b ↔ f a ≤ f b) := by
  classical
  letI : Preorder P := { le := R, le_refl := hr, le_trans := fun _ _ _ h h' => ht h h' }
  letI : Std.Total (α := P) (· ≤ ·) := ⟨hc⟩
  let Q := Antisymmetrization P (· ≤ ·)
  haveI : Countable Q := inferInstanceAs (Countable (Quotient _))
  obtain ⟨e⟩ := Order.embedding_from_countable_to_dense (α := Q) (β := A)
  refine ⟨fun a => e (toAntisymmetrization (· ≤ ·) a),fun a b => ?_⟩
  exact (e.le_iff_le.trans toAntisymmetrization_le_toAntisymmetrization_iff).symm

/-- A pair type is homogeneous on three tuples in the ambient order. -/
def RealizesThree (x y : I → A) : Prop :=
  ∃ z : Fin 3 → I → A,
    pairType (z 0) (z 1) = pairType x y ∧
    pairType (z 0) (z 2) = pairType x y ∧
    pairType (z 1) (z 2) = pairType x y

private lemma internal_of_three {x y : I → A} (h : RealizesThree x y) (i j : I) :
    (x i ≤ x j ↔ y i ≤ y j) := by
  obtain ⟨z,h₀,h₁,h₂⟩ := h
  have ha := (pairType_eq_iff.mp h₀).2.2.2 i j
  have hb := (pairType_eq_iff.mp h₂).1 i j
  exact hb.symm.trans ha

private lemma trans_of_three {R : Type*} [LinearOrder R]
    {x y : I → A} (h : RealizesThree x y) :
    Transitive (modelLE (R := R) x y) := by
  obtain ⟨z,h₀,h₁,h₂⟩ := h
  have ht := modelLE_trans (R := R) z (h₀.trans h₁.symm) (h₀.trans h₂.symm)
  intro p q r hpq hqr
  exact (modelLE_congr h₀ p r).mp
    (ht ((modelLE_congr h₀ p q).mpr hpq) ((modelLE_congr h₀ q r).mpr hqr))

private theorem four_of_tests_with_realizer
    (x y : I → A) (htest : ∀ k : Fin 3 → I, RealizesThree (x ∘ k) (y ∘ k))
    (hreal : Reflexive (modelLE (R := Fin 4) x y) →
      Transitive (modelLE (R := Fin 4) x y) →
      (∀ p q : Fin 4 × I, modelLE x y p q ∨ modelLE x y q p) →
      ∃ f : Fin 4 × I → A, ∀ p q, modelLE x y p q ↔ f p ≤ f q) :
    ∃ z : Fin 4 → I → A, ∀ i j, i < j → pairType (z i) (z j) = pairType x y := by
  classical
  have hi (i j : I) : (x i ≤ x j ↔ y i ≤ y j) :=
    internal_of_three (htest ![i,j,i]) 0 1
  have ht : Transitive (modelLE (R := Fin 4) x y) := by
    intro p q r hpq hqr
    let k : Fin 3 → I := ![p.2,q.2,r.2]
    have h := trans_of_three (R := Fin 4) (htest k)
    have h₁ : modelLE (x ∘ k) (y ∘ k) (p.1,0) (q.1,1) := by
      simpa only [modelLE,Function.comp_apply,k,Matrix.cons_val_zero,
        Matrix.cons_val_one] using hpq
    have h₂ : modelLE (x ∘ k) (y ∘ k) (q.1,1) (r.1,2) := by
      simpa only [modelLE,Function.comp_apply,k,Matrix.cons_val_one,
        Matrix.cons_val_two] using hqr
    simpa only [modelLE,Function.comp_apply,k,Matrix.cons_val_zero,
      Matrix.cons_val_two] using h h₁ h₂
  have hr : Reflexive (modelLE (R := Fin 4) x y) := by
    intro p
    simp [modelLE]
  have hc : ∀ p q : Fin 4 × I, modelLE x y p q ∨ modelLE x y q p := by
    intro p q
    by_cases h : p.1 < q.1
    · simp only [modelLE,h,not_lt_of_gt h,↓reduceIte]
      exact le_total _ _
    · by_cases h' : q.1 < p.1
      · simp only [modelLE,h,h',↓reduceIte]
        exact le_total _ _
      · simp only [modelLE,h,h',↓reduceIte]
        exact le_total _ _
  obtain ⟨f,hf⟩ := hreal hr ht hc
  refine ⟨fun i a => f (i,a),fun i j hij => ?_⟩
  apply pairType_eq_iff.mpr
  refine ⟨?_,?_,?_,?_⟩
  · intro a b
    simpa only [modelLE,lt_self_iff_false,↓reduceIte] using (hf (i,a) (i,b)).symm
  · intro a b
    simpa only [modelLE,hij,not_lt_of_gt hij,↓reduceIte] using (hf (i,a) (j,b)).symm
  · intro a b
    simpa only [modelLE,hij,not_lt_of_gt hij,↓reduceIte] using (hf (j,a) (i,b)).symm
  · intro a b
    have he : f (j,a) ≤ f (j,b) ↔ x a ≤ x b := by
      simpa only [modelLE,lt_self_iff_false,↓reduceIte] using (hf (j,a) (j,b)).symm
    exact he.trans (hi a b)

/-- Three-coordinate tests suffice for the consistency of the complete pair type.
The realization step uses countability and density of the ambient order. -/
theorem four_of_all_three_tests [Countable I] [DenselyOrdered A] [Nontrivial A]
    (x y : I → A) (htest : ∀ k : Fin 3 → I, RealizesThree (x ∘ k) (y ∘ k)) :
    ∃ z : Fin 4 → I → A, ∀ i j, i < j → pairType (z i) (z j) = pairType x y :=
  four_of_tests_with_realizer x y htest (realize_countable_preorder (A := A) _)

/-- Every edge has a finite, three-coordinate obstruction to a homogeneous
triangle. No finite-prefix locality of the adjacency relation is assumed. -/
theorem finite_witness [Countable I] [DenselyOrdered A] [Nontrivial A]
    (G : SimpleGraph (I → A)) (hG : G.CliqueFree 4) (hInv : OrderTypeInvariant G)
    {x y : I → A} (hxy : G.Adj x y) :
    ∃ k : Fin 3 → I, ¬RealizesThree (x ∘ k) (y ∘ k) := by
  classical
  by_contra hn
  push_neg at hn
  obtain ⟨z,hz⟩ := four_of_all_three_tests x y hn
  have ha (i j : Fin 4) (hij : i < j) : G.Adj (z i) (z j) :=
    hInv _ _ _ _ (hz i j hij).symm hxy
  exact Erdos595Work.no_adj_common_neighbors hG
    (ha 0 1 (by decide)) (ha 0 2 (by decide)) (ha 1 2 (by decide))
    (ha 0 3 (by decide)) (ha 1 3 (by decide)) (ha 2 3 (by decide))

/-- A countable palette of finite comparison data. -/
abbrev Pattern (I : Type*) :=
  (Fin 3 → I) × ((Bool × Fin 3) → (Bool × Fin 3) → Prop)

/-- Finite comparison witnesses give a countable edge cover. -/
theorem countable_cover_of_finite_witness [Countable I]
    (G : SimpleGraph (I → A))
    (hW : ∀ {x y : I → A}, G.Adj x y →
      ∃ k : Fin 3 → I, ¬RealizesThree (x ∘ k) (y ∘ k)) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  classical
  let code : (I → A) → (I → A) → Option (Pattern I) := fun x y =>
    if h : G.Adj x y then
      let k := (hW h).choose
      some (k,pairType (x ∘ k) (y ∘ k))
    else none
  have spec {x y : I → A} (h : G.Adj x y) :
      ∃ k : Fin 3 → I,
        code x y = some (k,pairType (x ∘ k) (y ∘ k)) ∧
        ¬RealizesThree (x ∘ k) (y ∘ k) := by
    exact ⟨(hW h).choose,by simp only [code,dif_pos h],
      (hW h).choose_spec⟩
  letI : LinearOrder (I → A) := IsWellOrder.linearOrder WellOrderingRel
  apply Erdos595NegativeInner.cover_of_ordered_patterns G code
  intro a b c _ _ hab hac hbc he
  obtain ⟨k,hk,hbad⟩ := spec hab
  obtain ⟨l,hl,_⟩ := spec hac
  obtain ⟨m,hm,_⟩ := spec hbc
  have h₁ := Option.some.inj (hk.symm.trans (he.1.trans hl))
  have h₂ := Option.some.inj (hk.symm.trans (he.2.trans hm))
  have hkl := congrArg Prod.fst h₁
  have hkm := congrArg Prod.fst h₂
  dsimp only at hkl hkm
  subst l
  subst m
  apply hbad
  refine ⟨![a ∘ k,b ∘ k,c ∘ k],rfl,?_,?_⟩
  · exact (congrArg Prod.snd h₁).symm
  · exact (congrArg Prod.snd h₂).symm

/-- Countably many tuple coordinates are allowed. The ambient order may
have arbitrary cardinality; density supplies realizations of countable orders. -/
theorem countable_cover [Countable I] [DenselyOrdered A] [Nontrivial A]
    (G : SimpleGraph (I → A)) (hG : G.CliqueFree 4) (hInv : OrderTypeInvariant G) :
    Erdos595Work.IsCountableUnionOfTriangleFree G :=
  countable_cover_of_finite_witness G (finite_witness G hG hInv)

private lemma realize_wellorder_model [Countable I] [Uncountable A] [WellFoundedLT A]
    (x y : I → A) (hr : Reflexive (modelLE (R := Fin 4) x y))
    (ht : Transitive (modelLE (R := Fin 4) x y))
    (hc : ∀ p q : Fin 4 × I, modelLE x y p q ∨ modelLE x y q p) :
    ∃ f : Fin 4 × I → A, ∀ p q, modelLE x y p q ↔ f p ≤ f q := by
  classical
  let P := Fin 4 × I
  let R : P → P → Prop := modelLE x y
  letI : Preorder P := { le := R, le_refl := hr, le_trans := fun _ _ _ h h' => ht h h' }
  letI : Std.Total (α := P) (· ≤ ·) := ⟨hc⟩
  let Q := Antisymmetrization P (· ≤ ·)
  haveI : Countable Q := inferInstanceAs (Countable (Quotient _))
  let q : P → Q := toAntisymmetrization (· ≤ ·)
  let S : Fin 4 → Set Q := fun i => Set.range (fun j : I => q (i,j))
  have hs (i : Fin 4) : (S i).IsWF := by
    choose j hj using fun z : S i => z.property
    dsimp only at hj
    let f : S i → A := fun z => x (j z)
    have hf : StrictMono f := by
      intro z w hzw
      have hh : q (i,j z) < q (i,j w) := by rw [hj z,hj w]; exact hzw
      have hh' := toAntisymmetrization_lt_toAntisymmetrization_iff.mp hh
      change R (i,j z) (i,j w) ∧ ¬R (i,j w) (i,j z) at hh'
      simpa only [R,modelLE,lt_self_iff_false,↓reduceIte,← lt_iff_le_not_ge] using hh'
    exact (InvImage.wf f wellFounded_lt).mono (fun _ _ h => hf h)
  have hcover : (⋃ i ∈ (Finset.univ : Finset (Fin 4)), S i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨p,rfl⟩ := Quotient.mk_surjective z
    exact Set.mem_iUnion.mpr ⟨p.1,Set.mem_iUnion.mpr ⟨Finset.mem_univ _,⟨p.2,rfl⟩⟩⟩
  have hwhole : (Set.univ : Set Q).IsWF := by
    rw [← hcover]
    exact Finset.isWF_bUnion _ |>.mpr (fun i _ => hs i)
  letI : WellFoundedLT Q := Set.isWF_univ_iff.mp hwhole
  have he : Nonempty (Q ↪o A) := by
    cases InitialSeg.total ((· < ·) : Q → Q → Prop) ((· < ·) : A → A → Prop) with
    | inl e => exact ⟨e.toRelEmbedding.orderEmbeddingOfLTEmbedding⟩
    | inr e =>
      have hca : Countable A := Function.Injective.countable e.injective
      exact (not_countable (α := A) hca).elim
  obtain ⟨e⟩ := he
  refine ⟨fun p => e (q p),fun p r => ?_⟩
  exact (e.le_iff_le.trans toAntisymmetrization_le_toAntisymmetrization_iff).symm

/-- The same finite comparison test works over every uncountable well order. -/
theorem four_of_all_three_tests_wellorder [Countable I] [Uncountable A] [WellFoundedLT A]
    (x y : I → A) (htest : ∀ k : Fin 3 → I, RealizesThree (x ∘ k) (y ∘ k)) :
    ∃ z : Fin 4 → I → A, ∀ i j, i < j → pairType (z i) (z j) = pairType x y :=
  four_of_tests_with_realizer x y htest (realize_wellorder_model x y)

/-- Finite witnesses do not require density when the ambient order is an
uncountable well order. -/
theorem finite_witness_wellorder [Countable I] [Uncountable A] [WellFoundedLT A]
    (G : SimpleGraph (I → A)) (hG : G.CliqueFree 4) (hInv : OrderTypeInvariant G)
    {x y : I → A} (hxy : G.Adj x y) :
    ∃ k : Fin 3 → I, ¬RealizesThree (x ∘ k) (y ∘ k) := by
  classical
  by_contra hn
  push_neg at hn
  obtain ⟨z,hz⟩ := four_of_all_three_tests_wellorder x y hn
  have ha (i j : Fin 4) (hij : i < j) : G.Adj (z i) (z j) :=
    hInv _ _ _ _ (hz i j hij).symm hxy
  exact Erdos595Work.no_adj_common_neighbors hG
    (ha 0 1 (by decide)) (ha 0 2 (by decide)) (ha 1 2 (by decide))
    (ha 0 3 (by decide)) (ha 1 3 (by decide)) (ha 2 3 (by decide))

/-- Full order-type-invariant K4-free graphs on countable tuples over an
uncountable well order admit countable triangle-free edge covers. -/
theorem countable_cover_wellorder [Countable I] [Uncountable A] [WellFoundedLT A]
    (G : SimpleGraph (I → A)) (hG : G.CliqueFree 4) (hInv : OrderTypeInvariant G) :
    Erdos595Work.IsCountableUnionOfTriangleFree G :=
  countable_cover_of_finite_witness G (finite_witness_wellorder G hG hInv)

#print axioms countable_cover_wellorder

#print axioms four_of_all_three_tests
#print axioms finite_witness
#print axioms countable_cover
end Erdos595CountableTupleType
