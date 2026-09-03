import Submission.FiniteFolkmanAmalgamation

/-! Finite-palette triangle partite lemma. This is auxiliary work on Erdős 595. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595FiniteTrianglePartite

variable {A J : Type*}

def IsTriangle (H : SimpleGraph A) (x : Fin 3 → A) : Prop :=
  ∀ i j, i ≠ j → H.Adj (x i) (x j)

abbrev Triangle (H : SimpleGraph A) (π : A → Fin 3) :=
  {x : Fin 3 → A // (∀ i, π (x i) = i) ∧ IsTriangle H x}

def productGraph (H : SimpleGraph A) [Nonempty J] : SimpleGraph (J → A) where
  Adj f g := ∀ j, H.Adj (f j) (g j)
  symm := fun _ _ h j => (h j).symm
  loopless := fun f h => H.loopless _ (h (Classical.arbitrary J))

noncomputable def lineMap (H : SimpleGraph A) (π : A → Fin 3)
    (l : Combinatorics.Line (Triangle H π) J) (a : A) (j : J) : A :=
  match l.idxFun j with
  | none => a
  | some x => x.val (π a)

lemma lineMap_none (H : SimpleGraph A) (π : A → Fin 3)
    (l : Combinatorics.Line (Triangle H π) J) (a : A) {j : J}
    (hj : l.idxFun j = none) : lineMap H π l a j = a := by simp [lineMap,hj]

lemma lineMap_part (H : SimpleGraph A) (π : A → Fin 3)
    (l : Combinatorics.Line (Triangle H π) J) (a : A) (j : J) :
    π (lineMap H π l a j) = π a := by
  cases hj : l.idxFun j with
  | none => simp [lineMap,hj]
  | some x => simpa [lineMap,hj] using x.property.1 (π a)

lemma lineMap_rel (H : SimpleGraph A) (π : A → Fin 3)
    (hπ : ∀ a b, H.Adj a b → π a ≠ π b) [Nonempty J]
    (l : Combinatorics.Line (Triangle H π) J) (a b : A) :
    (productGraph H).Adj (lineMap H π l a) (lineMap H π l b) ↔ H.Adj a b := by
  constructor
  · intro h
    obtain ⟨j,hj⟩ := l.proper
    simpa [lineMap,hj] using h j
  · intro h j
    cases hj : l.idxFun j with
    | none => simpa [lineMap,hj] using h
    | some x => simpa [lineMap,hj] using x.property.2 (π a) (π b) (hπ a b h)

noncomputable def lineEmbedding (H : SimpleGraph A) (π : A → Fin 3)
    (hπ : ∀ a b, H.Adj a b → π a ≠ π b) [Nonempty J]
    (l : Combinatorics.Line (Triangle H π) J) : H ↪g productGraph H (J := J) where
  toFun := lineMap H π l
  inj' := by
    intro a b h
    obtain ⟨j,hj⟩ := l.proper
    simpa [lineMap,hj] using congrFun h j
  map_rel_iff' := lineMap_rel H π hπ l _ _

lemma lineMap_triangle (H : SimpleGraph A) (π : A → Fin 3)
    (l : Combinatorics.Line (Triangle H π) J) (x : Triangle H π) :
    (fun i => lineMap H π l (x.val i)) = fun i j => (l x j).val i := by
  funext i j
  cases hj : l.idxFun j <;> simp [lineMap,Combinatorics.Line.coe_apply,hj,x.property.1]

/-- Partite Ramsey for ordered triangles and a finite palette. -/
theorem partite {A C : Type} [Finite A] [Finite C] [Nonempty C]
    (H : SimpleGraph A) (π : A → Fin 3)
    (hπ : ∀ a b, H.Adj a b → π a ≠ π b) [Nonempty (Triangle H π)] :
    ∃ (B : Type) (_ : Finite B) (K : SimpleGraph B) (ρ : B → Fin 3),
      K.CliqueFree 4 ∧ (∀ a b, K.Adj a b → ρ a ≠ ρ b) ∧
      ∀ c : (Fin 3 → B) → C, ∃ (f : H ↪g K) (z : C),
        (∀ a, ρ (f a) = π a) ∧
        ∀ x : Fin 3 → A, IsTriangle H x → (∀ i, π (x i) = i) → c (f ∘ x) = z := by
  classical
  obtain ⟨J,hJ,hRam⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Triangle H π) C
  letI := hJ
  haveI : Nonempty J := by
    obtain ⟨l,_⟩ := hRam (fun _ => Classical.arbitrary C)
    exact ⟨l.proper.choose⟩
  let j₀ : J := Classical.arbitrary J
  let K := productGraph H (J := J)
  let ρ : (J → A) → Fin 3 := fun f => π (f j₀)
  have hρ : ∀ a b, K.Adj a b → ρ a ≠ ρ b := fun a b h => hπ _ _ (h j₀)
  have hK : K.CliqueFree 4 :=
    (SimpleGraph.Coloring.mk ρ (fun h => hρ _ _ h)).colorable.cliqueFree (by decide)
  refine ⟨J → A,inferInstance,K,ρ,hK,hρ,?_⟩
  intro c
  let d : (J → Triangle H π) → C := fun w => c (fun i j => (w j).val i)
  obtain ⟨l,z,hz⟩ := hRam d
  let f := lineEmbedding H π hπ l
  refine ⟨f,z,fun a => lineMap_part H π l a j₀,?_⟩
  intro x hx hp
  let t : Triangle H π := ⟨x,hp,hx⟩
  change c (fun i => lineMap H π l (t.val i)) = z
  rw [lineMap_triangle]
  exact hz t

#print axioms partite
end Erdos595FiniteTrianglePartite
