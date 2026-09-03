import Submission.FiniteFolkmanAmalgamation

/-!
The finite-palette bipartite partite lemma, using Mathlib Hales--Jewett.
Both the alphabet and the palette in that application are finite.
-/

open SimpleGraph Set
namespace Erdos595FiniteFolkmanPartite

variable {A R : Type*} (H : SimpleGraph A) (π : A → R) (r s : R)

abbrev Domain := {a : A // π a = r ∨ π a = s}
abbrev Edge := {p : A × A // H.Adj p.1 p.2 ∧ π p.1 = r ∧ π p.2 = s}

def left (x : Edge H π r s) : Domain π r s := ⟨x.val.1,Or.inl x.property.2.1⟩
def right (x : Edge H π r s) : Domain π r s := ⟨x.val.2,Or.inr x.property.2.2⟩

variable {J : Type*}

def productGraph [Nonempty J] : SimpleGraph (J → Domain π r s) where
  Adj f g := ∀ j, H.Adj (f j).val (g j).val
  symm := fun f g h j => (h j).symm
  loopless := fun f h => H.loopless _ (h (Classical.arbitrary J))


noncomputable def lineMap (l : Combinatorics.Line (Edge H π r s) J)
    (d : Domain π r s) : J → Domain π r s := by
  classical
  exact fun j => match l.idxFun j with
    | none => d
    | some x => if π d.val = r then left H π r s x else right H π r s x

lemma lineMap_none (l : Combinatorics.Line (Edge H π r s) J)
    (d : Domain π r s) {j : J} (hj : l.idxFun j = none) :
    lineMap H π r s l d j = d := by simp [lineMap,hj]

lemma lineMap_color (l : Combinatorics.Line (Edge H π r s) J)
    (d : Domain π r s) (j : J) : π (lineMap H π r s l d j).val = π d.val := by
  classical
  cases hj : l.idxFun j with
  | none => rw [lineMap_none _ _ _ _ _ _ hj]
  | some x =>
    by_cases hd : π d.val = r
    · simp only [lineMap,hj,if_pos hd,left]
      exact x.property.2.1.trans hd.symm
    · have he : π d.val = s := d.property.resolve_left hd
      simp only [lineMap,hj,if_neg hd,right]
      exact x.property.2.2.trans he.symm

lemma lineMap_rel [Nonempty J] (hπ : ∀ a b, H.Adj a b → π a ≠ π b) (l : Combinatorics.Line (Edge H π r s) J)
    (a b : Domain π r s) :
    (productGraph H π r s).Adj (lineMap H π r s l a) (lineMap H π r s l b) ↔ H.Adj a.val b.val := by
  classical
  constructor
  · intro h
    obtain ⟨j,hj⟩ := l.proper
    have hh := h j
    simpa only [lineMap_none _ _ _ _ _ _ hj] using hh
  · intro hab j
    cases hj : l.idxFun j with
    | none => simpa only [lineMap_none _ _ _ _ _ _ hj] using hab
    | some x =>
      have hne := hπ a.val b.val hab
      by_cases ha : π a.val = r
      · have hb : π b.val ≠ r := fun he => hne (ha.trans he.symm)
        simpa only [lineMap,hj,if_pos ha,if_neg hb,left,right] using x.property.1
      · have has : π a.val = s := a.property.resolve_left ha
        have hb : π b.val = r := b.property.resolve_right (fun he => hne (has.trans he.symm))
        simpa only [lineMap,hj,if_neg ha,if_pos hb,left,right] using x.property.1.symm

noncomputable def lineEmbedding [Nonempty J] (hπ : ∀ a b, H.Adj a b → π a ≠ π b) (l : Combinatorics.Line (Edge H π r s) J) :
    H.induce {a | π a = r ∨ π a = s} ↪g productGraph H π r s (J := J) where
  toFun := lineMap H π r s l
  inj' := by
    intro a b h
    obtain ⟨j,hj⟩ := l.proper
    have he := congrFun h j
    simpa only [lineMap_none _ _ _ _ _ _ hj] using he
  map_rel_iff' := lineMap_rel H π r s hπ l _ _

lemma lineMap_left (l : Combinatorics.Line (Edge H π r s) J) (x : Edge H π r s) :
    lineMap H π r s l (left H π r s x) = fun j => left H π r s (l x j) := by
  classical
  funext j
  cases hj : l.idxFun j with
  | none => simp [lineMap,Combinatorics.Line.coe_apply,hj]
  | some y => simp [lineMap,Combinatorics.Line.coe_apply,hj,left,x.property.2.1]

lemma lineMap_right (hrs : r ≠ s) (l : Combinatorics.Line (Edge H π r s) J) (x : Edge H π r s) :
    lineMap H π r s l (right H π r s x) = fun j => right H π r s (l x j) := by
  classical
  funext j
  have hx : π x.val.2 ≠ r := fun h => hrs (h.symm.trans x.property.2.2)
  cases hj : l.idxFun j with
  | none => simp [lineMap,Combinatorics.Line.coe_apply,hj]
  | some y => simp [lineMap,Combinatorics.Line.coe_apply,hj,right,hx]

/-- Bipartite partite Ramsey lemma for a FINITE palette and a finite graph. -/
theorem partite {A R C : Type} [Finite A] [Finite C] [Nonempty C]
    (H : SimpleGraph A) (hH : H.CliqueFree 4) (π : A → R)
    (hπ : ∀ a b, H.Adj a b → π a ≠ π b) (r s : R) (hrs : r ≠ s)
    [Nonempty (Edge H π r s)] :
    ∃ (B : Type) (_ : Finite B) (K : SimpleGraph B) (ρ : B → R),
      K.CliqueFree 4 ∧ (∀ a b, K.Adj a b → ρ a ≠ ρ b) ∧
      ∀ c : Sym2 B → C, ∃ (f : H.induce {a | π a = r ∨ π a = s} ↪g K) (z : C),
        (∀ a, ρ (f a) = π a.val) ∧
        ∀ a b, H.Adj a.val b.val → c s(f a,f b) = z := by
  classical
  obtain ⟨J,hJ,hRam⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Edge H π r s) C
  letI := hJ
  haveI : Nonempty J := by
    obtain ⟨l,_⟩ := hRam (fun _ => Classical.arbitrary C)
    exact ⟨l.proper.choose⟩
  let j₀ : J := Classical.arbitrary J
  let K := productGraph H π r s (J := J)
  let ρ : (J → Domain π r s) → R := fun f => π (f j₀).val
  have hK : K.CliqueFree 4 := by
    by_contra hn
    let f := SimpleGraph.topEmbeddingOfNotCliqueFree hn
    have he : ∀ i j : Fin 4, i ≠ j → H.Adj (f i j₀).val (f j j₀).val :=
      fun i j h => f.map_rel_iff.mpr h j₀
    exact Erdos595Work.no_adj_common_neighbors hH (he 0 1 (by decide)) (he 0 2 (by decide))
      (he 1 2 (by decide)) (he 0 3 (by decide)) (he 1 3 (by decide)) (he 2 3 (by decide))
  refine ⟨J → Domain π r s,inferInstance,K,ρ,hK,?_,?_⟩
  · intro a b h
    exact hπ _ _ (h j₀)
  · intro c
    let d : (J → Edge H π r s) → C := fun w =>
      c s((fun j => left H π r s (w j)),(fun j => right H π r s (w j)))
    obtain ⟨l,z,hz⟩ := hRam d
    let f := lineEmbedding H π r s hπ l
    refine ⟨f,z,fun a => lineMap_color H π r s l a j₀,?_⟩
    intro a b hab
    have hne := hπ a.val b.val hab
    have hed : ∀ x : Edge H π r s, c s(f (left H π r s x),f (right H π r s x)) = z := by
      intro x
      change c s(lineMap H π r s l (left H π r s x),lineMap H π r s l (right H π r s x)) = z
      rw [lineMap_left,lineMap_right H π r s hrs]
      exact hz x
    by_cases ha : π a.val = r
    · have hb : π b.val = s := b.property.resolve_left (fun he => hne (ha.trans he.symm))
      exact hed ⟨(a.val,b.val),hab,ha,hb⟩
    · have has : π a.val = s := a.property.resolve_left ha
      have hb : π b.val = r := b.property.resolve_right (fun he => hne (has.trans he.symm))
      have he := hed ⟨(b.val,a.val),hab.symm,hb,has⟩
      change c s(f b,f a) = z at he
      simpa only [Sym2.eq_swap] using he

#print axioms partite
end Erdos595FiniteFolkmanPartite
