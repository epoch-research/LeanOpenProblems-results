import FormalConjecturesUtil

/-!
A uniform obstruction to thickening a binary bilinear voltage graph.
This is an obstruction to a construction, not a disproof of Erdős 714.
-/

open SimpleGraph
open scoped CharTwo

namespace Erdos714BilinearThickening

variable {A B G : Type*} [AddMonoid A] [Ring B] [CharP B 2]
    [Ring G] [CharP G 2]

/-- The two label groups need not be the same. -/
def graph (β : A →+ B →+ G) (S : Set G) :
    SimpleGraph ((G × A) ⊕ (G × B)) where
  Adj p q := match p, q with
    | .inl x, .inr y => x.1 + y.1 + β x.2 y.2 ∈ S
    | .inr y, .inl x => x.1 + y.1 + β x.2 y.2 ∈ S
    | _, _ => False
  symm := by intro p q; cases p <;> cases q <;> simp
  loopless := by intro p; cases p <;> simp

/-- A two-by-two grid within one side, indexed without quotient multiplicities. -/
def pairGrid {X Y : Type*} (x₀ x₁ : X) (y₀ y₁ : Y) : Fin 4 → X × Y :=
  ![(x₀,y₀), (x₁,y₀), (x₀,y₁), (x₁,y₁)]

lemma pairGrid_injective {X Y : Type*} {x₀ x₁ : X} {y₀ y₁ : Y}
    (hx : x₀ ≠ x₁) (hy : y₀ ≠ y₁) :
    Function.Injective (pairGrid x₀ x₁ y₀ y₁) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [pairGrid, hx, hy, Ne.symm hx, Ne.symm hy] at hij ⊢

/-- Two connection values whose difference is a nonzero bilinear value give an
actual `K₄,₄`. No assumption about the additive energy of `S` is needed. -/
def gridCopy (β : A →+ B →+ G) (S : Set G) {u : A} {v : B} {s t : G}
    (hu : u ≠ 0) (hv : v ≠ 0) (hs : s ∈ S) (ht : t ∈ S) (hst : s ≠ t)
    (hβ : β u v = s + t) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy (graph β S) := by
  let L := pairGrid (0 : G) (s+t) (0 : A) u
  let R := pairGrid s t (0 : B) v
  have hL : Function.Injective L :=
    pairGrid_injective (Ne.symm (fun h => hst (CharTwo.add_eq_zero.mp h))) hu.symm
  have hR : Function.Injective R := pairGrid_injective hst hv.symm
  have hE (i j : Fin 4) : (graph β S).Adj (.inl (L i)) (.inr (R j)) := by
    change (L i).1 + (R j).1 + β (L i).2 (R j).2 ∈ S
    fin_cases i <;> fin_cases j <;>
      simp [L, R, pairGrid, hβ, add_left_comm, add_comm, hs, ht]
  refine ⟨⟨Sum.map L R, ?_⟩, Sum.map_injective.mpr ⟨hL, hR⟩⟩
  intro p q hpq
  cases p with
  | inl i =>
    cases q with
    | inl j => simp at hpq
    | inr j => exact hE i j
  | inr i =>
    cases q with
    | inl j => exact (hE j i).symm
    | inr j => simp at hpq

/-- If one row difference acts injectively, too many connections force a grid. -/
theorem not_free_of_card [Fintype B] [Fintype G]
    (β : A →+ B →+ G) (S : Finset G) {u : A} (hu : u ≠ 0)
    (hβ : Function.Injective (β u))
    (hcard : Fintype.card G < S.card * Fintype.card B) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph β (S : Set G)) := by
  classical
  let f : S × B → G := fun p => (p.1 : G) + β u p.2
  have hcard' : Fintype.card G < Fintype.card (S × B) := by
    simpa only [Fintype.card_prod, Fintype.card_coe] using hcard
  obtain ⟨p, q, hpq, he⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard'
  have hst : (p.1 : G) ≠ (q.1 : G) := by
    intro h
    apply hpq
    apply Prod.ext (Subtype.ext h)
    apply hβ
    exact add_left_cancel (show (p.1 : G) + β u p.2 = (p.1 : G) + β u q.2 by
      simpa only [f, h] using he)
  have hv : p.2 + q.2 ≠ 0 := by
    intro h
    have heq := CharTwo.add_eq_zero.mp h
    apply hst
    exact add_right_cancel (show (p.1 : G) + β u p.2 = (q.1 : G) + β u p.2 by
      simpa only [f, heq] using he)
  have hval : β u (p.2 + q.2) = (p.1 : G) + (q.1 : G) := by
    have hh := congrArg (fun z : G => z + (q.1 : G) + β u p.2) he
    simpa [f, map_add, add_assoc, add_left_comm, add_comm] using hh.symm
  intro hfree
  exact hfree ⟨gridCopy β (S : Set G) hu hv p.1.property q.1.property hst hval⟩

/-- A necessary bound on the connection set in any free graph of this form. -/
theorem connection_card_bound [Fintype B] [Fintype G]
    (β : A →+ B →+ G) (S : Finset G) {u : A} (hu : u ≠ 0)
    (hβ : Function.Injective (β u))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph β (S : Set G))) :
    S.card * Fintype.card B ≤ Fintype.card G := by
  exact le_of_not_gt (fun h => not_free_of_card β S hu hβ h hfree)

#print axioms gridCopy
#print axioms not_free_of_card
#print axioms connection_card_bound

end Erdos714BilinearThickening
