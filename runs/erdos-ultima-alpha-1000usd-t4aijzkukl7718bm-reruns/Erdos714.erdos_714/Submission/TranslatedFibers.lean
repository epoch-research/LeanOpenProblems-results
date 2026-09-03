import Submission.BilinearThickening
import Submission.BinaryLift
import Submission.Packing

/-!
Even nonlinear voltage tables cannot glue many translates of a fixed binary
connection set into a K44-free graph. This is not a resolution of Erdős 714.
-/

open SimpleGraph
open scoped CharTwo

namespace Erdos714TranslatedFibers

variable {A B G : Type*} [Ring G] [CharP G 2]

/-- A partial-translation graph whose local fibers all have the same shape. -/
def graph (β : A → B → G) (S : Set G) :
    SimpleGraph ((G × A) ⊕ (G × B)) where
  Adj p q := match p, q with
    | .inl x, .inr y => x.1 + y.1 + β x.2 y.2 ∈ S
    | .inr y, .inl x => x.1 + y.1 + β x.2 y.2 ∈ S
    | _, _ => False
  symm := by intro p q; cases p <;> cases q <;> simp
  loopless := by intro p; cases p <;> simp

/-- Changing voltage by one row term and one column term just changes the
point coordinates of the vertices. -/
def gaugeIso (β : A → B → G) (S : Set G) (r : A → G) (c : B → G) :
    graph (fun a b => r a + c b + β a b) S ≃g graph β S where
  toEquiv := Equiv.sumCongr
    { toFun := fun x => (x.1 + r x.2, x.2)
      invFun := fun x => (x.1 + r x.2, x.2)
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
    { toFun := fun y => (y.1 + c y.2, y.2)
      invFun := fun y => (y.1 + c y.2, y.2)
      left_inv := by intro y; simp
      right_inv := by intro y; simp }
  map_rel_iff' := by
    intro x y
    cases x <;> cases y <;> simp [graph, add_left_comm, add_comm]

/-- The only gauge-invariant datum of a two-by-two voltage rectangle. -/
def defect (β : A → B → G) (a₀ a₁ : A) (b₀ b₁ : B) : G :=
  β a₀ b₀ + β a₀ b₁ + β a₁ b₀ + β a₁ b₁

lemma two_sum (a b c d : G) (h : a + b = c + d) : b + d = a + c := by
  have hh := congrArg (fun z => z + c + b) h
  simpa [add_assoc, add_left_comm, add_comm] using hh.symm

/-- A defect of zero or the sum of two distinct connection values gives a
copy. All four vertices on each side have distinct actual coordinates. -/
def gridCopy (β : A → B → G) (S : Set G) {a₀ a₁ : A} {b₀ b₁ : B} {s t : G}
    (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) (hs : s ∈ S) (ht : t ∈ S) (hst : s ≠ t)
    (hd : defect β a₀ a₁ b₀ b₁ = 0 ∨ defect β a₀ a₁ b₀ b₁ = s+t) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy (graph β S) := by
  classical
  let r (a : A) := β a b₀ + β a₀ b₀
  let c (b : B) := β a₀ b
  let γ (a : A) (b : B) := r a + c b + β a b
  have h₀₀ : γ a₀ b₀ = 0 := by simp [γ, r, c]
  have h₀₁ : γ a₀ b₁ = 0 := by simp [γ, r, c]
  have h₁₀ : γ a₁ b₀ = 0 := by simp [γ, r, c, add_left_comm, add_comm]
  have h₁₁ : γ a₁ b₁ = defect β a₀ a₁ b₀ b₁ := by
    simp only [γ, r, c, defect]
    abel
  let L := Erdos714BilinearThickening.pairGrid (0 : G) (s+t) a₀ a₁
  let R := Erdos714BilinearThickening.pairGrid s t b₀ b₁
  have hL : Function.Injective L :=
    Erdos714BilinearThickening.pairGrid_injective
      (Ne.symm (fun h => hst (CharTwo.add_eq_zero.mp h))) ha
  have hR : Function.Injective R := Erdos714BilinearThickening.pairGrid_injective hst hb
  have hE (i j : Fin 4) : (graph γ S).Adj (.inl (L i)) (.inr (R j)) := by
    change (L i).1 + (R j).1 + γ (L i).2 (R j).2 ∈ S
    rcases hd with hd | hd <;>
      fin_cases i <;> fin_cases j <;>
      simp [L, R, Erdos714BilinearThickening.pairGrid, h₀₀, h₀₁, h₁₀, h₁₁, hd,
        add_left_comm, add_comm, hs, ht]
  let f : (completeBipartiteGraph (Fin 4) (Fin 4)).Copy (graph γ S) := by
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
  exact (gaugeIso β S r c).toCopy.comp f

/-- Pigeonhole on `(s,b) ↦ s + β(a₀,b) + β(a₁,b)` yields a forbidden defect.
No additivity, injectivity, or polynomial hypothesis on `β` is used. -/
theorem not_free_of_card [Fintype B] [Fintype G]
    (β : A → B → G) (S : Finset G) {a₀ a₁ : A} (ha : a₀ ≠ a₁)
    (hS : 2 ≤ S.card) (hcard : Fintype.card G < S.card * Fintype.card B) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph β (S : Set G)) := by
  classical
  let d (b : B) := β a₀ b + β a₁ b
  let f : S × B → G := fun p => (p.1 : G) + d p.2
  have hcard' : Fintype.card G < Fintype.card (S × B) := by
    simpa only [Fintype.card_prod, Fintype.card_coe] using hcard
  obtain ⟨p, q, hpq, he⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard'
  have hb : p.2 ≠ q.2 := by
    intro h
    apply hpq
    apply Prod.ext _ h
    apply Subtype.ext
    exact add_right_cancel (show (p.1 : G) + d p.2 = (q.1 : G) + d p.2 by
      simpa only [f, h] using he)
  have hdef : defect β a₀ a₁ p.2 q.2 = (p.1 : G) + (q.1 : G) := by
    convert two_sum (p.1 : G) (d p.2) (q.1 : G) (d q.2) he using 1
    simp only [defect, d]
    abel
  intro hfree
  by_cases hst : (p.1 : G) = (q.1 : G)
  · obtain ⟨s, hs, t, ht, hne⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
    have hz : defect β a₀ a₁ p.2 q.2 = 0 := by simp [hdef, hst]
    exact hfree ⟨gridCopy β (S : Set G) ha hb hs ht hne (Or.inl hz)⟩
  · exact hfree ⟨gridCopy β (S : Set G) ha hb p.1.property q.1.property hst (Or.inr hdef)⟩

/-- All translated-fiber constructions obey this necessary size bound. -/
theorem connection_card_bound [Fintype B] [Fintype G]
    (β : A → B → G) (S : Finset G) {a₀ a₁ : A} (ha : a₀ ≠ a₁)
    (hS : 2 ≤ S.card)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph β (S : Set G))) :
    S.card * Fintype.card B ≤ Fintype.card G := by
  exact le_of_not_gt (fun h => not_free_of_card β S ha hS h hfree)

/-- Fixing both labels and translating one point coordinate embeds the original
Cayley graph. In particular the common connection set must be Sidon-sized. -/
def fiberCopy (β : A → B → G) (S : Set G) (a : A) (b : B) :
    (Erdos714BinaryLift.cayley S).Copy (graph β S) where
  toHom := {
    toFun := fun p => if p.1 then Sum.inr (p.2 + β a b,b) else Sum.inl (p.2,a)
    map_rel' := by
      rintro ⟨bx,x⟩ ⟨cy,y⟩ h
      cases bx <;> cases cy <;>
        simp_all [Erdos714BinaryLift.cayley, graph, add_left_comm, add_comm] }
  injective' := by
    rintro ⟨bx,x⟩ ⟨cy,y⟩ h
    cases bx <;> cases cy <;> simp_all

lemma connection_square_bound [Fintype G]
    (β : A → B → G) (S : Finset G) (a : A) (b : B)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph β (S : Set G))) :
    S.card ^ 2 ≤ 3 * Fintype.card G := by
  have hc : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714BinaryLift.cayley (S : Set G)) := by
    rintro ⟨f⟩
    exact hfree ⟨(fiberCopy β (S : Set G) a b).comp f⟩
  have hb := Erdos714BinaryLift.cayley_card_bound S hc
  have hS : S.card ≤ Fintype.card G := Finset.card_le_univ _
  by_cases hz : S.card = 0
  · simp [hz]
  · have hs : S.card - 1 + 1 = S.card := Nat.sub_add_cancel (by omega)
    nlinarith

open Classical Finset in
lemma neighbor_card [Fintype B] [Fintype G]
    (β : A → B → G) (S : Finset G) (x : G) (a : A) :
    (univ.filter (fun q : G × B => x + q.1 + β a q.2 ∈ S)).card =
      Fintype.card B * S.card := by
  rw [← card_univ (α := B), ← card_product]
  apply card_bij (fun q _ => (q.2, x + q.1 + β a q.2))
  · intro q hq
    simpa using hq
  · intro p hp q hq he
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    dsimp only at h₁ h₂
    rw [h₁] at h₂
    exact Prod.ext (add_left_cancel (add_right_cancel h₂)) h₁
  · rintro ⟨b,s⟩ hbs
    refine ⟨(x+s+β a b,b), ?_, ?_⟩
    · simpa [add_assoc, add_left_comm, add_comm] using hbs
    · simp [add_left_comm, add_comm]

open Classical Finset in
/-- Exact edge count for an arbitrary voltage table, with no freeness hypothesis. -/
theorem edges [Fintype A] [Fintype B] [Fintype G]
    (β : A → B → G) (S : Finset G) :
    (graph β (S : Set G)).edgeFinset.card =
      Fintype.card G * Fintype.card A * Fintype.card B * S.card := by
  have he : graph β (S : Set G) = Erdos714Packing.incidence
      (fun p : G × A => univ.filter (fun q : G × B => p.1 + q.1 + β p.2 q.2 ∈ S)) := by
    ext p q
    cases p <;> cases q <;> simp [graph, Erdos714Packing.incidence]
  rw [he, Erdos714Packing.incidence_edges]
  simp_rw [neighbor_card]
  simp only [sum_const, card_univ, Fintype.card_prod, smul_eq_mul]
  ring

open Classical in
/-- Nontrivial translated thickenings with at least two row labels lose a
power compared with the desired `7/4` exponent: their edge count is `O(n^(5/3))`.
Singleton connection sets and arbitrary edge thinnings are not covered. -/
theorem edge_cube_bound [Fintype A] [Fintype B] [Fintype G] [Nonempty B]
    (β : A → B → G) (S : Finset G) {a₀ a₁ : A} (ha : a₀ ≠ a₁)
    (hS : 2 ≤ S.card)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph β (S : Set G))) :
    (graph β (S : Set G)).edgeFinset.card ^ 3 ≤
      3 * Fintype.card ((G × A) ⊕ (G × B)) ^ 5 := by
  have h₁ := connection_card_bound β S ha hS hfree
  have h₂ := connection_square_bound β S a₀ (Classical.choice ‹Nonempty B›) hfree
  rw [edges]
  calc
    _ = Fintype.card G ^ 3 * Fintype.card A ^ 3 * Fintype.card B ^ 2 *
        (S.card ^ 2) * (S.card * Fintype.card B) := by ring
    _ ≤ Fintype.card G ^ 3 * Fintype.card A ^ 3 * Fintype.card B ^ 2 *
        (3 * Fintype.card G) * Fintype.card G := by gcongr
    _ = 3 * Fintype.card G ^ 5 * Fintype.card A ^ 3 * Fintype.card B ^ 2 := by ring
    _ ≤ 3 * Fintype.card G ^ 5 * (Fintype.card A + Fintype.card B) ^ 3 *
        (Fintype.card A + Fintype.card B) ^ 2 := by gcongr <;> omega
    _ = _ := by simp only [Fintype.card_sum, Fintype.card_prod]; ring

#print axioms fiberCopy
#print axioms connection_square_bound
#print axioms edges
#print axioms edge_cube_bound

#print axioms gaugeIso
#print axioms gridCopy
#print axioms not_free_of_card
#print axioms connection_card_bound

end Erdos714TranslatedFibers
