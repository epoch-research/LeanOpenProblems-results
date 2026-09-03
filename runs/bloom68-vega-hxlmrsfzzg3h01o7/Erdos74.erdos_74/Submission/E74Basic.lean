import Mathlib

open SimpleGraph

namespace E74

universe u
variable {V : Type u} [DecidableEq V]

/-- The edges on which a two-valued assignment fails to be proper. -/
def badGraph (G : SimpleGraph V) (p : V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ p u = p v
  symm := fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩
  loopless := fun v h ↦ G.loopless v h.1

noncomputable def badEdges [Fintype V] (G : SimpleGraph V) (p : V → Bool) :
    Finset (Sym2 V) := by
  classical
  exact (badGraph G p).edgeFinset

noncomputable def ends (E : Finset (Sym2 V)) : Finset V := by
  classical
  exact E.biUnion Sym2.toFinset

/-- A vertex deletion, represented on the unchanged ambient type. -/
def mask (G : SimpleGraph V) (Z : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ Z ∧ v ∉ Z
  symm := fun _ _ h ↦ ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := fun v h ↦ G.loopless v h.1

def Independent (G : SimpleGraph V) (Z : Set V) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → u ∈ Z → v ∈ Z → False

def ProperOff (G : SimpleGraph V) (Z : Set V) (p : V → Bool) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → u ∉ Z → v ∉ Z → p u ≠ p v

/-- Bounded reachability; unlike natural graph distance, this handles disconnected vertices. -/
def Near (G : SimpleGraph V) (X : Set V) (r : ℕ) (v : V) : Prop :=
  ∃ x ∈ X, ∃ w : G.Walk v x, w.length ≤ r

/-- Sum of edge labels, retaining multiplicities along a walk. -/
def walkXor {G : SimpleGraph V} (a : Sym2 V → Bool) {u v : V} : G.Walk u v → Bool
  | .nil => false
  | @Walk.cons _ _ u v w h p => a s(u, v) ^^ walkXor a p

noncomputable def twist (S : Finset (Sym2 V)) (e : Sym2 V) : Bool := by
  classical
  exact !decide (e ∈ S)

/-- A finite support for all parity constraints at a given length scale. -/
def ShortSupport (G : SimpleGraph V) (L : ℕ) (S : Finset (Sym2 V)) : Prop :=
  (S : Set (Sym2 V)) ⊆ G.edgeSet ∧
  ∀ (v : V) (w : G.Walk v v), w.length ≤ L → walkXor (twist S) w = false

def MinimalSupport (G : SimpleGraph V) (L : ℕ) (S : Finset (Sym2 V)) : Prop :=
  ShortSupport G L S ∧ ∀ T, ShortSupport G L T → S.card ≤ T.card

/-- The only hereditary numerical hypothesis used in the finite coloring argument. -/
def SmallCuts [Fintype V] (G : SimpleGraph V) (B : ℕ → ℕ) : Prop :=
  ∀ k, 2 ≤ k → ∀ H : G.Subgraph, H.verts.ncard ≤ B k →
    ∃ p : V → Bool, (badEdges H.spanningCoe p).card < k

@[simp] theorem badGraph_adj (G : SimpleGraph V) (p : V → Bool) (u v : V) :
    (badGraph G p).Adj u v ↔ G.Adj u v ∧ p u = p v := Iff.rfl

@[simp] theorem mask_adj (G : SimpleGraph V) (Z : Set V) (u v : V) :
    (mask G Z).Adj u v ↔ G.Adj u v ∧ u ∉ Z ∧ v ∉ Z := Iff.rfl

theorem mask_le (G : SimpleGraph V) (Z : Set V) : mask G Z ≤ G := fun _ _ h ↦ h.1

@[simp] theorem mem_badEdges [Fintype V] (G : SimpleGraph V) (p : V → Bool) (u v : V) :
    s(u, v) ∈ badEdges G p ↔ G.Adj u v ∧ p u = p v := by
  classical
  simp [badEdges]

@[simp] theorem mem_ends {E : Finset (Sym2 V)} {v : V} :
    v ∈ ends E ↔ ∃ e ∈ E, v ∈ e := by
  classical
  simp [ends]

@[simp] theorem ends_empty : ends (∅ : Finset (Sym2 V)) = ∅ := by
  classical
  simp [ends]

@[simp] theorem ends_union (E F : Finset (Sym2 V)) : ends (E ∪ F) = ends E ∪ ends F := by
  classical
  ext v
  simp only [mem_ends, Finset.mem_union]
  aesop

theorem card_ends_le (E : Finset (Sym2 V)) : (ends E).card ≤ 2 * E.card := by
  classical
  dsimp [ends]
  simpa [Nat.mul_comm] using
    Finset.card_biUnion_le_card_mul E Sym2.toFinset 2 (fun e _ ↦ by rw [Sym2.card_toFinset]; split_ifs <;> omega)

@[simp] theorem walkXor_nil {G : SimpleGraph V} (a : Sym2 V → Bool) (v : V) :
    walkXor a (Walk.nil : G.Walk v v) = false := rfl

@[simp] theorem walkXor_cons {G : SimpleGraph V} (a : Sym2 V → Bool)
    {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    walkXor a (p.cons h) = (a s(u, v) ^^ walkXor a p) := rfl

end E74
