import FormalConjecturesUtil

/-!
A signed additive charge on the even edge subsets of K5 need not be an
edge-weight sum. This does not assume invariant cycle-partition count,
does not refute the invariant-count variant, and does not settle Erdos 184.
-/
namespace K5EvenCharge
open scoped BigOperators
abbrev V := Fin 5
abbrev E := Fin 10

def endpoints : E → V × V := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
def incident (e : E) (v : V) : Prop :=
  v = (endpoints e).1 ∨ v = (endpoints e).2
instance (e : E) (v : V) : Decidable (incident e v) :=
  inferInstanceAs (Decidable (_ ∨ _))

def EvenEdges (s : Finset E) : Prop :=
  ∀ v : V, (s.filter (fun e => incident e v)).card % 2 = 0
instance (s : Finset E) : Decidable (EvenEdges s) :=
  inferInstanceAs (Decidable (∀ v : V, (s.filter (fun e => incident e v)).card % 2 = 0))

def A : Finset E := {0,3,4,7,9}
def B : Finset E := {1,2,5,6,8}
def evenAt : Fin 64 → Finset E := ![∅,
  {0,1,4},
  {0,2,5},
  {1,2,4,5},
  {0,3,6},
  {1,3,4,6},
  {2,3,5,6},
  {0,1,2,3,4,5,6},
  {1,2,7},
  {0,2,4,7},
  {0,1,5,7},
  {4,5,7},
  {0,1,2,3,6,7},
  {2,3,4,6,7},
  {1,3,5,6,7},
  {0,3,4,5,6,7},
  {1,3,8},
  {0,3,4,8},
  {0,1,2,3,5,8},
  {2,3,4,5,8},
  {0,1,6,8},
  {4,6,8},
  {1,2,5,6,8},
  {0,2,4,5,6,8},
  {2,3,7,8},
  {0,1,2,3,4,7,8},
  {0,3,5,7,8},
  {1,3,4,5,7,8},
  {0,2,6,7,8},
  {1,2,4,6,7,8},
  {5,6,7,8},
  {0,1,4,5,6,7,8},
  {2,3,9},
  {0,1,2,3,4,9},
  {0,3,5,9},
  {1,3,4,5,9},
  {0,2,6,9},
  {1,2,4,6,9},
  {5,6,9},
  {0,1,4,5,6,9},
  {1,3,7,9},
  {0,3,4,7,9},
  {0,1,2,3,5,7,9},
  {2,3,4,5,7,9},
  {0,1,6,7,9},
  {4,6,7,9},
  {1,2,5,6,7,9},
  {0,2,4,5,6,7,9},
  {1,2,8,9},
  {0,2,4,8,9},
  {0,1,5,8,9},
  {4,5,8,9},
  {0,1,2,3,6,8,9},
  {2,3,4,6,8,9},
  {1,3,5,6,8,9},
  {0,3,4,5,6,8,9},
  {7,8,9},
  {0,1,4,7,8,9},
  {0,2,5,7,8,9},
  {1,2,4,5,7,8,9},
  {0,3,6,7,8,9},
  {1,3,4,6,7,8,9},
  {2,3,5,6,7,8,9},
  {0,1,2,3,4,5,6,7,8,9}]
def evenIndex (s : Finset E) : Fin 64 :=
  Fin.ofNat 64 (∑ i : Fin 6, if Fin.ofNat 10 (i.val + 4) ∈ s then 2 ^ i.val else 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma even_index : ∀ s : Finset E, EvenEdges s → evenAt (evenIndex s) = s := by decide

def charge (s : Finset E) : ℤ := if s = A then 1 else if s = B then -1 else 0

lemma charge_empty : charge ∅ = 0 := by decide
lemma even_A : EvenEdges A := by decide
lemma even_B : EvenEdges B := by decide
lemma disjoint_AB : Disjoint A B := by decide
lemma union_AB : A ∪ B = Finset.univ := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma charge_add_table :
    ∀ i j : Fin 64, Disjoint (evenAt i) (evenAt j) →
      charge (evenAt i ∪ evenAt j) = charge (evenAt i) + charge (evenAt j) := by decide

lemma charge_add {a b : Finset E} (ha : EvenEdges a) (hb : EvenEdges b)
    (hab : Disjoint a b) : charge (a ∪ b) = charge a + charge b := by
  have hh := charge_add_table (evenIndex a) (evenIndex b)
  rw [even_index a ha, even_index b hb] at hh
  exact hh hab

def triangles : Fin 10 → Finset E := ![{0,1,4},{0,2,5},{0,3,6},{1,2,7},{1,3,8},{2,3,9},{4,5,7},{4,6,8},{5,6,9},{7,8,9}]
lemma triangles_even : ∀ i, EvenEdges (triangles i) := by decide
lemma triangles_charge : ∀ i, charge (triangles i) = 0 := by decide

/-- There is no real edge-weight representation of this additive charge. -/
theorem not_edge_weight_sum :
    ¬ ∃ w : E → ℝ, ∀ s : Finset E, EvenEdges s →
      (charge s : ℝ) = ∑ e ∈ s, w e := by
  rintro ⟨w, hw⟩
  have h0 := hw (triangles 0) (triangles_even 0)
  have h1 := hw (triangles 1) (triangles_even 1)
  have h2 := hw (triangles 2) (triangles_even 2)
  have h3 := hw (triangles 3) (triangles_even 3)
  have h4 := hw (triangles 4) (triangles_even 4)
  have h5 := hw (triangles 5) (triangles_even 5)
  have h6 := hw (triangles 6) (triangles_even 6)
  have h7 := hw (triangles 7) (triangles_even 7)
  have h8 := hw (triangles 8) (triangles_even 8)
  have h9 := hw (triangles 9) (triangles_even 9)
  have hA := hw A even_A
  simp only [triangles_charge, Int.cast_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [triangles, Matrix.cons_val, charge, A, Finset.sum_insert] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hA
  linarith

/-- Explicit finite counterexample to unrestricted signed-charge extension. -/
theorem additive_charge_not_representable :
    charge ∅ = 0 ∧
    (∀ a b : Finset E, EvenEdges a → EvenEdges b → Disjoint a b →
      charge (a ∪ b) = charge a + charge b) ∧
    ¬ (∃ w : E → ℝ, ∀ s : Finset E, EvenEdges s →
      (charge s : ℝ) = ∑ e ∈ s, w e) :=
  ⟨charge_empty, fun _ _ ha hb hab => charge_add ha hb hab, not_edge_weight_sum⟩

end K5EvenCharge
