/-
Copyright 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FormalConjecturesUtil

/-!
# A concrete non-Fano incidence graph

Development file only: the results here concern explicitly specified finite graphs.
They do not assert a resolution of Erdős problem 713.

The seven point vertices are `A, B, C, D, X, Y, Z = 0, ..., 6`. The nine
line vertices `ABX, CDX, ACY, BDY, ADZ, BCZ, XY, XZ, YZ = 7, ..., 15`
have exactly the neighborhoods indicated by their names.

The prescribed copies in `C6[4]` and in the folded 6-cube are constructed explicitly.
They are subgraph copies, not induced embeddings. The folded cube is modeled on
`Fin 5 → ZMod 2`, with the five basis vectors and the all-ones vector as generators;
the quotient map from six coordinates is also checked.

All finite computations below use the kernel-checked `decide` tactic.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Erdos713

namespace NonFano

abbrev A : Fin 16 := 0
abbrev B : Fin 16 := 1
abbrev C : Fin 16 := 2
abbrev D : Fin 16 := 3
abbrev X : Fin 16 := 4
abbrev Y : Fin 16 := 5
abbrev Z : Fin 16 := 6

abbrev ABX : Fin 16 := 7
abbrev CDX : Fin 16 := 8
abbrev ACY : Fin 16 := 9
abbrev BDY : Fin 16 := 10
abbrev ADZ : Fin 16 := 11
abbrev BCZ : Fin 16 := 12
abbrev XY : Fin 16 := 13
abbrev XZ : Fin 16 := 14
abbrev YZ : Fin 16 := 15

/-- The incidence table, empty on point roles and listing points on line roles. -/
def linePoints : Fin 16 → Finset (Fin 16) :=
  ![∅, ∅, ∅, ∅, ∅, ∅, ∅,
    {A, B, X}, {C, D, X}, {A, C, Y}, {B, D, Y}, {A, D, Z}, {B, C, Z},
    {X, Y}, {X, Z}, {Y, Z}]

end NonFano

/-- The 16-vertex, 24-edge non-Fano incidence graph. -/
def nonFanoGraph : SimpleGraph (Fin 16) where
  Adj u v := u ∈ NonFano.linePoints v ∨ v ∈ NonFano.linePoints u
  symm _ _ := Or.symm
  loopless := by
    change ∀ v : Fin 16, ¬(v ∈ NonFano.linePoints v ∨ v ∈ NonFano.linePoints v)
    decide

instance nonFanoGraph_decidableAdj : DecidableRel nonFanoGraph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- An explicit adjacency characterization, also fixing the role convention. -/
theorem nonFanoGraph_adj_iff (u v : Fin 16) :
    nonFanoGraph.Adj u v ↔
      u ∈ NonFano.linePoints v ∨ v ∈ NonFano.linePoints u := Iff.rfl

/-- Each of the nine line roles has exactly its specified neighborhood. -/
theorem nonFanoGraph_line_neighborhoods :
    ∀ v : Fin 16, 7 ≤ v.val → nonFanoGraph.neighborFinset v = NonFano.linePoints v := by
  decide

/-- Points are colored zero and lines one. -/
def nonFanoGraphBicoloring : nonFanoGraph.Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk (fun v => if v.val < 7 then 0 else 1) (by decide)

/-- The specified incidence graph is bipartite. -/
theorem nonFanoGraph_isBipartite : nonFanoGraph.IsBipartite :=
  ⟨nonFanoGraphBicoloring⟩

/-- The six triple lines and three double lines contribute exactly 24 edges. -/
theorem nonFanoGraph_edgeFinset_card : nonFanoGraph.edgeFinset.card = 24 := by
  decide

/-- In particular the graph has at least two edges. -/
theorem nonFanoGraph_two_le_edgeFinset_card : 2 ≤ nonFanoGraph.edgeFinset.card := by
  rw [nonFanoGraph_edgeFinset_card]
  decide

/-- Two distinct vertices have at most one common neighbor. -/
theorem nonFanoGraph_common_neighbor_unique :
    ∀ a b c d : Fin 16, a ≠ b →
      nonFanoGraph.Adj a c → nonFanoGraph.Adj b c →
      nonFanoGraph.Adj a d → nonFanoGraph.Adj b d → c = d := by
  decide

/-- There is no (not necessarily induced) copy of the 4-cycle. -/
theorem nonFanoGraph_C4_free : (SimpleGraph.cycleGraph 4).Free nonFanoGraph := by
  rintro ⟨f⟩
  have h02 : f 0 ≠ f 2 := fun h => (by decide : (0 : Fin 4) ≠ 2) (f.injective h)
  have h13 : f 1 = f 3 :=
    nonFanoGraph_common_neighbor_unique (f 0) (f 2) (f 1) (f 3) h02
      (f.toHom.map_adj (by decide : (SimpleGraph.cycleGraph 4).Adj 0 1))
      (f.toHom.map_adj (by decide : (SimpleGraph.cycleGraph 4).Adj 2 1))
      (f.toHom.map_adj (by decide : (SimpleGraph.cycleGraph 4).Adj 0 3))
      (f.toHom.map_adj (by decide : (SimpleGraph.cycleGraph 4).Adj 2 3))
  exact (by decide : (1 : Fin 4) ≠ 3) (f.injective h13)

/- ## The specified copy in the four-fold blowup of a 6-cycle -/

/-- Each vertex of the usual 6-cycle is replaced by an independent set of size four. -/
def c6Blowup4 : SimpleGraph (Fin 6 × Fin 4) :=
  (SimpleGraph.cycleGraph 6).comap Prod.fst

instance c6Blowup4_decidableAdj : DecidableRel c6Blowup4.Adj :=
  inferInstanceAs (DecidableRel ((SimpleGraph.cycleGraph 6).comap
    (Prod.fst : Fin 6 × Fin 4 → Fin 6)).Adj)

/-- Adjacency depends only on consecutive base vertices modulo six. -/
theorem c6Blowup4_adj_iff (u v : Fin 6 × Fin 4) :
    c6Blowup4.Adj u v ↔ u.1 - v.1 = 1 ∨ v.1 - u.1 = 1 :=
  SimpleGraph.cycleGraph_adj

/-- The base-fibre order is `(P1, L2, P3, L1, P2, L3)`.

The occupied fibres are:
* `P1`: A, B, Y, Z;
* `P2`: C, D;
* `P3`: X;
* `L1`: CDX;
* `L2`: ABX, XY, XZ, YZ;
* `L3`: ACY, BDY, ADZ, BCZ.
-/
def nonFanoC6Placement : Fin 16 → Fin 6 × Fin 4 :=
  ![(0, 0), (0, 1), (4, 0), (4, 1), (2, 0), (0, 2), (0, 3),
    (1, 0), (3, 0), (5, 0), (5, 1), (5, 2), (5, 3), (1, 1), (1, 2), (1, 3)]

/-- The sixteen occupied positions are distinct. -/
theorem nonFanoC6Placement_injective : Function.Injective nonFanoC6Placement := by
  change ∀ u v, nonFanoC6Placement u = nonFanoC6Placement v → u = v
  decide

/-- Every incidence edge joins consecutive base fibres. -/
theorem nonFanoC6Placement_adj :
    ∀ u v, nonFanoGraph.Adj u v →
      c6Blowup4.Adj (nonFanoC6Placement u) (nonFanoC6Placement v) := by
  decide

/-- The vertex embedding underlying the prescribed placement. -/
def nonFanoC6Embedding : Fin 16 ↪ Fin 6 × Fin 4 :=
  ⟨nonFanoC6Placement, nonFanoC6Placement_injective⟩

/-- An explicit subgraph copy, not an induced graph embedding. -/
def nonFanoC6Copy : SimpleGraph.Copy nonFanoGraph c6Blowup4 where
  toHom := ⟨nonFanoC6Placement, fun {u v} => nonFanoC6Placement_adj u v⟩
  injective' := nonFanoC6Placement_injective

/-- The image edge set is a subgraph of `C6[4]` on its 24-vertex type. -/
theorem nonFanoGraph_map_le_c6Blowup4 :
    nonFanoGraph.map nonFanoC6Embedding ≤ c6Blowup4 := by
  rw [SimpleGraph.map_le_iff_le_comap]
  exact nonFanoC6Placement_adj

/-- The exact finite containment `H ⊑ C6[4]`. -/
theorem nonFanoGraph_isContained_c6Blowup4 : nonFanoGraph.IsContained c6Blowup4 :=
  ⟨nonFanoC6Copy⟩

/- ## A copy in the folded 6-cube on 32 vertices -/

open scoped BigOperators

/-- Five independent binary coordinates for the quotient of Q6 by its antipodal pairs. -/
abbrev Folded6Vertex := Fin 5 → ZMod 2

/-- The five standard basis vectors, followed by the all-ones vector. -/
def folded6Generators : Fin 6 → Folded6Vertex :=
  ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1, Pi.single 4 1,
    fun _ => 1]

theorem folded6Generators_ne_zero : ∀ i, folded6Generators i ≠ 0 := by
  decide

/-- The Cayley model for the folded 6-cube: differences are the six specified generators.
In characteristic two, the difference of two vertices equals their sum. -/
def folded6Cube : SimpleGraph Folded6Vertex where
  Adj u v := ∃ i : Fin 6, u + v = folded6Generators i
  symm u v h := by simpa only [add_comm] using h
  loopless u := by
    rintro ⟨i, hi⟩
    have hu : u + u = 0 := by
      funext j
      exact (by decide : ∀ x : ZMod 2, x + x = 0) (u j)
    exact folded6Generators_ne_zero i (hi.symm.trans hu)

instance folded6Cube_decidableAdj : DecidableRel folded6Cube.Adj :=
  fun _ _ => inferInstanceAs (Decidable (∃ i : Fin 6, _ = folded6Generators i))

theorem folded6Cube_card : Fintype.card Folded6Vertex = 32 := by
  decide

/-- Coordinate-sum parity, a two-coloring because all six generators have odd weight. -/
def folded6Parity (v : Folded6Vertex) : ZMod 2 := ∑ i : Fin 5, v i

def folded6CubeBicoloring : folded6Cube.Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk folded6Parity (by decide)

theorem folded6Cube_isBipartite : folded6Cube.IsBipartite :=
  ⟨folded6CubeBicoloring⟩

/-- Delete coordinate 5 after adding that coordinate to all six coordinates.
This picks the representative with last coordinate zero in each antipodal pair. -/
def folded6QuotientMap : (Fin 6 → ZMod 2) →+ Folded6Vertex where
  toFun v i := v i.castSucc + v 5
  map_zero' := by ext i; simp
  map_add' u v := by ext i; simp; ring

/-- The kernel is exactly the two antipodal translations. -/
theorem folded6QuotientMap_eq_zero :
    ∀ v : Fin 6 → ZMod 2,
      folded6QuotientMap v = 0 ↔ v = 0 ∨ v = (fun _ => 1) := by
  decide

/-- The images of the six directions of Q6 are precisely the listed generators. -/
theorem folded6QuotientMap_basis :
    ∀ i : Fin 6, folded6QuotientMap (Pi.single i 1) = folded6Generators i := by
  decide

/-- Every five-coordinate vector has a representative. -/
theorem folded6QuotientMap_surjective : Function.Surjective folded6QuotientMap := by
  change ∀ w : Folded6Vertex, ∃ v : Fin 6 → ZMod 2, folded6QuotientMap v = w
  decide


/-- The specified folded-cube placement, with `s1,...,s5` the five basis vectors.
The sixth direction is their sum, i.e. the all-ones vector.
The entries are in the same point/line order as `nonFanoGraph`. -/
def nonFanoFolded6Placement : Fin 16 → Folded6Vertex :=
  let s1 := folded6Generators 0
  let s2 := folded6Generators 1
  let s3 := folded6Generators 2
  let s4 := folded6Generators 3
  let s5 := folded6Generators 4
  ![0, s1 + s2, s1 + s3, s1 + s4, s2 + s5, s3 + s5, s4 + s5,
    s2, s1 + s3 + s4, s3, s1 + s2 + s4, s4, s1 + s2 + s3,
    s2 + s3 + s5, s2 + s4 + s5, s3 + s4 + s5]

/-- All sixteen folded-cube images are distinct. -/
theorem nonFanoFolded6Placement_injective : Function.Injective nonFanoFolded6Placement := by
  change ∀ u v, nonFanoFolded6Placement u = nonFanoFolded6Placement v → u = v
  decide

/-- Each of the 24 incidences becomes a generator edge of the folded cube. -/
theorem nonFanoFolded6Placement_adj :
    ∀ u v, nonFanoGraph.Adj u v →
      folded6Cube.Adj (nonFanoFolded6Placement u) (nonFanoFolded6Placement v) := by
  decide

/-- The supplied placement is not induced: its extra edges are B--YZ, C--XZ, D--XY. -/
theorem nonFanoFolded6Placement_adj_iff :
    ∀ u v, folded6Cube.Adj (nonFanoFolded6Placement u) (nonFanoFolded6Placement v) ↔
      nonFanoGraph.Adj u v ∨
      (u = NonFano.B ∧ v = NonFano.YZ) ∨ (u = NonFano.YZ ∧ v = NonFano.B) ∨
      (u = NonFano.C ∧ v = NonFano.XZ) ∨ (u = NonFano.XZ ∧ v = NonFano.C) ∨
      (u = NonFano.D ∧ v = NonFano.XY) ∨ (u = NonFano.XY ∧ v = NonFano.D) := by
  decide

/-- The injective map of vertex types used for the folded-cube copy. -/
def nonFanoFolded6Embedding : Fin 16 ↪ Folded6Vertex :=
  ⟨nonFanoFolded6Placement, nonFanoFolded6Placement_injective⟩

/-- An explicit, not necessarily induced, copy in the folded 6-cube. -/
def nonFanoFolded6Copy : SimpleGraph.Copy nonFanoGraph folded6Cube where
  toHom := ⟨nonFanoFolded6Placement, fun {u v} => nonFanoFolded6Placement_adj u v⟩
  injective' := nonFanoFolded6Placement_injective

/-- The image graph is a subgraph of the 32-vertex folded cube. -/
theorem nonFanoGraph_map_le_folded6Cube :
    nonFanoGraph.map nonFanoFolded6Embedding ≤ folded6Cube := by
  rw [SimpleGraph.map_le_iff_le_comap]
  exact nonFanoFolded6Placement_adj

/-- The requested finite containment in the folded 6-cube. -/
theorem nonFanoGraph_isContained_folded6Cube : nonFanoGraph.IsContained folded6Cube :=
  ⟨nonFanoFolded6Copy⟩

end Erdos713

/- Axiom audit: every public theorem, plus the proof-bearing constructions. -/
#print axioms Erdos713.nonFanoGraph_adj_iff
#print axioms Erdos713.nonFanoGraph_line_neighborhoods
#print axioms Erdos713.nonFanoGraph_isBipartite
#print axioms Erdos713.nonFanoGraph_edgeFinset_card
#print axioms Erdos713.nonFanoGraph_two_le_edgeFinset_card
#print axioms Erdos713.nonFanoGraph_common_neighbor_unique
#print axioms Erdos713.nonFanoGraph_C4_free
#print axioms Erdos713.c6Blowup4_adj_iff
#print axioms Erdos713.nonFanoC6Placement_injective
#print axioms Erdos713.nonFanoC6Placement_adj
#print axioms Erdos713.nonFanoGraph_map_le_c6Blowup4
#print axioms Erdos713.nonFanoGraph_isContained_c6Blowup4
#print axioms Erdos713.folded6Generators_ne_zero
#print axioms Erdos713.folded6Cube_card
#print axioms Erdos713.folded6Cube_isBipartite
#print axioms Erdos713.folded6QuotientMap_eq_zero
#print axioms Erdos713.folded6QuotientMap_basis
#print axioms Erdos713.folded6QuotientMap_surjective
#print axioms Erdos713.nonFanoFolded6Placement_injective
#print axioms Erdos713.nonFanoFolded6Placement_adj
#print axioms Erdos713.nonFanoFolded6Placement_adj_iff
#print axioms Erdos713.nonFanoGraph_map_le_folded6Cube
#print axioms Erdos713.nonFanoGraph_isContained_folded6Cube
#print axioms Erdos713.nonFanoGraph
#print axioms Erdos713.nonFanoGraphBicoloring
#print axioms Erdos713.nonFanoC6Embedding
#print axioms Erdos713.nonFanoC6Copy
#print axioms Erdos713.folded6Cube
#print axioms Erdos713.folded6CubeBicoloring
#print axioms Erdos713.folded6QuotientMap
#print axioms Erdos713.nonFanoFolded6Embedding
#print axioms Erdos713.nonFanoFolded6Copy
