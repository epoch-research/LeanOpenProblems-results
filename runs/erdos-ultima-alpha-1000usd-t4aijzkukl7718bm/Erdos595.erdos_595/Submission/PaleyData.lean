import Submission.TriangleHit

/-!
An exact finite obstruction to a convex strengthening of triangle-hitting:
the K4-free Paley graph on 17 vertices has no unit-vector assignment for
which every triangle has sum of pairwise inner products at most -1.
This does not settle Erdős 595 or obstruct the weaker minimum-edge condition.
-/

open SimpleGraph Set
open scoped BigOperators

namespace Erdos595Paley

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def adjacent (a b : Fin 17) : Prop :=
  (a.val + 17 - b.val) % 17 ∈ ([1, 2, 4, 8, 9, 13, 15, 16] : List ℕ)

instance : DecidableRel adjacent := fun _ _ => inferInstanceAs (Decidable (_ ∈ (_ : List ℕ)))

private theorem adj_symm : ∀ a b, adjacent a b → adjacent b a := by decide +kernel
private theorem adj_irrefl : ∀ a, ¬adjacent a a := by decide +kernel

def G : SimpleGraph (Fin 17) where
  Adj := adjacent
  symm := fun a b h => adj_symm a b h
  loopless := adj_irrefl

def vertices : List (Fin 17) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]

theorem vertices_mem : ∀ a : Fin 17, a ∈ vertices := by decide +kernel

private theorem no_four_check : vertices.all (fun a => vertices.all (fun b =>
    vertices.all (fun c => vertices.all (fun d => decide
      (¬(adjacent a b ∧ adjacent a c ∧ adjacent a d ∧
        adjacent b c ∧ adjacent b d ∧ adjacent c d)))))) = true := by decide +kernel

private theorem no_four : ∀ a b c d : Fin 17,
    ¬(adjacent a b ∧ adjacent a c ∧ adjacent a d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by
  intro a b c d
  have ha := List.all_eq_true.mp no_four_check a (vertices_mem a)
  have hb := List.all_eq_true.mp ha b (vertices_mem b)
  have hc := List.all_eq_true.mp hb c (vertices_mem c)
  exact of_decide_eq_true (List.all_eq_true.mp hc d (vertices_mem d))

#check no_four

theorem G_cliqueFree : G.CliqueFree 4 := by
  classical
  by_contra h
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree h
  apply no_four (f 0) (f 1) (f 2) (f 3)
  exact ⟨f.map_rel_iff.mpr (by decide), f.map_rel_iff.mpr (by decide),
    f.map_rel_iff.mpr (by decide), f.map_rel_iff.mpr (by decide),
    f.map_rel_iff.mpr (by decide), f.map_rel_iff.mpr (by decide)⟩

def edges : Fin 68 → Fin 17 × Fin 17 :=
  ![(0, 1),
    (0, 2),
    (0, 4),
    (0, 8),
    (0, 9),
    (0, 13),
    (0, 15),
    (0, 16),
    (1, 2),
    (1, 3),
    (1, 5),
    (1, 9),
    (1, 10),
    (1, 14),
    (1, 16),
    (2, 3),
    (2, 4),
    (2, 6),
    (2, 10),
    (2, 11),
    (2, 15),
    (3, 4),
    (3, 5),
    (3, 7),
    (3, 11),
    (3, 12),
    (3, 16),
    (4, 5),
    (4, 6),
    (4, 8),
    (4, 12),
    (4, 13),
    (5, 6),
    (5, 7),
    (5, 9),
    (5, 13),
    (5, 14),
    (6, 7),
    (6, 8),
    (6, 10),
    (6, 14),
    (6, 15),
    (7, 8),
    (7, 9),
    (7, 11),
    (7, 15),
    (7, 16),
    (8, 9),
    (8, 10),
    (8, 12),
    (8, 16),
    (9, 10),
    (9, 11),
    (9, 13),
    (10, 11),
    (10, 12),
    (10, 14),
    (11, 12),
    (11, 13),
    (11, 15),
    (12, 13),
    (12, 14),
    (12, 16),
    (13, 14),
    (13, 15),
    (14, 15),
    (14, 16),
    (15, 16)]

def triangles : Fin 68 → Fin 17 × Fin 17 × Fin 17 :=
  ![(0, 1, 2),
    (0, 1, 9),
    (0, 1, 16),
    (0, 2, 4),
    (0, 2, 15),
    (0, 4, 8),
    (0, 4, 13),
    (0, 8, 9),
    (0, 8, 16),
    (0, 9, 13),
    (0, 13, 15),
    (0, 15, 16),
    (1, 2, 3),
    (1, 2, 10),
    (1, 3, 5),
    (1, 3, 16),
    (1, 5, 9),
    (1, 5, 14),
    (1, 9, 10),
    (1, 10, 14),
    (1, 14, 16),
    (2, 3, 4),
    (2, 3, 11),
    (2, 4, 6),
    (2, 6, 10),
    (2, 6, 15),
    (2, 10, 11),
    (2, 11, 15),
    (3, 4, 5),
    (3, 4, 12),
    (3, 5, 7),
    (3, 7, 11),
    (3, 7, 16),
    (3, 11, 12),
    (3, 12, 16),
    (4, 5, 6),
    (4, 5, 13),
    (4, 6, 8),
    (4, 8, 12),
    (4, 12, 13),
    (5, 6, 7),
    (5, 6, 14),
    (5, 7, 9),
    (5, 9, 13),
    (5, 13, 14),
    (6, 7, 8),
    (6, 7, 15),
    (6, 8, 10),
    (6, 10, 14),
    (6, 14, 15),
    (7, 8, 9),
    (7, 8, 16),
    (7, 9, 11),
    (7, 11, 15),
    (7, 15, 16),
    (8, 9, 10),
    (8, 10, 12),
    (8, 12, 16),
    (9, 10, 11),
    (9, 11, 13),
    (10, 11, 12),
    (10, 12, 14),
    (11, 12, 13),
    (11, 13, 15),
    (12, 13, 14),
    (12, 14, 16),
    (13, 14, 15),
    (14, 15, 16)]

theorem triangles_valid : ∀ t : Fin 68,
    adjacent (triangles t).1 (triangles t).2.1 ∧
    adjacent (triangles t).1 (triangles t).2.2 ∧
    adjacent (triangles t).2.1 (triangles t).2.2 := by decide +kernel

def S (i j : Fin 17) : ℤ := if i = j then 40 else if adjacent i j then 6 else -11

def C (i j : Fin 17) : ℤ := if i = j then 3757 else if adjacent i j then 1445 else 0

/-- An exact integer Gram certificate. It is (17 A + 51 I - 11 J)^2
plus 901 J, equal to 3757 I + 1445 A. -/
private theorem certificate_check : vertices.all (fun i => vertices.all (fun j =>
    decide ((∑ k : Fin 17, S k i * S k j) + 901 = C i j))) = true := by decide +kernel

theorem certificate : ∀ i j : Fin 17,
    (∑ k : Fin 17, S k i * S k j) + 901 = C i j := by
  intro i j
  have hi := List.all_eq_true.mp certificate_check i (vertices_mem i)
  exact of_decide_eq_true (List.all_eq_true.mp hi j (vertices_mem j))

#check certificate


end Erdos595Paley
