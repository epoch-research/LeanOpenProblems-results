import Submission.SecondConeCliqueCover

/-!
A kernel-checked finite certificate gives the converse to the five-walk
obstruction: right^2(cone G) is K4-free exactly when G has no closed
five-step walk. This class is already countably edge-coverable.
-/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
open SimpleGraph Set
namespace Erdos595SecondConeCriterion
open Erdos595ArcAdjoint Erdos595Work Erdos595SecondConeRight
abbrev K4 := (⊤ : SimpleGraph (Fin 4))
abbrev A1 := arcGraph K4
abbrev A2 := arcGraph A1
local instance : DecidableRel A1.Adj := fun p q =>
  inferInstanceAs (Decidable (p.val.2 = q.val.1 ∨ q.val.2 = p.val.1))
local instance : DecidableRel A2.Adj := fun p q =>
  inferInstanceAs (Decidable (p.val.2 = q.val.1 ∨ q.val.2 = p.val.1))

private def raw : Fin 60 → Fin 4 → Fin 4 := ![![0, 1, 1, 0],
  ![0, 1, 1, 2],
  ![0, 1, 1, 3],
  ![0, 1, 2, 0],
  ![0, 1, 3, 0],
  ![0, 2, 1, 0],
  ![0, 2, 2, 0],
  ![0, 2, 2, 1],
  ![0, 2, 2, 3],
  ![0, 2, 3, 0],
  ![0, 3, 1, 0],
  ![0, 3, 2, 0],
  ![0, 3, 3, 0],
  ![0, 3, 3, 1],
  ![0, 3, 3, 2],
  ![1, 0, 0, 1],
  ![1, 0, 0, 2],
  ![1, 0, 0, 3],
  ![1, 0, 2, 1],
  ![1, 0, 3, 1],
  ![1, 2, 0, 1],
  ![1, 2, 2, 0],
  ![1, 2, 2, 1],
  ![1, 2, 2, 3],
  ![1, 2, 3, 1],
  ![1, 3, 0, 1],
  ![1, 3, 2, 1],
  ![1, 3, 3, 0],
  ![1, 3, 3, 1],
  ![1, 3, 3, 2],
  ![2, 0, 0, 1],
  ![2, 0, 0, 2],
  ![2, 0, 0, 3],
  ![2, 0, 1, 2],
  ![2, 0, 3, 2],
  ![2, 1, 0, 2],
  ![2, 1, 1, 0],
  ![2, 1, 1, 2],
  ![2, 1, 1, 3],
  ![2, 1, 3, 2],
  ![2, 3, 0, 2],
  ![2, 3, 1, 2],
  ![2, 3, 3, 0],
  ![2, 3, 3, 1],
  ![2, 3, 3, 2],
  ![3, 0, 0, 1],
  ![3, 0, 0, 2],
  ![3, 0, 0, 3],
  ![3, 0, 1, 3],
  ![3, 0, 2, 3],
  ![3, 1, 0, 3],
  ![3, 1, 1, 0],
  ![3, 1, 1, 2],
  ![3, 1, 1, 3],
  ![3, 1, 2, 3],
  ![3, 2, 0, 3],
  ![3, 2, 1, 3],
  ![3, 2, 2, 0],
  ![3, 2, 2, 1],
  ![3, 2, 2, 3]]
private lemma raw_valid : ∀ i : Fin 60,
    raw i 0 ≠ raw i 1 ∧ raw i 2 ≠ raw i 3 ∧
      (raw i 1 = raw i 2 ∨ raw i 3 = raw i 0) := by decide +kernel

def point (i : Fin 60) : Arc A1 :=
  ⟨(⟨(raw i 0,raw i 1),(raw_valid i).1⟩,
    ⟨(raw i 2,raw i 3),(raw_valid i).2.1⟩),(raw_valid i).2.2⟩

private def excluded : Fin 119 → Fin 60 × Fin 60 := ![(0,17), (0,18), (0,20), (0,30), (1,20), (2,45), (2,20), (2,29), (2,30), (3,32), (3,33), (3,30), (3,31), (4,20), (4,30), (5,35), (5,16), (5,18), (6,40), (7,35), (7,36), (7,39), (7,40), (7,16), (8,41), (8,43), (8,46), (8,16), (9,35), (9,46), (9,47), (9,16), (9,48), (9,49), (9,31), (10,32), (10,16), (10,18), (10,47), (10,55), (11,34), (11,17), (11,55), (11,31), (12,45), (12,55), (13,32), (13,50), (13,51), (13,52), (13,53), (14,32), (14,17), (14,55), (14,57), (16,36), (16,51), (17,51), (18,35), (18,36), (18,37), (18,39), (19,36), (19,50), (19,51), (19,53), (20,37), (20,52), (21,32), (21,41), (21,52), (21,30), (21,31), (23,37), (23,41), (23,52), (24,37), (24,41), (25,48), (25,53), (26,37), (26,38), (26,39), (26,48), (26,53), (27,38), (27,47), (27,48), (28,50), (28,52), (29,38), (29,48), (29,53), (29,57), (29,59), (33,57), (34,55), (34,57), (34,58), (34,59), (37,58), (38,58), (39,55), (39,57), (39,59), (40,49), (40,54), (40,59), (41,49), (41,54), (41,59), (42,45), (42,46), (42,47), (42,54), (42,59), (43,49), (43,50), (43,51)]
private def cycles : Fin 44 → Fin 5 → Fin 60 := ![![0, 16, 8, 41, 20],
  ![12, 32, 21, 41, 49],
  ![8, 41, 21, 52, 43],
  ![4, 46, 8, 40, 49],
  ![3, 20, 37, 21, 34],
  ![5, 18, 39, 7, 40],
  ![8, 16, 51, 18, 35],
  ![10, 19, 52, 13, 32],
  ![3, 20, 37, 21, 32],
  ![9, 40, 23, 42, 45],
  ![23, 37, 24, 53, 43],
  ![2, 25, 4, 46, 27],
  ![10, 19, 51, 13, 55],
  ![11, 31, 57, 14, 50],
  ![8, 35, 9, 48, 42],
  ![2, 25, 4, 49, 27],
  ![10, 19, 54, 13, 55],
  ![10, 19, 52, 13, 47],
  ![1, 21, 32, 3, 45],
  ![2, 20, 41, 21, 30],
  ![10, 16, 51, 43, 50],
  ![10, 18, 51, 24, 50],
  ![11, 34, 59, 14, 50],
  ![18, 38, 29, 55, 39],
  ![11, 32, 57, 29, 55],
  ![7, 16, 51, 18, 38],
  ![2, 20, 4, 48, 28],
  ![11, 17, 14, 59, 34],
  ![5, 17, 13, 53, 19],
  ![0, 16, 7, 37, 18],
  ![9, 16, 36, 18, 35],
  ![8, 35, 26, 53, 43],
  ![20, 41, 59, 43, 52],
  ![8, 31, 9, 49, 42],
  ![10, 18, 51, 13, 50],
  ![5, 17, 36, 7, 31],
  ![26, 35, 58, 29, 48],
  ![0, 18, 39, 57, 30],
  ![0, 20, 33, 21, 30],
  ![5, 19, 53, 27, 46],
  ![6, 32, 14, 55, 34],
  ![26, 39, 55, 29, 53],
  ![13, 32, 57, 29, 55],
  ![9, 35, 58, 14, 47]]
private lemma excluded_adj : ∀ i : Fin 119,
    A2.Adj (point (excluded i).1) (point (excluded i).2) := by decide +kernel
private lemma cycles_adj : ∀ i : Fin 44, ∀ j : Fin 5,
    A2.Adj (point (cycles i j)) (point (cycles i (j+1))) := by decide +kernel

/-- First clause of the explicit propositional certificate. -/
private theorem step164 (s : Fin 60 → Bool)
    (c116 : s 42 ≠ true ∨ s 59 ≠ true)
    (c111 : s 41 ≠ true ∨ s 59 ≠ true)
    (c108 : s 40 ≠ true ∨ s 59 ≠ true)
    (c100 : s 34 ≠ true ∨ s 59 ≠ true)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    (c71 : s 21 ≠ true ∨ s 52 ≠ true)
    (c76 : s 23 ≠ true ∨ s 52 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c10 : s 3 ≠ true ∨ s 32 ≠ true)
    (c12 : s 3 ≠ true ∨ s 30 ≠ true)
    (c121 : s 12 = true ∨ s 21 = true ∨ s 32 = true ∨ s 41 = true ∨ s 49 = true)
    (c139 : s 2 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 41 = true)
    (c34 : s 9 ≠ true ∨ s 49 ≠ true)
    (c6 : s 2 ≠ true ∨ s 45 ≠ true)
    (c129 : s 9 = true ∨ s 23 = true ∨ s 40 = true ∨ s 42 = true ∨ s 45 = true)
    : s 52 ≠ true ∨ s 12 = true ∨ s 37 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 42 ≠ true := (Or.elim c116 (fun h => h) (fun h => (False.elim (h a3))))
  have u1 : s 41 ≠ true := (Or.elim c111 (fun h => h) (fun h => (False.elim (h a3))))
  have u2 : s 40 ≠ true := (Or.elim c108 (fun h => h) (fun h => (False.elim (h a3))))
  have u3 : s 34 ≠ true := (Or.elim c100 (fun h => h) (fun h => (False.elim (h a3))))
  have u4 : s 20 ≠ true := (Or.elim c68 (fun h => h) (fun h => (False.elim (h a0))))
  have u5 : s 21 ≠ true := (Or.elim c71 (fun h => h) (fun h => (False.elim (h a0))))
  have u6 : s 23 ≠ true := (Or.elim c76 (fun h => h) (fun h => (False.elim (h a0))))
  have u7 : s 3 = true := (Or.elim c124 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (a2 h))))))))))
  have u8 : s 32 ≠ true := (Or.elim c10 (fun h => (False.elim (h u7))) (fun h => h))
  have u9 : s 30 ≠ true := (Or.elim c12 (fun h => (False.elim (h u7))) (fun h => h))
  have u10 : s 49 = true := (Or.elim c121 (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => h))))))))
  have u11 : s 2 = true := (Or.elim c139 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u1 h))))))))))
  have u12 : s 9 ≠ true := (Or.elim c34 (fun h => h) (fun h => (False.elim (h u10))))
  have u13 : s 45 ≠ true := (Or.elim c6 (fun h => (False.elim (h u11))) (fun h => h))
  exact (Or.elim c129 (fun h => (u12 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u13 h)))))))))

private theorem step165 (s : Fin 60 → Bool)
    (c46 : s 12 ≠ true ∨ s 55 ≠ true)
    (c164 : s 52 ≠ true ∨ s 12 = true ∨ s 37 = true ∨ s 59 ≠ true)
    (c40 : s 10 ≠ true ∨ s 55 ≠ true)
    (c111 : s 41 ≠ true ∨ s 59 ≠ true)
    (c100 : s 34 ≠ true ∨ s 59 ≠ true)
    (c51 : s 13 ≠ true ∨ s 53 ≠ true)
    (c66 : s 19 ≠ true ∨ s 53 ≠ true)
    (c80 : s 25 ≠ true ∨ s 53 ≠ true)
    (c127 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 32 = true ∨ s 52 = true)
    (c137 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 47 = true ∨ s 52 = true)
    (c10 : s 3 ≠ true ∨ s 32 ≠ true)
    (c69 : s 21 ≠ true ∨ s 32 ≠ true)
    (c87 : s 27 ≠ true ∨ s 47 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c7 : s 2 ≠ true ∨ s 20 ≠ true)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    (c131 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 46 = true)
    (c135 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 49 = true)
    (c27 : s 8 ≠ true ∨ s 46 ≠ true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    (c122 : s 8 = true ∨ s 21 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true)
    : s 53 ≠ true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 12 ≠ true := (Or.elim c46 (fun h => h) (fun h => (False.elim (h a1))))
  have u1 : s 52 ≠ true := (Or.elim c164 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (h a3))))))))
  have u2 : s 10 ≠ true := (Or.elim c40 (fun h => h) (fun h => (False.elim (h a1))))
  have u3 : s 41 ≠ true := (Or.elim c111 (fun h => h) (fun h => (False.elim (h a3))))
  have u4 : s 34 ≠ true := (Or.elim c100 (fun h => h) (fun h => (False.elim (h a3))))
  have u5 : s 13 ≠ true := (Or.elim c51 (fun h => h) (fun h => (False.elim (h a0))))
  have u6 : s 19 ≠ true := (Or.elim c66 (fun h => h) (fun h => (False.elim (h a0))))
  have u7 : s 25 ≠ true := (Or.elim c80 (fun h => h) (fun h => (False.elim (h a0))))
  have u8 : s 32 = true := (Or.elim c127 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u1 h))))))))))
  have u9 : s 47 = true := (Or.elim c137 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u1 h))))))))))
  have u10 : s 3 ≠ true := (Or.elim c10 (fun h => h) (fun h => (False.elim (h u8))))
  have u11 : s 21 ≠ true := (Or.elim c69 (fun h => h) (fun h => (False.elim (h u8))))
  have u12 : s 27 ≠ true := (Or.elim c87 (fun h => h) (fun h => (False.elim (h u9))))
  have u13 : s 20 = true := (Or.elim c124 (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (a2 h))))))))))
  have u14 : s 2 ≠ true := (Or.elim c7 (fun h => h) (fun h => (False.elim (h u13))))
  have u15 : s 4 ≠ true := (Or.elim c14 (fun h => h) (fun h => (False.elim (h u13))))
  have u16 : s 46 = true := (Or.elim c131 (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => h))))))))
  have u17 : s 49 = true := (Or.elim c135 (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => h))))))))
  have u18 : s 8 ≠ true := (Or.elim c27 (fun h => h) (fun h => (False.elim (h u16))))
  have u19 : s 43 ≠ true := (Or.elim c117 (fun h => h) (fun h => (False.elim (h u17))))
  exact (Or.elim c122 (fun h => (u18 h)) (fun h => (Or.elim h (fun h => (u11 h)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (Or.elim h (fun h => (u19 h)) (fun h => (u1 h)))))))))

private theorem step166 (s : Fin 60 → Bool)
    (c16 : s 5 ≠ true ∨ s 35 ≠ true)
    (c18 : s 5 ≠ true ∨ s 18 ≠ true)
    (c150 : s 9 = true ∨ s 16 = true ∨ s 18 = true ∨ s 35 = true ∨ s 36 = true)
    (c149 : s 0 = true ∨ s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 37 = true)
    (c21 : s 7 ≠ true ∨ s 36 ≠ true)
    : s 5 ≠ true ∨ s 16 = true ∨ s 0 = true ∨ s 9 = true ∨ s 37 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 35 ≠ true := (Or.elim c16 (fun h => (False.elim (h a0))) (fun h => h))
  have u1 : s 18 ≠ true := (Or.elim c18 (fun h => (False.elim (h a0))) (fun h => h))
  have u2 : s 36 = true := (Or.elim c150 (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => h))))))))
  have u3 : s 7 = true := (Or.elim c149 (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a4 h))))))))))
  exact (Or.elim c21 (fun h => (h u3)) (fun h => (h u2)))

private theorem step167 (s : Fin 60 → Bool)
    (c64 : s 19 ≠ true ∨ s 50 ≠ true)
    (c65 : s 19 ≠ true ∨ s 51 ≠ true)
    (c140 : s 10 = true ∨ s 16 = true ∨ s 43 = true ∨ s 50 = true ∨ s 51 = true)
    : s 19 ≠ true ∨ s 16 = true ∨ s 43 = true ∨ s 10 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 50 ≠ true := (Or.elim c64 (fun h => (False.elim (h a0))) (fun h => h))
  have u1 : s 51 ≠ true := (Or.elim c65 (fun h => (False.elim (h a0))) (fun h => h))
  exact (Or.elim c140 (fun h => (a3 h)) (fun h => (Or.elim h (fun h => (a1 h)) (fun h => (Or.elim h (fun h => (a2 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))))))

private theorem step168 (s : Fin 60 → Bool)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    (c34 : s 9 ≠ true ∨ s 49 ≠ true)
    (c165 : s 53 ≠ true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true)
    (c46 : s 12 ≠ true ∨ s 55 ≠ true)
    (c164 : s 52 ≠ true ∨ s 12 = true ∨ s 37 = true ∨ s 59 ≠ true)
    (c40 : s 10 ≠ true ∨ s 55 ≠ true)
    (c111 : s 41 ≠ true ∨ s 59 ≠ true)
    (c100 : s 34 ≠ true ∨ s 59 ≠ true)
    (c10 : s 3 ≠ true ∨ s 32 ≠ true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    (c69 : s 21 ≠ true ∨ s 32 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c122 : s 8 = true ∨ s 21 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true)
    (c3 : s 0 ≠ true ∨ s 20 ≠ true)
    (c27 : s 8 ≠ true ∨ s 46 ≠ true)
    (c28 : s 8 ≠ true ∨ s 16 ≠ true)
    (c166 : s 5 ≠ true ∨ s 16 = true ∨ s 0 = true ∨ s 9 = true ∨ s 37 = true)
    (c167 : s 19 ≠ true ∨ s 16 = true ∨ s 43 = true ∨ s 10 = true)
    (c137 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 47 = true ∨ s 52 = true)
    (c159 : s 5 = true ∨ s 19 = true ∨ s 27 = true ∨ s 46 = true ∨ s 53 = true)
    (c87 : s 27 ≠ true ∨ s 47 ≠ true)
    : s 32 ≠ true ∨ s 49 ≠ true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 43 ≠ true := (Or.elim c117 (fun h => h) (fun h => (False.elim (h a1))))
  have u1 : s 9 ≠ true := (Or.elim c34 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 53 ≠ true := (Or.elim c165 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a2))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (h a4))))))))
  have u3 : s 12 ≠ true := (Or.elim c46 (fun h => h) (fun h => (False.elim (h a2))))
  have u4 : s 52 ≠ true := (Or.elim c164 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (h a4))))))))
  have u5 : s 10 ≠ true := (Or.elim c40 (fun h => h) (fun h => (False.elim (h a2))))
  have u6 : s 41 ≠ true := (Or.elim c111 (fun h => h) (fun h => (False.elim (h a4))))
  have u7 : s 34 ≠ true := (Or.elim c100 (fun h => h) (fun h => (False.elim (h a4))))
  have u8 : s 3 ≠ true := (Or.elim c10 (fun h => h) (fun h => (False.elim (h a0))))
  have u9 : s 13 ≠ true := (Or.elim c47 (fun h => h) (fun h => (False.elim (h a0))))
  have u10 : s 21 ≠ true := (Or.elim c69 (fun h => h) (fun h => (False.elim (h a0))))
  have u11 : s 20 = true := (Or.elim c124 (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (a3 h))))))))))
  have u12 : s 8 = true := (Or.elim c122 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (u4 h))))))))))
  have u13 : s 0 ≠ true := (Or.elim c3 (fun h => h) (fun h => (False.elim (h u11))))
  have u14 : s 46 ≠ true := (Or.elim c27 (fun h => (False.elim (h u12))) (fun h => h))
  have u15 : s 16 ≠ true := (Or.elim c28 (fun h => (False.elim (h u12))) (fun h => h))
  have u16 : s 5 ≠ true := (Or.elim c166 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a3 h))))))))))
  have u17 : s 19 ≠ true := (Or.elim c167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (u5 h))))))))
  have u18 : s 47 = true := (Or.elim c137 (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u4 h))))))))))
  have u19 : s 27 = true := (Or.elim c159 (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (u2 h))))))))))
  exact (Or.elim c87 (fun h => (h u19)) (fun h => (h u18)))

private theorem step169 (s : Fin 60 → Bool)
    (c116 : s 42 ≠ true ∨ s 59 ≠ true)
    (c108 : s 40 ≠ true ∨ s 59 ≠ true)
    (c105 : s 39 ≠ true ∨ s 59 ≠ true)
    (c17 : s 5 ≠ true ∨ s 16 ≠ true)
    (c24 : s 7 ≠ true ∨ s 16 ≠ true)
    (c28 : s 8 ≠ true ∨ s 16 ≠ true)
    (c125 : s 5 = true ∨ s 7 = true ∨ s 18 = true ∨ s 39 = true ∨ s 40 = true)
    (c134 : s 8 = true ∨ s 9 = true ∨ s 35 = true ∨ s 42 = true ∨ s 48 = true)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    : s 16 ≠ true ∨ s 48 = true ∨ s 9 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 42 ≠ true := (Or.elim c116 (fun h => h) (fun h => (False.elim (h a3))))
  have u1 : s 40 ≠ true := (Or.elim c108 (fun h => h) (fun h => (False.elim (h a3))))
  have u2 : s 39 ≠ true := (Or.elim c105 (fun h => h) (fun h => (False.elim (h a3))))
  have u3 : s 5 ≠ true := (Or.elim c17 (fun h => h) (fun h => (False.elim (h a0))))
  have u4 : s 7 ≠ true := (Or.elim c24 (fun h => h) (fun h => (False.elim (h a0))))
  have u5 : s 8 ≠ true := (Or.elim c28 (fun h => h) (fun h => (False.elim (h a0))))
  have u6 : s 18 = true := (Or.elim c125 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u1 h))))))))))
  have u7 : s 35 = true := (Or.elim c134 (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (a1 h))))))))))
  exact (Or.elim c59 (fun h => (h u6)) (fun h => (h u7)))

private theorem step170 (s : Fin 60 → Bool)
    (c167 : s 19 ≠ true ∨ s 16 = true ∨ s 43 = true ∨ s 10 = true)
    (c127 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 32 = true ∨ s 52 = true)
    (c48 : s 13 ≠ true ∨ s 50 ≠ true)
    (c49 : s 13 ≠ true ∨ s 51 ≠ true)
    (c140 : s 10 = true ∨ s 16 = true ∨ s 43 = true ∨ s 50 = true ∨ s 51 = true)
    : s 16 = true ∨ s 32 = true ∨ s 43 = true ∨ s 52 = true ∨ s 10 = true := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 19 ≠ true := (Or.elim c167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (a4 h))))))))
  have u1 : s 13 = true := (Or.elim c127 (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (a3 h))))))))))
  have u2 : s 50 ≠ true := (Or.elim c48 (fun h => (False.elim (h u1))) (fun h => h))
  have u3 : s 51 ≠ true := (Or.elim c49 (fun h => (False.elim (h u1))) (fun h => h))
  exact (Or.elim c140 (fun h => (a4 h)) (fun h => (Or.elim h (fun h => (a0 h)) (fun h => (Or.elim h (fun h => (a2 h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (u3 h)))))))))

private theorem step171 (s : Fin 60 → Bool)
    (c165 : s 53 ≠ true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true)
    (c46 : s 12 ≠ true ∨ s 55 ≠ true)
    (c164 : s 52 ≠ true ∨ s 12 = true ∨ s 37 = true ∨ s 59 ≠ true)
    (c40 : s 10 ≠ true ∨ s 55 ≠ true)
    (c108 : s 40 ≠ true ∨ s 59 ≠ true)
    (c105 : s 39 ≠ true ∨ s 59 ≠ true)
    (c34 : s 9 ≠ true ∨ s 49 ≠ true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    (c168 : s 32 ≠ true ∨ s 49 ≠ true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true)
    (c170 : s 16 = true ∨ s 32 = true ∨ s 43 = true ∨ s 52 = true ∨ s 10 = true)
    (c17 : s 5 ≠ true ∨ s 16 ≠ true)
    (c24 : s 7 ≠ true ∨ s 16 ≠ true)
    (c28 : s 8 ≠ true ∨ s 16 ≠ true)
    (c169 : s 16 ≠ true ∨ s 48 = true ∨ s 9 = true ∨ s 59 ≠ true)
    (c125 : s 5 = true ∨ s 7 = true ∨ s 18 = true ∨ s 39 = true ∨ s 40 = true)
    (c84 : s 26 ≠ true ∨ s 48 ≠ true)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    (c151 : s 8 = true ∨ s 26 = true ∨ s 35 = true ∨ s 43 = true ∨ s 53 = true)
    : s 49 ≠ true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 53 ≠ true := (Or.elim c165 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a1))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (h a3))))))))
  have u1 : s 12 ≠ true := (Or.elim c46 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 52 ≠ true := (Or.elim c164 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (h a3))))))))
  have u3 : s 10 ≠ true := (Or.elim c40 (fun h => h) (fun h => (False.elim (h a1))))
  have u4 : s 40 ≠ true := (Or.elim c108 (fun h => h) (fun h => (False.elim (h a3))))
  have u5 : s 39 ≠ true := (Or.elim c105 (fun h => h) (fun h => (False.elim (h a3))))
  have u6 : s 9 ≠ true := (Or.elim c34 (fun h => h) (fun h => (False.elim (h a0))))
  have u7 : s 43 ≠ true := (Or.elim c117 (fun h => h) (fun h => (False.elim (h a0))))
  have u8 : s 32 ≠ true := (Or.elim c168 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => (False.elim (h a1))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (h a3))))))))))
  have u9 : s 16 = true := (Or.elim c170 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u3 h))))))))))
  have u10 : s 5 ≠ true := (Or.elim c17 (fun h => h) (fun h => (False.elim (h u9))))
  have u11 : s 7 ≠ true := (Or.elim c24 (fun h => h) (fun h => (False.elim (h u9))))
  have u12 : s 8 ≠ true := (Or.elim c28 (fun h => h) (fun h => (False.elim (h u9))))
  have u13 : s 48 = true := (Or.elim c169 (fun h => (False.elim (h u9))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (h a3))))))))
  have u14 : s 18 = true := (Or.elim c125 (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u4 h))))))))))
  have u15 : s 26 ≠ true := (Or.elim c84 (fun h => h) (fun h => (False.elim (h u13))))
  have u16 : s 35 ≠ true := (Or.elim c59 (fun h => (False.elim (h u14))) (fun h => h))
  exact (Or.elim c151 (fun h => (u12 h)) (fun h => (Or.elim h (fun h => (u15 h)) (fun h => (Or.elim h (fun h => (u16 h)) (fun h => (Or.elim h (fun h => (u7 h)) (fun h => (u0 h)))))))))

private theorem step172 (s : Fin 60 → Bool)
    (c116 : s 42 ≠ true ∨ s 59 ≠ true)
    (c100 : s 34 ≠ true ∨ s 59 ≠ true)
    (c28 : s 8 ≠ true ∨ s 16 ≠ true)
    (c32 : s 9 ≠ true ∨ s 16 ≠ true)
    (c169 : s 16 ≠ true ∨ s 48 = true ∨ s 9 = true ∨ s 59 ≠ true)
    (c153 : s 8 = true ∨ s 9 = true ∨ s 31 = true ∨ s 42 = true ∨ s 49 = true)
    (c79 : s 25 ≠ true ∨ s 48 ≠ true)
    (c88 : s 27 ≠ true ∨ s 48 ≠ true)
    (c13 : s 3 ≠ true ∨ s 31 ≠ true)
    (c73 : s 21 ≠ true ∨ s 31 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c7 : s 2 ≠ true ∨ s 20 ≠ true)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    (c135 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 49 = true)
    : s 16 ≠ true ∨ s 49 = true ∨ s 37 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 42 ≠ true := (Or.elim c116 (fun h => h) (fun h => (False.elim (h a3))))
  have u1 : s 34 ≠ true := (Or.elim c100 (fun h => h) (fun h => (False.elim (h a3))))
  have u2 : s 8 ≠ true := (Or.elim c28 (fun h => h) (fun h => (False.elim (h a0))))
  have u3 : s 9 ≠ true := (Or.elim c32 (fun h => h) (fun h => (False.elim (h a0))))
  have u4 : s 48 = true := (Or.elim c169 (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (h a3))))))))
  have u5 : s 31 = true := (Or.elim c153 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (a1 h))))))))))
  have u6 : s 25 ≠ true := (Or.elim c79 (fun h => h) (fun h => (False.elim (h u4))))
  have u7 : s 27 ≠ true := (Or.elim c88 (fun h => h) (fun h => (False.elim (h u4))))
  have u8 : s 3 ≠ true := (Or.elim c13 (fun h => h) (fun h => (False.elim (h u5))))
  have u9 : s 21 ≠ true := (Or.elim c73 (fun h => h) (fun h => (False.elim (h u5))))
  have u10 : s 20 = true := (Or.elim c124 (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a2 h))))))))))
  have u11 : s 2 ≠ true := (Or.elim c7 (fun h => h) (fun h => (False.elim (h u10))))
  have u12 : s 4 ≠ true := (Or.elim c14 (fun h => h) (fun h => (False.elim (h u10))))
  exact (Or.elim c135 (fun h => (u11 h)) (fun h => (Or.elim h (fun h => (u12 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (u7 h)) (fun h => (a1 h)))))))))

private theorem step173 (s : Fin 60 → Bool)
    (c88 : s 27 ≠ true ∨ s 48 ≠ true)
    (c79 : s 25 ≠ true ∨ s 48 ≠ true)
    (c7 : s 2 ≠ true ∨ s 20 ≠ true)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    (c135 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 49 = true)
    : s 20 ≠ true ∨ s 48 ≠ true ∨ s 49 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 27 ≠ true := (Or.elim c88 (fun h => h) (fun h => (False.elim (h a1))))
  have u1 : s 25 ≠ true := (Or.elim c79 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 2 ≠ true := (Or.elim c7 (fun h => h) (fun h => (False.elim (h a0))))
  have u3 : s 4 ≠ true := (Or.elim c14 (fun h => h) (fun h => (False.elim (h a0))))
  exact (Or.elim c135 (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (a2 h)))))))))

private theorem step174 (s : Fin 60 → Bool)
    (c171 : s 49 ≠ true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true)
    (c46 : s 12 ≠ true ∨ s 55 ≠ true)
    (c111 : s 41 ≠ true ∨ s 59 ≠ true)
    (c100 : s 34 ≠ true ∨ s 59 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c121 : s 12 = true ∨ s 21 = true ∨ s 32 = true ∨ s 41 = true ∨ s 49 = true)
    (c10 : s 3 ≠ true ∨ s 32 ≠ true)
    : s 21 = true ∨ s 20 = true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 49 ≠ true := (Or.elim c171 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a2))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (h a4))))))))
  have u1 : s 12 ≠ true := (Or.elim c46 (fun h => h) (fun h => (False.elim (h a2))))
  have u2 : s 41 ≠ true := (Or.elim c111 (fun h => h) (fun h => (False.elim (h a4))))
  have u3 : s 34 ≠ true := (Or.elim c100 (fun h => h) (fun h => (False.elim (h a4))))
  have u4 : s 3 = true := (Or.elim c124 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (a3 h))))))))))
  have u5 : s 32 = true := (Or.elim c121 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u0 h))))))))))
  exact (Or.elim c10 (fun h => (h u4)) (fun h => (h u5)))

private theorem step175 (s : Fin 60 → Bool)
    (c69 : s 21 ≠ true ∨ s 32 ≠ true)
    (c73 : s 21 ≠ true ∨ s 31 ≠ true)
    (c170 : s 16 = true ∨ s 32 = true ∨ s 43 = true ∨ s 52 = true ∨ s 10 = true)
    (c153 : s 8 = true ∨ s 9 = true ∨ s 31 = true ∨ s 42 = true ∨ s 49 = true)
    (c26 : s 8 ≠ true ∨ s 43 ≠ true)
    : s 21 ≠ true ∨ s 9 = true ∨ s 16 = true ∨ s 49 = true ∨ s 52 = true ∨ s 10 = true ∨ s 42 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6⟩ := hc
  have u0 : s 32 ≠ true := (Or.elim c69 (fun h => (False.elim (h a0))) (fun h => h))
  have u1 : s 31 ≠ true := (Or.elim c73 (fun h => (False.elim (h a0))) (fun h => h))
  have u2 : s 43 = true := (Or.elim c170 (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (False.elim (a5 h))))))))))
  have u3 : s 8 = true := (Or.elim c153 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a6 h))) (fun h => (False.elim (a3 h))))))))))
  exact (Or.elim c26 (fun h => (h u3)) (fun h => (h u2)))

private theorem step176 (s : Fin 60 → Bool)
    (c26 : s 8 ≠ true ∨ s 43 ≠ true)
    (c27 : s 8 ≠ true ∨ s 46 ≠ true)
    (c167 : s 19 ≠ true ∨ s 16 = true ∨ s 43 = true ∨ s 10 = true)
    (c137 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 47 = true ∨ s 52 = true)
    (c159 : s 5 = true ∨ s 19 = true ∨ s 27 = true ∨ s 46 = true ∨ s 53 = true)
    (c87 : s 27 ≠ true ∨ s 47 ≠ true)
    : s 8 ≠ true ∨ s 5 = true ∨ s 13 = true ∨ s 16 = true ∨ s 53 = true ∨ s 52 = true ∨ s 10 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6⟩ := hc
  have u0 : s 43 ≠ true := (Or.elim c26 (fun h => (False.elim (h a0))) (fun h => h))
  have u1 : s 46 ≠ true := (Or.elim c27 (fun h => (False.elim (h a0))) (fun h => h))
  have u2 : s 19 ≠ true := (Or.elim c167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (a6 h))))))))
  have u3 : s 47 = true := (Or.elim c137 (fun h => (False.elim (a6 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a5 h))))))))))
  have u4 : s 27 = true := (Or.elim c159 (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a4 h))))))))))
  exact (Or.elim c87 (fun h => (h u4)) (fun h => (h u3)))

private theorem step177 (s : Fin 60 → Bool)
    (c171 : s 49 ≠ true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true)
    (c172 : s 16 ≠ true ∨ s 49 = true ∨ s 37 = true ∨ s 59 ≠ true)
    (c165 : s 53 ≠ true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true)
    (c46 : s 12 ≠ true ∨ s 55 ≠ true)
    (c164 : s 52 ≠ true ∨ s 12 = true ∨ s 37 = true ∨ s 59 ≠ true)
    (c40 : s 10 ≠ true ∨ s 55 ≠ true)
    (c116 : s 42 ≠ true ∨ s 59 ≠ true)
    (c111 : s 41 ≠ true ∨ s 59 ≠ true)
    (c175 : s 21 ≠ true ∨ s 9 = true ∨ s 16 = true ∨ s 49 = true ∨ s 52 = true ∨ s 10 = true ∨ s 42 = true)
    (c121 : s 12 = true ∨ s 21 = true ∨ s 32 = true ∨ s 41 = true ∨ s 49 = true)
    (c174 : s 21 = true ∨ s 20 = true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    (c3 : s 0 ≠ true ∨ s 20 ≠ true)
    (c173 : s 20 ≠ true ∨ s 48 ≠ true ∨ s 49 = true)
    (c166 : s 5 ≠ true ∨ s 16 = true ∨ s 0 = true ∨ s 9 = true ∨ s 37 = true)
    (c176 : s 8 ≠ true ∨ s 5 = true ∨ s 13 = true ∨ s 16 = true ∨ s 53 = true ∨ s 52 = true ∨ s 10 = true)
    (c134 : s 8 = true ∨ s 9 = true ∨ s 35 = true ∨ s 42 = true ∨ s 48 = true)
    (c20 : s 7 ≠ true ∨ s 35 ≠ true)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    (c149 : s 0 = true ∨ s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 37 = true)
    : s 9 = true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 49 ≠ true := (Or.elim c171 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a1))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (h a3))))))))
  have u1 : s 16 ≠ true := (Or.elim c172 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (h a3))))))))
  have u2 : s 53 ≠ true := (Or.elim c165 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a1))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (h a3))))))))
  have u3 : s 12 ≠ true := (Or.elim c46 (fun h => h) (fun h => (False.elim (h a1))))
  have u4 : s 52 ≠ true := (Or.elim c164 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (h a3))))))))
  have u5 : s 10 ≠ true := (Or.elim c40 (fun h => h) (fun h => (False.elim (h a1))))
  have u6 : s 42 ≠ true := (Or.elim c116 (fun h => h) (fun h => (False.elim (h a3))))
  have u7 : s 41 ≠ true := (Or.elim c111 (fun h => h) (fun h => (False.elim (h a3))))
  have u8 : s 21 ≠ true := (Or.elim c175 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u6 h))))))))))))))
  have u9 : s 32 = true := (Or.elim c121 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u0 h))))))))))
  have u10 : s 20 = true := (Or.elim c174 (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a1))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (h a3))))))))))
  have u11 : s 13 ≠ true := (Or.elim c47 (fun h => h) (fun h => (False.elim (h u9))))
  have u12 : s 0 ≠ true := (Or.elim c3 (fun h => h) (fun h => (False.elim (h u10))))
  have u13 : s 48 ≠ true := (Or.elim c173 (fun h => (False.elim (h u10))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))
  have u14 : s 5 ≠ true := (Or.elim c166 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a2 h))))))))))
  have u15 : s 8 ≠ true := (Or.elim c176 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u5 h))))))))))))))
  have u16 : s 35 = true := (Or.elim c134 (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u13 h))))))))))
  have u17 : s 7 ≠ true := (Or.elim c20 (fun h => h) (fun h => (False.elim (h u16))))
  have u18 : s 18 ≠ true := (Or.elim c59 (fun h => h) (fun h => (False.elim (h u16))))
  exact (Or.elim c149 (fun h => (u12 h)) (fun h => (Or.elim h (fun h => (u17 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u18 h)) (fun h => (a2 h)))))))))

private theorem step178 (s : Fin 60 → Bool)
    (c177 : s 9 = true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true)
    (c31 : s 9 ≠ true ∨ s 47 ≠ true)
    (c30 : s 9 ≠ true ∨ s 46 ≠ true)
    (c171 : s 49 ≠ true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true)
    (c172 : s 16 ≠ true ∨ s 49 = true ∨ s 37 = true ∨ s 59 ≠ true)
    (c46 : s 12 ≠ true ∨ s 55 ≠ true)
    (c164 : s 52 ≠ true ∨ s 12 = true ∨ s 37 = true ∨ s 59 ≠ true)
    (c40 : s 10 ≠ true ∨ s 55 ≠ true)
    (c108 : s 40 ≠ true ∨ s 59 ≠ true)
    (c100 : s 34 ≠ true ∨ s 59 ≠ true)
    (c10 : s 3 ≠ true ∨ s 32 ≠ true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    (c69 : s 21 ≠ true ∨ s 32 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c137 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 47 = true ∨ s 52 = true)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    (c167 : s 19 ≠ true ∨ s 16 = true ∨ s 43 = true ∨ s 10 = true)
    (c123 : s 4 = true ∨ s 8 = true ∨ s 40 = true ∨ s 46 = true ∨ s 49 = true)
    (c26 : s 8 ≠ true ∨ s 43 ≠ true)
    : s 32 ≠ true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 9 = true := (Or.elim c177 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a1))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (h a3))))))))
  have u1 : s 47 ≠ true := (Or.elim c31 (fun h => (False.elim (h u0))) (fun h => h))
  have u2 : s 46 ≠ true := (Or.elim c30 (fun h => (False.elim (h u0))) (fun h => h))
  have u3 : s 49 ≠ true := (Or.elim c171 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a1))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (h a3))))))))
  have u4 : s 16 ≠ true := (Or.elim c172 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (h a3))))))))
  have u5 : s 12 ≠ true := (Or.elim c46 (fun h => h) (fun h => (False.elim (h a1))))
  have u6 : s 52 ≠ true := (Or.elim c164 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (h a3))))))))
  have u7 : s 10 ≠ true := (Or.elim c40 (fun h => h) (fun h => (False.elim (h a1))))
  have u8 : s 40 ≠ true := (Or.elim c108 (fun h => h) (fun h => (False.elim (h a3))))
  have u9 : s 34 ≠ true := (Or.elim c100 (fun h => h) (fun h => (False.elim (h a3))))
  have u10 : s 3 ≠ true := (Or.elim c10 (fun h => h) (fun h => (False.elim (h a0))))
  have u11 : s 13 ≠ true := (Or.elim c47 (fun h => h) (fun h => (False.elim (h a0))))
  have u12 : s 21 ≠ true := (Or.elim c69 (fun h => h) (fun h => (False.elim (h a0))))
  have u13 : s 20 = true := (Or.elim c124 (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (a2 h))))))))))
  have u14 : s 19 = true := (Or.elim c137 (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u6 h))))))))))
  have u15 : s 4 ≠ true := (Or.elim c14 (fun h => h) (fun h => (False.elim (h u13))))
  have u16 : s 43 = true := (Or.elim c167 (fun h => (False.elim (h u14))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u7 h))))))))
  have u17 : s 8 = true := (Or.elim c123 (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u3 h))))))))))
  exact (Or.elim c26 (fun h => (h u17)) (fun h => (h u16)))

private theorem step179 (s : Fin 60 → Bool)
    (c111 : s 41 ≠ true ∨ s 59 ≠ true)
    (c108 : s 40 ≠ true ∨ s 59 ≠ true)
    (c40 : s 10 ≠ true ∨ s 55 ≠ true)
    (c46 : s 12 ≠ true ∨ s 55 ≠ true)
    (c164 : s 52 ≠ true ∨ s 12 = true ∨ s 37 = true ∨ s 59 ≠ true)
    (c171 : s 49 ≠ true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true)
    (c172 : s 16 ≠ true ∨ s 49 = true ∨ s 37 = true ∨ s 59 ≠ true)
    (c177 : s 9 = true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true)
    (c29 : s 9 ≠ true ∨ s 35 ≠ true)
    (c30 : s 9 ≠ true ∨ s 46 ≠ true)
    (c178 : s 32 ≠ true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true)
    (c170 : s 16 = true ∨ s 32 = true ∨ s 43 = true ∨ s 52 = true ∨ s 10 = true)
    (c26 : s 8 ≠ true ∨ s 43 ≠ true)
    (c119 : s 43 ≠ true ∨ s 51 ≠ true)
    (c123 : s 4 = true ∨ s 8 = true ∨ s 40 = true ∨ s 46 = true ∨ s 49 = true)
    (c126 : s 8 = true ∨ s 16 = true ∨ s 18 = true ∨ s 35 = true ∨ s 51 = true)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    (c2 : s 0 ≠ true ∨ s 18 ≠ true)
    (c120 : s 0 = true ∨ s 8 = true ∨ s 16 = true ∨ s 20 = true ∨ s 41 = true)
    : s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 41 ≠ true := (Or.elim c111 (fun h => h) (fun h => (False.elim (h a2))))
  have u1 : s 40 ≠ true := (Or.elim c108 (fun h => h) (fun h => (False.elim (h a2))))
  have u2 : s 10 ≠ true := (Or.elim c40 (fun h => h) (fun h => (False.elim (h a0))))
  have u3 : s 12 ≠ true := (Or.elim c46 (fun h => h) (fun h => (False.elim (h a0))))
  have u4 : s 52 ≠ true := (Or.elim c164 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (h a2))))))))
  have u5 : s 49 ≠ true := (Or.elim c171 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (h a2))))))))
  have u6 : s 16 ≠ true := (Or.elim c172 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (h a2))))))))
  have u7 : s 9 = true := (Or.elim c177 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (h a2))))))))
  have u8 : s 35 ≠ true := (Or.elim c29 (fun h => (False.elim (h u7))) (fun h => h))
  have u9 : s 46 ≠ true := (Or.elim c30 (fun h => (False.elim (h u7))) (fun h => h))
  have u10 : s 32 ≠ true := (Or.elim c178 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (h a2))))))))
  have u11 : s 43 = true := (Or.elim c170 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))))))
  have u12 : s 8 ≠ true := (Or.elim c26 (fun h => h) (fun h => (False.elim (h u11))))
  have u13 : s 51 ≠ true := (Or.elim c119 (fun h => (False.elim (h u11))) (fun h => h))
  have u14 : s 4 = true := (Or.elim c123 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u5 h))))))))))
  have u15 : s 18 = true := (Or.elim c126 (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u13 h))))))))))
  have u16 : s 20 ≠ true := (Or.elim c14 (fun h => (False.elim (h u14))) (fun h => h))
  have u17 : s 0 ≠ true := (Or.elim c2 (fun h => h) (fun h => (False.elim (h u15))))
  exact (Or.elim c120 (fun h => (u17 h)) (fun h => (Or.elim h (fun h => (u12 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (u16 h)) (fun h => (u0 h)))))))))

private theorem step180 (s : Fin 60 → Bool)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    (c2 : s 0 ≠ true ∨ s 18 ≠ true)
    (c116 : s 42 ≠ true ∨ s 59 ≠ true)
    (c111 : s 41 ≠ true ∨ s 59 ≠ true)
    (c108 : s 40 ≠ true ∨ s 59 ≠ true)
    (c120 : s 0 = true ∨ s 8 = true ∨ s 16 = true ∨ s 20 = true ∨ s 41 = true)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    (c173 : s 20 ≠ true ∨ s 48 ≠ true ∨ s 49 = true)
    (c123 : s 4 = true ∨ s 8 = true ∨ s 40 = true ∨ s 46 = true ∨ s 49 = true)
    (c134 : s 8 = true ∨ s 9 = true ∨ s 35 = true ∨ s 42 = true ∨ s 48 = true)
    (c30 : s 9 ≠ true ∨ s 46 ≠ true)
    : s 8 = true ∨ s 16 = true ∨ s 49 = true ∨ s 18 ≠ true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 35 ≠ true := (Or.elim c59 (fun h => (False.elim (h a3))) (fun h => h))
  have u1 : s 0 ≠ true := (Or.elim c2 (fun h => h) (fun h => (False.elim (h a3))))
  have u2 : s 42 ≠ true := (Or.elim c116 (fun h => h) (fun h => (False.elim (h a4))))
  have u3 : s 41 ≠ true := (Or.elim c111 (fun h => h) (fun h => (False.elim (h a4))))
  have u4 : s 40 ≠ true := (Or.elim c108 (fun h => h) (fun h => (False.elim (h a4))))
  have u5 : s 20 = true := (Or.elim c120 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u3 h))))))))))
  have u6 : s 4 ≠ true := (Or.elim c14 (fun h => h) (fun h => (False.elim (h u5))))
  have u7 : s 48 ≠ true := (Or.elim c173 (fun h => (False.elim (h u5))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a2 h))))))
  have u8 : s 46 = true := (Or.elim c123 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a2 h))))))))))
  have u9 : s 9 = true := (Or.elim c134 (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u7 h))))))))))
  exact (Or.elim c30 (fun h => (h u9)) (fun h => (h u8)))

private theorem step181 (s : Fin 60 → Bool)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    (c71 : s 21 ≠ true ∨ s 52 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c158 : s 0 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 33 = true)
    (c12 : s 3 ≠ true ∨ s 30 ≠ true)
    : s 52 ≠ true ∨ s 33 = true ∨ s 0 = true ∨ s 37 = true ∨ s 34 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 20 ≠ true := (Or.elim c68 (fun h => h) (fun h => (False.elim (h a0))))
  have u1 : s 21 ≠ true := (Or.elim c71 (fun h => h) (fun h => (False.elim (h a0))))
  have u2 : s 3 = true := (Or.elim c124 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (False.elim (a3 h))))))))))
  have u3 : s 30 = true := (Or.elim c158 (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a1 h))))))))))
  exact (Or.elim c12 (fun h => (h u2)) (fun h => (h u3)))

private theorem step182 (s : Fin 60 → Bool)
    (c95 : s 29 ≠ true ∨ s 59 ≠ true)
    (c105 : s 39 ≠ true ∨ s 59 ≠ true)
    (c102 : s 38 ≠ true ∨ s 58 ≠ true)
    (c101 : s 37 ≠ true ∨ s 58 ≠ true)
    (c179 : s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true)
    (c143 : s 18 = true ∨ s 29 = true ∨ s 38 = true ∨ s 39 = true ∨ s 55 = true)
    (c38 : s 10 ≠ true ∨ s 18 ≠ true)
    (c18 : s 5 ≠ true ∨ s 18 ≠ true)
    (c100 : s 34 ≠ true ∨ s 59 ≠ true)
    (c172 : s 16 ≠ true ∨ s 49 = true ∨ s 37 = true ∨ s 59 ≠ true)
    (c180 : s 8 = true ∨ s 16 = true ∨ s 49 = true ∨ s 18 ≠ true ∨ s 59 ≠ true)
    (c26 : s 8 ≠ true ∨ s 43 ≠ true)
    (c167 : s 19 ≠ true ∨ s 16 = true ∨ s 43 = true ∨ s 10 = true)
    (c170 : s 16 = true ∨ s 32 = true ∨ s 43 = true ∨ s 52 = true ∨ s 10 = true)
    (c10 : s 3 ≠ true ∨ s 32 ≠ true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    (c69 : s 21 ≠ true ∨ s 32 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c137 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 47 = true ∨ s 52 = true)
    (c176 : s 8 ≠ true ∨ s 5 = true ∨ s 13 = true ∨ s 16 = true ∨ s 53 = true ∨ s 52 = true ∨ s 10 = true)
    (c7 : s 2 ≠ true ∨ s 20 ≠ true)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    (c87 : s 27 ≠ true ∨ s 47 ≠ true)
    (c80 : s 25 ≠ true ∨ s 53 ≠ true)
    (c135 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 49 = true)
    : s 49 = true ∨ s 52 = true ∨ s 58 ≠ true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 29 ≠ true := (Or.elim c95 (fun h => h) (fun h => (False.elim (h a3))))
  have u1 : s 39 ≠ true := (Or.elim c105 (fun h => h) (fun h => (False.elim (h a3))))
  have u2 : s 38 ≠ true := (Or.elim c102 (fun h => h) (fun h => (False.elim (h a2))))
  have u3 : s 37 ≠ true := (Or.elim c101 (fun h => h) (fun h => (False.elim (h a2))))
  have u4 : s 55 ≠ true := (Or.elim c179 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (h a3))))))
  have u5 : s 18 = true := (Or.elim c143 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u4 h))))))))))
  have u6 : s 10 ≠ true := (Or.elim c38 (fun h => h) (fun h => (False.elim (h u5))))
  have u7 : s 5 ≠ true := (Or.elim c18 (fun h => h) (fun h => (False.elim (h u5))))
  have u8 : s 34 ≠ true := (Or.elim c100 (fun h => h) (fun h => (False.elim (h a3))))
  have u9 : s 16 ≠ true := (Or.elim c172 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (h a3))))))))
  have u10 : s 8 = true := (Or.elim c180 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (h u5))) (fun h => (False.elim (h a3))))))))))
  have u11 : s 43 ≠ true := (Or.elim c26 (fun h => (False.elim (h u10))) (fun h => h))
  have u12 : s 19 ≠ true := (Or.elim c167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u6 h))))))))
  have u13 : s 32 = true := (Or.elim c170 (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u6 h))))))))))
  have u14 : s 3 ≠ true := (Or.elim c10 (fun h => h) (fun h => (False.elim (h u13))))
  have u15 : s 13 ≠ true := (Or.elim c47 (fun h => h) (fun h => (False.elim (h u13))))
  have u16 : s 21 ≠ true := (Or.elim c69 (fun h => h) (fun h => (False.elim (h u13))))
  have u17 : s 20 = true := (Or.elim c124 (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u3 h))))))))))
  have u18 : s 47 = true := (Or.elim c137 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a1 h))))))))))
  have u19 : s 53 = true := (Or.elim c176 (fun h => (False.elim (h u10))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u6 h))))))))))))))
  have u20 : s 2 ≠ true := (Or.elim c7 (fun h => h) (fun h => (False.elim (h u17))))
  have u21 : s 4 ≠ true := (Or.elim c14 (fun h => h) (fun h => (False.elim (h u17))))
  have u22 : s 27 ≠ true := (Or.elim c87 (fun h => h) (fun h => (False.elim (h u18))))
  have u23 : s 25 ≠ true := (Or.elim c80 (fun h => h) (fun h => (False.elim (h u19))))
  exact (Or.elim c135 (fun h => (u20 h)) (fun h => (Or.elim h (fun h => (u21 h)) (fun h => (Or.elim h (fun h => (u23 h)) (fun h => (Or.elim h (fun h => (u22 h)) (fun h => (a0 h)))))))))

private theorem step183 (s : Fin 60 → Bool)
    (c182 : s 49 = true ∨ s 52 = true ∨ s 58 ≠ true ∨ s 59 ≠ true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    (c95 : s 29 ≠ true ∨ s 59 ≠ true)
    (c105 : s 39 ≠ true ∨ s 59 ≠ true)
    (c102 : s 38 ≠ true ∨ s 58 ≠ true)
    (c101 : s 37 ≠ true ∨ s 58 ≠ true)
    (c179 : s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true)
    (c143 : s 18 = true ∨ s 29 = true ∨ s 38 = true ∨ s 39 = true ∨ s 55 = true)
    (c38 : s 10 ≠ true ∨ s 18 ≠ true)
    (c18 : s 5 ≠ true ∨ s 18 ≠ true)
    (c111 : s 41 ≠ true ∨ s 59 ≠ true)
    (c100 : s 34 ≠ true ∨ s 59 ≠ true)
    (c167 : s 19 ≠ true ∨ s 16 = true ∨ s 43 = true ∨ s 10 = true)
    (c170 : s 16 = true ∨ s 32 = true ∨ s 43 = true ∨ s 52 = true ∨ s 10 = true)
    (c10 : s 3 ≠ true ∨ s 32 ≠ true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    (c69 : s 21 ≠ true ∨ s 32 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c137 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 47 = true ∨ s 52 = true)
    (c122 : s 8 = true ∨ s 21 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true)
    (c7 : s 2 ≠ true ∨ s 20 ≠ true)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    (c87 : s 27 ≠ true ∨ s 47 ≠ true)
    (c27 : s 8 ≠ true ∨ s 46 ≠ true)
    (c176 : s 8 ≠ true ∨ s 5 = true ∨ s 13 = true ∨ s 16 = true ∨ s 53 = true ∨ s 52 = true ∨ s 10 = true)
    (c131 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 46 = true)
    (c80 : s 25 ≠ true ∨ s 53 ≠ true)
    : s 16 = true ∨ s 52 = true ∨ s 58 ≠ true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 49 = true := (Or.elim c182 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (h a2))) (fun h => (False.elim (h a3))))))))
  have u1 : s 43 ≠ true := (Or.elim c117 (fun h => h) (fun h => (False.elim (h u0))))
  have u2 : s 29 ≠ true := (Or.elim c95 (fun h => h) (fun h => (False.elim (h a3))))
  have u3 : s 39 ≠ true := (Or.elim c105 (fun h => h) (fun h => (False.elim (h a3))))
  have u4 : s 38 ≠ true := (Or.elim c102 (fun h => h) (fun h => (False.elim (h a2))))
  have u5 : s 37 ≠ true := (Or.elim c101 (fun h => h) (fun h => (False.elim (h a2))))
  have u6 : s 55 ≠ true := (Or.elim c179 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (h a3))))))
  have u7 : s 18 = true := (Or.elim c143 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u6 h))))))))))
  have u8 : s 10 ≠ true := (Or.elim c38 (fun h => h) (fun h => (False.elim (h u7))))
  have u9 : s 5 ≠ true := (Or.elim c18 (fun h => h) (fun h => (False.elim (h u7))))
  have u10 : s 41 ≠ true := (Or.elim c111 (fun h => h) (fun h => (False.elim (h a3))))
  have u11 : s 34 ≠ true := (Or.elim c100 (fun h => h) (fun h => (False.elim (h a3))))
  have u12 : s 19 ≠ true := (Or.elim c167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u8 h))))))))
  have u13 : s 32 = true := (Or.elim c170 (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u8 h))))))))))
  have u14 : s 3 ≠ true := (Or.elim c10 (fun h => h) (fun h => (False.elim (h u13))))
  have u15 : s 13 ≠ true := (Or.elim c47 (fun h => h) (fun h => (False.elim (h u13))))
  have u16 : s 21 ≠ true := (Or.elim c69 (fun h => h) (fun h => (False.elim (h u13))))
  have u17 : s 20 = true := (Or.elim c124 (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u5 h))))))))))
  have u18 : s 47 = true := (Or.elim c137 (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a1 h))))))))))
  have u19 : s 8 = true := (Or.elim c122 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))))))
  have u20 : s 2 ≠ true := (Or.elim c7 (fun h => h) (fun h => (False.elim (h u17))))
  have u21 : s 4 ≠ true := (Or.elim c14 (fun h => h) (fun h => (False.elim (h u17))))
  have u22 : s 27 ≠ true := (Or.elim c87 (fun h => h) (fun h => (False.elim (h u18))))
  have u23 : s 46 ≠ true := (Or.elim c27 (fun h => (False.elim (h u19))) (fun h => h))
  have u24 : s 53 = true := (Or.elim c176 (fun h => (False.elim (h u19))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u8 h))))))))))))))
  have u25 : s 25 = true := (Or.elim c131 (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u23 h))))))))))
  exact (Or.elim c80 (fun h => (h u25)) (fun h => (h u24)))

private theorem step184 (s : Fin 60 → Bool)
    (c95 : s 29 ≠ true ∨ s 59 ≠ true)
    (c105 : s 39 ≠ true ∨ s 59 ≠ true)
    (c102 : s 38 ≠ true ∨ s 58 ≠ true)
    (c101 : s 37 ≠ true ∨ s 58 ≠ true)
    (c179 : s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true)
    (c143 : s 18 = true ∨ s 29 = true ∨ s 38 = true ∨ s 39 = true ∨ s 55 = true)
    (c38 : s 10 ≠ true ∨ s 18 ≠ true)
    (c111 : s 41 ≠ true ∨ s 59 ≠ true)
    (c182 : s 49 = true ∨ s 52 = true ∨ s 58 ≠ true ∨ s 59 ≠ true)
    (c34 : s 9 ≠ true ∨ s 49 ≠ true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    (c183 : s 16 = true ∨ s 52 = true ∨ s 58 ≠ true ∨ s 59 ≠ true)
    (c28 : s 8 ≠ true ∨ s 16 ≠ true)
    (c169 : s 16 ≠ true ∨ s 48 = true ∨ s 9 = true ∨ s 59 ≠ true)
    (c122 : s 8 = true ∨ s 21 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true)
    (c84 : s 26 ≠ true ∨ s 48 ≠ true)
    (c69 : s 21 ≠ true ∨ s 32 ≠ true)
    (c161 : s 26 = true ∨ s 29 = true ∨ s 39 = true ∨ s 53 = true ∨ s 55 = true)
    (c51 : s 13 ≠ true ∨ s 53 ≠ true)
    (c66 : s 19 ≠ true ∨ s 53 ≠ true)
    (c127 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 32 = true ∨ s 52 = true)
    : s 52 = true ∨ s 58 ≠ true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 29 ≠ true := (Or.elim c95 (fun h => h) (fun h => (False.elim (h a2))))
  have u1 : s 39 ≠ true := (Or.elim c105 (fun h => h) (fun h => (False.elim (h a2))))
  have u2 : s 38 ≠ true := (Or.elim c102 (fun h => h) (fun h => (False.elim (h a1))))
  have u3 : s 37 ≠ true := (Or.elim c101 (fun h => h) (fun h => (False.elim (h a1))))
  have u4 : s 55 ≠ true := (Or.elim c179 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (h a2))))))
  have u5 : s 18 = true := (Or.elim c143 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u4 h))))))))))
  have u6 : s 10 ≠ true := (Or.elim c38 (fun h => h) (fun h => (False.elim (h u5))))
  have u7 : s 41 ≠ true := (Or.elim c111 (fun h => h) (fun h => (False.elim (h a2))))
  have u8 : s 49 = true := (Or.elim c182 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (h a1))) (fun h => (False.elim (h a2))))))))
  have u9 : s 9 ≠ true := (Or.elim c34 (fun h => h) (fun h => (False.elim (h u8))))
  have u10 : s 43 ≠ true := (Or.elim c117 (fun h => h) (fun h => (False.elim (h u8))))
  have u11 : s 16 = true := (Or.elim c183 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (h a1))) (fun h => (False.elim (h a2))))))))
  have u12 : s 8 ≠ true := (Or.elim c28 (fun h => h) (fun h => (False.elim (h u11))))
  have u13 : s 48 = true := (Or.elim c169 (fun h => (False.elim (h u11))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (h a2))))))))
  have u14 : s 21 = true := (Or.elim c122 (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (a0 h))))))))))
  have u15 : s 26 ≠ true := (Or.elim c84 (fun h => h) (fun h => (False.elim (h u13))))
  have u16 : s 32 ≠ true := (Or.elim c69 (fun h => (False.elim (h u14))) (fun h => h))
  have u17 : s 53 = true := (Or.elim c161 (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u4 h))))))))))
  have u18 : s 13 ≠ true := (Or.elim c51 (fun h => h) (fun h => (False.elim (h u17))))
  have u19 : s 19 ≠ true := (Or.elim c66 (fun h => h) (fun h => (False.elim (h u17))))
  exact (Or.elim c127 (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (u18 h)) (fun h => (Or.elim h (fun h => (u19 h)) (fun h => (Or.elim h (fun h => (u16 h)) (fun h => (a0 h)))))))))

private theorem step185 (s : Fin 60 → Bool)
    (c105 : s 39 ≠ true ∨ s 59 ≠ true)
    (c100 : s 34 ≠ true ∨ s 59 ≠ true)
    (c95 : s 29 ≠ true ∨ s 59 ≠ true)
    (c101 : s 37 ≠ true ∨ s 58 ≠ true)
    (c102 : s 38 ≠ true ∨ s 58 ≠ true)
    (c179 : s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true)
    (c143 : s 18 = true ∨ s 29 = true ∨ s 38 = true ∨ s 39 = true ∨ s 55 = true)
    (c2 : s 0 ≠ true ∨ s 18 ≠ true)
    (c184 : s 52 = true ∨ s 58 ≠ true ∨ s 59 ≠ true)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    (c71 : s 21 ≠ true ∨ s 52 ≠ true)
    (c181 : s 52 ≠ true ∨ s 33 = true ∨ s 0 = true ∨ s 37 = true ∨ s 34 = true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c11 : s 3 ≠ true ∨ s 33 ≠ true)
    : s 58 ≠ true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 39 ≠ true := (Or.elim c105 (fun h => h) (fun h => (False.elim (h a1))))
  have u1 : s 34 ≠ true := (Or.elim c100 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 29 ≠ true := (Or.elim c95 (fun h => h) (fun h => (False.elim (h a1))))
  have u3 : s 37 ≠ true := (Or.elim c101 (fun h => h) (fun h => (False.elim (h a0))))
  have u4 : s 38 ≠ true := (Or.elim c102 (fun h => h) (fun h => (False.elim (h a0))))
  have u5 : s 55 ≠ true := (Or.elim c179 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (h a1))))))
  have u6 : s 18 = true := (Or.elim c143 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (u5 h))))))))))
  have u7 : s 0 ≠ true := (Or.elim c2 (fun h => h) (fun h => (False.elim (h u6))))
  have u8 : s 52 = true := (Or.elim c184 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (False.elim (h a1))))))
  have u9 : s 20 ≠ true := (Or.elim c68 (fun h => h) (fun h => (False.elim (h u8))))
  have u10 : s 21 ≠ true := (Or.elim c71 (fun h => h) (fun h => (False.elim (h u8))))
  have u11 : s 33 = true := (Or.elim c181 (fun h => (False.elim (h u8))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u1 h))))))))))
  have u12 : s 3 = true := (Or.elim c124 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u3 h))))))))))
  exact (Or.elim c11 (fun h => (h u12)) (fun h => (h u11)))

private theorem step186 (s : Fin 60 → Bool)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    (c71 : s 21 ≠ true ∨ s 52 ≠ true)
    (c181 : s 52 ≠ true ∨ s 33 = true ∨ s 0 = true ∨ s 37 = true ∨ s 34 = true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c11 : s 3 ≠ true ∨ s 33 ≠ true)
    : s 52 ≠ true ∨ s 0 = true ∨ s 37 = true ∨ s 34 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 20 ≠ true := (Or.elim c68 (fun h => h) (fun h => (False.elim (h a0))))
  have u1 : s 21 ≠ true := (Or.elim c71 (fun h => h) (fun h => (False.elim (h a0))))
  have u2 : s 33 = true := (Or.elim c181 (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (a3 h))))))))))
  have u3 : s 3 = true := (Or.elim c124 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (a2 h))))))))))
  exact (Or.elim c11 (fun h => (h u3)) (fun h => (h u2)))

private theorem step187 (s : Fin 60 → Bool)
    (c111 : s 41 ≠ true ∨ s 59 ≠ true)
    (c28 : s 8 ≠ true ∨ s 16 ≠ true)
    (c172 : s 16 ≠ true ∨ s 49 = true ∨ s 37 = true ∨ s 59 ≠ true)
    (c122 : s 8 = true ∨ s 21 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    : s 16 ≠ true ∨ s 21 = true ∨ s 52 = true ∨ s 37 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 41 ≠ true := (Or.elim c111 (fun h => h) (fun h => (False.elim (h a4))))
  have u1 : s 8 ≠ true := (Or.elim c28 (fun h => h) (fun h => (False.elim (h a0))))
  have u2 : s 49 = true := (Or.elim c172 (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (h a4))))))))
  have u3 : s 43 = true := (Or.elim c122 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a2 h))))))))))
  exact (Or.elim c117 (fun h => (h u3)) (fun h => (h u2)))

private theorem step188 (s : Fin 60 → Bool)
    (c26 : s 8 ≠ true ∨ s 43 ≠ true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    (c180 : s 8 = true ∨ s 16 = true ∨ s 49 = true ∨ s 18 ≠ true ∨ s 59 ≠ true)
    : s 43 ≠ true ∨ s 18 ≠ true ∨ s 16 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 8 ≠ true := (Or.elim c26 (fun h => h) (fun h => (False.elim (h a0))))
  have u1 : s 49 ≠ true := (Or.elim c117 (fun h => (False.elim (h a0))) (fun h => h))
  exact (Or.elim c180 (fun h => (u0 h)) (fun h => (Or.elim h (fun h => (a2 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (h a1)) (fun h => (h a3)))))))))

private theorem step189 (s : Fin 60 → Bool)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    (c7 : s 2 ≠ true ∨ s 20 ≠ true)
    (c111 : s 41 ≠ true ∨ s 59 ≠ true)
    (c18 : s 5 ≠ true ∨ s 18 ≠ true)
    (c38 : s 10 ≠ true ∨ s 18 ≠ true)
    (c188 : s 43 ≠ true ∨ s 18 ≠ true ∨ s 16 = true ∨ s 59 ≠ true)
    (c122 : s 8 = true ∨ s 21 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true)
    (c167 : s 19 ≠ true ∨ s 16 = true ∨ s 43 = true ∨ s 10 = true)
    (c170 : s 16 = true ∨ s 32 = true ∨ s 43 = true ∨ s 52 = true ∨ s 10 = true)
    (c27 : s 8 ≠ true ∨ s 46 ≠ true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    (c137 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 47 = true ∨ s 52 = true)
    (c176 : s 8 ≠ true ∨ s 5 = true ∨ s 13 = true ∨ s 16 = true ∨ s 53 = true ∨ s 52 = true ∨ s 10 = true)
    (c87 : s 27 ≠ true ∨ s 47 ≠ true)
    (c80 : s 25 ≠ true ∨ s 53 ≠ true)
    (c131 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 46 = true)
    : s 18 ≠ true ∨ s 20 ≠ true ∨ s 16 = true ∨ s 21 = true ∨ s 52 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5⟩ := hc
  have u0 : s 4 ≠ true := (Or.elim c14 (fun h => h) (fun h => (False.elim (h a1))))
  have u1 : s 2 ≠ true := (Or.elim c7 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 41 ≠ true := (Or.elim c111 (fun h => h) (fun h => (False.elim (h a5))))
  have u3 : s 5 ≠ true := (Or.elim c18 (fun h => h) (fun h => (False.elim (h a0))))
  have u4 : s 10 ≠ true := (Or.elim c38 (fun h => h) (fun h => (False.elim (h a0))))
  have u5 : s 43 ≠ true := (Or.elim c188 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (h a5))))))))
  have u6 : s 8 = true := (Or.elim c122 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (a4 h))))))))))
  have u7 : s 19 ≠ true := (Or.elim c167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u4 h))))))))
  have u8 : s 32 = true := (Or.elim c170 (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (False.elim (u4 h))))))))))
  have u9 : s 46 ≠ true := (Or.elim c27 (fun h => (False.elim (h u6))) (fun h => h))
  have u10 : s 13 ≠ true := (Or.elim c47 (fun h => h) (fun h => (False.elim (h u8))))
  have u11 : s 47 = true := (Or.elim c137 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a4 h))))))))))
  have u12 : s 53 = true := (Or.elim c176 (fun h => (False.elim (h u6))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (False.elim (u4 h))))))))))))))
  have u13 : s 27 ≠ true := (Or.elim c87 (fun h => h) (fun h => (False.elim (h u11))))
  have u14 : s 25 ≠ true := (Or.elim c80 (fun h => h) (fun h => (False.elim (h u12))))
  exact (Or.elim c131 (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (Or.elim h (fun h => (u14 h)) (fun h => (Or.elim h (fun h => (u13 h)) (fun h => (u9 h)))))))))

private theorem step190 (s : Fin 60 → Bool)
    (c179 : s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true)
    (c185 : s 58 ≠ true ∨ s 59 ≠ true)
    (c105 : s 39 ≠ true ∨ s 59 ≠ true)
    (c95 : s 29 ≠ true ∨ s 59 ≠ true)
    (c149 : s 0 = true ∨ s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 37 = true)
    (c143 : s 18 = true ∨ s 29 = true ∨ s 38 = true ∨ s 39 = true ∨ s 55 = true)
    (c20 : s 7 ≠ true ∨ s 35 ≠ true)
    (c21 : s 7 ≠ true ∨ s 36 ≠ true)
    (c82 : s 26 ≠ true ∨ s 38 ≠ true)
    (c150 : s 9 = true ∨ s 16 = true ∨ s 18 = true ∨ s 35 = true ∨ s 36 = true)
    (c156 : s 26 = true ∨ s 29 = true ∨ s 35 = true ∨ s 48 = true ∨ s 58 = true)
    (c33 : s 9 ≠ true ∨ s 48 ≠ true)
    : s 18 = true ∨ s 16 = true ∨ s 0 = true ∨ s 37 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 55 ≠ true := (Or.elim c179 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (h a4))))))
  have u1 : s 58 ≠ true := (Or.elim c185 (fun h => h) (fun h => (False.elim (h a4))))
  have u2 : s 39 ≠ true := (Or.elim c105 (fun h => h) (fun h => (False.elim (h a4))))
  have u3 : s 29 ≠ true := (Or.elim c95 (fun h => h) (fun h => (False.elim (h a4))))
  have u4 : s 7 = true := (Or.elim c149 (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a3 h))))))))))
  have u5 : s 38 = true := (Or.elim c143 (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u0 h))))))))))
  have u6 : s 35 ≠ true := (Or.elim c20 (fun h => (False.elim (h u4))) (fun h => h))
  have u7 : s 36 ≠ true := (Or.elim c21 (fun h => (False.elim (h u4))) (fun h => h))
  have u8 : s 26 ≠ true := (Or.elim c82 (fun h => h) (fun h => (False.elim (h u5))))
  have u9 : s 9 = true := (Or.elim c150 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u7 h))))))))))
  have u10 : s 48 = true := (Or.elim c156 (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u1 h))))))))))
  exact (Or.elim c33 (fun h => (h u9)) (fun h => (h u10)))

private theorem step191 (s : Fin 60 → Bool)
    (c100 : s 34 ≠ true ∨ s 59 ≠ true)
    (c186 : s 52 ≠ true ∨ s 0 = true ∨ s 37 = true ∨ s 34 = true)
    (c187 : s 16 ≠ true ∨ s 21 = true ∨ s 52 = true ∨ s 37 = true ∨ s 59 ≠ true)
    (c190 : s 18 = true ∨ s 16 = true ∨ s 0 = true ∨ s 37 = true ∨ s 59 ≠ true)
    (c38 : s 10 ≠ true ∨ s 18 ≠ true)
    (c188 : s 43 ≠ true ∨ s 18 ≠ true ∨ s 16 = true ∨ s 59 ≠ true)
    (c189 : s 18 ≠ true ∨ s 20 ≠ true ∨ s 16 = true ∨ s 21 = true ∨ s 52 = true ∨ s 59 ≠ true)
    (c170 : s 16 = true ∨ s 32 = true ∨ s 43 = true ∨ s 52 = true ∨ s 10 = true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c10 : s 3 ≠ true ∨ s 32 ≠ true)
    : s 21 = true ∨ s 0 = true ∨ s 37 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 34 ≠ true := (Or.elim c100 (fun h => h) (fun h => (False.elim (h a3))))
  have u1 : s 52 ≠ true := (Or.elim c186 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u0 h))))))))
  have u2 : s 16 ≠ true := (Or.elim c187 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (h a3))))))))))
  have u3 : s 18 = true := (Or.elim c190 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (h a3))))))))))
  have u4 : s 10 ≠ true := (Or.elim c38 (fun h => h) (fun h => (False.elim (h u3))))
  have u5 : s 43 ≠ true := (Or.elim c188 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h u3))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (h a3))))))))
  have u6 : s 20 ≠ true := (Or.elim c189 (fun h => (False.elim (h u3))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (h a3))))))))))))
  have u7 : s 32 = true := (Or.elim c170 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u4 h))))))))))
  have u8 : s 3 = true := (Or.elim c124 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (a2 h))))))))))
  exact (Or.elim c10 (fun h => (h u8)) (fun h => (h u7)))

private theorem step192 (s : Fin 60 → Bool)
    (c191 : s 21 = true ∨ s 0 = true ∨ s 37 = true ∨ s 59 ≠ true)
    (c69 : s 21 ≠ true ∨ s 32 ≠ true)
    (c100 : s 34 ≠ true ∨ s 59 ≠ true)
    (c186 : s 52 ≠ true ∨ s 0 = true ∨ s 37 = true ∨ s 34 = true)
    (c190 : s 18 = true ∨ s 16 = true ∨ s 0 = true ∨ s 37 = true ∨ s 59 ≠ true)
    (c38 : s 10 ≠ true ∨ s 18 ≠ true)
    (c188 : s 43 ≠ true ∨ s 18 ≠ true ∨ s 16 = true ∨ s 59 ≠ true)
    (c170 : s 16 = true ∨ s 32 = true ∨ s 43 = true ∨ s 52 = true ∨ s 10 = true)
    : s 16 = true ∨ s 0 = true ∨ s 37 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 21 = true := (Or.elim c191 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (h a3))))))))
  have u1 : s 32 ≠ true := (Or.elim c69 (fun h => (False.elim (h u0))) (fun h => h))
  have u2 : s 34 ≠ true := (Or.elim c100 (fun h => h) (fun h => (False.elim (h a3))))
  have u3 : s 52 ≠ true := (Or.elim c186 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u2 h))))))))
  have u4 : s 18 = true := (Or.elim c190 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (h a3))))))))))
  have u5 : s 10 ≠ true := (Or.elim c38 (fun h => h) (fun h => (False.elim (h u4))))
  have u6 : s 43 ≠ true := (Or.elim c188 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h u4))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (h a3))))))))
  exact (Or.elim c170 (fun h => (a0 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (u5 h)))))))))

private theorem step193 (s : Fin 60 → Bool)
    (c105 : s 39 ≠ true ∨ s 59 ≠ true)
    (c95 : s 29 ≠ true ∨ s 59 ≠ true)
    (c32 : s 9 ≠ true ∨ s 16 ≠ true)
    (c37 : s 10 ≠ true ∨ s 16 ≠ true)
    (c57 : s 16 ≠ true ∨ s 51 ≠ true)
    (c169 : s 16 ≠ true ∨ s 48 = true ∨ s 9 = true ∨ s 59 ≠ true)
    (c84 : s 26 ≠ true ∨ s 48 ≠ true)
    (c161 : s 26 = true ∨ s 29 = true ∨ s 39 = true ∨ s 53 = true ∨ s 55 = true)
    (c51 : s 13 ≠ true ∨ s 53 ≠ true)
    (c66 : s 19 ≠ true ∨ s 53 ≠ true)
    (c132 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 51 = true ∨ s 55 = true)
    : s 16 ≠ true ∨ s 55 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 39 ≠ true := (Or.elim c105 (fun h => h) (fun h => (False.elim (h a2))))
  have u1 : s 29 ≠ true := (Or.elim c95 (fun h => h) (fun h => (False.elim (h a2))))
  have u2 : s 9 ≠ true := (Or.elim c32 (fun h => h) (fun h => (False.elim (h a0))))
  have u3 : s 10 ≠ true := (Or.elim c37 (fun h => h) (fun h => (False.elim (h a0))))
  have u4 : s 51 ≠ true := (Or.elim c57 (fun h => (False.elim (h a0))) (fun h => h))
  have u5 : s 48 = true := (Or.elim c169 (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (h a2))))))))
  have u6 : s 26 ≠ true := (Or.elim c84 (fun h => h) (fun h => (False.elim (h u5))))
  have u7 : s 53 = true := (Or.elim c161 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a1 h))))))))))
  have u8 : s 13 ≠ true := (Or.elim c51 (fun h => h) (fun h => (False.elim (h u7))))
  have u9 : s 19 ≠ true := (Or.elim c66 (fun h => h) (fun h => (False.elim (h u7))))
  exact (Or.elim c132 (fun h => (u3 h)) (fun h => (Or.elim h (fun h => (u8 h)) (fun h => (Or.elim h (fun h => (u9 h)) (fun h => (Or.elim h (fun h => (u4 h)) (fun h => (a1 h)))))))))

private theorem step194 (s : Fin 60 → Bool)
    (c10 : s 3 ≠ true ∨ s 32 ≠ true)
    (c69 : s 21 ≠ true ∨ s 32 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    : s 32 ≠ true ∨ s 20 = true ∨ s 37 = true ∨ s 34 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 3 ≠ true := (Or.elim c10 (fun h => h) (fun h => (False.elim (h a0))))
  have u1 : s 21 ≠ true := (Or.elim c69 (fun h => h) (fun h => (False.elim (h a0))))
  exact (Or.elim c124 (fun h => (u0 h)) (fun h => (Or.elim h (fun h => (a1 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (a3 h)) (fun h => (a2 h)))))))))

private theorem step195 (s : Fin 60 → Bool)
    (c185 : s 58 ≠ true ∨ s 59 ≠ true)
    (c95 : s 29 ≠ true ∨ s 59 ≠ true)
    (c29 : s 9 ≠ true ∨ s 35 ≠ true)
    (c33 : s 9 ≠ true ∨ s 48 ≠ true)
    (c156 : s 26 = true ∨ s 29 = true ∨ s 35 = true ∨ s 48 = true ∨ s 58 = true)
    : s 9 ≠ true ∨ s 26 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 58 ≠ true := (Or.elim c185 (fun h => h) (fun h => (False.elim (h a2))))
  have u1 : s 29 ≠ true := (Or.elim c95 (fun h => h) (fun h => (False.elim (h a2))))
  have u2 : s 35 ≠ true := (Or.elim c29 (fun h => (False.elim (h a0))) (fun h => h))
  have u3 : s 48 ≠ true := (Or.elim c33 (fun h => (False.elim (h a0))) (fun h => h))
  exact (Or.elim c156 (fun h => (a1 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (u0 h)))))))))

private theorem step196 (s : Fin 60 → Bool)
    (c108 : s 40 ≠ true ∨ s 59 ≠ true)
    (c105 : s 39 ≠ true ∨ s 59 ≠ true)
    (c16 : s 5 ≠ true ∨ s 35 ≠ true)
    (c20 : s 7 ≠ true ∨ s 35 ≠ true)
    (c125 : s 5 = true ∨ s 7 = true ∨ s 18 = true ∨ s 39 = true ∨ s 40 = true)
    : s 35 ≠ true ∨ s 18 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 40 ≠ true := (Or.elim c108 (fun h => h) (fun h => (False.elim (h a2))))
  have u1 : s 39 ≠ true := (Or.elim c105 (fun h => h) (fun h => (False.elim (h a2))))
  have u2 : s 5 ≠ true := (Or.elim c16 (fun h => h) (fun h => (False.elim (h a0))))
  have u3 : s 7 ≠ true := (Or.elim c20 (fun h => h) (fun h => (False.elim (h a0))))
  exact (Or.elim c125 (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (Or.elim h (fun h => (a1 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u0 h)))))))))

private theorem step197 (s : Fin 60 → Bool)
    (c185 : s 58 ≠ true ∨ s 59 ≠ true)
    (c116 : s 42 ≠ true ∨ s 59 ≠ true)
    (c108 : s 40 ≠ true ∨ s 59 ≠ true)
    (c105 : s 39 ≠ true ∨ s 59 ≠ true)
    (c100 : s 34 ≠ true ∨ s 59 ≠ true)
    (c95 : s 29 ≠ true ∨ s 59 ≠ true)
    (c179 : s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true)
    (c193 : s 16 ≠ true ∨ s 55 = true ∨ s 59 ≠ true)
    (c192 : s 16 = true ∨ s 0 = true ∨ s 37 = true ∨ s 59 ≠ true)
    (c2 : s 0 ≠ true ∨ s 18 ≠ true)
    (c3 : s 0 ≠ true ∨ s 20 ≠ true)
    (c143 : s 18 = true ∨ s 29 = true ∨ s 38 = true ∨ s 39 = true ∨ s 55 = true)
    (c82 : s 26 ≠ true ∨ s 38 ≠ true)
    (c161 : s 26 = true ∨ s 29 = true ∨ s 39 = true ∨ s 53 = true ∨ s 55 = true)
    (c51 : s 13 ≠ true ∨ s 53 ≠ true)
    (c66 : s 19 ≠ true ∨ s 53 ≠ true)
    (c194 : s 32 ≠ true ∨ s 20 = true ∨ s 37 = true ∨ s 34 = true)
    (c162 : s 13 = true ∨ s 29 = true ∨ s 32 = true ∨ s 55 = true ∨ s 57 = true)
    (c55 : s 14 ≠ true ∨ s 57 ≠ true)
    (c195 : s 9 ≠ true ∨ s 26 = true ∨ s 59 ≠ true)
    (c196 : s 35 ≠ true ∨ s 18 = true ∨ s 59 ≠ true)
    (c163 : s 9 = true ∨ s 14 = true ∨ s 35 = true ∨ s 47 = true ∨ s 58 = true)
    (c39 : s 10 ≠ true ∨ s 47 ≠ true)
    (c127 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 32 = true ∨ s 52 = true)
    (c76 : s 23 ≠ true ∨ s 52 ≠ true)
    (c164 : s 52 ≠ true ∨ s 12 = true ∨ s 37 = true ∨ s 59 ≠ true)
    (c129 : s 9 = true ∨ s 23 = true ∨ s 40 = true ∨ s 42 = true ∨ s 45 = true)
    (c45 : s 12 ≠ true ∨ s 45 ≠ true)
    : s 37 = true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 58 ≠ true := (Or.elim c185 (fun h => h) (fun h => (False.elim (h a1))))
  have u1 : s 42 ≠ true := (Or.elim c116 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 40 ≠ true := (Or.elim c108 (fun h => h) (fun h => (False.elim (h a1))))
  have u3 : s 39 ≠ true := (Or.elim c105 (fun h => h) (fun h => (False.elim (h a1))))
  have u4 : s 34 ≠ true := (Or.elim c100 (fun h => h) (fun h => (False.elim (h a1))))
  have u5 : s 29 ≠ true := (Or.elim c95 (fun h => h) (fun h => (False.elim (h a1))))
  have u6 : s 55 ≠ true := (Or.elim c179 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (h a1))))))
  have u7 : s 16 ≠ true := (Or.elim c193 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (h a1))))))
  have u8 : s 0 = true := (Or.elim c192 (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (h a1))))))))
  have u9 : s 18 ≠ true := (Or.elim c2 (fun h => (False.elim (h u8))) (fun h => h))
  have u10 : s 20 ≠ true := (Or.elim c3 (fun h => (False.elim (h u8))) (fun h => h))
  have u11 : s 38 = true := (Or.elim c143 (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u6 h))))))))))
  have u12 : s 26 ≠ true := (Or.elim c82 (fun h => h) (fun h => (False.elim (h u11))))
  have u13 : s 53 = true := (Or.elim c161 (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u6 h))))))))))
  have u14 : s 13 ≠ true := (Or.elim c51 (fun h => h) (fun h => (False.elim (h u13))))
  have u15 : s 19 ≠ true := (Or.elim c66 (fun h => h) (fun h => (False.elim (h u13))))
  have u16 : s 32 ≠ true := (Or.elim c194 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u4 h))))))))
  have u17 : s 57 = true := (Or.elim c162 (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => h))))))))
  have u18 : s 14 ≠ true := (Or.elim c55 (fun h => h) (fun h => (False.elim (h u17))))
  have u19 : s 9 ≠ true := (Or.elim c195 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (h a1))))))
  have u20 : s 35 ≠ true := (Or.elim c196 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (h a1))))))
  have u21 : s 47 = true := (Or.elim c163 (fun h => (False.elim (u19 h))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))))))
  have u22 : s 10 ≠ true := (Or.elim c39 (fun h => h) (fun h => (False.elim (h u21))))
  have u23 : s 52 = true := (Or.elim c127 (fun h => (False.elim (u22 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => h))))))))
  have u24 : s 23 ≠ true := (Or.elim c76 (fun h => h) (fun h => (False.elim (h u23))))
  have u25 : s 12 = true := (Or.elim c164 (fun h => (False.elim (h u23))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (h a1))))))))
  have u26 : s 45 = true := (Or.elim c129 (fun h => (False.elim (u19 h))) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => h))))))))
  exact (Or.elim c45 (fun h => (h u25)) (fun h => (h u26)))

private theorem step198 (s : Fin 60 → Bool)
    (c71 : s 21 ≠ true ∨ s 52 ≠ true)
    (c69 : s 21 ≠ true ∨ s 32 ≠ true)
    (c127 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 32 = true ∨ s 52 = true)
    (c64 : s 19 ≠ true ∨ s 50 ≠ true)
    (c65 : s 19 ≠ true ∨ s 51 ≠ true)
    (c154 : s 10 = true ∨ s 13 = true ∨ s 18 = true ∨ s 50 = true ∨ s 51 = true)
    : s 13 = true ∨ s 10 = true ∨ s 21 ≠ true ∨ s 18 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 52 ≠ true := (Or.elim c71 (fun h => (False.elim (h a2))) (fun h => h))
  have u1 : s 32 ≠ true := (Or.elim c69 (fun h => (False.elim (h a2))) (fun h => h))
  have u2 : s 19 = true := (Or.elim c127 (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))))
  have u3 : s 50 ≠ true := (Or.elim c64 (fun h => (False.elim (h u2))) (fun h => h))
  have u4 : s 51 ≠ true := (Or.elim c65 (fun h => (False.elim (h u2))) (fun h => h))
  exact (Or.elim c154 (fun h => (a1 h)) (fun h => (Or.elim h (fun h => (a0 h)) (fun h => (Or.elim h (fun h => (a3 h)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (u4 h)))))))))

private theorem step199 (s : Fin 60 → Bool)
    (c77 : s 24 ≠ true ∨ s 37 ≠ true)
    (c61 : s 18 ≠ true ∨ s 37 ≠ true)
    (c198 : s 13 = true ∨ s 10 = true ∨ s 21 ≠ true ∨ s 18 = true)
    (c48 : s 13 ≠ true ∨ s 50 ≠ true)
    (c49 : s 13 ≠ true ∨ s 51 ≠ true)
    (c141 : s 10 = true ∨ s 18 = true ∨ s 24 = true ∨ s 50 = true ∨ s 51 = true)
    : s 10 = true ∨ s 21 ≠ true ∨ s 37 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 24 ≠ true := (Or.elim c77 (fun h => h) (fun h => (False.elim (h a2))))
  have u1 : s 18 ≠ true := (Or.elim c61 (fun h => h) (fun h => (False.elim (h a2))))
  have u2 : s 13 = true := (Or.elim c198 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (h a1))) (fun h => (False.elim (u1 h))))))))
  have u3 : s 50 ≠ true := (Or.elim c48 (fun h => (False.elim (h u2))) (fun h => h))
  have u4 : s 51 ≠ true := (Or.elim c49 (fun h => (False.elim (h u2))) (fun h => h))
  exact (Or.elim c141 (fun h => (a0 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (u4 h)))))))))

private theorem step200 (s : Fin 60 → Bool)
    (c197 : s 37 = true ∨ s 59 ≠ true)
    (c81 : s 26 ≠ true ∨ s 37 ≠ true)
    (c195 : s 9 ≠ true ∨ s 26 = true ∨ s 59 ≠ true)
    (c61 : s 18 ≠ true ∨ s 37 ≠ true)
    (c196 : s 35 ≠ true ∨ s 18 = true ∨ s 59 ≠ true)
    (c185 : s 58 ≠ true ∨ s 59 ≠ true)
    (c105 : s 39 ≠ true ∨ s 59 ≠ true)
    (c95 : s 29 ≠ true ∨ s 59 ≠ true)
    (c69 : s 21 ≠ true ∨ s 32 ≠ true)
    (c199 : s 10 = true ∨ s 21 ≠ true ∨ s 37 ≠ true)
    (c39 : s 10 ≠ true ∨ s 47 ≠ true)
    (c40 : s 10 ≠ true ∨ s 55 ≠ true)
    (c163 : s 9 = true ∨ s 14 = true ∨ s 35 = true ∨ s 47 = true ∨ s 58 = true)
    (c161 : s 26 = true ∨ s 29 = true ∨ s 39 = true ∨ s 53 = true ∨ s 55 = true)
    (c55 : s 14 ≠ true ∨ s 57 ≠ true)
    (c51 : s 13 ≠ true ∨ s 53 ≠ true)
    (c162 : s 13 = true ∨ s 29 = true ∨ s 32 = true ∨ s 55 = true ∨ s 57 = true)
    : s 21 ≠ true ∨ s 59 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 37 = true := (Or.elim c197 (fun h => h) (fun h => (False.elim (h a1))))
  have u1 : s 26 ≠ true := (Or.elim c81 (fun h => h) (fun h => (False.elim (h u0))))
  have u2 : s 9 ≠ true := (Or.elim c195 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (h a1))))))
  have u3 : s 18 ≠ true := (Or.elim c61 (fun h => h) (fun h => (False.elim (h u0))))
  have u4 : s 35 ≠ true := (Or.elim c196 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (h a1))))))
  have u5 : s 58 ≠ true := (Or.elim c185 (fun h => h) (fun h => (False.elim (h a1))))
  have u6 : s 39 ≠ true := (Or.elim c105 (fun h => h) (fun h => (False.elim (h a1))))
  have u7 : s 29 ≠ true := (Or.elim c95 (fun h => h) (fun h => (False.elim (h a1))))
  have u8 : s 32 ≠ true := (Or.elim c69 (fun h => (False.elim (h a0))) (fun h => h))
  have u9 : s 10 = true := (Or.elim c199 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (False.elim (h u0))))))
  have u10 : s 47 ≠ true := (Or.elim c39 (fun h => (False.elim (h u9))) (fun h => h))
  have u11 : s 55 ≠ true := (Or.elim c40 (fun h => (False.elim (h u9))) (fun h => h))
  have u12 : s 14 = true := (Or.elim c163 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u5 h))))))))))
  have u13 : s 53 = true := (Or.elim c161 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u11 h))))))))))
  have u14 : s 57 ≠ true := (Or.elim c55 (fun h => (False.elim (h u12))) (fun h => h))
  have u15 : s 13 ≠ true := (Or.elim c51 (fun h => h) (fun h => (False.elim (h u13))))
  exact (Or.elim c162 (fun h => (u15 h)) (fun h => (Or.elim h (fun h => (u7 h)) (fun h => (Or.elim h (fun h => (u8 h)) (fun h => (Or.elim h (fun h => (u11 h)) (fun h => (u14 h)))))))))

private theorem step201 (s : Fin 60 → Bool)
    (c95 : s 29 ≠ true ∨ s 59 ≠ true)
    (c105 : s 39 ≠ true ∨ s 59 ≠ true)
    (c108 : s 40 ≠ true ∨ s 59 ≠ true)
    (c111 : s 41 ≠ true ∨ s 59 ≠ true)
    (c116 : s 42 ≠ true ∨ s 59 ≠ true)
    (c185 : s 58 ≠ true ∨ s 59 ≠ true)
    (c197 : s 37 = true ∨ s 59 ≠ true)
    (c61 : s 18 ≠ true ∨ s 37 ≠ true)
    (c67 : s 20 ≠ true ∨ s 37 ≠ true)
    (c74 : s 23 ≠ true ∨ s 37 ≠ true)
    (c81 : s 26 ≠ true ∨ s 37 ≠ true)
    (c196 : s 35 ≠ true ∨ s 18 = true ∨ s 59 ≠ true)
    (c195 : s 9 ≠ true ∨ s 26 = true ∨ s 59 ≠ true)
    (c156 : s 26 = true ∨ s 29 = true ∨ s 35 = true ∨ s 48 = true ∨ s 58 = true)
    (c129 : s 9 = true ∨ s 23 = true ∨ s 40 = true ∨ s 42 = true ∨ s 45 = true)
    (c79 : s 25 ≠ true ∨ s 48 ≠ true)
    (c88 : s 27 ≠ true ∨ s 48 ≠ true)
    (c6 : s 2 ≠ true ∨ s 45 ≠ true)
    (c200 : s 21 ≠ true ∨ s 59 ≠ true)
    (c139 : s 2 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 41 = true)
    (c4 : s 0 ≠ true ∨ s 30 ≠ true)
    (c15 : s 4 ≠ true ∨ s 30 ≠ true)
    (c131 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 46 = true)
    (c27 : s 8 ≠ true ∨ s 46 ≠ true)
    (c120 : s 0 = true ∨ s 8 = true ∨ s 16 = true ∨ s 20 = true ∨ s 41 = true)
    (c17 : s 5 ≠ true ∨ s 16 ≠ true)
    (c24 : s 7 ≠ true ∨ s 16 ≠ true)
    (c125 : s 5 = true ∨ s 7 = true ∨ s 18 = true ∨ s 39 = true ∨ s 40 = true)
    : s 59 ≠ true := by
  by_contra hc
  have u0 : s 29 ≠ true := (Or.elim c95 (fun h => h) (fun h => (False.elim (h hc))))
  have u1 : s 39 ≠ true := (Or.elim c105 (fun h => h) (fun h => (False.elim (h hc))))
  have u2 : s 40 ≠ true := (Or.elim c108 (fun h => h) (fun h => (False.elim (h hc))))
  have u3 : s 41 ≠ true := (Or.elim c111 (fun h => h) (fun h => (False.elim (h hc))))
  have u4 : s 42 ≠ true := (Or.elim c116 (fun h => h) (fun h => (False.elim (h hc))))
  have u5 : s 58 ≠ true := (Or.elim c185 (fun h => h) (fun h => (False.elim (h hc))))
  have u6 : s 37 = true := (Or.elim c197 (fun h => h) (fun h => (False.elim (h hc))))
  have u7 : s 18 ≠ true := (Or.elim c61 (fun h => h) (fun h => (False.elim (h u6))))
  have u8 : s 20 ≠ true := (Or.elim c67 (fun h => h) (fun h => (False.elim (h u6))))
  have u9 : s 23 ≠ true := (Or.elim c74 (fun h => h) (fun h => (False.elim (h u6))))
  have u10 : s 26 ≠ true := (Or.elim c81 (fun h => h) (fun h => (False.elim (h u6))))
  have u11 : s 35 ≠ true := (Or.elim c196 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (h hc))))))
  have u12 : s 9 ≠ true := (Or.elim c195 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (h hc))))))
  have u13 : s 48 = true := (Or.elim c156 (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u5 h))))))))))
  have u14 : s 45 = true := (Or.elim c129 (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => h))))))))
  have u15 : s 25 ≠ true := (Or.elim c79 (fun h => h) (fun h => (False.elim (h u13))))
  have u16 : s 27 ≠ true := (Or.elim c88 (fun h => h) (fun h => (False.elim (h u13))))
  have u17 : s 2 ≠ true := (Or.elim c6 (fun h => h) (fun h => (False.elim (h u14))))
  have u18 : s 21 ≠ true := (Or.elim c200 (fun h => h) (fun h => (False.elim (h hc))))
  have u19 : s 30 = true := (Or.elim c139 (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u3 h))))))))))
  have u20 : s 0 ≠ true := (Or.elim c4 (fun h => h) (fun h => (False.elim (h u19))))
  have u21 : s 4 ≠ true := (Or.elim c15 (fun h => h) (fun h => (False.elim (h u19))))
  have u22 : s 46 = true := (Or.elim c131 (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => h))))))))
  have u23 : s 8 ≠ true := (Or.elim c27 (fun h => h) (fun h => (False.elim (h u22))))
  have u24 : s 16 = true := (Or.elim c120 (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u3 h))))))))))
  have u25 : s 5 ≠ true := (Or.elim c17 (fun h => h) (fun h => (False.elim (h u24))))
  have u26 : s 7 ≠ true := (Or.elim c24 (fun h => h) (fun h => (False.elim (h u24))))
  exact (Or.elim c125 (fun h => (u25 h)) (fun h => (Or.elim h (fun h => (u26 h)) (fun h => (Or.elim h (fun h => (u7 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u2 h)))))))))

private theorem step202 (s : Fin 60 → Bool)
    (c67 : s 20 ≠ true ∨ s 37 ≠ true)
    (c199 : s 10 = true ∨ s 21 ≠ true ∨ s 37 ≠ true)
    (c139 : s 2 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 41 = true)
    (c15 : s 4 ≠ true ∨ s 30 ≠ true)
    (c4 : s 0 ≠ true ∨ s 30 ≠ true)
    (c101 : s 37 ≠ true ∨ s 58 ≠ true)
    (c81 : s 26 ≠ true ∨ s 37 ≠ true)
    (c61 : s 18 ≠ true ∨ s 37 ≠ true)
    (c156 : s 26 = true ∨ s 29 = true ∨ s 35 = true ∨ s 48 = true ∨ s 58 = true)
    (c79 : s 25 ≠ true ∨ s 48 ≠ true)
    (c88 : s 27 ≠ true ∨ s 48 ≠ true)
    (c131 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 46 = true)
    (c135 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 49 = true)
    (c27 : s 8 ≠ true ∨ s 46 ≠ true)
    (c106 : s 40 ≠ true ∨ s 49 ≠ true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    (c120 : s 0 = true ∨ s 8 = true ∨ s 16 = true ∨ s 20 = true ∨ s 41 = true)
    (c151 : s 8 = true ∨ s 26 = true ∨ s 35 = true ∨ s 43 = true ∨ s 53 = true)
    (c17 : s 5 ≠ true ∨ s 16 ≠ true)
    (c24 : s 7 ≠ true ∨ s 16 ≠ true)
    (c57 : s 16 ≠ true ∨ s 51 ≠ true)
    (c66 : s 19 ≠ true ∨ s 53 ≠ true)
    (c125 : s 5 = true ∨ s 7 = true ∨ s 18 = true ∨ s 39 = true ∨ s 40 = true)
    (c132 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 51 = true ∨ s 55 = true)
    (c103 : s 39 ≠ true ∨ s 55 ≠ true)
    : s 35 = true ∨ s 29 = true ∨ s 2 = true ∨ s 41 = true ∨ s 13 = true ∨ s 10 = true ∨ s 37 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6⟩ := hc
  have u0 : s 20 ≠ true := (Or.elim c67 (fun h => h) (fun h => (False.elim (h a6))))
  have u1 : s 21 ≠ true := (Or.elim c199 (fun h => (False.elim (a5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (h a6))))))
  have u2 : s 30 = true := (Or.elim c139 (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a3 h))))))))))
  have u3 : s 4 ≠ true := (Or.elim c15 (fun h => h) (fun h => (False.elim (h u2))))
  have u4 : s 0 ≠ true := (Or.elim c4 (fun h => h) (fun h => (False.elim (h u2))))
  have u5 : s 58 ≠ true := (Or.elim c101 (fun h => (False.elim (h a6))) (fun h => h))
  have u6 : s 26 ≠ true := (Or.elim c81 (fun h => h) (fun h => (False.elim (h a6))))
  have u7 : s 18 ≠ true := (Or.elim c61 (fun h => h) (fun h => (False.elim (h a6))))
  have u8 : s 48 = true := (Or.elim c156 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u5 h))))))))))
  have u9 : s 25 ≠ true := (Or.elim c79 (fun h => h) (fun h => (False.elim (h u8))))
  have u10 : s 27 ≠ true := (Or.elim c88 (fun h => h) (fun h => (False.elim (h u8))))
  have u11 : s 46 = true := (Or.elim c131 (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => h))))))))
  have u12 : s 49 = true := (Or.elim c135 (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => h))))))))
  have u13 : s 8 ≠ true := (Or.elim c27 (fun h => h) (fun h => (False.elim (h u11))))
  have u14 : s 40 ≠ true := (Or.elim c106 (fun h => h) (fun h => (False.elim (h u12))))
  have u15 : s 43 ≠ true := (Or.elim c117 (fun h => h) (fun h => (False.elim (h u12))))
  have u16 : s 16 = true := (Or.elim c120 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (a3 h))))))))))
  have u17 : s 53 = true := (Or.elim c151 (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => h))))))))
  have u18 : s 5 ≠ true := (Or.elim c17 (fun h => h) (fun h => (False.elim (h u16))))
  have u19 : s 7 ≠ true := (Or.elim c24 (fun h => h) (fun h => (False.elim (h u16))))
  have u20 : s 51 ≠ true := (Or.elim c57 (fun h => (False.elim (h u16))) (fun h => h))
  have u21 : s 19 ≠ true := (Or.elim c66 (fun h => h) (fun h => (False.elim (h u17))))
  have u22 : s 39 = true := (Or.elim c125 (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u14 h))))))))))
  have u23 : s 55 = true := (Or.elim c132 (fun h => (False.elim (a5 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => h))))))))
  exact (Or.elim c103 (fun h => (h u22)) (fun h => (h u23)))

private theorem step203 (s : Fin 60 → Bool)
    (c103 : s 39 ≠ true ∨ s 55 ≠ true)
    (c104 : s 39 ≠ true ∨ s 57 ≠ true)
    (c162 : s 13 = true ∨ s 29 = true ∨ s 32 = true ∨ s 55 = true ∨ s 57 = true)
    : s 39 ≠ true ∨ s 29 = true ∨ s 32 = true ∨ s 13 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 55 ≠ true := (Or.elim c103 (fun h => (False.elim (h a0))) (fun h => h))
  have u1 : s 57 ≠ true := (Or.elim c104 (fun h => (False.elim (h a0))) (fun h => h))
  exact (Or.elim c162 (fun h => (a3 h)) (fun h => (Or.elim h (fun h => (a1 h)) (fun h => (Or.elim h (fun h => (a2 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))))))

private theorem step204 (s : Fin 60 → Bool)
    (c199 : s 10 = true ∨ s 21 ≠ true ∨ s 37 ≠ true)
    (c81 : s 26 ≠ true ∨ s 37 ≠ true)
    (c61 : s 18 ≠ true ∨ s 37 ≠ true)
    (c202 : s 35 = true ∨ s 29 = true ∨ s 2 = true ∨ s 41 = true ∨ s 13 = true ∨ s 10 = true ∨ s 37 ≠ true)
    (c16 : s 5 ≠ true ∨ s 35 ≠ true)
    (c20 : s 7 ≠ true ∨ s 35 ≠ true)
    (c203 : s 39 ≠ true ∨ s 29 = true ∨ s 32 = true ∨ s 13 = true)
    (c125 : s 5 = true ∨ s 7 = true ∨ s 18 = true ∨ s 39 = true ∨ s 40 = true)
    (c106 : s 40 ≠ true ∨ s 49 ≠ true)
    (c107 : s 40 ≠ true ∨ s 54 ≠ true)
    (c121 : s 12 = true ∨ s 21 = true ∨ s 32 = true ∨ s 41 = true ∨ s 49 = true)
    (c46 : s 12 ≠ true ∨ s 55 ≠ true)
    (c161 : s 26 = true ∨ s 29 = true ∨ s 39 = true ∨ s 53 = true ∨ s 55 = true)
    (c136 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 54 = true ∨ s 55 = true)
    (c66 : s 19 ≠ true ∨ s 53 ≠ true)
    : s 29 = true ∨ s 32 = true ∨ s 2 = true ∨ s 41 = true ∨ s 13 = true ∨ s 10 = true ∨ s 37 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6⟩ := hc
  have u0 : s 21 ≠ true := (Or.elim c199 (fun h => (False.elim (a5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (h a6))))))
  have u1 : s 26 ≠ true := (Or.elim c81 (fun h => h) (fun h => (False.elim (h a6))))
  have u2 : s 18 ≠ true := (Or.elim c61 (fun h => h) (fun h => (False.elim (h a6))))
  have u3 : s 35 = true := (Or.elim c202 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => (False.elim (h a6))))))))))))))
  have u4 : s 5 ≠ true := (Or.elim c16 (fun h => h) (fun h => (False.elim (h u3))))
  have u5 : s 7 ≠ true := (Or.elim c20 (fun h => h) (fun h => (False.elim (h u3))))
  have u6 : s 39 ≠ true := (Or.elim c203 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (a4 h))))))))
  have u7 : s 40 = true := (Or.elim c125 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => h))))))))
  have u8 : s 49 ≠ true := (Or.elim c106 (fun h => (False.elim (h u7))) (fun h => h))
  have u9 : s 54 ≠ true := (Or.elim c107 (fun h => (False.elim (h u7))) (fun h => h))
  have u10 : s 12 = true := (Or.elim c121 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (u8 h))))))))))
  have u11 : s 55 ≠ true := (Or.elim c46 (fun h => (False.elim (h u10))) (fun h => h))
  have u12 : s 53 = true := (Or.elim c161 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u11 h))))))))))
  have u13 : s 19 = true := (Or.elim c136 (fun h => (False.elim (a5 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u11 h))))))))))
  exact (Or.elim c66 (fun h => (h u13)) (fun h => (h u12)))

private theorem step205 (s : Fin 60 → Bool)
    (c201 : s 59 ≠ true)
    (c67 : s 20 ≠ true ∨ s 37 ≠ true)
    (c61 : s 18 ≠ true ∨ s 37 ≠ true)
    (c89 : s 28 ≠ true ∨ s 50 ≠ true)
    (c90 : s 28 ≠ true ∨ s 52 ≠ true)
    (c154 : s 10 = true ∨ s 13 = true ∨ s 18 = true ∨ s 50 = true ∨ s 51 = true)
    (c152 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true ∨ s 59 = true)
    (c119 : s 43 ≠ true ∨ s 51 ≠ true)
    : s 28 ≠ true ∨ s 41 = true ∨ s 13 = true ∨ s 10 = true ∨ s 37 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 59 ≠ true := c201
  have u1 : s 20 ≠ true := (Or.elim c67 (fun h => h) (fun h => (False.elim (h a4))))
  have u2 : s 18 ≠ true := (Or.elim c61 (fun h => h) (fun h => (False.elim (h a4))))
  have u3 : s 50 ≠ true := (Or.elim c89 (fun h => (False.elim (h a0))) (fun h => h))
  have u4 : s 52 ≠ true := (Or.elim c90 (fun h => (False.elim (h a0))) (fun h => h))
  have u5 : s 51 = true := (Or.elim c154 (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => h))))))))
  have u6 : s 43 = true := (Or.elim c152 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u0 h))))))))))
  exact (Or.elim c119 (fun h => (h u6)) (fun h => (h u5)))

private theorem step206 (s : Fin 60 → Bool)
    (c205 : s 28 ≠ true ∨ s 41 = true ∨ s 13 = true ∨ s 10 = true ∨ s 37 ≠ true)
    (c199 : s 10 = true ∨ s 21 ≠ true ∨ s 37 ≠ true)
    (c67 : s 20 ≠ true ∨ s 37 ≠ true)
    (c61 : s 18 ≠ true ∨ s 37 ≠ true)
    (c139 : s 2 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 41 = true)
    (c4 : s 0 ≠ true ∨ s 30 ≠ true)
    (c15 : s 4 ≠ true ∨ s 30 ≠ true)
    (c146 : s 2 = true ∨ s 4 = true ∨ s 20 = true ∨ s 28 = true ∨ s 48 = true)
    (c79 : s 25 ≠ true ∨ s 48 ≠ true)
    (c88 : s 27 ≠ true ∨ s 48 ≠ true)
    (c92 : s 29 ≠ true ∨ s 48 ≠ true)
    (c131 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 46 = true)
    (c135 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 49 = true)
    (c202 : s 35 = true ∨ s 29 = true ∨ s 2 = true ∨ s 41 = true ∨ s 13 = true ∨ s 10 = true ∨ s 37 ≠ true)
    (c27 : s 8 ≠ true ∨ s 46 ≠ true)
    (c106 : s 40 ≠ true ∨ s 49 ≠ true)
    (c16 : s 5 ≠ true ∨ s 35 ≠ true)
    (c20 : s 7 ≠ true ∨ s 35 ≠ true)
    (c120 : s 0 = true ∨ s 8 = true ∨ s 16 = true ∨ s 20 = true ∨ s 41 = true)
    (c125 : s 5 = true ∨ s 7 = true ∨ s 18 = true ∨ s 39 = true ∨ s 40 = true)
    (c57 : s 16 ≠ true ∨ s 51 ≠ true)
    (c103 : s 39 ≠ true ∨ s 55 ≠ true)
    (c154 : s 10 = true ∨ s 13 = true ∨ s 18 = true ∨ s 50 = true ∨ s 51 = true)
    (c132 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 51 = true ∨ s 55 = true)
    (c64 : s 19 ≠ true ∨ s 50 ≠ true)
    : s 2 = true ∨ s 41 = true ∨ s 13 = true ∨ s 10 = true ∨ s 37 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 28 ≠ true := (Or.elim c205 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (h a4))))))))))
  have u1 : s 21 ≠ true := (Or.elim c199 (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (h a4))))))
  have u2 : s 20 ≠ true := (Or.elim c67 (fun h => h) (fun h => (False.elim (h a4))))
  have u3 : s 18 ≠ true := (Or.elim c61 (fun h => h) (fun h => (False.elim (h a4))))
  have u4 : s 30 = true := (Or.elim c139 (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a1 h))))))))))
  have u5 : s 0 ≠ true := (Or.elim c4 (fun h => h) (fun h => (False.elim (h u4))))
  have u6 : s 4 ≠ true := (Or.elim c15 (fun h => h) (fun h => (False.elim (h u4))))
  have u7 : s 48 = true := (Or.elim c146 (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => h))))))))
  have u8 : s 25 ≠ true := (Or.elim c79 (fun h => h) (fun h => (False.elim (h u7))))
  have u9 : s 27 ≠ true := (Or.elim c88 (fun h => h) (fun h => (False.elim (h u7))))
  have u10 : s 29 ≠ true := (Or.elim c92 (fun h => h) (fun h => (False.elim (h u7))))
  have u11 : s 46 = true := (Or.elim c131 (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => h))))))))
  have u12 : s 49 = true := (Or.elim c135 (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => h))))))))
  have u13 : s 35 = true := (Or.elim c202 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (h a4))))))))))))))
  have u14 : s 8 ≠ true := (Or.elim c27 (fun h => h) (fun h => (False.elim (h u11))))
  have u15 : s 40 ≠ true := (Or.elim c106 (fun h => h) (fun h => (False.elim (h u12))))
  have u16 : s 5 ≠ true := (Or.elim c16 (fun h => h) (fun h => (False.elim (h u13))))
  have u17 : s 7 ≠ true := (Or.elim c20 (fun h => h) (fun h => (False.elim (h u13))))
  have u18 : s 16 = true := (Or.elim c120 (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a1 h))))))))))
  have u19 : s 39 = true := (Or.elim c125 (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u15 h))))))))))
  have u20 : s 51 ≠ true := (Or.elim c57 (fun h => (False.elim (h u18))) (fun h => h))
  have u21 : s 55 ≠ true := (Or.elim c103 (fun h => (False.elim (h u19))) (fun h => h))
  have u22 : s 50 = true := (Or.elim c154 (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u20 h))))))))))
  have u23 : s 19 = true := (Or.elim c132 (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u21 h))))))))))
  exact (Or.elim c64 (fun h => (h u23)) (fun h => (h u22)))

private theorem step207 (s : Fin 60 → Bool)
    (c201 : s 59 ≠ true)
    (c67 : s 20 ≠ true ∨ s 37 ≠ true)
    (c61 : s 18 ≠ true ∨ s 37 ≠ true)
    (c43 : s 11 ≠ true ∨ s 55 ≠ true)
    (c54 : s 14 ≠ true ∨ s 55 ≠ true)
    (c97 : s 34 ≠ true ∨ s 55 ≠ true)
    (c103 : s 39 ≠ true ∨ s 55 ≠ true)
    (c147 : s 11 = true ∨ s 14 = true ∨ s 17 = true ∨ s 34 = true ∨ s 59 = true)
    (c1 : s 0 ≠ true ∨ s 17 ≠ true)
    (c157 : s 0 = true ∨ s 18 = true ∨ s 30 = true ∨ s 39 = true ∨ s 57 = true)
    (c158 : s 0 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 33 = true)
    (c96 : s 33 ≠ true ∨ s 57 ≠ true)
    : s 55 ≠ true ∨ s 30 = true ∨ s 21 = true ∨ s 37 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 59 ≠ true := c201
  have u1 : s 20 ≠ true := (Or.elim c67 (fun h => h) (fun h => (False.elim (h a3))))
  have u2 : s 18 ≠ true := (Or.elim c61 (fun h => h) (fun h => (False.elim (h a3))))
  have u3 : s 11 ≠ true := (Or.elim c43 (fun h => h) (fun h => (False.elim (h a0))))
  have u4 : s 14 ≠ true := (Or.elim c54 (fun h => h) (fun h => (False.elim (h a0))))
  have u5 : s 34 ≠ true := (Or.elim c97 (fun h => h) (fun h => (False.elim (h a0))))
  have u6 : s 39 ≠ true := (Or.elim c103 (fun h => h) (fun h => (False.elim (h a0))))
  have u7 : s 17 = true := (Or.elim c147 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u0 h))))))))))
  have u8 : s 0 ≠ true := (Or.elim c1 (fun h => h) (fun h => (False.elim (h u7))))
  have u9 : s 57 = true := (Or.elim c157 (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => h))))))))
  have u10 : s 33 = true := (Or.elim c158 (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => h))))))))
  exact (Or.elim c96 (fun h => (h u10)) (fun h => (h u9)))

private theorem step208 (s : Fin 60 → Bool)
    (c154 : s 10 = true ∨ s 13 = true ∨ s 18 = true ∨ s 50 = true ∨ s 51 = true)
    (c132 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 51 = true ∨ s 55 = true)
    (c64 : s 19 ≠ true ∨ s 50 ≠ true)
    : s 51 = true ∨ s 55 = true ∨ s 13 = true ∨ s 10 = true ∨ s 18 = true := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 50 = true := (Or.elim c154 (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a0 h))))))))))
  have u1 : s 19 = true := (Or.elim c132 (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))))))
  exact (Or.elim c64 (fun h => (h u1)) (fun h => (h u0)))

private theorem step209 (s : Fin 60 → Bool)
    (c199 : s 10 = true ∨ s 21 ≠ true ∨ s 37 ≠ true)
    (c101 : s 37 ≠ true ∨ s 58 ≠ true)
    (c81 : s 26 ≠ true ∨ s 37 ≠ true)
    (c74 : s 23 ≠ true ∨ s 37 ≠ true)
    (c61 : s 18 ≠ true ∨ s 37 ≠ true)
    (c6 : s 2 ≠ true ∨ s 45 ≠ true)
    (c8 : s 2 ≠ true ∨ s 29 ≠ true)
    (c9 : s 2 ≠ true ∨ s 30 ≠ true)
    (c207 : s 55 ≠ true ∨ s 30 = true ∨ s 21 = true ∨ s 37 ≠ true)
    (c208 : s 51 = true ∨ s 55 = true ∨ s 13 = true ∨ s 10 = true ∨ s 18 = true)
    (c65 : s 19 ≠ true ∨ s 51 ≠ true)
    (c136 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 54 = true ∨ s 55 = true)
    (c107 : s 40 ≠ true ∨ s 54 ≠ true)
    (c115 : s 42 ≠ true ∨ s 54 ≠ true)
    (c129 : s 9 = true ∨ s 23 = true ∨ s 40 = true ∨ s 42 = true ∨ s 45 = true)
    (c29 : s 9 ≠ true ∨ s 35 ≠ true)
    (c33 : s 9 ≠ true ∨ s 48 ≠ true)
    (c156 : s 26 = true ∨ s 29 = true ∨ s 35 = true ∨ s 48 = true ∨ s 58 = true)
    : s 2 ≠ true ∨ s 13 = true ∨ s 10 = true ∨ s 37 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 21 ≠ true := (Or.elim c199 (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (h a3))))))
  have u1 : s 58 ≠ true := (Or.elim c101 (fun h => (False.elim (h a3))) (fun h => h))
  have u2 : s 26 ≠ true := (Or.elim c81 (fun h => h) (fun h => (False.elim (h a3))))
  have u3 : s 23 ≠ true := (Or.elim c74 (fun h => h) (fun h => (False.elim (h a3))))
  have u4 : s 18 ≠ true := (Or.elim c61 (fun h => h) (fun h => (False.elim (h a3))))
  have u5 : s 45 ≠ true := (Or.elim c6 (fun h => (False.elim (h a0))) (fun h => h))
  have u6 : s 29 ≠ true := (Or.elim c8 (fun h => (False.elim (h a0))) (fun h => h))
  have u7 : s 30 ≠ true := (Or.elim c9 (fun h => (False.elim (h a0))) (fun h => h))
  have u8 : s 55 ≠ true := (Or.elim c207 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (h a3))))))))
  have u9 : s 51 = true := (Or.elim c208 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u4 h))))))))))
  have u10 : s 19 ≠ true := (Or.elim c65 (fun h => h) (fun h => (False.elim (h u9))))
  have u11 : s 54 = true := (Or.elim c136 (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u8 h))))))))))
  have u12 : s 40 ≠ true := (Or.elim c107 (fun h => h) (fun h => (False.elim (h u11))))
  have u13 : s 42 ≠ true := (Or.elim c115 (fun h => h) (fun h => (False.elim (h u11))))
  have u14 : s 9 = true := (Or.elim c129 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u5 h))))))))))
  have u15 : s 35 ≠ true := (Or.elim c29 (fun h => (False.elim (h u14))) (fun h => h))
  have u16 : s 48 ≠ true := (Or.elim c33 (fun h => (False.elim (h u14))) (fun h => h))
  exact (Or.elim c156 (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (u15 h)) (fun h => (Or.elim h (fun h => (u16 h)) (fun h => (u1 h)))))))))

private theorem step210 (s : Fin 60 → Bool)
    (c201 : s 59 ≠ true)
    (c58 : s 17 ≠ true ∨ s 51 ≠ true)
    (c65 : s 19 ≠ true ∨ s 51 ≠ true)
    (c136 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 54 = true ∨ s 55 = true)
    (c43 : s 11 ≠ true ∨ s 55 ≠ true)
    (c54 : s 14 ≠ true ∨ s 55 ≠ true)
    (c97 : s 34 ≠ true ∨ s 55 ≠ true)
    (c147 : s 11 = true ∨ s 14 = true ∨ s 17 = true ∨ s 34 = true ∨ s 59 = true)
    : s 51 ≠ true ∨ s 54 = true ∨ s 13 = true ∨ s 10 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 59 ≠ true := c201
  have u1 : s 17 ≠ true := (Or.elim c58 (fun h => h) (fun h => (False.elim (h a0))))
  have u2 : s 19 ≠ true := (Or.elim c65 (fun h => h) (fun h => (False.elim (h a0))))
  have u3 : s 55 = true := (Or.elim c136 (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => h))))))))
  have u4 : s 11 ≠ true := (Or.elim c43 (fun h => h) (fun h => (False.elim (h u3))))
  have u5 : s 14 ≠ true := (Or.elim c54 (fun h => h) (fun h => (False.elim (h u3))))
  have u6 : s 34 ≠ true := (Or.elim c97 (fun h => h) (fun h => (False.elim (h u3))))
  exact (Or.elim c147 (fun h => (u4 h)) (fun h => (Or.elim h (fun h => (u5 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (u0 h)))))))))

private theorem step211 (s : Fin 60 → Bool)
    (c199 : s 10 = true ∨ s 21 ≠ true ∨ s 37 ≠ true)
    (c67 : s 20 ≠ true ∨ s 37 ≠ true)
    (c61 : s 18 ≠ true ∨ s 37 ≠ true)
    (c209 : s 2 ≠ true ∨ s 13 = true ∨ s 10 = true ∨ s 37 ≠ true)
    (c206 : s 2 = true ∨ s 41 = true ∨ s 13 = true ∨ s 10 = true ∨ s 37 ≠ true)
    (c109 : s 41 ≠ true ∨ s 49 ≠ true)
    (c110 : s 41 ≠ true ∨ s 54 ≠ true)
    (c210 : s 51 ≠ true ∨ s 54 = true ∨ s 13 = true ∨ s 10 = true)
    (c154 : s 10 = true ∨ s 13 = true ∨ s 18 = true ∨ s 50 = true ∨ s 51 = true)
    (c208 : s 51 = true ∨ s 55 = true ∨ s 13 = true ∨ s 10 = true ∨ s 18 = true)
    (c89 : s 28 ≠ true ∨ s 50 ≠ true)
    (c207 : s 55 ≠ true ∨ s 30 = true ∨ s 21 = true ∨ s 37 ≠ true)
    (c15 : s 4 ≠ true ∨ s 30 ≠ true)
    (c146 : s 2 = true ∨ s 4 = true ∨ s 20 = true ∨ s 28 = true ∨ s 48 = true)
    (c79 : s 25 ≠ true ∨ s 48 ≠ true)
    (c88 : s 27 ≠ true ∨ s 48 ≠ true)
    (c135 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 49 = true)
    : s 13 = true ∨ s 10 = true ∨ s 37 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 21 ≠ true := (Or.elim c199 (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (h a2))))))
  have u1 : s 20 ≠ true := (Or.elim c67 (fun h => h) (fun h => (False.elim (h a2))))
  have u2 : s 18 ≠ true := (Or.elim c61 (fun h => h) (fun h => (False.elim (h a2))))
  have u3 : s 2 ≠ true := (Or.elim c209 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (h a2))))))))
  have u4 : s 41 = true := (Or.elim c206 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (h a2))))))))))
  have u5 : s 49 ≠ true := (Or.elim c109 (fun h => (False.elim (h u4))) (fun h => h))
  have u6 : s 54 ≠ true := (Or.elim c110 (fun h => (False.elim (h u4))) (fun h => h))
  have u7 : s 51 ≠ true := (Or.elim c210 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))))
  have u8 : s 50 = true := (Or.elim c154 (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u7 h))))))))))
  have u9 : s 55 = true := (Or.elim c208 (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u2 h))))))))))
  have u10 : s 28 ≠ true := (Or.elim c89 (fun h => h) (fun h => (False.elim (h u8))))
  have u11 : s 30 = true := (Or.elim c207 (fun h => (False.elim (h u9))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (h a2))))))))
  have u12 : s 4 ≠ true := (Or.elim c15 (fun h => h) (fun h => (False.elim (h u11))))
  have u13 : s 48 = true := (Or.elim c146 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => h))))))))
  have u14 : s 25 ≠ true := (Or.elim c79 (fun h => h) (fun h => (False.elim (h u13))))
  have u15 : s 27 ≠ true := (Or.elim c88 (fun h => h) (fun h => (False.elim (h u13))))
  exact (Or.elim c135 (fun h => (u3 h)) (fun h => (Or.elim h (fun h => (u12 h)) (fun h => (Or.elim h (fun h => (u14 h)) (fun h => (Or.elim h (fun h => (u15 h)) (fun h => (u5 h)))))))))

private theorem step212 (s : Fin 60 → Bool)
    (c77 : s 24 ≠ true ∨ s 37 ≠ true)
    (c61 : s 18 ≠ true ∨ s 37 ≠ true)
    (c211 : s 13 = true ∨ s 10 = true ∨ s 37 ≠ true)
    (c48 : s 13 ≠ true ∨ s 50 ≠ true)
    (c49 : s 13 ≠ true ∨ s 51 ≠ true)
    (c141 : s 10 = true ∨ s 18 = true ∨ s 24 = true ∨ s 50 = true ∨ s 51 = true)
    : s 10 = true ∨ s 37 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 24 ≠ true := (Or.elim c77 (fun h => h) (fun h => (False.elim (h a1))))
  have u1 : s 18 ≠ true := (Or.elim c61 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 13 = true := (Or.elim c211 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (h a1))))))
  have u3 : s 50 ≠ true := (Or.elim c48 (fun h => (False.elim (h u2))) (fun h => h))
  have u4 : s 51 ≠ true := (Or.elim c49 (fun h => (False.elim (h u2))) (fun h => h))
  exact (Or.elim c141 (fun h => (a0 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (u4 h)))))))))

private theorem step213 (s : Fin 60 → Bool)
    (c51 : s 13 ≠ true ∨ s 53 ≠ true)
    (c49 : s 13 ≠ true ∨ s 51 ≠ true)
    (c212 : s 10 = true ∨ s 37 ≠ true)
    (c40 : s 10 ≠ true ∨ s 55 ≠ true)
    (c37 : s 10 ≠ true ∨ s 16 ≠ true)
    (c36 : s 10 ≠ true ∨ s 32 ≠ true)
    (c81 : s 26 ≠ true ∨ s 37 ≠ true)
    (c61 : s 18 ≠ true ∨ s 37 ≠ true)
    (c25 : s 8 ≠ true ∨ s 41 ≠ true)
    (c109 : s 41 ≠ true ∨ s 49 ≠ true)
    (c126 : s 8 = true ∨ s 16 = true ∨ s 18 = true ∨ s 35 = true ∨ s 51 = true)
    (c16 : s 5 ≠ true ∨ s 35 ≠ true)
    (c20 : s 7 ≠ true ∨ s 35 ≠ true)
    (c29 : s 9 ≠ true ∨ s 35 ≠ true)
    (c145 : s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 38 = true ∨ s 51 = true)
    (c86 : s 27 ≠ true ∨ s 38 ≠ true)
    (c91 : s 29 ≠ true ∨ s 38 ≠ true)
    (c161 : s 26 = true ∨ s 29 = true ∨ s 39 = true ∨ s 53 = true ∨ s 55 = true)
    (c104 : s 39 ≠ true ∨ s 57 ≠ true)
    (c144 : s 11 = true ∨ s 29 = true ∨ s 32 = true ∨ s 55 = true ∨ s 57 = true)
    (c42 : s 11 ≠ true ∨ s 17 ≠ true)
    (c44 : s 11 ≠ true ∨ s 31 ≠ true)
    (c155 : s 5 = true ∨ s 7 = true ∨ s 17 = true ∨ s 31 = true ∨ s 36 = true)
    (c153 : s 8 = true ∨ s 9 = true ∨ s 31 = true ∨ s 42 = true ∨ s 49 = true)
    (c63 : s 19 ≠ true ∨ s 36 ≠ true)
    (c113 : s 42 ≠ true ∨ s 46 ≠ true)
    (c159 : s 5 = true ∨ s 19 = true ∨ s 27 = true ∨ s 46 = true ∨ s 53 = true)
    : s 41 ≠ true ∨ s 13 ≠ true ∨ s 37 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 53 ≠ true := (Or.elim c51 (fun h => (False.elim (h a1))) (fun h => h))
  have u1 : s 51 ≠ true := (Or.elim c49 (fun h => (False.elim (h a1))) (fun h => h))
  have u2 : s 10 = true := (Or.elim c212 (fun h => h) (fun h => (False.elim (h a2))))
  have u3 : s 55 ≠ true := (Or.elim c40 (fun h => (False.elim (h u2))) (fun h => h))
  have u4 : s 16 ≠ true := (Or.elim c37 (fun h => (False.elim (h u2))) (fun h => h))
  have u5 : s 32 ≠ true := (Or.elim c36 (fun h => (False.elim (h u2))) (fun h => h))
  have u6 : s 26 ≠ true := (Or.elim c81 (fun h => h) (fun h => (False.elim (h a2))))
  have u7 : s 18 ≠ true := (Or.elim c61 (fun h => h) (fun h => (False.elim (h a2))))
  have u8 : s 8 ≠ true := (Or.elim c25 (fun h => h) (fun h => (False.elim (h a0))))
  have u9 : s 49 ≠ true := (Or.elim c109 (fun h => (False.elim (h a0))) (fun h => h))
  have u10 : s 35 = true := (Or.elim c126 (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u1 h))))))))))
  have u11 : s 5 ≠ true := (Or.elim c16 (fun h => h) (fun h => (False.elim (h u10))))
  have u12 : s 7 ≠ true := (Or.elim c20 (fun h => h) (fun h => (False.elim (h u10))))
  have u13 : s 9 ≠ true := (Or.elim c29 (fun h => h) (fun h => (False.elim (h u10))))
  have u14 : s 38 = true := (Or.elim c145 (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u1 h))))))))))
  have u15 : s 27 ≠ true := (Or.elim c86 (fun h => h) (fun h => (False.elim (h u14))))
  have u16 : s 29 ≠ true := (Or.elim c91 (fun h => h) (fun h => (False.elim (h u14))))
  have u17 : s 39 = true := (Or.elim c161 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (u3 h))))))))))
  have u18 : s 57 ≠ true := (Or.elim c104 (fun h => (False.elim (h u17))) (fun h => h))
  have u19 : s 11 = true := (Or.elim c144 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u18 h))))))))))
  have u20 : s 17 ≠ true := (Or.elim c42 (fun h => (False.elim (h u19))) (fun h => h))
  have u21 : s 31 ≠ true := (Or.elim c44 (fun h => (False.elim (h u19))) (fun h => h))
  have u22 : s 36 = true := (Or.elim c155 (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => h))))))))
  have u23 : s 42 = true := (Or.elim c153 (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u9 h))))))))))
  have u24 : s 19 ≠ true := (Or.elim c63 (fun h => h) (fun h => (False.elim (h u22))))
  have u25 : s 46 ≠ true := (Or.elim c113 (fun h => (False.elim (h u23))) (fun h => h))
  exact (Or.elim c159 (fun h => (u11 h)) (fun h => (Or.elim h (fun h => (u24 h)) (fun h => (Or.elim h (fun h => (u15 h)) (fun h => (Or.elim h (fun h => (u25 h)) (fun h => (u0 h)))))))))

private theorem step214 (s : Fin 60 → Bool)
    (c201 : s 59 ≠ true)
    (c212 : s 10 = true ∨ s 37 ≠ true)
    (c40 : s 10 ≠ true ∨ s 55 ≠ true)
    (c37 : s 10 ≠ true ∨ s 16 ≠ true)
    (c36 : s 10 ≠ true ∨ s 32 ≠ true)
    (c81 : s 26 ≠ true ∨ s 37 ≠ true)
    (c67 : s 20 ≠ true ∨ s 37 ≠ true)
    (c61 : s 18 ≠ true ∨ s 37 ≠ true)
    (c49 : s 13 ≠ true ∨ s 51 ≠ true)
    (c50 : s 13 ≠ true ∨ s 52 ≠ true)
    (c51 : s 13 ≠ true ∨ s 53 ≠ true)
    (c213 : s 41 ≠ true ∨ s 13 ≠ true ∨ s 37 ≠ true)
    (c152 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true ∨ s 59 = true)
    (c26 : s 8 ≠ true ∨ s 43 ≠ true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    (c126 : s 8 = true ∨ s 16 = true ∨ s 18 = true ∨ s 35 = true ∨ s 51 = true)
    (c120 : s 0 = true ∨ s 8 = true ∨ s 16 = true ∨ s 20 = true ∨ s 41 = true)
    (c16 : s 5 ≠ true ∨ s 35 ≠ true)
    (c20 : s 7 ≠ true ∨ s 35 ≠ true)
    (c29 : s 9 ≠ true ∨ s 35 ≠ true)
    (c1 : s 0 ≠ true ∨ s 17 ≠ true)
    (c145 : s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 38 = true ∨ s 51 = true)
    (c86 : s 27 ≠ true ∨ s 38 ≠ true)
    (c91 : s 29 ≠ true ∨ s 38 ≠ true)
    (c161 : s 26 = true ∨ s 29 = true ∨ s 39 = true ∨ s 53 = true ∨ s 55 = true)
    (c104 : s 39 ≠ true ∨ s 57 ≠ true)
    (c144 : s 11 = true ∨ s 29 = true ∨ s 32 = true ∨ s 55 = true ∨ s 57 = true)
    (c44 : s 11 ≠ true ∨ s 31 ≠ true)
    (c155 : s 5 = true ∨ s 7 = true ∨ s 17 = true ∨ s 31 = true ∨ s 36 = true)
    (c153 : s 8 = true ∨ s 9 = true ∨ s 31 = true ∨ s 42 = true ∨ s 49 = true)
    (c63 : s 19 ≠ true ∨ s 36 ≠ true)
    (c113 : s 42 ≠ true ∨ s 46 ≠ true)
    (c159 : s 5 = true ∨ s 19 = true ∨ s 27 = true ∨ s 46 = true ∨ s 53 = true)
    : s 13 ≠ true ∨ s 37 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 59 ≠ true := c201
  have u1 : s 10 = true := (Or.elim c212 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 55 ≠ true := (Or.elim c40 (fun h => (False.elim (h u1))) (fun h => h))
  have u3 : s 16 ≠ true := (Or.elim c37 (fun h => (False.elim (h u1))) (fun h => h))
  have u4 : s 32 ≠ true := (Or.elim c36 (fun h => (False.elim (h u1))) (fun h => h))
  have u5 : s 26 ≠ true := (Or.elim c81 (fun h => h) (fun h => (False.elim (h a1))))
  have u6 : s 20 ≠ true := (Or.elim c67 (fun h => h) (fun h => (False.elim (h a1))))
  have u7 : s 18 ≠ true := (Or.elim c61 (fun h => h) (fun h => (False.elim (h a1))))
  have u8 : s 51 ≠ true := (Or.elim c49 (fun h => (False.elim (h a0))) (fun h => h))
  have u9 : s 52 ≠ true := (Or.elim c50 (fun h => (False.elim (h a0))) (fun h => h))
  have u10 : s 53 ≠ true := (Or.elim c51 (fun h => (False.elim (h a0))) (fun h => h))
  have u11 : s 41 ≠ true := (Or.elim c213 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (False.elim (h a1))))))
  have u12 : s 43 = true := (Or.elim c152 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u0 h))))))))))
  have u13 : s 8 ≠ true := (Or.elim c26 (fun h => h) (fun h => (False.elim (h u12))))
  have u14 : s 49 ≠ true := (Or.elim c117 (fun h => (False.elim (h u12))) (fun h => h))
  have u15 : s 35 = true := (Or.elim c126 (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u8 h))))))))))
  have u16 : s 0 = true := (Or.elim c120 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u11 h))))))))))
  have u17 : s 5 ≠ true := (Or.elim c16 (fun h => h) (fun h => (False.elim (h u15))))
  have u18 : s 7 ≠ true := (Or.elim c20 (fun h => h) (fun h => (False.elim (h u15))))
  have u19 : s 9 ≠ true := (Or.elim c29 (fun h => h) (fun h => (False.elim (h u15))))
  have u20 : s 17 ≠ true := (Or.elim c1 (fun h => (False.elim (h u16))) (fun h => h))
  have u21 : s 38 = true := (Or.elim c145 (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u8 h))))))))))
  have u22 : s 27 ≠ true := (Or.elim c86 (fun h => h) (fun h => (False.elim (h u21))))
  have u23 : s 29 ≠ true := (Or.elim c91 (fun h => h) (fun h => (False.elim (h u21))))
  have u24 : s 39 = true := (Or.elim c161 (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u2 h))))))))))
  have u25 : s 57 ≠ true := (Or.elim c104 (fun h => (False.elim (h u24))) (fun h => h))
  have u26 : s 11 = true := (Or.elim c144 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u25 h))))))))))
  have u27 : s 31 ≠ true := (Or.elim c44 (fun h => (False.elim (h u26))) (fun h => h))
  have u28 : s 36 = true := (Or.elim c155 (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => h))))))))
  have u29 : s 42 = true := (Or.elim c153 (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u14 h))))))))))
  have u30 : s 19 ≠ true := (Or.elim c63 (fun h => h) (fun h => (False.elim (h u28))))
  have u31 : s 46 ≠ true := (Or.elim c113 (fun h => (False.elim (h u29))) (fun h => h))
  exact (Or.elim c159 (fun h => (u17 h)) (fun h => (Or.elim h (fun h => (u30 h)) (fun h => (Or.elim h (fun h => (u22 h)) (fun h => (Or.elim h (fun h => (u31 h)) (fun h => (u10 h)))))))))

private theorem step215 (s : Fin 60 → Bool)
    (c16 : s 5 ≠ true ∨ s 35 ≠ true)
    (c20 : s 7 ≠ true ∨ s 35 ≠ true)
    (c125 : s 5 = true ∨ s 7 = true ∨ s 18 = true ∨ s 39 = true ∨ s 40 = true)
    : s 35 ≠ true ∨ s 40 = true ∨ s 39 = true ∨ s 18 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 5 ≠ true := (Or.elim c16 (fun h => h) (fun h => (False.elim (h a0))))
  have u1 : s 7 ≠ true := (Or.elim c20 (fun h => h) (fun h => (False.elim (h a0))))
  exact (Or.elim c125 (fun h => (u0 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (a3 h)) (fun h => (Or.elim h (fun h => (a2 h)) (fun h => (a1 h)))))))))

private theorem step216 (s : Fin 60 → Bool)
    (c214 : s 13 ≠ true ∨ s 37 ≠ true)
    (c212 : s 10 = true ∨ s 37 ≠ true)
    (c40 : s 10 ≠ true ∨ s 55 ≠ true)
    (c39 : s 10 ≠ true ∨ s 47 ≠ true)
    (c36 : s 10 ≠ true ∨ s 32 ≠ true)
    (c101 : s 37 ≠ true ∨ s 58 ≠ true)
    (c81 : s 26 ≠ true ∨ s 37 ≠ true)
    (c61 : s 18 ≠ true ∨ s 37 ≠ true)
    (c203 : s 39 ≠ true ∨ s 29 = true ∨ s 32 = true ∨ s 13 = true)
    (c162 : s 13 = true ∨ s 29 = true ∨ s 32 = true ∨ s 55 = true ∨ s 57 = true)
    (c55 : s 14 ≠ true ∨ s 57 ≠ true)
    (c160 : s 6 = true ∨ s 14 = true ∨ s 32 = true ∨ s 34 = true ∨ s 55 = true)
    (c19 : s 6 ≠ true ∨ s 40 ≠ true)
    (c215 : s 35 ≠ true ∨ s 40 = true ∨ s 39 = true ∨ s 18 = true)
    (c156 : s 26 = true ∨ s 29 = true ∨ s 35 = true ∨ s 48 = true ∨ s 58 = true)
    (c163 : s 9 = true ∨ s 14 = true ∨ s 35 = true ∨ s 47 = true ∨ s 58 = true)
    (c33 : s 9 ≠ true ∨ s 48 ≠ true)
    : s 29 = true ∨ s 34 = true ∨ s 37 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 13 ≠ true := (Or.elim c214 (fun h => h) (fun h => (False.elim (h a2))))
  have u1 : s 10 = true := (Or.elim c212 (fun h => h) (fun h => (False.elim (h a2))))
  have u2 : s 55 ≠ true := (Or.elim c40 (fun h => (False.elim (h u1))) (fun h => h))
  have u3 : s 47 ≠ true := (Or.elim c39 (fun h => (False.elim (h u1))) (fun h => h))
  have u4 : s 32 ≠ true := (Or.elim c36 (fun h => (False.elim (h u1))) (fun h => h))
  have u5 : s 58 ≠ true := (Or.elim c101 (fun h => (False.elim (h a2))) (fun h => h))
  have u6 : s 26 ≠ true := (Or.elim c81 (fun h => h) (fun h => (False.elim (h a2))))
  have u7 : s 18 ≠ true := (Or.elim c61 (fun h => h) (fun h => (False.elim (h a2))))
  have u8 : s 39 ≠ true := (Or.elim c203 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u0 h))))))))
  have u9 : s 57 = true := (Or.elim c162 (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => h))))))))
  have u10 : s 14 ≠ true := (Or.elim c55 (fun h => h) (fun h => (False.elim (h u9))))
  have u11 : s 6 = true := (Or.elim c160 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u2 h))))))))))
  have u12 : s 40 ≠ true := (Or.elim c19 (fun h => (False.elim (h u11))) (fun h => h))
  have u13 : s 35 ≠ true := (Or.elim c215 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u7 h))))))))
  have u14 : s 48 = true := (Or.elim c156 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u5 h))))))))))
  have u15 : s 9 = true := (Or.elim c163 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))))))
  exact (Or.elim c33 (fun h => (h u15)) (fun h => (h u14)))

private theorem step217 (s : Fin 60 → Bool)
    (c201 : s 59 ≠ true)
    (c212 : s 10 = true ∨ s 37 ≠ true)
    (c37 : s 10 ≠ true ∨ s 16 ≠ true)
    (c67 : s 20 ≠ true ∨ s 37 ≠ true)
    (c61 : s 18 ≠ true ∨ s 37 ≠ true)
    (c8 : s 2 ≠ true ∨ s 29 ≠ true)
    (c91 : s 29 ≠ true ∨ s 38 ≠ true)
    (c92 : s 29 ≠ true ∨ s 48 ≠ true)
    (c145 : s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 38 = true ∨ s 51 = true)
    (c20 : s 7 ≠ true ∨ s 35 ≠ true)
    (c126 : s 8 = true ∨ s 16 = true ∨ s 18 = true ∨ s 35 = true ∨ s 51 = true)
    (c26 : s 8 ≠ true ∨ s 43 ≠ true)
    (c152 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true ∨ s 59 = true)
    (c71 : s 21 ≠ true ∨ s 52 ≠ true)
    (c90 : s 28 ≠ true ∨ s 52 ≠ true)
    (c139 : s 2 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 41 = true)
    (c146 : s 2 = true ∨ s 4 = true ∨ s 20 = true ∨ s 28 = true ∨ s 48 = true)
    (c15 : s 4 ≠ true ∨ s 30 ≠ true)
    : s 29 ≠ true ∨ s 41 = true ∨ s 51 = true ∨ s 37 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 59 ≠ true := c201
  have u1 : s 10 = true := (Or.elim c212 (fun h => h) (fun h => (False.elim (h a3))))
  have u2 : s 16 ≠ true := (Or.elim c37 (fun h => (False.elim (h u1))) (fun h => h))
  have u3 : s 20 ≠ true := (Or.elim c67 (fun h => h) (fun h => (False.elim (h a3))))
  have u4 : s 18 ≠ true := (Or.elim c61 (fun h => h) (fun h => (False.elim (h a3))))
  have u5 : s 2 ≠ true := (Or.elim c8 (fun h => h) (fun h => (False.elim (h a0))))
  have u6 : s 38 ≠ true := (Or.elim c91 (fun h => (False.elim (h a0))) (fun h => h))
  have u7 : s 48 ≠ true := (Or.elim c92 (fun h => (False.elim (h a0))) (fun h => h))
  have u8 : s 7 = true := (Or.elim c145 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (a2 h))))))))))
  have u9 : s 35 ≠ true := (Or.elim c20 (fun h => (False.elim (h u8))) (fun h => h))
  have u10 : s 8 = true := (Or.elim c126 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (a2 h))))))))))
  have u11 : s 43 ≠ true := (Or.elim c26 (fun h => (False.elim (h u10))) (fun h => h))
  have u12 : s 52 = true := (Or.elim c152 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))))))
  have u13 : s 21 ≠ true := (Or.elim c71 (fun h => h) (fun h => (False.elim (h u12))))
  have u14 : s 28 ≠ true := (Or.elim c90 (fun h => h) (fun h => (False.elim (h u12))))
  have u15 : s 30 = true := (Or.elim c139 (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a1 h))))))))))
  have u16 : s 4 = true := (Or.elim c146 (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (u7 h))))))))))
  exact (Or.elim c15 (fun h => (h u16)) (fun h => (h u15)))

private theorem step218 (s : Fin 60 → Bool)
    (c214 : s 13 ≠ true ∨ s 37 ≠ true)
    (c212 : s 10 = true ∨ s 37 ≠ true)
    (c40 : s 10 ≠ true ∨ s 55 ≠ true)
    (c36 : s 10 ≠ true ∨ s 32 ≠ true)
    (c162 : s 13 = true ∨ s 29 = true ∨ s 32 = true ∨ s 55 = true ∨ s 57 = true)
    (c216 : s 29 = true ∨ s 34 = true ∨ s 37 ≠ true)
    (c98 : s 34 ≠ true ∨ s 57 ≠ true)
    : s 29 = true ∨ s 37 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 13 ≠ true := (Or.elim c214 (fun h => h) (fun h => (False.elim (h a1))))
  have u1 : s 10 = true := (Or.elim c212 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 55 ≠ true := (Or.elim c40 (fun h => (False.elim (h u1))) (fun h => h))
  have u3 : s 32 ≠ true := (Or.elim c36 (fun h => (False.elim (h u1))) (fun h => h))
  have u4 : s 57 = true := (Or.elim c162 (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => h))))))))
  have u5 : s 34 = true := (Or.elim c216 (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (h a1))))))
  exact (Or.elim c98 (fun h => (h u5)) (fun h => (h u4)))

private theorem step219 (s : Fin 60 → Bool)
    (c218 : s 29 = true ∨ s 37 ≠ true)
    (c91 : s 29 ≠ true ∨ s 38 ≠ true)
    (c212 : s 10 = true ∨ s 37 ≠ true)
    (c37 : s 10 ≠ true ∨ s 16 ≠ true)
    (c61 : s 18 ≠ true ∨ s 37 ≠ true)
    (c217 : s 29 ≠ true ∨ s 41 = true ∨ s 51 = true ∨ s 37 ≠ true)
    (c145 : s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 38 = true ∨ s 51 = true)
    (c25 : s 8 ≠ true ∨ s 41 ≠ true)
    (c20 : s 7 ≠ true ∨ s 35 ≠ true)
    (c126 : s 8 = true ∨ s 16 = true ∨ s 18 = true ∨ s 35 = true ∨ s 51 = true)
    : s 51 = true ∨ s 37 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 29 = true := (Or.elim c218 (fun h => h) (fun h => (False.elim (h a1))))
  have u1 : s 38 ≠ true := (Or.elim c91 (fun h => (False.elim (h u0))) (fun h => h))
  have u2 : s 10 = true := (Or.elim c212 (fun h => h) (fun h => (False.elim (h a1))))
  have u3 : s 16 ≠ true := (Or.elim c37 (fun h => (False.elim (h u2))) (fun h => h))
  have u4 : s 18 ≠ true := (Or.elim c61 (fun h => h) (fun h => (False.elim (h a1))))
  have u5 : s 41 = true := (Or.elim c217 (fun h => (False.elim (h u0))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (h a1))))))))
  have u6 : s 7 = true := (Or.elim c145 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a0 h))))))))))
  have u7 : s 8 ≠ true := (Or.elim c25 (fun h => h) (fun h => (False.elim (h u5))))
  have u8 : s 35 ≠ true := (Or.elim c20 (fun h => (False.elim (h u6))) (fun h => h))
  exact (Or.elim c126 (fun h => (u7 h)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (Or.elim h (fun h => (u4 h)) (fun h => (Or.elim h (fun h => (u8 h)) (fun h => (a0 h)))))))))

private theorem step220 (s : Fin 60 → Bool)
    (c201 : s 59 ≠ true)
    (c67 : s 20 ≠ true ∨ s 37 ≠ true)
    (c81 : s 26 ≠ true ∨ s 37 ≠ true)
    (c214 : s 13 ≠ true ∨ s 37 ≠ true)
    (c218 : s 29 = true ∨ s 37 ≠ true)
    (c8 : s 2 ≠ true ∨ s 29 ≠ true)
    (c92 : s 29 ≠ true ∨ s 48 ≠ true)
    (c93 : s 29 ≠ true ∨ s 53 ≠ true)
    (c219 : s 51 = true ∨ s 37 ≠ true)
    (c58 : s 17 ≠ true ∨ s 51 ≠ true)
    (c65 : s 19 ≠ true ∨ s 51 ≠ true)
    (c119 : s 43 ≠ true ∨ s 51 ≠ true)
    (c148 : s 5 = true ∨ s 13 = true ∨ s 17 = true ∨ s 19 = true ∨ s 53 = true)
    (c16 : s 5 ≠ true ∨ s 35 ≠ true)
    (c151 : s 8 = true ∨ s 26 = true ∨ s 35 = true ∨ s 43 = true ∨ s 53 = true)
    (c25 : s 8 ≠ true ∨ s 41 ≠ true)
    (c152 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true ∨ s 59 = true)
    (c71 : s 21 ≠ true ∨ s 52 ≠ true)
    (c90 : s 28 ≠ true ∨ s 52 ≠ true)
    (c139 : s 2 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 41 = true)
    (c146 : s 2 = true ∨ s 4 = true ∨ s 20 = true ∨ s 28 = true ∨ s 48 = true)
    (c15 : s 4 ≠ true ∨ s 30 ≠ true)
    : s 37 ≠ true := by
  by_contra hc
  have u0 : s 59 ≠ true := c201
  have u1 : s 20 ≠ true := (Or.elim c67 (fun h => h) (fun h => (False.elim (h hc))))
  have u2 : s 26 ≠ true := (Or.elim c81 (fun h => h) (fun h => (False.elim (h hc))))
  have u3 : s 13 ≠ true := (Or.elim c214 (fun h => h) (fun h => (False.elim (h hc))))
  have u4 : s 29 = true := (Or.elim c218 (fun h => h) (fun h => (False.elim (h hc))))
  have u5 : s 2 ≠ true := (Or.elim c8 (fun h => h) (fun h => (False.elim (h u4))))
  have u6 : s 48 ≠ true := (Or.elim c92 (fun h => (False.elim (h u4))) (fun h => h))
  have u7 : s 53 ≠ true := (Or.elim c93 (fun h => (False.elim (h u4))) (fun h => h))
  have u8 : s 51 = true := (Or.elim c219 (fun h => h) (fun h => (False.elim (h hc))))
  have u9 : s 17 ≠ true := (Or.elim c58 (fun h => h) (fun h => (False.elim (h u8))))
  have u10 : s 19 ≠ true := (Or.elim c65 (fun h => h) (fun h => (False.elim (h u8))))
  have u11 : s 43 ≠ true := (Or.elim c119 (fun h => h) (fun h => (False.elim (h u8))))
  have u12 : s 5 = true := (Or.elim c148 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u7 h))))))))))
  have u13 : s 35 ≠ true := (Or.elim c16 (fun h => (False.elim (h u12))) (fun h => h))
  have u14 : s 8 = true := (Or.elim c151 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u7 h))))))))))
  have u15 : s 41 ≠ true := (Or.elim c25 (fun h => (False.elim (h u14))) (fun h => h))
  have u16 : s 52 = true := (Or.elim c152 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))))))
  have u17 : s 21 ≠ true := (Or.elim c71 (fun h => h) (fun h => (False.elim (h u16))))
  have u18 : s 28 ≠ true := (Or.elim c90 (fun h => h) (fun h => (False.elim (h u16))))
  have u19 : s 30 = true := (Or.elim c139 (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u15 h))))))))))
  have u20 : s 4 = true := (Or.elim c146 (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (False.elim (u6 h))))))))))
  exact (Or.elim c15 (fun h => (h u20)) (fun h => (h u19)))

private theorem step221 (s : Fin 60 → Bool)
    (c201 : s 59 ≠ true)
    (c92 : s 29 ≠ true ∨ s 48 ≠ true)
    (c8 : s 2 ≠ true ∨ s 29 ≠ true)
    (c152 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true ∨ s 59 = true)
    (c71 : s 21 ≠ true ∨ s 52 ≠ true)
    (c90 : s 28 ≠ true ∨ s 52 ≠ true)
    (c139 : s 2 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 41 = true)
    (c146 : s 2 = true ∨ s 4 = true ∨ s 20 = true ∨ s 28 = true ∨ s 48 = true)
    (c15 : s 4 ≠ true ∨ s 30 ≠ true)
    : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 59 ≠ true := c201
  have u1 : s 48 ≠ true := (Or.elim c92 (fun h => (False.elim (h a3))) (fun h => h))
  have u2 : s 2 ≠ true := (Or.elim c8 (fun h => h) (fun h => (False.elim (h a3))))
  have u3 : s 52 = true := (Or.elim c152 (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))))))
  have u4 : s 21 ≠ true := (Or.elim c71 (fun h => h) (fun h => (False.elim (h u3))))
  have u5 : s 28 ≠ true := (Or.elim c90 (fun h => h) (fun h => (False.elim (h u3))))
  have u6 : s 30 = true := (Or.elim c139 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a1 h))))))))))
  have u7 : s 4 = true := (Or.elim c146 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u1 h))))))))))
  exact (Or.elim c15 (fun h => (h u7)) (fun h => (h u6)))

private theorem step222 (s : Fin 60 → Bool)
    (c138 : s 1 = true ∨ s 3 = true ∨ s 21 = true ∨ s 32 = true ∨ s 45 = true)
    (c121 : s 12 = true ∨ s 21 = true ∨ s 32 = true ∨ s 41 = true ∨ s 49 = true)
    (c45 : s 12 ≠ true ∨ s 45 ≠ true)
    : s 32 = true ∨ s 21 = true ∨ s 3 = true ∨ s 49 = true ∨ s 1 = true ∨ s 41 = true := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5⟩ := hc
  have u0 : s 45 = true := (Or.elim c138 (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => h))))))))
  have u1 : s 12 = true := (Or.elim c121 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => (False.elim (a3 h))))))))))
  exact (Or.elim c45 (fun h => (h u1)) (fun h => (h u0)))

private theorem step223 (s : Fin 60 → Bool)
    (c21 : s 7 ≠ true ∨ s 36 ≠ true)
    (c22 : s 7 ≠ true ∨ s 39 ≠ true)
    (c150 : s 9 = true ∨ s 16 = true ∨ s 18 = true ∨ s 35 = true ∨ s 36 = true)
    (c31 : s 9 ≠ true ∨ s 47 ≠ true)
    (c34 : s 9 ≠ true ∨ s 49 ≠ true)
    (c157 : s 0 = true ∨ s 18 = true ∨ s 30 = true ∨ s 39 = true ∨ s 57 = true)
    (c12 : s 3 ≠ true ∨ s 30 ≠ true)
    (c72 : s 21 ≠ true ∨ s 30 ≠ true)
    (c222 : s 32 = true ∨ s 21 = true ∨ s 3 = true ∨ s 49 = true ∨ s 1 = true ∨ s 41 = true)
    (c137 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 47 = true ∨ s 52 = true)
    (c36 : s 10 ≠ true ∨ s 32 ≠ true)
    : s 7 ≠ true ∨ s 52 = true ∨ s 1 = true ∨ s 0 = true ∨ s 41 = true ∨ s 18 = true ∨ s 35 = true ∨ s 19 = true ∨ s 16 = true ∨ s 13 = true ∨ s 57 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10⟩ := hc
  have u0 : s 36 ≠ true := (Or.elim c21 (fun h => (False.elim (h a0))) (fun h => h))
  have u1 : s 39 ≠ true := (Or.elim c22 (fun h => (False.elim (h a0))) (fun h => h))
  have u2 : s 9 = true := (Or.elim c150 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a8 h))) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => (Or.elim h (fun h => (False.elim (a6 h))) (fun h => (False.elim (u0 h))))))))))
  have u3 : s 47 ≠ true := (Or.elim c31 (fun h => (False.elim (h u2))) (fun h => h))
  have u4 : s 49 ≠ true := (Or.elim c34 (fun h => (False.elim (h u2))) (fun h => h))
  have u5 : s 30 = true := (Or.elim c157 (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a10 h))))))))))
  have u6 : s 3 ≠ true := (Or.elim c12 (fun h => h) (fun h => (False.elim (h u5))))
  have u7 : s 21 ≠ true := (Or.elim c72 (fun h => h) (fun h => (False.elim (h u5))))
  have u8 : s 32 = true := (Or.elim c222 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (a4 h))))))))))))
  have u9 : s 10 = true := (Or.elim c137 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a9 h))) (fun h => (Or.elim h (fun h => (False.elim (a7 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (a1 h))))))))))
  exact (Or.elim c36 (fun h => (h u9)) (fun h => (h u8)))

private theorem step224 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c223 : s 7 ≠ true ∨ s 52 = true ∨ s 1 = true ∨ s 0 = true ∨ s 41 = true ∨ s 18 = true ∨ s 35 = true ∨ s 19 = true ∨ s 16 = true ∨ s 13 = true ∨ s 57 = true)
    (c149 : s 0 = true ∨ s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 37 = true)
    : s 52 = true ∨ s 1 = true ∨ s 57 = true ∨ s 0 = true ∨ s 41 = true ∨ s 18 = true ∨ s 35 = true ∨ s 19 = true ∨ s 16 = true ∨ s 13 = true := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 7 ≠ true := (Or.elim c223 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => (Or.elim h (fun h => (False.elim (a6 h))) (fun h => (Or.elim h (fun h => (False.elim (a7 h))) (fun h => (Or.elim h (fun h => (False.elim (a8 h))) (fun h => (Or.elim h (fun h => (False.elim (a9 h))) (fun h => (False.elim (a2 h))))))))))))))))))))))
  exact (Or.elim c149 (fun h => (a3 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (a8 h)) (fun h => (Or.elim h (fun h => (a5 h)) (fun h => (u0 h)))))))))

private theorem step225 (s : Fin 60 → Bool)
    (c93 : s 29 ≠ true ∨ s 53 ≠ true)
    (c65 : s 19 ≠ true ∨ s 51 ≠ true)
    (c49 : s 13 ≠ true ∨ s 51 ≠ true)
    (c58 : s 17 ≠ true ∨ s 51 ≠ true)
    (c148 : s 5 = true ∨ s 13 = true ∨ s 17 = true ∨ s 19 = true ∨ s 53 = true)
    (c18 : s 5 ≠ true ∨ s 18 ≠ true)
    (c16 : s 5 ≠ true ∨ s 35 ≠ true)
    (c119 : s 43 ≠ true ∨ s 51 ≠ true)
    (c57 : s 16 ≠ true ∨ s 51 ≠ true)
    (c94 : s 29 ≠ true ∨ s 57 ≠ true)
    (c221 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 29 ≠ true)
    (c3 : s 0 ≠ true ∨ s 20 ≠ true)
    (c5 : s 1 ≠ true ∨ s 20 ≠ true)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    (c224 : s 52 = true ∨ s 1 = true ∨ s 57 = true ∨ s 0 = true ∨ s 41 = true ∨ s 18 = true ∨ s 35 = true ∨ s 19 = true ∨ s 16 = true ∨ s 13 = true)
    : s 41 = true ∨ s 51 ≠ true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 53 ≠ true := (Or.elim c93 (fun h => (False.elim (h a2))) (fun h => h))
  have u1 : s 19 ≠ true := (Or.elim c65 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 13 ≠ true := (Or.elim c49 (fun h => h) (fun h => (False.elim (h a1))))
  have u3 : s 17 ≠ true := (Or.elim c58 (fun h => h) (fun h => (False.elim (h a1))))
  have u4 : s 5 = true := (Or.elim c148 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))))
  have u5 : s 18 ≠ true := (Or.elim c18 (fun h => (False.elim (h u4))) (fun h => h))
  have u6 : s 35 ≠ true := (Or.elim c16 (fun h => (False.elim (h u4))) (fun h => h))
  have u7 : s 43 ≠ true := (Or.elim c119 (fun h => h) (fun h => (False.elim (h a1))))
  have u8 : s 16 ≠ true := (Or.elim c57 (fun h => h) (fun h => (False.elim (h a1))))
  have u9 : s 57 ≠ true := (Or.elim c94 (fun h => (False.elim (h a2))) (fun h => h))
  have u10 : s 20 = true := (Or.elim c221 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (h a2))))))))
  have u11 : s 0 ≠ true := (Or.elim c3 (fun h => h) (fun h => (False.elim (h u10))))
  have u12 : s 1 ≠ true := (Or.elim c5 (fun h => h) (fun h => (False.elim (h u10))))
  have u13 : s 52 ≠ true := (Or.elim c68 (fun h => (False.elim (h u10))) (fun h => h))
  exact (Or.elim c224 (fun h => (u13 h)) (fun h => (Or.elim h (fun h => (u12 h)) (fun h => (Or.elim h (fun h => (u9 h)) (fun h => (Or.elim h (fun h => (u11 h)) (fun h => (Or.elim h (fun h => (a0 h)) (fun h => (Or.elim h (fun h => (u5 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u8 h)) (fun h => (u2 h)))))))))))))))))))

private theorem step226 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c93 : s 29 ≠ true ∨ s 53 ≠ true)
    (c119 : s 43 ≠ true ∨ s 51 ≠ true)
    (c225 : s 41 = true ∨ s 51 ≠ true ∨ s 29 ≠ true)
    (c75 : s 23 ≠ true ∨ s 41 ≠ true)
    (c78 : s 24 ≠ true ∨ s 41 ≠ true)
    (c130 : s 23 = true ∨ s 24 = true ∨ s 37 = true ∨ s 43 = true ∨ s 53 = true)
    : s 51 ≠ true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 53 ≠ true := (Or.elim c93 (fun h => (False.elim (h a1))) (fun h => h))
  have u2 : s 43 ≠ true := (Or.elim c119 (fun h => h) (fun h => (False.elim (h a0))))
  have u3 : s 41 = true := (Or.elim c225 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (False.elim (h a1))))))
  have u4 : s 23 ≠ true := (Or.elim c75 (fun h => h) (fun h => (False.elim (h u3))))
  have u5 : s 24 ≠ true := (Or.elim c78 (fun h => h) (fun h => (False.elim (h u3))))
  exact (Or.elim c130 (fun h => (u4 h)) (fun h => (Or.elim h (fun h => (u5 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (u1 h)))))))))

private theorem step227 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c75 : s 23 ≠ true ∨ s 41 ≠ true)
    (c93 : s 29 ≠ true ∨ s 53 ≠ true)
    (c78 : s 24 ≠ true ∨ s 41 ≠ true)
    (c130 : s 23 = true ∨ s 24 = true ∨ s 37 = true ∨ s 43 = true ∨ s 53 = true)
    (c118 : s 43 ≠ true ∨ s 50 ≠ true)
    (c25 : s 8 ≠ true ∨ s 41 ≠ true)
    (c226 : s 51 ≠ true ∨ s 29 ≠ true)
    (c91 : s 29 ≠ true ∨ s 38 ≠ true)
    (c141 : s 10 = true ∨ s 18 = true ∨ s 24 = true ∨ s 50 = true ∨ s 51 = true)
    (c37 : s 10 ≠ true ∨ s 16 ≠ true)
    (c145 : s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 38 = true ∨ s 51 = true)
    (c126 : s 8 = true ∨ s 16 = true ∨ s 18 = true ∨ s 35 = true ∨ s 51 = true)
    (c20 : s 7 ≠ true ∨ s 35 ≠ true)
    : s 18 = true ∨ s 41 ≠ true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 23 ≠ true := (Or.elim c75 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 53 ≠ true := (Or.elim c93 (fun h => (False.elim (h a2))) (fun h => h))
  have u3 : s 24 ≠ true := (Or.elim c78 (fun h => h) (fun h => (False.elim (h a1))))
  have u4 : s 43 = true := (Or.elim c130 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u2 h))))))))))
  have u5 : s 50 ≠ true := (Or.elim c118 (fun h => (False.elim (h u4))) (fun h => h))
  have u6 : s 8 ≠ true := (Or.elim c25 (fun h => h) (fun h => (False.elim (h a1))))
  have u7 : s 51 ≠ true := (Or.elim c226 (fun h => h) (fun h => (False.elim (h a2))))
  have u8 : s 38 ≠ true := (Or.elim c91 (fun h => (False.elim (h a2))) (fun h => h))
  have u9 : s 10 = true := (Or.elim c141 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u7 h))))))))))
  have u10 : s 16 ≠ true := (Or.elim c37 (fun h => (False.elim (h u9))) (fun h => h))
  have u11 : s 7 = true := (Or.elim c145 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u7 h))))))))))
  have u12 : s 35 = true := (Or.elim c126 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u7 h))))))))))
  exact (Or.elim c20 (fun h => (h u11)) (fun h => (h u12)))

private theorem step228 (s : Fin 60 → Bool)
    (c201 : s 59 ≠ true)
    (c43 : s 11 ≠ true ∨ s 55 ≠ true)
    (c54 : s 14 ≠ true ∨ s 55 ≠ true)
    (c97 : s 34 ≠ true ∨ s 55 ≠ true)
    (c142 : s 11 = true ∨ s 14 = true ∨ s 34 = true ∨ s 50 = true ∨ s 59 = true)
    : s 55 ≠ true ∨ s 50 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 59 ≠ true := c201
  have u1 : s 11 ≠ true := (Or.elim c43 (fun h => h) (fun h => (False.elim (h a0))))
  have u2 : s 14 ≠ true := (Or.elim c54 (fun h => h) (fun h => (False.elim (h a0))))
  have u3 : s 34 ≠ true := (Or.elim c97 (fun h => h) (fun h => (False.elim (h a0))))
  exact (Or.elim c142 (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (Or.elim h (fun h => (a1 h)) (fun h => (u0 h)))))))))

private theorem step229 (s : Fin 60 → Bool)
    (c30 : s 9 ≠ true ∨ s 46 ≠ true)
    (c113 : s 42 ≠ true ∨ s 46 ≠ true)
    (c134 : s 8 = true ∨ s 9 = true ∨ s 35 = true ∨ s 42 = true ∨ s 48 = true)
    : s 46 ≠ true ∨ s 35 = true ∨ s 8 = true ∨ s 48 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 9 ≠ true := (Or.elim c30 (fun h => h) (fun h => (False.elim (h a0))))
  have u1 : s 42 ≠ true := (Or.elim c113 (fun h => h) (fun h => (False.elim (h a0))))
  exact (Or.elim c134 (fun h => (a2 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (Or.elim h (fun h => (a1 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (a3 h)))))))))

private theorem step230 (s : Fin 60 → Bool)
    (c52 : s 14 ≠ true ∨ s 32 ≠ true)
    (c53 : s 14 ≠ true ∨ s 17 ≠ true)
    (c138 : s 1 = true ∨ s 3 = true ∨ s 21 = true ∨ s 32 = true ∨ s 45 = true)
    (c155 : s 5 = true ∨ s 7 = true ∨ s 17 = true ∨ s 31 = true ∨ s 36 = true)
    (c13 : s 3 ≠ true ∨ s 31 ≠ true)
    : s 14 ≠ true ∨ s 7 = true ∨ s 45 = true ∨ s 1 = true ∨ s 36 = true ∨ s 5 = true ∨ s 21 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6⟩ := hc
  have u0 : s 32 ≠ true := (Or.elim c52 (fun h => (False.elim (h a0))) (fun h => h))
  have u1 : s 17 ≠ true := (Or.elim c53 (fun h => (False.elim (h a0))) (fun h => h))
  have u2 : s 3 = true := (Or.elim c138 (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a6 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (a2 h))))))))))
  have u3 : s 31 = true := (Or.elim c155 (fun h => (False.elim (a5 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a4 h))))))))))
  exact (Or.elim c13 (fun h => (h u2)) (fun h => (h u3)))

private theorem step231 (s : Fin 60 → Bool)
    (c60 : s 18 ≠ true ∨ s 36 ≠ true)
    (c18 : s 5 ≠ true ∨ s 18 ≠ true)
    (c42 : s 11 ≠ true ∨ s 17 ≠ true)
    (c44 : s 11 ≠ true ∨ s 31 ≠ true)
    (c155 : s 5 = true ∨ s 7 = true ∨ s 17 = true ∨ s 31 = true ∨ s 36 = true)
    : s 11 ≠ true ∨ s 7 = true ∨ s 18 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 36 ≠ true := (Or.elim c60 (fun h => (False.elim (h a2))) (fun h => h))
  have u1 : s 5 ≠ true := (Or.elim c18 (fun h => h) (fun h => (False.elim (h a2))))
  have u2 : s 17 ≠ true := (Or.elim c42 (fun h => (False.elim (h a0))) (fun h => h))
  have u3 : s 31 ≠ true := (Or.elim c44 (fun h => (False.elim (h a0))) (fun h => h))
  exact (Or.elim c155 (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (a1 h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (u0 h)))))))))

private theorem step232 (s : Fin 60 → Bool)
    (c201 : s 59 ≠ true)
    (c60 : s 18 ≠ true ∨ s 36 ≠ true)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    (c18 : s 5 ≠ true ∨ s 18 ≠ true)
    (c230 : s 14 ≠ true ∨ s 7 = true ∨ s 45 = true ∨ s 1 = true ∨ s 36 = true ∨ s 5 = true ∨ s 21 = true)
    (c163 : s 9 = true ∨ s 14 = true ∨ s 35 = true ∨ s 47 = true ∨ s 58 = true)
    (c231 : s 11 ≠ true ∨ s 7 = true ∨ s 18 ≠ true)
    (c99 : s 34 ≠ true ∨ s 58 ≠ true)
    (c142 : s 11 = true ∨ s 14 = true ∨ s 34 = true ∨ s 50 = true ∨ s 59 = true)
    : s 7 = true ∨ s 47 = true ∨ s 45 = true ∨ s 9 = true ∨ s 1 = true ∨ s 18 ≠ true ∨ s 50 = true ∨ s 21 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7⟩ := hc
  have u0 : s 59 ≠ true := c201
  have u1 : s 36 ≠ true := (Or.elim c60 (fun h => (False.elim (h a5))) (fun h => h))
  have u2 : s 35 ≠ true := (Or.elim c59 (fun h => (False.elim (h a5))) (fun h => h))
  have u3 : s 5 ≠ true := (Or.elim c18 (fun h => h) (fun h => (False.elim (h a5))))
  have u4 : s 14 ≠ true := (Or.elim c230 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (a7 h))))))))))))))
  have u5 : s 58 = true := (Or.elim c163 (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => h))))))))
  have u6 : s 11 ≠ true := (Or.elim c231 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (h a5))))))
  have u7 : s 34 ≠ true := (Or.elim c99 (fun h => h) (fun h => (False.elim (h u5))))
  exact (Or.elim c142 (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (u4 h)) (fun h => (Or.elim h (fun h => (u7 h)) (fun h => (Or.elim h (fun h => (a6 h)) (fun h => (u0 h)))))))))

private theorem step233 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    (c229 : s 46 ≠ true ∨ s 35 = true ∨ s 8 = true ∨ s 48 = true)
    (c2 : s 0 ≠ true ∨ s 18 ≠ true)
    (c134 : s 8 = true ∨ s 9 = true ∨ s 35 = true ∨ s 42 = true ∨ s 48 = true)
    (c112 : s 42 ≠ true ∨ s 45 ≠ true)
    (c114 : s 42 ≠ true ∨ s 47 ≠ true)
    (c232 : s 7 = true ∨ s 47 = true ∨ s 45 = true ∨ s 9 = true ∨ s 1 = true ∨ s 18 ≠ true ∨ s 50 = true ∨ s 21 = true)
    (c23 : s 7 ≠ true ∨ s 40 ≠ true)
    (c123 : s 4 = true ∨ s 8 = true ∨ s 40 = true ∨ s 46 = true ∨ s 49 = true)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    (c15 : s 4 ≠ true ∨ s 30 ≠ true)
    (c158 : s 0 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 33 = true)
    (c11 : s 3 ≠ true ∨ s 33 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c128 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 32 = true ∨ s 37 = true)
    (c99 : s 34 ≠ true ∨ s 58 ≠ true)
    (c52 : s 14 ≠ true ∨ s 32 ≠ true)
    (c163 : s 9 = true ∨ s 14 = true ∨ s 35 = true ∨ s 47 = true ∨ s 58 = true)
    : s 9 = true ∨ s 1 = true ∨ s 18 ≠ true ∨ s 50 = true ∨ s 49 = true ∨ s 21 = true ∨ s 8 = true ∨ s 48 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 35 ≠ true := (Or.elim c59 (fun h => (False.elim (h a2))) (fun h => h))
  have u2 : s 46 ≠ true := (Or.elim c229 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a6 h))) (fun h => (False.elim (a7 h))))))))
  have u3 : s 0 ≠ true := (Or.elim c2 (fun h => h) (fun h => (False.elim (h a2))))
  have u4 : s 42 = true := (Or.elim c134 (fun h => (False.elim (a6 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a7 h))))))))))
  have u5 : s 45 ≠ true := (Or.elim c112 (fun h => (False.elim (h u4))) (fun h => h))
  have u6 : s 47 ≠ true := (Or.elim c114 (fun h => (False.elim (h u4))) (fun h => h))
  have u7 : s 7 = true := (Or.elim c232 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (h a2))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (a5 h))))))))))))))))
  have u8 : s 40 ≠ true := (Or.elim c23 (fun h => (False.elim (h u7))) (fun h => h))
  have u9 : s 4 = true := (Or.elim c123 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a6 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a4 h))))))))))
  have u10 : s 20 ≠ true := (Or.elim c14 (fun h => (False.elim (h u9))) (fun h => h))
  have u11 : s 30 ≠ true := (Or.elim c15 (fun h => (False.elim (h u9))) (fun h => h))
  have u12 : s 33 = true := (Or.elim c158 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => h))))))))
  have u13 : s 3 ≠ true := (Or.elim c11 (fun h => h) (fun h => (False.elim (h u12))))
  have u14 : s 34 = true := (Or.elim c124 (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))))))
  have u15 : s 32 = true := (Or.elim c128 (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))))))
  have u16 : s 58 ≠ true := (Or.elim c99 (fun h => (False.elim (h u14))) (fun h => h))
  have u17 : s 14 ≠ true := (Or.elim c52 (fun h => h) (fun h => (False.elim (h u15))))
  exact (Or.elim c163 (fun h => (a0 h)) (fun h => (Or.elim h (fun h => (u17 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (u16 h)))))))))

private theorem step234 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    (c15 : s 4 ≠ true ∨ s 30 ≠ true)
    (c158 : s 0 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 33 = true)
    (c11 : s 3 ≠ true ∨ s 33 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c128 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 32 = true ∨ s 37 = true)
    (c41 : s 11 ≠ true ∨ s 34 ≠ true)
    (c52 : s 14 ≠ true ∨ s 32 ≠ true)
    (c133 : s 11 = true ∨ s 14 = true ∨ s 31 = true ∨ s 50 = true ∨ s 57 = true)
    : s 4 ≠ true ∨ s 31 = true ∨ s 0 = true ∨ s 50 = true ∨ s 21 = true ∨ s 57 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 20 ≠ true := (Or.elim c14 (fun h => (False.elim (h a0))) (fun h => h))
  have u2 : s 30 ≠ true := (Or.elim c15 (fun h => (False.elim (h a0))) (fun h => h))
  have u3 : s 33 = true := (Or.elim c158 (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => h))))))))
  have u4 : s 3 ≠ true := (Or.elim c11 (fun h => h) (fun h => (False.elim (h u3))))
  have u5 : s 34 = true := (Or.elim c124 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))))))
  have u6 : s 32 = true := (Or.elim c128 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))))))
  have u7 : s 11 ≠ true := (Or.elim c41 (fun h => h) (fun h => (False.elim (h u5))))
  have u8 : s 14 ≠ true := (Or.elim c52 (fun h => h) (fun h => (False.elim (h u6))))
  exact (Or.elim c133 (fun h => (u7 h)) (fun h => (Or.elim h (fun h => (u8 h)) (fun h => (Or.elim h (fun h => (a1 h)) (fun h => (Or.elim h (fun h => (a3 h)) (fun h => (a5 h)))))))))

private theorem step235 (s : Fin 60 → Bool)
    (c60 : s 18 ≠ true ∨ s 36 ≠ true)
    (c18 : s 5 ≠ true ∨ s 18 ≠ true)
    (c2 : s 0 ≠ true ∨ s 18 ≠ true)
    (c234 : s 4 ≠ true ∨ s 31 = true ∨ s 0 = true ∨ s 50 = true ∨ s 21 = true ∨ s 57 = true)
    (c123 : s 4 = true ∨ s 8 = true ∨ s 40 = true ∨ s 46 = true ∨ s 49 = true)
    (c23 : s 7 ≠ true ∨ s 40 ≠ true)
    (c231 : s 11 ≠ true ∨ s 7 = true ∨ s 18 ≠ true)
    (c155 : s 5 = true ∨ s 7 = true ∨ s 17 = true ∨ s 31 = true ∨ s 36 = true)
    (c133 : s 11 = true ∨ s 14 = true ∨ s 31 = true ∨ s 50 = true ∨ s 57 = true)
    (c53 : s 14 ≠ true ∨ s 17 ≠ true)
    : s 31 = true ∨ s 46 = true ∨ s 18 ≠ true ∨ s 50 = true ∨ s 49 = true ∨ s 21 = true ∨ s 8 = true ∨ s 57 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7⟩ := hc
  have u0 : s 36 ≠ true := (Or.elim c60 (fun h => (False.elim (h a2))) (fun h => h))
  have u1 : s 5 ≠ true := (Or.elim c18 (fun h => h) (fun h => (False.elim (h a2))))
  have u2 : s 0 ≠ true := (Or.elim c2 (fun h => h) (fun h => (False.elim (h a2))))
  have u3 : s 4 ≠ true := (Or.elim c234 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => (False.elim (a7 h))))))))))))
  have u4 : s 40 = true := (Or.elim c123 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (a6 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (a4 h))))))))))
  have u5 : s 7 ≠ true := (Or.elim c23 (fun h => h) (fun h => (False.elim (h u4))))
  have u6 : s 11 ≠ true := (Or.elim c231 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (h a2))))))
  have u7 : s 17 = true := (Or.elim c155 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u0 h))))))))))
  have u8 : s 14 = true := (Or.elim c133 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (a7 h))))))))))
  exact (Or.elim c53 (fun h => (h u8)) (fun h => (h u7)))

private theorem step236 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c94 : s 29 ≠ true ∨ s 57 ≠ true)
    (c93 : s 29 ≠ true ∨ s 53 ≠ true)
    (c92 : s 29 ≠ true ∨ s 48 ≠ true)
    (c25 : s 8 ≠ true ∨ s 41 ≠ true)
    (c70 : s 21 ≠ true ∨ s 41 ≠ true)
    (c75 : s 23 ≠ true ∨ s 41 ≠ true)
    (c78 : s 24 ≠ true ∨ s 41 ≠ true)
    (c109 : s 41 ≠ true ∨ s 49 ≠ true)
    (c130 : s 23 = true ∨ s 24 = true ∨ s 37 = true ∨ s 43 = true ∨ s 53 = true)
    (c118 : s 43 ≠ true ∨ s 50 ≠ true)
    (c227 : s 18 = true ∨ s 41 ≠ true ∨ s 29 ≠ true)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    (c229 : s 46 ≠ true ∨ s 35 = true ∨ s 8 = true ∨ s 48 = true)
    (c235 : s 31 = true ∨ s 46 = true ∨ s 18 ≠ true ∨ s 50 = true ∨ s 49 = true ∨ s 21 = true ∨ s 8 = true ∨ s 57 = true)
    (c13 : s 3 ≠ true ∨ s 31 ≠ true)
    (c35 : s 9 ≠ true ∨ s 31 ≠ true)
    (c134 : s 8 = true ∨ s 9 = true ∨ s 35 = true ∨ s 42 = true ∨ s 48 = true)
    (c233 : s 9 = true ∨ s 1 = true ∨ s 18 ≠ true ∨ s 50 = true ∨ s 49 = true ∨ s 21 = true ∨ s 8 = true ∨ s 48 = true)
    (c114 : s 42 ≠ true ∨ s 47 ≠ true)
    (c5 : s 1 ≠ true ∨ s 20 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c128 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 32 = true ∨ s 37 = true)
    (c99 : s 34 ≠ true ∨ s 58 ≠ true)
    (c52 : s 14 ≠ true ∨ s 32 ≠ true)
    (c163 : s 9 = true ∨ s 14 = true ∨ s 35 = true ∨ s 47 = true ∨ s 58 = true)
    : s 41 ≠ true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 57 ≠ true := (Or.elim c94 (fun h => (False.elim (h a1))) (fun h => h))
  have u2 : s 53 ≠ true := (Or.elim c93 (fun h => (False.elim (h a1))) (fun h => h))
  have u3 : s 48 ≠ true := (Or.elim c92 (fun h => (False.elim (h a1))) (fun h => h))
  have u4 : s 8 ≠ true := (Or.elim c25 (fun h => h) (fun h => (False.elim (h a0))))
  have u5 : s 21 ≠ true := (Or.elim c70 (fun h => h) (fun h => (False.elim (h a0))))
  have u6 : s 23 ≠ true := (Or.elim c75 (fun h => h) (fun h => (False.elim (h a0))))
  have u7 : s 24 ≠ true := (Or.elim c78 (fun h => h) (fun h => (False.elim (h a0))))
  have u8 : s 49 ≠ true := (Or.elim c109 (fun h => (False.elim (h a0))) (fun h => h))
  have u9 : s 43 = true := (Or.elim c130 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u2 h))))))))))
  have u10 : s 50 ≠ true := (Or.elim c118 (fun h => (False.elim (h u9))) (fun h => h))
  have u11 : s 18 = true := (Or.elim c227 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (False.elim (h a1))))))
  have u12 : s 35 ≠ true := (Or.elim c59 (fun h => (False.elim (h u11))) (fun h => h))
  have u13 : s 46 ≠ true := (Or.elim c229 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u3 h))))))))
  have u14 : s 31 = true := (Or.elim c235 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (h u11))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))))))))))))
  have u15 : s 3 ≠ true := (Or.elim c13 (fun h => h) (fun h => (False.elim (h u14))))
  have u16 : s 9 ≠ true := (Or.elim c35 (fun h => h) (fun h => (False.elim (h u14))))
  have u17 : s 42 = true := (Or.elim c134 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u3 h))))))))))
  have u18 : s 1 = true := (Or.elim c233 (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h u11))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u3 h))))))))))))))))
  have u19 : s 47 ≠ true := (Or.elim c114 (fun h => (False.elim (h u17))) (fun h => h))
  have u20 : s 20 ≠ true := (Or.elim c5 (fun h => (False.elim (h u18))) (fun h => h))
  have u21 : s 34 = true := (Or.elim c124 (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))))))
  have u22 : s 32 = true := (Or.elim c128 (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))))))
  have u23 : s 58 ≠ true := (Or.elim c99 (fun h => (False.elim (h u21))) (fun h => h))
  have u24 : s 14 ≠ true := (Or.elim c52 (fun h => h) (fun h => (False.elim (h u22))))
  exact (Or.elim c163 (fun h => (u16 h)) (fun h => (Or.elim h (fun h => (u24 h)) (fun h => (Or.elim h (fun h => (u12 h)) (fun h => (Or.elim h (fun h => (u19 h)) (fun h => (u23 h)))))))))

private theorem step237 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    (c94 : s 29 ≠ true ∨ s 57 ≠ true)
    (c92 : s 29 ≠ true ∨ s 48 ≠ true)
    (c26 : s 8 ≠ true ∨ s 43 ≠ true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    (c229 : s 46 ≠ true ∨ s 35 = true ∨ s 8 = true ∨ s 48 = true)
    (c134 : s 8 = true ∨ s 9 = true ∨ s 35 = true ∨ s 42 = true ∨ s 48 = true)
    (c233 : s 9 = true ∨ s 1 = true ∨ s 18 ≠ true ∨ s 50 = true ∨ s 49 = true ∨ s 21 = true ∨ s 8 = true ∨ s 48 = true)
    (c235 : s 31 = true ∨ s 46 = true ∨ s 18 ≠ true ∨ s 50 = true ∨ s 49 = true ∨ s 21 = true ∨ s 8 = true ∨ s 57 = true)
    (c114 : s 42 ≠ true ∨ s 47 ≠ true)
    (c5 : s 1 ≠ true ∨ s 20 ≠ true)
    (c13 : s 3 ≠ true ∨ s 31 ≠ true)
    (c163 : s 9 = true ∨ s 14 = true ∨ s 35 = true ∨ s 47 = true ∨ s 58 = true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c99 : s 34 ≠ true ∨ s 58 ≠ true)
    : s 43 ≠ true ∨ s 9 = true ∨ s 21 = true ∨ s 14 = true ∨ s 50 = true ∨ s 18 ≠ true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 35 ≠ true := (Or.elim c59 (fun h => (False.elim (h a5))) (fun h => h))
  have u2 : s 57 ≠ true := (Or.elim c94 (fun h => (False.elim (h a6))) (fun h => h))
  have u3 : s 48 ≠ true := (Or.elim c92 (fun h => (False.elim (h a6))) (fun h => h))
  have u4 : s 8 ≠ true := (Or.elim c26 (fun h => h) (fun h => (False.elim (h a0))))
  have u5 : s 49 ≠ true := (Or.elim c117 (fun h => (False.elim (h a0))) (fun h => h))
  have u6 : s 46 ≠ true := (Or.elim c229 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u3 h))))))))
  have u7 : s 42 = true := (Or.elim c134 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u3 h))))))))))
  have u8 : s 1 = true := (Or.elim c233 (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a5))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u3 h))))))))))))))))
  have u9 : s 31 = true := (Or.elim c235 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (h a5))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))))))))))))
  have u10 : s 47 ≠ true := (Or.elim c114 (fun h => (False.elim (h u7))) (fun h => h))
  have u11 : s 20 ≠ true := (Or.elim c5 (fun h => (False.elim (h u8))) (fun h => h))
  have u12 : s 3 ≠ true := (Or.elim c13 (fun h => h) (fun h => (False.elim (h u9))))
  have u13 : s 58 = true := (Or.elim c163 (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => h))))))))
  have u14 : s 34 = true := (Or.elim c124 (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))))))
  exact (Or.elim c99 (fun h => (h u14)) (fun h => (h u13)))

private theorem step238 (s : Fin 60 → Bool)
    (c236 : s 41 ≠ true ∨ s 29 ≠ true)
    (c226 : s 51 ≠ true ∨ s 29 ≠ true)
    (c221 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 29 ≠ true)
    (c140 : s 10 = true ∨ s 16 = true ∨ s 43 = true ∨ s 50 = true ∨ s 51 = true)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    (c28 : s 8 ≠ true ∨ s 16 ≠ true)
    (c122 : s 8 = true ∨ s 21 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true)
    : s 43 = true ∨ s 21 = true ∨ s 50 = true ∨ s 10 = true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 41 ≠ true := (Or.elim c236 (fun h => h) (fun h => (False.elim (h a4))))
  have u1 : s 51 ≠ true := (Or.elim c226 (fun h => h) (fun h => (False.elim (h a4))))
  have u2 : s 20 = true := (Or.elim c221 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (h a4))))))))
  have u3 : s 16 = true := (Or.elim c140 (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u1 h))))))))))
  have u4 : s 52 ≠ true := (Or.elim c68 (fun h => (False.elim (h u2))) (fun h => h))
  have u5 : s 8 ≠ true := (Or.elim c28 (fun h => h) (fun h => (False.elim (h u3))))
  exact (Or.elim c122 (fun h => (u5 h)) (fun h => (Or.elim h (fun h => (a1 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (Or.elim h (fun h => (a0 h)) (fun h => (u4 h)))))))))

private theorem step239 (s : Fin 60 → Bool)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    (c38 : s 10 ≠ true ∨ s 18 ≠ true)
    (c94 : s 29 ≠ true ∨ s 57 ≠ true)
    (c92 : s 29 ≠ true ∨ s 48 ≠ true)
    (c238 : s 43 = true ∨ s 21 = true ∨ s 50 = true ∨ s 10 = true ∨ s 29 ≠ true)
    (c26 : s 8 ≠ true ∨ s 43 ≠ true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    (c237 : s 43 ≠ true ∨ s 9 = true ∨ s 21 = true ∨ s 14 = true ∨ s 50 = true ∨ s 18 ≠ true ∨ s 29 ≠ true)
    (c229 : s 46 ≠ true ∨ s 35 = true ∨ s 8 = true ∨ s 48 = true)
    (c35 : s 9 ≠ true ∨ s 31 ≠ true)
    (c235 : s 31 = true ∨ s 46 = true ∨ s 18 ≠ true ∨ s 50 = true ∨ s 49 = true ∨ s 21 = true ∨ s 8 = true ∨ s 57 = true)
    : s 21 = true ∨ s 14 = true ∨ s 50 = true ∨ s 18 ≠ true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 35 ≠ true := (Or.elim c59 (fun h => (False.elim (h a3))) (fun h => h))
  have u1 : s 10 ≠ true := (Or.elim c38 (fun h => h) (fun h => (False.elim (h a3))))
  have u2 : s 57 ≠ true := (Or.elim c94 (fun h => (False.elim (h a4))) (fun h => h))
  have u3 : s 48 ≠ true := (Or.elim c92 (fun h => (False.elim (h a4))) (fun h => h))
  have u4 : s 43 = true := (Or.elim c238 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (h a4))))))))))
  have u5 : s 8 ≠ true := (Or.elim c26 (fun h => h) (fun h => (False.elim (h u4))))
  have u6 : s 49 ≠ true := (Or.elim c117 (fun h => (False.elim (h u4))) (fun h => h))
  have u7 : s 9 = true := (Or.elim c237 (fun h => (False.elim (h u4))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (h a3))) (fun h => (False.elim (h a4))))))))))))))
  have u8 : s 46 ≠ true := (Or.elim c229 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u3 h))))))))
  have u9 : s 31 ≠ true := (Or.elim c35 (fun h => (False.elim (h u7))) (fun h => h))
  exact (Or.elim c235 (fun h => (u9 h)) (fun h => (Or.elim h (fun h => (u8 h)) (fun h => (Or.elim h (fun h => (h a3)) (fun h => (Or.elim h (fun h => (a2 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (a0 h)) (fun h => (Or.elim h (fun h => (u5 h)) (fun h => (u2 h)))))))))))))))

private theorem step240 (s : Fin 60 → Bool)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    (c38 : s 10 ≠ true ∨ s 18 ≠ true)
    (c2 : s 0 ≠ true ∨ s 18 ≠ true)
    (c236 : s 41 ≠ true ∨ s 29 ≠ true)
    (c226 : s 51 ≠ true ∨ s 29 ≠ true)
    (c92 : s 29 ≠ true ∨ s 48 ≠ true)
    (c23 : s 7 ≠ true ∨ s 40 ≠ true)
    (c24 : s 7 ≠ true ∨ s 16 ≠ true)
    (c140 : s 10 = true ∨ s 16 = true ∨ s 43 = true ∨ s 50 = true ∨ s 51 = true)
    (c26 : s 8 ≠ true ∨ s 43 ≠ true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    (c229 : s 46 ≠ true ∨ s 35 = true ∨ s 8 = true ∨ s 48 = true)
    (c120 : s 0 = true ∨ s 8 = true ∨ s 16 = true ∨ s 20 = true ∨ s 41 = true)
    (c123 : s 4 = true ∨ s 8 = true ∨ s 40 = true ∨ s 46 = true ∨ s 49 = true)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    : s 7 ≠ true ∨ s 50 = true ∨ s 18 ≠ true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 35 ≠ true := (Or.elim c59 (fun h => (False.elim (h a2))) (fun h => h))
  have u1 : s 10 ≠ true := (Or.elim c38 (fun h => h) (fun h => (False.elim (h a2))))
  have u2 : s 0 ≠ true := (Or.elim c2 (fun h => h) (fun h => (False.elim (h a2))))
  have u3 : s 41 ≠ true := (Or.elim c236 (fun h => h) (fun h => (False.elim (h a3))))
  have u4 : s 51 ≠ true := (Or.elim c226 (fun h => h) (fun h => (False.elim (h a3))))
  have u5 : s 48 ≠ true := (Or.elim c92 (fun h => (False.elim (h a3))) (fun h => h))
  have u6 : s 40 ≠ true := (Or.elim c23 (fun h => (False.elim (h a0))) (fun h => h))
  have u7 : s 16 ≠ true := (Or.elim c24 (fun h => (False.elim (h a0))) (fun h => h))
  have u8 : s 43 = true := (Or.elim c140 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u4 h))))))))))
  have u9 : s 8 ≠ true := (Or.elim c26 (fun h => h) (fun h => (False.elim (h u8))))
  have u10 : s 49 ≠ true := (Or.elim c117 (fun h => (False.elim (h u8))) (fun h => h))
  have u11 : s 46 ≠ true := (Or.elim c229 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u5 h))))))))
  have u12 : s 20 = true := (Or.elim c120 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u3 h))))))))))
  have u13 : s 4 = true := (Or.elim c123 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u10 h))))))))))
  exact (Or.elim c14 (fun h => (h u13)) (fun h => (h u12)))

private theorem step241 (s : Fin 60 → Bool)
    (c240 : s 7 ≠ true ∨ s 50 = true ∨ s 18 ≠ true ∨ s 29 ≠ true)
    (c231 : s 11 ≠ true ∨ s 7 = true ∨ s 18 ≠ true)
    (c94 : s 29 ≠ true ∨ s 57 ≠ true)
    (c239 : s 21 = true ∨ s 14 = true ∨ s 50 = true ∨ s 18 ≠ true ∨ s 29 ≠ true)
    (c133 : s 11 = true ∨ s 14 = true ∨ s 31 = true ∨ s 50 = true ∨ s 57 = true)
    (c73 : s 21 ≠ true ∨ s 31 ≠ true)
    : s 14 = true ∨ s 50 = true ∨ s 18 ≠ true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 7 ≠ true := (Or.elim c240 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (h a2))) (fun h => (False.elim (h a3))))))))
  have u1 : s 11 ≠ true := (Or.elim c231 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (h a2))))))
  have u2 : s 57 ≠ true := (Or.elim c94 (fun h => (False.elim (h a3))) (fun h => h))
  have u3 : s 21 = true := (Or.elim c239 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (h a2))) (fun h => (False.elim (h a3))))))))))
  have u4 : s 31 = true := (Or.elim c133 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u2 h))))))))))
  exact (Or.elim c73 (fun h => (h u3)) (fun h => (h u4)))

private theorem step242 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c60 : s 18 ≠ true ∨ s 36 ≠ true)
    (c38 : s 10 ≠ true ∨ s 18 ≠ true)
    (c18 : s 5 ≠ true ∨ s 18 ≠ true)
    (c236 : s 41 ≠ true ∨ s 29 ≠ true)
    (c240 : s 7 ≠ true ∨ s 50 = true ∨ s 18 ≠ true ∨ s 29 ≠ true)
    (c241 : s 14 = true ∨ s 50 = true ∨ s 18 ≠ true ∨ s 29 ≠ true)
    (c52 : s 14 ≠ true ∨ s 32 ≠ true)
    (c53 : s 14 ≠ true ∨ s 17 ≠ true)
    (c155 : s 5 = true ∨ s 7 = true ∨ s 17 = true ∨ s 31 = true ∨ s 36 = true)
    (c13 : s 3 ≠ true ∨ s 31 ≠ true)
    (c73 : s 21 ≠ true ∨ s 31 ≠ true)
    (c128 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 32 = true ∨ s 37 = true)
    (c5 : s 1 ≠ true ∨ s 20 ≠ true)
    (c238 : s 43 = true ∨ s 21 = true ∨ s 50 = true ∨ s 10 = true ∨ s 29 ≠ true)
    (c222 : s 32 = true ∨ s 21 = true ∨ s 3 = true ∨ s 49 = true ∨ s 1 = true ∨ s 41 = true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    : s 50 = true ∨ s 18 ≠ true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 36 ≠ true := (Or.elim c60 (fun h => (False.elim (h a1))) (fun h => h))
  have u2 : s 10 ≠ true := (Or.elim c38 (fun h => h) (fun h => (False.elim (h a1))))
  have u3 : s 5 ≠ true := (Or.elim c18 (fun h => h) (fun h => (False.elim (h a1))))
  have u4 : s 41 ≠ true := (Or.elim c236 (fun h => h) (fun h => (False.elim (h a2))))
  have u5 : s 7 ≠ true := (Or.elim c240 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (h a1))) (fun h => (False.elim (h a2))))))))
  have u6 : s 14 = true := (Or.elim c241 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (h a1))) (fun h => (False.elim (h a2))))))))
  have u7 : s 32 ≠ true := (Or.elim c52 (fun h => (False.elim (h u6))) (fun h => h))
  have u8 : s 17 ≠ true := (Or.elim c53 (fun h => (False.elim (h u6))) (fun h => h))
  have u9 : s 31 = true := (Or.elim c155 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u1 h))))))))))
  have u10 : s 3 ≠ true := (Or.elim c13 (fun h => h) (fun h => (False.elim (h u9))))
  have u11 : s 21 ≠ true := (Or.elim c73 (fun h => h) (fun h => (False.elim (h u9))))
  have u12 : s 20 = true := (Or.elim c128 (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u0 h))))))))))
  have u13 : s 1 ≠ true := (Or.elim c5 (fun h => h) (fun h => (False.elim (h u12))))
  have u14 : s 43 = true := (Or.elim c238 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (h a2))))))))))
  have u15 : s 49 = true := (Or.elim c222 (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u4 h))))))))))))
  exact (Or.elim c117 (fun h => (h u14)) (fun h => (h u15)))

private theorem step243 (s : Fin 60 → Bool)
    (c236 : s 41 ≠ true ∨ s 29 ≠ true)
    (c93 : s 29 ≠ true ∨ s 53 ≠ true)
    (c92 : s 29 ≠ true ∨ s 48 ≠ true)
    (c18 : s 5 ≠ true ∨ s 18 ≠ true)
    (c38 : s 10 ≠ true ∨ s 18 ≠ true)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    (c242 : s 50 = true ∨ s 18 ≠ true ∨ s 29 ≠ true)
    (c48 : s 13 ≠ true ∨ s 50 ≠ true)
    (c64 : s 19 ≠ true ∨ s 50 ≠ true)
    (c118 : s 43 ≠ true ∨ s 50 ≠ true)
    (c221 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 29 ≠ true)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    (c137 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 47 = true ∨ s 52 = true)
    (c31 : s 9 ≠ true ∨ s 47 ≠ true)
    (c87 : s 27 ≠ true ∨ s 47 ≠ true)
    (c114 : s 42 ≠ true ∨ s 47 ≠ true)
    (c159 : s 5 = true ∨ s 19 = true ∨ s 27 = true ∨ s 46 = true ∨ s 53 = true)
    (c134 : s 8 = true ∨ s 9 = true ∨ s 35 = true ∨ s 42 = true ∨ s 48 = true)
    (c27 : s 8 ≠ true ∨ s 46 ≠ true)
    : s 18 ≠ true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 41 ≠ true := (Or.elim c236 (fun h => h) (fun h => (False.elim (h a1))))
  have u1 : s 53 ≠ true := (Or.elim c93 (fun h => (False.elim (h a1))) (fun h => h))
  have u2 : s 48 ≠ true := (Or.elim c92 (fun h => (False.elim (h a1))) (fun h => h))
  have u3 : s 5 ≠ true := (Or.elim c18 (fun h => h) (fun h => (False.elim (h a0))))
  have u4 : s 10 ≠ true := (Or.elim c38 (fun h => h) (fun h => (False.elim (h a0))))
  have u5 : s 35 ≠ true := (Or.elim c59 (fun h => (False.elim (h a0))) (fun h => h))
  have u6 : s 50 = true := (Or.elim c242 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (False.elim (h a1))))))
  have u7 : s 13 ≠ true := (Or.elim c48 (fun h => h) (fun h => (False.elim (h u6))))
  have u8 : s 19 ≠ true := (Or.elim c64 (fun h => h) (fun h => (False.elim (h u6))))
  have u9 : s 43 ≠ true := (Or.elim c118 (fun h => h) (fun h => (False.elim (h u6))))
  have u10 : s 20 = true := (Or.elim c221 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (h a1))))))))
  have u11 : s 52 ≠ true := (Or.elim c68 (fun h => (False.elim (h u10))) (fun h => h))
  have u12 : s 47 = true := (Or.elim c137 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u11 h))))))))))
  have u13 : s 9 ≠ true := (Or.elim c31 (fun h => h) (fun h => (False.elim (h u12))))
  have u14 : s 27 ≠ true := (Or.elim c87 (fun h => h) (fun h => (False.elim (h u12))))
  have u15 : s 42 ≠ true := (Or.elim c114 (fun h => h) (fun h => (False.elim (h u12))))
  have u16 : s 46 = true := (Or.elim c159 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u1 h))))))))))
  have u17 : s 8 = true := (Or.elim c134 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u2 h))))))))))
  exact (Or.elim c27 (fun h => (h u17)) (fun h => (h u16)))

private theorem step244 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c236 : s 41 ≠ true ∨ s 29 ≠ true)
    (c118 : s 43 ≠ true ∨ s 50 ≠ true)
    (c221 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 29 ≠ true)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    (c3 : s 0 ≠ true ∨ s 20 ≠ true)
    (c64 : s 19 ≠ true ∨ s 50 ≠ true)
    (c48 : s 13 ≠ true ∨ s 50 ≠ true)
    (c243 : s 18 ≠ true ∨ s 29 ≠ true)
    (c93 : s 29 ≠ true ∨ s 53 ≠ true)
    (c198 : s 13 = true ∨ s 10 = true ∨ s 21 ≠ true ∨ s 18 = true)
    (c137 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 47 = true ∨ s 52 = true)
    (c122 : s 8 = true ∨ s 21 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true)
    (c31 : s 9 ≠ true ∨ s 47 ≠ true)
    (c87 : s 27 ≠ true ∨ s 47 ≠ true)
    (c27 : s 8 ≠ true ∨ s 46 ≠ true)
    (c28 : s 8 ≠ true ∨ s 16 ≠ true)
    (c166 : s 5 ≠ true ∨ s 16 = true ∨ s 0 = true ∨ s 9 = true ∨ s 37 = true)
    (c159 : s 5 = true ∨ s 19 = true ∨ s 27 = true ∨ s 46 = true ∨ s 53 = true)
    : s 10 = true ∨ s 50 ≠ true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 41 ≠ true := (Or.elim c236 (fun h => h) (fun h => (False.elim (h a2))))
  have u2 : s 43 ≠ true := (Or.elim c118 (fun h => h) (fun h => (False.elim (h a1))))
  have u3 : s 20 = true := (Or.elim c221 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (h a2))))))))
  have u4 : s 52 ≠ true := (Or.elim c68 (fun h => (False.elim (h u3))) (fun h => h))
  have u5 : s 0 ≠ true := (Or.elim c3 (fun h => h) (fun h => (False.elim (h u3))))
  have u6 : s 19 ≠ true := (Or.elim c64 (fun h => h) (fun h => (False.elim (h a1))))
  have u7 : s 13 ≠ true := (Or.elim c48 (fun h => h) (fun h => (False.elim (h a1))))
  have u8 : s 18 ≠ true := (Or.elim c243 (fun h => h) (fun h => (False.elim (h a2))))
  have u9 : s 53 ≠ true := (Or.elim c93 (fun h => (False.elim (h a2))) (fun h => h))
  have u10 : s 21 ≠ true := (Or.elim c198 (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u8 h))))))))
  have u11 : s 47 = true := (Or.elim c137 (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u4 h))))))))))
  have u12 : s 8 = true := (Or.elim c122 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u4 h))))))))))
  have u13 : s 9 ≠ true := (Or.elim c31 (fun h => h) (fun h => (False.elim (h u11))))
  have u14 : s 27 ≠ true := (Or.elim c87 (fun h => h) (fun h => (False.elim (h u11))))
  have u15 : s 46 ≠ true := (Or.elim c27 (fun h => (False.elim (h u12))) (fun h => h))
  have u16 : s 16 ≠ true := (Or.elim c28 (fun h => (False.elim (h u12))) (fun h => h))
  have u17 : s 5 ≠ true := (Or.elim c166 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u0 h))))))))))
  exact (Or.elim c159 (fun h => (u17 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (u14 h)) (fun h => (Or.elim h (fun h => (u15 h)) (fun h => (u9 h)))))))))

private theorem step245 (s : Fin 60 → Bool)
    (c243 : s 18 ≠ true ∨ s 29 ≠ true)
    (c236 : s 41 ≠ true ∨ s 29 ≠ true)
    (c226 : s 51 ≠ true ∨ s 29 ≠ true)
    (c94 : s 29 ≠ true ∨ s 57 ≠ true)
    (c91 : s 29 ≠ true ∨ s 38 ≠ true)
    (c48 : s 13 ≠ true ∨ s 50 ≠ true)
    (c64 : s 19 ≠ true ∨ s 50 ≠ true)
    (c118 : s 43 ≠ true ∨ s 50 ≠ true)
    (c221 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 29 ≠ true)
    (c3 : s 0 ≠ true ∨ s 20 ≠ true)
    (c5 : s 1 ≠ true ∨ s 20 ≠ true)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    (c244 : s 10 = true ∨ s 50 ≠ true ∨ s 29 ≠ true)
    (c37 : s 10 ≠ true ∨ s 16 ≠ true)
    (c145 : s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 38 = true ∨ s 51 = true)
    (c224 : s 52 = true ∨ s 1 = true ∨ s 57 = true ∨ s 0 = true ∨ s 41 = true ∨ s 18 = true ∨ s 35 = true ∨ s 19 = true ∨ s 16 = true ∨ s 13 = true)
    (c20 : s 7 ≠ true ∨ s 35 ≠ true)
    : s 50 ≠ true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 18 ≠ true := (Or.elim c243 (fun h => h) (fun h => (False.elim (h a1))))
  have u1 : s 41 ≠ true := (Or.elim c236 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 51 ≠ true := (Or.elim c226 (fun h => h) (fun h => (False.elim (h a1))))
  have u3 : s 57 ≠ true := (Or.elim c94 (fun h => (False.elim (h a1))) (fun h => h))
  have u4 : s 38 ≠ true := (Or.elim c91 (fun h => (False.elim (h a1))) (fun h => h))
  have u5 : s 13 ≠ true := (Or.elim c48 (fun h => h) (fun h => (False.elim (h a0))))
  have u6 : s 19 ≠ true := (Or.elim c64 (fun h => h) (fun h => (False.elim (h a0))))
  have u7 : s 43 ≠ true := (Or.elim c118 (fun h => h) (fun h => (False.elim (h a0))))
  have u8 : s 20 = true := (Or.elim c221 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (h a1))))))))
  have u9 : s 0 ≠ true := (Or.elim c3 (fun h => h) (fun h => (False.elim (h u8))))
  have u10 : s 1 ≠ true := (Or.elim c5 (fun h => h) (fun h => (False.elim (h u8))))
  have u11 : s 52 ≠ true := (Or.elim c68 (fun h => (False.elim (h u8))) (fun h => h))
  have u12 : s 10 = true := (Or.elim c244 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (False.elim (h a1))))))
  have u13 : s 16 ≠ true := (Or.elim c37 (fun h => (False.elim (h u12))) (fun h => h))
  have u14 : s 7 = true := (Or.elim c145 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))))))
  have u15 : s 35 = true := (Or.elim c224 (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u5 h))))))))))))))))))))
  exact (Or.elim c20 (fun h => (h u14)) (fun h => (h u15)))

private theorem step246 (s : Fin 60 → Bool)
    (c5 : s 1 ≠ true ∨ s 20 ≠ true)
    (c3 : s 0 ≠ true ∨ s 20 ≠ true)
    (c243 : s 18 ≠ true ∨ s 29 ≠ true)
    (c236 : s 41 ≠ true ∨ s 29 ≠ true)
    (c226 : s 51 ≠ true ∨ s 29 ≠ true)
    (c94 : s 29 ≠ true ∨ s 57 ≠ true)
    (c91 : s 29 ≠ true ∨ s 38 ≠ true)
    (c36 : s 10 ≠ true ∨ s 32 ≠ true)
    (c37 : s 10 ≠ true ∨ s 16 ≠ true)
    (c145 : s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 38 = true ∨ s 51 = true)
    (c20 : s 7 ≠ true ∨ s 35 ≠ true)
    (c21 : s 7 ≠ true ∨ s 36 ≠ true)
    (c22 : s 7 ≠ true ∨ s 39 ≠ true)
    (c150 : s 9 = true ∨ s 16 = true ∨ s 18 = true ∨ s 35 = true ∨ s 36 = true)
    (c157 : s 0 = true ∨ s 18 = true ∨ s 30 = true ∨ s 39 = true ∨ s 57 = true)
    (c34 : s 9 ≠ true ∨ s 49 ≠ true)
    (c12 : s 3 ≠ true ∨ s 30 ≠ true)
    (c72 : s 21 ≠ true ∨ s 30 ≠ true)
    (c222 : s 32 = true ∨ s 21 = true ∨ s 3 = true ∨ s 49 = true ∨ s 1 = true ∨ s 41 = true)
    : s 10 ≠ true ∨ s 20 ≠ true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 1 ≠ true := (Or.elim c5 (fun h => h) (fun h => (False.elim (h a1))))
  have u1 : s 0 ≠ true := (Or.elim c3 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 18 ≠ true := (Or.elim c243 (fun h => h) (fun h => (False.elim (h a2))))
  have u3 : s 41 ≠ true := (Or.elim c236 (fun h => h) (fun h => (False.elim (h a2))))
  have u4 : s 51 ≠ true := (Or.elim c226 (fun h => h) (fun h => (False.elim (h a2))))
  have u5 : s 57 ≠ true := (Or.elim c94 (fun h => (False.elim (h a2))) (fun h => h))
  have u6 : s 38 ≠ true := (Or.elim c91 (fun h => (False.elim (h a2))) (fun h => h))
  have u7 : s 32 ≠ true := (Or.elim c36 (fun h => (False.elim (h a0))) (fun h => h))
  have u8 : s 16 ≠ true := (Or.elim c37 (fun h => (False.elim (h a0))) (fun h => h))
  have u9 : s 7 = true := (Or.elim c145 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u4 h))))))))))
  have u10 : s 35 ≠ true := (Or.elim c20 (fun h => (False.elim (h u9))) (fun h => h))
  have u11 : s 36 ≠ true := (Or.elim c21 (fun h => (False.elim (h u9))) (fun h => h))
  have u12 : s 39 ≠ true := (Or.elim c22 (fun h => (False.elim (h u9))) (fun h => h))
  have u13 : s 9 = true := (Or.elim c150 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u11 h))))))))))
  have u14 : s 30 = true := (Or.elim c157 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u5 h))))))))))
  have u15 : s 49 ≠ true := (Or.elim c34 (fun h => (False.elim (h u13))) (fun h => h))
  have u16 : s 3 ≠ true := (Or.elim c12 (fun h => h) (fun h => (False.elim (h u14))))
  have u17 : s 21 ≠ true := (Or.elim c72 (fun h => h) (fun h => (False.elim (h u14))))
  exact (Or.elim c222 (fun h => (u7 h)) (fun h => (Or.elim h (fun h => (u17 h)) (fun h => (Or.elim h (fun h => (u16 h)) (fun h => (Or.elim h (fun h => (u15 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u3 h)))))))))))

private theorem step247 (s : Fin 60 → Bool)
    (c245 : s 50 ≠ true ∨ s 29 ≠ true)
    (c236 : s 41 ≠ true ∨ s 29 ≠ true)
    (c226 : s 51 ≠ true ∨ s 29 ≠ true)
    (c94 : s 29 ≠ true ∨ s 57 ≠ true)
    (c221 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 29 ≠ true)
    (c246 : s 10 ≠ true ∨ s 20 ≠ true ∨ s 29 ≠ true)
    (c140 : s 10 = true ∨ s 16 = true ∨ s 43 = true ∨ s 50 = true ∨ s 51 = true)
    (c238 : s 43 = true ∨ s 21 = true ∨ s 50 = true ∨ s 10 = true ∨ s 29 ≠ true)
    (c17 : s 5 ≠ true ∨ s 16 ≠ true)
    (c24 : s 7 ≠ true ∨ s 16 ≠ true)
    (c56 : s 16 ≠ true ∨ s 36 ≠ true)
    (c73 : s 21 ≠ true ∨ s 31 ≠ true)
    (c155 : s 5 = true ∨ s 7 = true ∨ s 17 = true ∨ s 31 = true ∨ s 36 = true)
    (c42 : s 11 ≠ true ∨ s 17 ≠ true)
    (c53 : s 14 ≠ true ∨ s 17 ≠ true)
    (c133 : s 11 = true ∨ s 14 = true ∨ s 31 = true ∨ s 50 = true ∨ s 57 = true)
    : s 43 = true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 50 ≠ true := (Or.elim c245 (fun h => h) (fun h => (False.elim (h a1))))
  have u1 : s 41 ≠ true := (Or.elim c236 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 51 ≠ true := (Or.elim c226 (fun h => h) (fun h => (False.elim (h a1))))
  have u3 : s 57 ≠ true := (Or.elim c94 (fun h => (False.elim (h a1))) (fun h => h))
  have u4 : s 20 = true := (Or.elim c221 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (h a1))))))))
  have u5 : s 10 ≠ true := (Or.elim c246 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h u4))) (fun h => (False.elim (h a1))))))
  have u6 : s 16 = true := (Or.elim c140 (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (u2 h))))))))))
  have u7 : s 21 = true := (Or.elim c238 (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (h a1))))))))))
  have u8 : s 5 ≠ true := (Or.elim c17 (fun h => h) (fun h => (False.elim (h u6))))
  have u9 : s 7 ≠ true := (Or.elim c24 (fun h => h) (fun h => (False.elim (h u6))))
  have u10 : s 36 ≠ true := (Or.elim c56 (fun h => (False.elim (h u6))) (fun h => h))
  have u11 : s 31 ≠ true := (Or.elim c73 (fun h => (False.elim (h u7))) (fun h => h))
  have u12 : s 17 = true := (Or.elim c155 (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u10 h))))))))))
  have u13 : s 11 ≠ true := (Or.elim c42 (fun h => h) (fun h => (False.elim (h u12))))
  have u14 : s 14 ≠ true := (Or.elim c53 (fun h => h) (fun h => (False.elim (h u12))))
  exact (Or.elim c133 (fun h => (u13 h)) (fun h => (Or.elim h (fun h => (u14 h)) (fun h => (Or.elim h (fun h => (u11 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u3 h)))))))))

private theorem step248 (s : Fin 60 → Bool)
    (c56 : s 16 ≠ true ∨ s 36 ≠ true)
    (c24 : s 7 ≠ true ∨ s 16 ≠ true)
    (c17 : s 5 ≠ true ∨ s 16 ≠ true)
    (c245 : s 50 ≠ true ∨ s 29 ≠ true)
    (c94 : s 29 ≠ true ∨ s 57 ≠ true)
    (c155 : s 5 = true ∨ s 7 = true ∨ s 17 = true ∨ s 31 = true ∨ s 36 = true)
    (c42 : s 11 ≠ true ∨ s 17 ≠ true)
    (c53 : s 14 ≠ true ∨ s 17 ≠ true)
    (c133 : s 11 = true ∨ s 14 = true ∨ s 31 = true ∨ s 50 = true ∨ s 57 = true)
    : s 31 = true ∨ s 16 ≠ true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 36 ≠ true := (Or.elim c56 (fun h => (False.elim (h a1))) (fun h => h))
  have u1 : s 7 ≠ true := (Or.elim c24 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 5 ≠ true := (Or.elim c17 (fun h => h) (fun h => (False.elim (h a1))))
  have u3 : s 50 ≠ true := (Or.elim c245 (fun h => h) (fun h => (False.elim (h a2))))
  have u4 : s 57 ≠ true := (Or.elim c94 (fun h => (False.elim (h a2))) (fun h => h))
  have u5 : s 17 = true := (Or.elim c155 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u0 h))))))))))
  have u6 : s 11 ≠ true := (Or.elim c42 (fun h => h) (fun h => (False.elim (h u5))))
  have u7 : s 14 ≠ true := (Or.elim c53 (fun h => h) (fun h => (False.elim (h u5))))
  exact (Or.elim c133 (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (u7 h)) (fun h => (Or.elim h (fun h => (a0 h)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (u4 h)))))))))

private theorem step249 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c222 : s 32 = true ∨ s 21 = true ∨ s 3 = true ∨ s 49 = true ∨ s 1 = true ∨ s 41 = true)
    (c128 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 32 = true ∨ s 37 = true)
    (c5 : s 1 ≠ true ∨ s 20 ≠ true)
    : s 3 = true ∨ s 21 = true ∨ s 41 = true ∨ s 49 = true ∨ s 32 = true := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 1 = true := (Or.elim c222 (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a2 h))))))))))))
  have u2 : s 20 = true := (Or.elim c128 (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (False.elim (u0 h))))))))))
  exact (Or.elim c5 (fun h => (h u1)) (fun h => (h u2)))

private theorem step250 (s : Fin 60 → Bool)
    (c247 : s 43 = true ∨ s 29 ≠ true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    (c236 : s 41 ≠ true ∨ s 29 ≠ true)
    (c13 : s 3 ≠ true ∨ s 31 ≠ true)
    (c73 : s 21 ≠ true ∨ s 31 ≠ true)
    (c249 : s 3 = true ∨ s 21 = true ∨ s 41 = true ∨ s 49 = true ∨ s 32 = true)
    : s 31 ≠ true ∨ s 32 = true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 43 = true := (Or.elim c247 (fun h => h) (fun h => (False.elim (h a2))))
  have u1 : s 49 ≠ true := (Or.elim c117 (fun h => (False.elim (h u0))) (fun h => h))
  have u2 : s 41 ≠ true := (Or.elim c236 (fun h => h) (fun h => (False.elim (h a2))))
  have u3 : s 3 ≠ true := (Or.elim c13 (fun h => h) (fun h => (False.elim (h a0))))
  have u4 : s 21 ≠ true := (Or.elim c73 (fun h => h) (fun h => (False.elim (h a0))))
  exact (Or.elim c249 (fun h => (u3 h)) (fun h => (Or.elim h (fun h => (u4 h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (a1 h)))))))))

private theorem step251 (s : Fin 60 → Bool)
    (c247 : s 43 = true ∨ s 29 ≠ true)
    (c26 : s 8 ≠ true ∨ s 43 ≠ true)
    (c243 : s 18 ≠ true ∨ s 29 ≠ true)
    (c226 : s 51 ≠ true ∨ s 29 ≠ true)
    (c91 : s 29 ≠ true ∨ s 38 ≠ true)
    (c145 : s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 38 = true ∨ s 51 = true)
    (c126 : s 8 = true ∨ s 16 = true ∨ s 18 = true ∨ s 35 = true ∨ s 51 = true)
    (c20 : s 7 ≠ true ∨ s 35 ≠ true)
    : s 16 = true ∨ s 29 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 43 = true := (Or.elim c247 (fun h => h) (fun h => (False.elim (h a1))))
  have u1 : s 8 ≠ true := (Or.elim c26 (fun h => h) (fun h => (False.elim (h u0))))
  have u2 : s 18 ≠ true := (Or.elim c243 (fun h => h) (fun h => (False.elim (h a1))))
  have u3 : s 51 ≠ true := (Or.elim c226 (fun h => h) (fun h => (False.elim (h a1))))
  have u4 : s 38 ≠ true := (Or.elim c91 (fun h => (False.elim (h a1))) (fun h => h))
  have u5 : s 7 = true := (Or.elim c145 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u3 h))))))))))
  have u6 : s 35 = true := (Or.elim c126 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u3 h))))))))))
  exact (Or.elim c20 (fun h => (h u5)) (fun h => (h u6)))

private theorem step252 (s : Fin 60 → Bool)
    (c226 : s 51 ≠ true ∨ s 29 ≠ true)
    (c243 : s 18 ≠ true ∨ s 29 ≠ true)
    (c245 : s 50 ≠ true ∨ s 29 ≠ true)
    (c251 : s 16 = true ∨ s 29 ≠ true)
    (c37 : s 10 ≠ true ∨ s 16 ≠ true)
    (c248 : s 31 = true ∨ s 16 ≠ true ∨ s 29 ≠ true)
    (c154 : s 10 = true ∨ s 13 = true ∨ s 18 = true ∨ s 50 = true ∨ s 51 = true)
    (c250 : s 31 ≠ true ∨ s 32 = true ∨ s 29 ≠ true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    : s 29 ≠ true := by
  by_contra hc
  have u0 : s 51 ≠ true := (Or.elim c226 (fun h => h) (fun h => (False.elim (h hc))))
  have u1 : s 18 ≠ true := (Or.elim c243 (fun h => h) (fun h => (False.elim (h hc))))
  have u2 : s 50 ≠ true := (Or.elim c245 (fun h => h) (fun h => (False.elim (h hc))))
  have u3 : s 16 = true := (Or.elim c251 (fun h => h) (fun h => (False.elim (h hc))))
  have u4 : s 10 ≠ true := (Or.elim c37 (fun h => h) (fun h => (False.elim (h u3))))
  have u5 : s 31 = true := (Or.elim c248 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h u3))) (fun h => (False.elim (h hc))))))
  have u6 : s 13 = true := (Or.elim c154 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u0 h))))))))))
  have u7 : s 32 = true := (Or.elim c250 (fun h => (False.elim (h u5))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (h hc))))))
  exact (Or.elim c47 (fun h => (h u6)) (fun h => (h u7)))

private theorem step253 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c57 : s 16 ≠ true ∨ s 51 ≠ true)
    (c37 : s 10 ≠ true ∨ s 16 ≠ true)
    (c28 : s 8 ≠ true ∨ s 16 ≠ true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    (c154 : s 10 = true ∨ s 13 = true ∨ s 18 = true ∨ s 50 = true ∨ s 51 = true)
    (c208 : s 51 = true ∨ s 55 = true ∨ s 13 = true ∨ s 10 = true ∨ s 18 = true)
    (c118 : s 43 ≠ true ∨ s 50 ≠ true)
    (c97 : s 34 ≠ true ∨ s 55 ≠ true)
    (c122 : s 8 = true ∨ s 21 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true)
    (c194 : s 32 ≠ true ∨ s 20 = true ∨ s 37 = true ∨ s 34 = true)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    : s 32 ≠ true ∨ s 41 = true ∨ s 18 = true ∨ s 21 = true ∨ s 16 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 51 ≠ true := (Or.elim c57 (fun h => (False.elim (h a4))) (fun h => h))
  have u2 : s 10 ≠ true := (Or.elim c37 (fun h => h) (fun h => (False.elim (h a4))))
  have u3 : s 8 ≠ true := (Or.elim c28 (fun h => h) (fun h => (False.elim (h a4))))
  have u4 : s 13 ≠ true := (Or.elim c47 (fun h => h) (fun h => (False.elim (h a0))))
  have u5 : s 50 = true := (Or.elim c154 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u1 h))))))))))
  have u6 : s 55 = true := (Or.elim c208 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a2 h))))))))))
  have u7 : s 43 ≠ true := (Or.elim c118 (fun h => h) (fun h => (False.elim (h u5))))
  have u8 : s 34 ≠ true := (Or.elim c97 (fun h => h) (fun h => (False.elim (h u6))))
  have u9 : s 52 = true := (Or.elim c122 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => h))))))))
  have u10 : s 20 = true := (Or.elim c194 (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (u8 h))))))))
  exact (Or.elim c68 (fun h => (h u10)) (fun h => (h u9)))

private theorem step254 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c73 : s 21 ≠ true ∨ s 31 ≠ true)
    (c13 : s 3 ≠ true ∨ s 31 ≠ true)
    (c28 : s 8 ≠ true ∨ s 16 ≠ true)
    (c253 : s 32 ≠ true ∨ s 41 = true ∨ s 18 = true ∨ s 21 = true ∨ s 16 ≠ true)
    (c128 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 32 = true ∨ s 37 = true)
    (c249 : s 3 = true ∨ s 21 = true ∨ s 41 = true ∨ s 49 = true ∨ s 32 = true)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    (c122 : s 8 = true ∨ s 21 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true)
    : s 41 = true ∨ s 18 = true ∨ s 31 ≠ true ∨ s 16 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 21 ≠ true := (Or.elim c73 (fun h => h) (fun h => (False.elim (h a2))))
  have u2 : s 3 ≠ true := (Or.elim c13 (fun h => h) (fun h => (False.elim (h a2))))
  have u3 : s 8 ≠ true := (Or.elim c28 (fun h => h) (fun h => (False.elim (h a3))))
  have u4 : s 32 ≠ true := (Or.elim c253 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (h a3))))))))))
  have u5 : s 20 = true := (Or.elim c128 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u0 h))))))))))
  have u6 : s 49 = true := (Or.elim c249 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u4 h))))))))))
  have u7 : s 52 ≠ true := (Or.elim c68 (fun h => (False.elim (h u5))) (fun h => h))
  have u8 : s 43 ≠ true := (Or.elim c117 (fun h => h) (fun h => (False.elim (h u6))))
  exact (Or.elim c122 (fun h => (u3 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (a0 h)) (fun h => (Or.elim h (fun h => (u8 h)) (fun h => (u7 h)))))))))

private theorem step255 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c73 : s 21 ≠ true ∨ s 31 ≠ true)
    (c13 : s 3 ≠ true ∨ s 31 ≠ true)
    (c57 : s 16 ≠ true ∨ s 51 ≠ true)
    (c37 : s 10 ≠ true ∨ s 16 ≠ true)
    (c254 : s 41 = true ∨ s 18 = true ∨ s 31 ≠ true ∨ s 16 ≠ true)
    (c75 : s 23 ≠ true ∨ s 41 ≠ true)
    (c78 : s 24 ≠ true ∨ s 41 ≠ true)
    (c109 : s 41 ≠ true ∨ s 49 ≠ true)
    (c141 : s 10 = true ∨ s 18 = true ∨ s 24 = true ∨ s 50 = true ∨ s 51 = true)
    (c48 : s 13 ≠ true ∨ s 50 ≠ true)
    (c64 : s 19 ≠ true ∨ s 50 ≠ true)
    (c118 : s 43 ≠ true ∨ s 50 ≠ true)
    (c208 : s 51 = true ∨ s 55 = true ∨ s 13 = true ∨ s 10 = true ∨ s 18 = true)
    (c130 : s 23 = true ∨ s 24 = true ∨ s 37 = true ∨ s 43 = true ∨ s 53 = true)
    (c97 : s 34 ≠ true ∨ s 55 ≠ true)
    (c80 : s 25 ≠ true ∨ s 53 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c7 : s 2 ≠ true ∨ s 20 ≠ true)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    (c135 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 49 = true)
    (c137 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 47 = true ∨ s 52 = true)
    (c87 : s 27 ≠ true ∨ s 47 ≠ true)
    : s 18 = true ∨ s 31 ≠ true ∨ s 16 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 21 ≠ true := (Or.elim c73 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 3 ≠ true := (Or.elim c13 (fun h => h) (fun h => (False.elim (h a1))))
  have u3 : s 51 ≠ true := (Or.elim c57 (fun h => (False.elim (h a2))) (fun h => h))
  have u4 : s 10 ≠ true := (Or.elim c37 (fun h => h) (fun h => (False.elim (h a2))))
  have u5 : s 41 = true := (Or.elim c254 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (h a1))) (fun h => (False.elim (h a2))))))))
  have u6 : s 23 ≠ true := (Or.elim c75 (fun h => h) (fun h => (False.elim (h u5))))
  have u7 : s 24 ≠ true := (Or.elim c78 (fun h => h) (fun h => (False.elim (h u5))))
  have u8 : s 49 ≠ true := (Or.elim c109 (fun h => (False.elim (h u5))) (fun h => h))
  have u9 : s 50 = true := (Or.elim c141 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u3 h))))))))))
  have u10 : s 13 ≠ true := (Or.elim c48 (fun h => h) (fun h => (False.elim (h u9))))
  have u11 : s 19 ≠ true := (Or.elim c64 (fun h => h) (fun h => (False.elim (h u9))))
  have u12 : s 43 ≠ true := (Or.elim c118 (fun h => h) (fun h => (False.elim (h u9))))
  have u13 : s 55 = true := (Or.elim c208 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (a0 h))))))))))
  have u14 : s 53 = true := (Or.elim c130 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => h))))))))
  have u15 : s 34 ≠ true := (Or.elim c97 (fun h => h) (fun h => (False.elim (h u13))))
  have u16 : s 25 ≠ true := (Or.elim c80 (fun h => h) (fun h => (False.elim (h u14))))
  have u17 : s 20 = true := (Or.elim c124 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u0 h))))))))))
  have u18 : s 2 ≠ true := (Or.elim c7 (fun h => h) (fun h => (False.elim (h u17))))
  have u19 : s 4 ≠ true := (Or.elim c14 (fun h => h) (fun h => (False.elim (h u17))))
  have u20 : s 52 ≠ true := (Or.elim c68 (fun h => (False.elim (h u17))) (fun h => h))
  have u21 : s 27 = true := (Or.elim c135 (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u8 h))))))))))
  have u22 : s 47 = true := (Or.elim c137 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u20 h))))))))))
  exact (Or.elim c87 (fun h => (h u21)) (fun h => (h u22)))

private theorem step256 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c255 : s 18 = true ∨ s 31 ≠ true ∨ s 16 ≠ true)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    (c2 : s 0 ≠ true ∨ s 18 ≠ true)
    (c73 : s 21 ≠ true ∨ s 31 ≠ true)
    (c13 : s 3 ≠ true ∨ s 31 ≠ true)
    (c57 : s 16 ≠ true ∨ s 51 ≠ true)
    (c37 : s 10 ≠ true ∨ s 16 ≠ true)
    (c32 : s 9 ≠ true ∨ s 16 ≠ true)
    (c28 : s 8 ≠ true ∨ s 16 ≠ true)
    (c51 : s 13 ≠ true ∨ s 53 ≠ true)
    (c66 : s 19 ≠ true ∨ s 53 ≠ true)
    (c132 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 51 = true ∨ s 55 = true)
    (c97 : s 34 ≠ true ∨ s 55 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c186 : s 52 ≠ true ∨ s 0 = true ∨ s 37 = true ∨ s 34 = true)
    (c173 : s 20 ≠ true ∨ s 48 ≠ true ∨ s 49 = true)
    (c137 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 47 = true ∨ s 52 = true)
    (c134 : s 8 = true ∨ s 9 = true ∨ s 35 = true ∨ s 42 = true ∨ s 48 = true)
    (c114 : s 42 ≠ true ∨ s 47 ≠ true)
    : s 53 ≠ true ∨ s 49 = true ∨ s 31 ≠ true ∨ s 16 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 18 = true := (Or.elim c255 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a2))) (fun h => (False.elim (h a3))))))
  have u2 : s 35 ≠ true := (Or.elim c59 (fun h => (False.elim (h u1))) (fun h => h))
  have u3 : s 0 ≠ true := (Or.elim c2 (fun h => h) (fun h => (False.elim (h u1))))
  have u4 : s 21 ≠ true := (Or.elim c73 (fun h => h) (fun h => (False.elim (h a2))))
  have u5 : s 3 ≠ true := (Or.elim c13 (fun h => h) (fun h => (False.elim (h a2))))
  have u6 : s 51 ≠ true := (Or.elim c57 (fun h => (False.elim (h a3))) (fun h => h))
  have u7 : s 10 ≠ true := (Or.elim c37 (fun h => h) (fun h => (False.elim (h a3))))
  have u8 : s 9 ≠ true := (Or.elim c32 (fun h => h) (fun h => (False.elim (h a3))))
  have u9 : s 8 ≠ true := (Or.elim c28 (fun h => h) (fun h => (False.elim (h a3))))
  have u10 : s 13 ≠ true := (Or.elim c51 (fun h => h) (fun h => (False.elim (h a0))))
  have u11 : s 19 ≠ true := (Or.elim c66 (fun h => h) (fun h => (False.elim (h a0))))
  have u12 : s 55 = true := (Or.elim c132 (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => h))))))))
  have u13 : s 34 ≠ true := (Or.elim c97 (fun h => h) (fun h => (False.elim (h u12))))
  have u14 : s 20 = true := (Or.elim c124 (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u0 h))))))))))
  have u15 : s 52 ≠ true := (Or.elim c186 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (u13 h))))))))
  have u16 : s 48 ≠ true := (Or.elim c173 (fun h => (False.elim (h u14))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a1 h))))))
  have u17 : s 47 = true := (Or.elim c137 (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u15 h))))))))))
  have u18 : s 42 = true := (Or.elim c134 (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u16 h))))))))))
  exact (Or.elim c114 (fun h => (h u18)) (fun h => (h u17)))

private theorem step257 (s : Fin 60 → Bool)
    (c252 : s 29 ≠ true)
    (c220 : s 37 ≠ true)
    (c255 : s 18 = true ∨ s 31 ≠ true ∨ s 16 ≠ true)
    (c62 : s 18 ≠ true ∨ s 39 ≠ true)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    (c73 : s 21 ≠ true ∨ s 31 ≠ true)
    (c13 : s 3 ≠ true ∨ s 31 ≠ true)
    (c32 : s 9 ≠ true ∨ s 16 ≠ true)
    (c28 : s 8 ≠ true ∨ s 16 ≠ true)
    (c75 : s 23 ≠ true ∨ s 41 ≠ true)
    (c78 : s 24 ≠ true ∨ s 41 ≠ true)
    (c109 : s 41 ≠ true ∨ s 49 ≠ true)
    (c256 : s 53 ≠ true ∨ s 49 = true ∨ s 31 ≠ true ∨ s 16 ≠ true)
    (c130 : s 23 = true ∨ s 24 = true ∨ s 37 = true ∨ s 43 = true ∨ s 53 = true)
    (c118 : s 43 ≠ true ∨ s 50 ≠ true)
    (c228 : s 55 ≠ true ∨ s 50 = true)
    (c161 : s 26 = true ∨ s 29 = true ∨ s 39 = true ∨ s 53 = true ∨ s 55 = true)
    (c84 : s 26 ≠ true ∨ s 48 ≠ true)
    (c134 : s 8 = true ∨ s 9 = true ∨ s 35 = true ∨ s 42 = true ∨ s 48 = true)
    (c233 : s 9 = true ∨ s 1 = true ∨ s 18 ≠ true ∨ s 50 = true ∨ s 49 = true ∨ s 21 = true ∨ s 8 = true ∨ s 48 = true)
    (c114 : s 42 ≠ true ∨ s 47 ≠ true)
    (c5 : s 1 ≠ true ∨ s 20 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c128 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 32 = true ∨ s 37 = true)
    (c99 : s 34 ≠ true ∨ s 58 ≠ true)
    (c52 : s 14 ≠ true ∨ s 32 ≠ true)
    (c163 : s 9 = true ∨ s 14 = true ∨ s 35 = true ∨ s 47 = true ∨ s 58 = true)
    : s 41 ≠ true ∨ s 31 ≠ true ∨ s 16 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 29 ≠ true := c252
  have u1 : s 37 ≠ true := c220
  have u2 : s 18 = true := (Or.elim c255 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a1))) (fun h => (False.elim (h a2))))))
  have u3 : s 39 ≠ true := (Or.elim c62 (fun h => (False.elim (h u2))) (fun h => h))
  have u4 : s 35 ≠ true := (Or.elim c59 (fun h => (False.elim (h u2))) (fun h => h))
  have u5 : s 21 ≠ true := (Or.elim c73 (fun h => h) (fun h => (False.elim (h a1))))
  have u6 : s 3 ≠ true := (Or.elim c13 (fun h => h) (fun h => (False.elim (h a1))))
  have u7 : s 9 ≠ true := (Or.elim c32 (fun h => h) (fun h => (False.elim (h a2))))
  have u8 : s 8 ≠ true := (Or.elim c28 (fun h => h) (fun h => (False.elim (h a2))))
  have u9 : s 23 ≠ true := (Or.elim c75 (fun h => h) (fun h => (False.elim (h a0))))
  have u10 : s 24 ≠ true := (Or.elim c78 (fun h => h) (fun h => (False.elim (h a0))))
  have u11 : s 49 ≠ true := (Or.elim c109 (fun h => (False.elim (h a0))) (fun h => h))
  have u12 : s 53 ≠ true := (Or.elim c256 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (h a1))) (fun h => (False.elim (h a2))))))))
  have u13 : s 43 = true := (Or.elim c130 (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u12 h))))))))))
  have u14 : s 50 ≠ true := (Or.elim c118 (fun h => (False.elim (h u13))) (fun h => h))
  have u15 : s 55 ≠ true := (Or.elim c228 (fun h => h) (fun h => (False.elim (u14 h))))
  have u16 : s 26 = true := (Or.elim c161 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u15 h))))))))))
  have u17 : s 48 ≠ true := (Or.elim c84 (fun h => (False.elim (h u16))) (fun h => h))
  have u18 : s 42 = true := (Or.elim c134 (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u17 h))))))))))
  have u19 : s 1 = true := (Or.elim c233 (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h u2))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u17 h))))))))))))))))
  have u20 : s 47 ≠ true := (Or.elim c114 (fun h => (False.elim (h u18))) (fun h => h))
  have u21 : s 20 ≠ true := (Or.elim c5 (fun h => (False.elim (h u19))) (fun h => h))
  have u22 : s 34 = true := (Or.elim c124 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u1 h))))))))))
  have u23 : s 32 = true := (Or.elim c128 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u1 h))))))))))
  have u24 : s 58 ≠ true := (Or.elim c99 (fun h => (False.elim (h u22))) (fun h => h))
  have u25 : s 14 ≠ true := (Or.elim c52 (fun h => h) (fun h => (False.elim (h u23))))
  exact (Or.elim c163 (fun h => (u7 h)) (fun h => (Or.elim h (fun h => (u25 h)) (fun h => (Or.elim h (fun h => (u4 h)) (fun h => (Or.elim h (fun h => (u20 h)) (fun h => (u24 h)))))))))

private theorem step258 (s : Fin 60 → Bool)
    (c201 : s 59 ≠ true)
    (c252 : s 29 ≠ true)
    (c13 : s 3 ≠ true ∨ s 31 ≠ true)
    (c257 : s 41 ≠ true ∨ s 31 ≠ true ∨ s 16 ≠ true)
    (c73 : s 21 ≠ true ∨ s 31 ≠ true)
    (c249 : s 3 = true ∨ s 21 = true ∨ s 41 = true ∨ s 49 = true ∨ s 32 = true)
    (c52 : s 14 ≠ true ∨ s 32 ≠ true)
    (c256 : s 53 ≠ true ∨ s 49 = true ∨ s 31 ≠ true ∨ s 16 ≠ true)
    (c255 : s 18 = true ∨ s 31 ≠ true ∨ s 16 ≠ true)
    (c62 : s 18 ≠ true ∨ s 39 ≠ true)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    (c44 : s 11 ≠ true ∨ s 31 ≠ true)
    (c32 : s 9 ≠ true ∨ s 16 ≠ true)
    (c28 : s 8 ≠ true ∨ s 16 ≠ true)
    (c228 : s 55 ≠ true ∨ s 50 = true)
    (c142 : s 11 = true ∨ s 14 = true ∨ s 34 = true ∨ s 50 = true ∨ s 59 = true)
    (c161 : s 26 = true ∨ s 29 = true ∨ s 39 = true ∨ s 53 = true ∨ s 55 = true)
    (c99 : s 34 ≠ true ∨ s 58 ≠ true)
    (c84 : s 26 ≠ true ∨ s 48 ≠ true)
    (c163 : s 9 = true ∨ s 14 = true ∨ s 35 = true ∨ s 47 = true ∨ s 58 = true)
    (c134 : s 8 = true ∨ s 9 = true ∨ s 35 = true ∨ s 42 = true ∨ s 48 = true)
    (c114 : s 42 ≠ true ∨ s 47 ≠ true)
    : s 50 = true ∨ s 49 = true ∨ s 31 ≠ true ∨ s 16 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 59 ≠ true := c201
  have u1 : s 29 ≠ true := c252
  have u2 : s 3 ≠ true := (Or.elim c13 (fun h => h) (fun h => (False.elim (h a2))))
  have u3 : s 41 ≠ true := (Or.elim c257 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a2))) (fun h => (False.elim (h a3))))))
  have u4 : s 21 ≠ true := (Or.elim c73 (fun h => h) (fun h => (False.elim (h a2))))
  have u5 : s 32 = true := (Or.elim c249 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => h))))))))
  have u6 : s 14 ≠ true := (Or.elim c52 (fun h => h) (fun h => (False.elim (h u5))))
  have u7 : s 53 ≠ true := (Or.elim c256 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (h a2))) (fun h => (False.elim (h a3))))))))
  have u8 : s 18 = true := (Or.elim c255 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a2))) (fun h => (False.elim (h a3))))))
  have u9 : s 39 ≠ true := (Or.elim c62 (fun h => (False.elim (h u8))) (fun h => h))
  have u10 : s 35 ≠ true := (Or.elim c59 (fun h => (False.elim (h u8))) (fun h => h))
  have u11 : s 11 ≠ true := (Or.elim c44 (fun h => h) (fun h => (False.elim (h a2))))
  have u12 : s 9 ≠ true := (Or.elim c32 (fun h => h) (fun h => (False.elim (h a3))))
  have u13 : s 8 ≠ true := (Or.elim c28 (fun h => h) (fun h => (False.elim (h a3))))
  have u14 : s 55 ≠ true := (Or.elim c228 (fun h => h) (fun h => (False.elim (a0 h))))
  have u15 : s 34 = true := (Or.elim c142 (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u0 h))))))))))
  have u16 : s 26 = true := (Or.elim c161 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u14 h))))))))))
  have u17 : s 58 ≠ true := (Or.elim c99 (fun h => (False.elim (h u15))) (fun h => h))
  have u18 : s 48 ≠ true := (Or.elim c84 (fun h => (False.elim (h u16))) (fun h => h))
  have u19 : s 47 = true := (Or.elim c163 (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u17 h))))))))))
  have u20 : s 42 = true := (Or.elim c134 (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u18 h))))))))))
  exact (Or.elim c114 (fun h => (h u20)) (fun h => (h u19)))

private theorem step259 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c257 : s 41 ≠ true ∨ s 31 ≠ true ∨ s 16 ≠ true)
    (c255 : s 18 = true ∨ s 31 ≠ true ∨ s 16 ≠ true)
    (c2 : s 0 ≠ true ∨ s 18 ≠ true)
    (c73 : s 21 ≠ true ∨ s 31 ≠ true)
    (c13 : s 3 ≠ true ∨ s 31 ≠ true)
    (c57 : s 16 ≠ true ∨ s 51 ≠ true)
    (c37 : s 10 ≠ true ∨ s 16 ≠ true)
    (c28 : s 8 ≠ true ∨ s 16 ≠ true)
    (c249 : s 3 = true ∨ s 21 = true ∨ s 41 = true ∨ s 49 = true ∨ s 32 = true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    (c258 : s 50 = true ∨ s 49 = true ∨ s 31 ≠ true ∨ s 16 ≠ true)
    (c64 : s 19 ≠ true ∨ s 50 ≠ true)
    (c118 : s 43 ≠ true ∨ s 50 ≠ true)
    (c132 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 51 = true ∨ s 55 = true)
    (c122 : s 8 = true ∨ s 21 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true)
    (c97 : s 34 ≠ true ∨ s 55 ≠ true)
    (c186 : s 52 ≠ true ∨ s 0 = true ∨ s 37 = true ∨ s 34 = true)
    : s 49 = true ∨ s 31 ≠ true ∨ s 16 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 41 ≠ true := (Or.elim c257 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a1))) (fun h => (False.elim (h a2))))))
  have u2 : s 18 = true := (Or.elim c255 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a1))) (fun h => (False.elim (h a2))))))
  have u3 : s 0 ≠ true := (Or.elim c2 (fun h => h) (fun h => (False.elim (h u2))))
  have u4 : s 21 ≠ true := (Or.elim c73 (fun h => h) (fun h => (False.elim (h a1))))
  have u5 : s 3 ≠ true := (Or.elim c13 (fun h => h) (fun h => (False.elim (h a1))))
  have u6 : s 51 ≠ true := (Or.elim c57 (fun h => (False.elim (h a2))) (fun h => h))
  have u7 : s 10 ≠ true := (Or.elim c37 (fun h => h) (fun h => (False.elim (h a2))))
  have u8 : s 8 ≠ true := (Or.elim c28 (fun h => h) (fun h => (False.elim (h a2))))
  have u9 : s 32 = true := (Or.elim c249 (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => h))))))))
  have u10 : s 13 ≠ true := (Or.elim c47 (fun h => h) (fun h => (False.elim (h u9))))
  have u11 : s 50 = true := (Or.elim c258 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (h a1))) (fun h => (False.elim (h a2))))))))
  have u12 : s 19 ≠ true := (Or.elim c64 (fun h => h) (fun h => (False.elim (h u11))))
  have u13 : s 43 ≠ true := (Or.elim c118 (fun h => h) (fun h => (False.elim (h u11))))
  have u14 : s 55 = true := (Or.elim c132 (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => h))))))))
  have u15 : s 52 = true := (Or.elim c122 (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => h))))))))
  have u16 : s 34 ≠ true := (Or.elim c97 (fun h => h) (fun h => (False.elim (h u14))))
  exact (Or.elim c186 (fun h => (h u15)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u16 h)))))))

private theorem step260 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c57 : s 16 ≠ true ∨ s 51 ≠ true)
    (c37 : s 10 ≠ true ∨ s 16 ≠ true)
    (c32 : s 9 ≠ true ∨ s 16 ≠ true)
    (c28 : s 8 ≠ true ∨ s 16 ≠ true)
    (c13 : s 3 ≠ true ∨ s 31 ≠ true)
    (c73 : s 21 ≠ true ∨ s 31 ≠ true)
    (c255 : s 18 = true ∨ s 31 ≠ true ∨ s 16 ≠ true)
    (c2 : s 0 ≠ true ∨ s 18 ≠ true)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    (c257 : s 41 ≠ true ∨ s 31 ≠ true ∨ s 16 ≠ true)
    (c259 : s 49 = true ∨ s 31 ≠ true ∨ s 16 ≠ true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    (c122 : s 8 = true ∨ s 21 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true)
    (c50 : s 13 ≠ true ∨ s 52 ≠ true)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    (c186 : s 52 ≠ true ∨ s 0 = true ∨ s 37 = true ∨ s 34 = true)
    (c128 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 32 = true ∨ s 37 = true)
    (c97 : s 34 ≠ true ∨ s 55 ≠ true)
    (c99 : s 34 ≠ true ∨ s 58 ≠ true)
    (c52 : s 14 ≠ true ∨ s 32 ≠ true)
    (c132 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 51 = true ∨ s 55 = true)
    (c163 : s 9 = true ∨ s 14 = true ∨ s 35 = true ∨ s 47 = true ∨ s 58 = true)
    (c66 : s 19 ≠ true ∨ s 53 ≠ true)
    (c114 : s 42 ≠ true ∨ s 47 ≠ true)
    (c151 : s 8 = true ∨ s 26 = true ∨ s 35 = true ∨ s 43 = true ∨ s 53 = true)
    (c134 : s 8 = true ∨ s 9 = true ∨ s 35 = true ∨ s 42 = true ∨ s 48 = true)
    (c84 : s 26 ≠ true ∨ s 48 ≠ true)
    : s 31 ≠ true ∨ s 16 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 51 ≠ true := (Or.elim c57 (fun h => (False.elim (h a1))) (fun h => h))
  have u2 : s 10 ≠ true := (Or.elim c37 (fun h => h) (fun h => (False.elim (h a1))))
  have u3 : s 9 ≠ true := (Or.elim c32 (fun h => h) (fun h => (False.elim (h a1))))
  have u4 : s 8 ≠ true := (Or.elim c28 (fun h => h) (fun h => (False.elim (h a1))))
  have u5 : s 3 ≠ true := (Or.elim c13 (fun h => h) (fun h => (False.elim (h a0))))
  have u6 : s 21 ≠ true := (Or.elim c73 (fun h => h) (fun h => (False.elim (h a0))))
  have u7 : s 18 = true := (Or.elim c255 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (False.elim (h a1))))))
  have u8 : s 0 ≠ true := (Or.elim c2 (fun h => h) (fun h => (False.elim (h u7))))
  have u9 : s 35 ≠ true := (Or.elim c59 (fun h => (False.elim (h u7))) (fun h => h))
  have u10 : s 41 ≠ true := (Or.elim c257 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (False.elim (h a1))))))
  have u11 : s 49 = true := (Or.elim c259 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (False.elim (h a1))))))
  have u12 : s 43 ≠ true := (Or.elim c117 (fun h => h) (fun h => (False.elim (h u11))))
  have u13 : s 52 = true := (Or.elim c122 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => h))))))))
  have u14 : s 13 ≠ true := (Or.elim c50 (fun h => h) (fun h => (False.elim (h u13))))
  have u15 : s 20 ≠ true := (Or.elim c68 (fun h => h) (fun h => (False.elim (h u13))))
  have u16 : s 34 = true := (Or.elim c186 (fun h => (False.elim (h u13))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => h))))))
  have u17 : s 32 = true := (Or.elim c128 (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))))))
  have u18 : s 55 ≠ true := (Or.elim c97 (fun h => (False.elim (h u16))) (fun h => h))
  have u19 : s 58 ≠ true := (Or.elim c99 (fun h => (False.elim (h u16))) (fun h => h))
  have u20 : s 14 ≠ true := (Or.elim c52 (fun h => h) (fun h => (False.elim (h u17))))
  have u21 : s 19 = true := (Or.elim c132 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u18 h))))))))))
  have u22 : s 47 = true := (Or.elim c163 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u19 h))))))))))
  have u23 : s 53 ≠ true := (Or.elim c66 (fun h => (False.elim (h u21))) (fun h => h))
  have u24 : s 42 ≠ true := (Or.elim c114 (fun h => h) (fun h => (False.elim (h u22))))
  have u25 : s 26 = true := (Or.elim c151 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u23 h))))))))))
  have u26 : s 48 = true := (Or.elim c134 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => h))))))))
  exact (Or.elim c84 (fun h => (h u25)) (fun h => (h u26)))

private theorem step261 (s : Fin 60 → Bool)
    (c252 : s 29 ≠ true)
    (c17 : s 5 ≠ true ∨ s 16 ≠ true)
    (c24 : s 7 ≠ true ∨ s 16 ≠ true)
    (c56 : s 16 ≠ true ∨ s 36 ≠ true)
    (c260 : s 31 ≠ true ∨ s 16 ≠ true)
    (c155 : s 5 = true ∨ s 7 = true ∨ s 17 = true ∨ s 31 = true ∨ s 36 = true)
    (c53 : s 14 ≠ true ∨ s 17 ≠ true)
    (c42 : s 11 ≠ true ∨ s 17 ≠ true)
    (c57 : s 16 ≠ true ∨ s 51 ≠ true)
    (c37 : s 10 ≠ true ∨ s 16 ≠ true)
    (c97 : s 34 ≠ true ∨ s 55 ≠ true)
    (c98 : s 34 ≠ true ∨ s 57 ≠ true)
    (c144 : s 11 = true ∨ s 29 = true ∨ s 32 = true ∨ s 55 = true ∨ s 57 = true)
    (c133 : s 11 = true ∨ s 14 = true ∨ s 31 = true ∨ s 50 = true ∨ s 57 = true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    (c64 : s 19 ≠ true ∨ s 50 ≠ true)
    (c132 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 51 = true ∨ s 55 = true)
    : s 34 ≠ true ∨ s 16 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 29 ≠ true := c252
  have u1 : s 5 ≠ true := (Or.elim c17 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 7 ≠ true := (Or.elim c24 (fun h => h) (fun h => (False.elim (h a1))))
  have u3 : s 36 ≠ true := (Or.elim c56 (fun h => (False.elim (h a1))) (fun h => h))
  have u4 : s 31 ≠ true := (Or.elim c260 (fun h => h) (fun h => (False.elim (h a1))))
  have u5 : s 17 = true := (Or.elim c155 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u3 h))))))))))
  have u6 : s 14 ≠ true := (Or.elim c53 (fun h => h) (fun h => (False.elim (h u5))))
  have u7 : s 11 ≠ true := (Or.elim c42 (fun h => h) (fun h => (False.elim (h u5))))
  have u8 : s 51 ≠ true := (Or.elim c57 (fun h => (False.elim (h a1))) (fun h => h))
  have u9 : s 10 ≠ true := (Or.elim c37 (fun h => h) (fun h => (False.elim (h a1))))
  have u10 : s 55 ≠ true := (Or.elim c97 (fun h => (False.elim (h a0))) (fun h => h))
  have u11 : s 57 ≠ true := (Or.elim c98 (fun h => (False.elim (h a0))) (fun h => h))
  have u12 : s 32 = true := (Or.elim c144 (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u11 h))))))))))
  have u13 : s 50 = true := (Or.elim c133 (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u11 h))))))))))
  have u14 : s 13 ≠ true := (Or.elim c47 (fun h => h) (fun h => (False.elim (h u12))))
  have u15 : s 19 ≠ true := (Or.elim c64 (fun h => h) (fun h => (False.elim (h u13))))
  exact (Or.elim c132 (fun h => (u9 h)) (fun h => (Or.elim h (fun h => (u14 h)) (fun h => (Or.elim h (fun h => (u15 h)) (fun h => (Or.elim h (fun h => (u8 h)) (fun h => (u10 h)))))))))

private theorem step262 (s : Fin 60 → Bool)
    (c201 : s 59 ≠ true)
    (c220 : s 37 ≠ true)
    (c17 : s 5 ≠ true ∨ s 16 ≠ true)
    (c24 : s 7 ≠ true ∨ s 16 ≠ true)
    (c28 : s 8 ≠ true ∨ s 16 ≠ true)
    (c32 : s 9 ≠ true ∨ s 16 ≠ true)
    (c37 : s 10 ≠ true ∨ s 16 ≠ true)
    (c56 : s 16 ≠ true ∨ s 36 ≠ true)
    (c260 : s 31 ≠ true ∨ s 16 ≠ true)
    (c155 : s 5 = true ∨ s 7 = true ∨ s 17 = true ∨ s 31 = true ∨ s 36 = true)
    (c1 : s 0 ≠ true ∨ s 17 ≠ true)
    (c42 : s 11 ≠ true ∨ s 17 ≠ true)
    (c53 : s 14 ≠ true ∨ s 17 ≠ true)
    (c261 : s 34 ≠ true ∨ s 16 ≠ true)
    (c142 : s 11 = true ∨ s 14 = true ∨ s 34 = true ∨ s 50 = true ∨ s 59 = true)
    (c186 : s 52 ≠ true ∨ s 0 = true ∨ s 37 = true ∨ s 34 = true)
    (c48 : s 13 ≠ true ∨ s 50 ≠ true)
    (c64 : s 19 ≠ true ∨ s 50 ≠ true)
    (c137 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 47 = true ∨ s 52 = true)
    (c127 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 32 = true ∨ s 52 = true)
    (c69 : s 21 ≠ true ∨ s 32 ≠ true)
    (c118 : s 43 ≠ true ∨ s 50 ≠ true)
    (c114 : s 42 ≠ true ∨ s 47 ≠ true)
    (c122 : s 8 = true ∨ s 21 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true)
    (c153 : s 8 = true ∨ s 9 = true ∨ s 31 = true ∨ s 42 = true ∨ s 49 = true)
    (c109 : s 41 ≠ true ∨ s 49 ≠ true)
    : s 16 ≠ true := by
  by_contra hc
  have u0 : s 59 ≠ true := c201
  have u1 : s 37 ≠ true := c220
  have u2 : s 5 ≠ true := (Or.elim c17 (fun h => h) (fun h => (False.elim (h hc))))
  have u3 : s 7 ≠ true := (Or.elim c24 (fun h => h) (fun h => (False.elim (h hc))))
  have u4 : s 8 ≠ true := (Or.elim c28 (fun h => h) (fun h => (False.elim (h hc))))
  have u5 : s 9 ≠ true := (Or.elim c32 (fun h => h) (fun h => (False.elim (h hc))))
  have u6 : s 10 ≠ true := (Or.elim c37 (fun h => h) (fun h => (False.elim (h hc))))
  have u7 : s 36 ≠ true := (Or.elim c56 (fun h => (False.elim (h hc))) (fun h => h))
  have u8 : s 31 ≠ true := (Or.elim c260 (fun h => h) (fun h => (False.elim (h hc))))
  have u9 : s 17 = true := (Or.elim c155 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u7 h))))))))))
  have u10 : s 0 ≠ true := (Or.elim c1 (fun h => h) (fun h => (False.elim (h u9))))
  have u11 : s 11 ≠ true := (Or.elim c42 (fun h => h) (fun h => (False.elim (h u9))))
  have u12 : s 14 ≠ true := (Or.elim c53 (fun h => h) (fun h => (False.elim (h u9))))
  have u13 : s 34 ≠ true := (Or.elim c261 (fun h => h) (fun h => (False.elim (h hc))))
  have u14 : s 50 = true := (Or.elim c142 (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))))))
  have u15 : s 52 ≠ true := (Or.elim c186 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u13 h))))))))
  have u16 : s 13 ≠ true := (Or.elim c48 (fun h => h) (fun h => (False.elim (h u14))))
  have u17 : s 19 ≠ true := (Or.elim c64 (fun h => h) (fun h => (False.elim (h u14))))
  have u18 : s 47 = true := (Or.elim c137 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u15 h))))))))))
  have u19 : s 32 = true := (Or.elim c127 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u15 h))))))))))
  have u20 : s 21 ≠ true := (Or.elim c69 (fun h => h) (fun h => (False.elim (h u19))))
  have u21 : s 43 ≠ true := (Or.elim c118 (fun h => h) (fun h => (False.elim (h u14))))
  have u22 : s 42 ≠ true := (Or.elim c114 (fun h => h) (fun h => (False.elim (h u18))))
  have u23 : s 41 = true := (Or.elim c122 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u15 h))))))))))
  have u24 : s 49 = true := (Or.elim c153 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => h))))))))
  exact (Or.elim c109 (fun h => (h u23)) (fun h => (h u24)))

private theorem step263 (s : Fin 60 → Bool)
    (c262 : s 16 ≠ true)
    (c27 : s 8 ≠ true ∨ s 46 ≠ true)
    (c176 : s 8 ≠ true ∨ s 5 = true ∨ s 13 = true ∨ s 16 = true ∨ s 53 = true ∨ s 52 = true ∨ s 10 = true)
    (c131 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 46 = true)
    (c80 : s 25 ≠ true ∨ s 53 ≠ true)
    : s 8 ≠ true ∨ s 4 = true ∨ s 2 = true ∨ s 5 = true ∨ s 27 = true ∨ s 52 = true ∨ s 13 = true ∨ s 10 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7⟩ := hc
  have u0 : s 16 ≠ true := c262
  have u1 : s 46 ≠ true := (Or.elim c27 (fun h => (False.elim (h a0))) (fun h => h))
  have u2 : s 53 = true := (Or.elim c176 (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a6 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => (False.elim (a7 h))))))))))))))
  have u3 : s 25 = true := (Or.elim c131 (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (False.elim (u1 h))))))))))
  exact (Or.elim c80 (fun h => (h u3)) (fun h => (h u2)))

private theorem step264 (s : Fin 60 → Bool)
    (c201 : s 59 ≠ true)
    (c220 : s 37 ≠ true)
    (c262 : s 16 ≠ true)
    (c40 : s 10 ≠ true ∨ s 55 ≠ true)
    (c43 : s 11 ≠ true ∨ s 55 ≠ true)
    (c54 : s 14 ≠ true ∨ s 55 ≠ true)
    (c228 : s 55 ≠ true ∨ s 50 = true)
    (c147 : s 11 = true ∨ s 14 = true ∨ s 17 = true ∨ s 34 = true ∨ s 59 = true)
    (c48 : s 13 ≠ true ∨ s 50 ≠ true)
    (c64 : s 19 ≠ true ∨ s 50 ≠ true)
    (c118 : s 43 ≠ true ∨ s 50 ≠ true)
    (c1 : s 0 ≠ true ∨ s 17 ≠ true)
    (c186 : s 52 ≠ true ∨ s 0 = true ∨ s 37 = true ∨ s 34 = true)
    (c137 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 47 = true ∨ s 52 = true)
    (c127 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 32 = true ∨ s 52 = true)
    (c31 : s 9 ≠ true ∨ s 47 ≠ true)
    (c87 : s 27 ≠ true ∨ s 47 ≠ true)
    (c114 : s 42 ≠ true ∨ s 47 ≠ true)
    (c69 : s 21 ≠ true ∨ s 32 ≠ true)
    (c194 : s 32 ≠ true ∨ s 20 = true ∨ s 37 = true ∨ s 34 = true)
    (c166 : s 5 ≠ true ∨ s 16 = true ∨ s 0 = true ∨ s 9 = true ∨ s 37 = true)
    (c7 : s 2 ≠ true ∨ s 20 ≠ true)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    (c263 : s 8 ≠ true ∨ s 4 = true ∨ s 2 = true ∨ s 5 = true ∨ s 27 = true ∨ s 52 = true ∨ s 13 = true ∨ s 10 = true)
    (c153 : s 8 = true ∨ s 9 = true ∨ s 31 = true ∨ s 42 = true ∨ s 49 = true)
    (c122 : s 8 = true ∨ s 21 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true)
    (c109 : s 41 ≠ true ∨ s 49 ≠ true)
    : s 55 ≠ true ∨ s 34 = true ∨ s 31 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 59 ≠ true := c201
  have u1 : s 37 ≠ true := c220
  have u2 : s 16 ≠ true := c262
  have u3 : s 10 ≠ true := (Or.elim c40 (fun h => h) (fun h => (False.elim (h a0))))
  have u4 : s 11 ≠ true := (Or.elim c43 (fun h => h) (fun h => (False.elim (h a0))))
  have u5 : s 14 ≠ true := (Or.elim c54 (fun h => h) (fun h => (False.elim (h a0))))
  have u6 : s 50 = true := (Or.elim c228 (fun h => (False.elim (h a0))) (fun h => h))
  have u7 : s 17 = true := (Or.elim c147 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u0 h))))))))))
  have u8 : s 13 ≠ true := (Or.elim c48 (fun h => h) (fun h => (False.elim (h u6))))
  have u9 : s 19 ≠ true := (Or.elim c64 (fun h => h) (fun h => (False.elim (h u6))))
  have u10 : s 43 ≠ true := (Or.elim c118 (fun h => h) (fun h => (False.elim (h u6))))
  have u11 : s 0 ≠ true := (Or.elim c1 (fun h => h) (fun h => (False.elim (h u7))))
  have u12 : s 52 ≠ true := (Or.elim c186 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))))
  have u13 : s 47 = true := (Or.elim c137 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u12 h))))))))))
  have u14 : s 32 = true := (Or.elim c127 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u12 h))))))))))
  have u15 : s 9 ≠ true := (Or.elim c31 (fun h => h) (fun h => (False.elim (h u13))))
  have u16 : s 27 ≠ true := (Or.elim c87 (fun h => h) (fun h => (False.elim (h u13))))
  have u17 : s 42 ≠ true := (Or.elim c114 (fun h => h) (fun h => (False.elim (h u13))))
  have u18 : s 21 ≠ true := (Or.elim c69 (fun h => h) (fun h => (False.elim (h u14))))
  have u19 : s 20 = true := (Or.elim c194 (fun h => (False.elim (h u14))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))))
  have u20 : s 5 ≠ true := (Or.elim c166 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u1 h))))))))))
  have u21 : s 2 ≠ true := (Or.elim c7 (fun h => h) (fun h => (False.elim (h u19))))
  have u22 : s 4 ≠ true := (Or.elim c14 (fun h => h) (fun h => (False.elim (h u19))))
  have u23 : s 8 ≠ true := (Or.elim c263 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u3 h))))))))))))))))
  have u24 : s 49 = true := (Or.elim c153 (fun h => (False.elim (u23 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => h))))))))
  have u25 : s 41 = true := (Or.elim c122 (fun h => (False.elim (u23 h))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u12 h))))))))))
  exact (Or.elim c109 (fun h => (h u25)) (fun h => (h u24)))

private theorem step265 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c252 : s 29 ≠ true)
    (c122 : s 8 = true ∨ s 21 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    (c76 : s 23 ≠ true ∨ s 52 ≠ true)
    (c186 : s 52 ≠ true ∨ s 0 = true ∨ s 37 = true ∨ s 34 = true)
    (c194 : s 32 ≠ true ∨ s 20 = true ∨ s 37 = true ∨ s 34 = true)
    (c2 : s 0 ≠ true ∨ s 18 ≠ true)
    (c4 : s 0 ≠ true ∨ s 30 ≠ true)
    (c203 : s 39 ≠ true ∨ s 29 = true ∨ s 32 = true ∨ s 13 = true)
    (c143 : s 18 = true ∨ s 29 = true ∨ s 38 = true ∨ s 39 = true ∨ s 55 = true)
    (c215 : s 35 ≠ true ∨ s 40 = true ∨ s 39 = true ∨ s 18 = true)
    (c139 : s 2 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 41 = true)
    (c82 : s 26 ≠ true ∨ s 38 ≠ true)
    (c102 : s 38 ≠ true ∨ s 58 ≠ true)
    (c6 : s 2 ≠ true ∨ s 45 ≠ true)
    (c156 : s 26 = true ∨ s 29 = true ∨ s 35 = true ∨ s 48 = true ∨ s 58 = true)
    (c129 : s 9 = true ∨ s 23 = true ∨ s 40 = true ∨ s 42 = true ∨ s 45 = true)
    (c33 : s 9 ≠ true ∨ s 48 ≠ true)
    : s 21 = true ∨ s 8 = true ∨ s 42 = true ∨ s 41 = true ∨ s 40 = true ∨ s 43 = true ∨ s 13 = true ∨ s 55 = true ∨ s 34 = true := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 29 ≠ true := c252
  have u2 : s 52 = true := (Or.elim c122 (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => h))))))))
  have u3 : s 20 ≠ true := (Or.elim c68 (fun h => h) (fun h => (False.elim (h u2))))
  have u4 : s 23 ≠ true := (Or.elim c76 (fun h => h) (fun h => (False.elim (h u2))))
  have u5 : s 0 = true := (Or.elim c186 (fun h => (False.elim (h u2))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (a8 h))))))))
  have u6 : s 32 ≠ true := (Or.elim c194 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (a8 h))))))))
  have u7 : s 18 ≠ true := (Or.elim c2 (fun h => (False.elim (h u5))) (fun h => h))
  have u8 : s 30 ≠ true := (Or.elim c4 (fun h => (False.elim (h u5))) (fun h => h))
  have u9 : s 39 ≠ true := (Or.elim c203 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (a6 h))))))))
  have u10 : s 38 = true := (Or.elim c143 (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (a7 h))))))))))
  have u11 : s 35 ≠ true := (Or.elim c215 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u7 h))))))))
  have u12 : s 2 = true := (Or.elim c139 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (a3 h))))))))))
  have u13 : s 26 ≠ true := (Or.elim c82 (fun h => h) (fun h => (False.elim (h u10))))
  have u14 : s 58 ≠ true := (Or.elim c102 (fun h => (False.elim (h u10))) (fun h => h))
  have u15 : s 45 ≠ true := (Or.elim c6 (fun h => (False.elim (h u12))) (fun h => h))
  have u16 : s 48 = true := (Or.elim c156 (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u14 h))))))))))
  have u17 : s 9 = true := (Or.elim c129 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u15 h))))))))))
  exact (Or.elim c33 (fun h => (h u17)) (fun h => (h u16)))

private theorem step266 (s : Fin 60 → Bool)
    (c262 : s 16 ≠ true)
    (c69 : s 21 ≠ true ∨ s 32 ≠ true)
    (c71 : s 21 ≠ true ∨ s 52 ≠ true)
    (c170 : s 16 = true ∨ s 32 = true ∨ s 43 = true ∨ s 52 = true ∨ s 10 = true)
    : s 21 ≠ true ∨ s 43 = true ∨ s 10 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 16 ≠ true := c262
  have u1 : s 32 ≠ true := (Or.elim c69 (fun h => (False.elim (h a0))) (fun h => h))
  have u2 : s 52 ≠ true := (Or.elim c71 (fun h => (False.elim (h a0))) (fun h => h))
  exact (Or.elim c170 (fun h => (u0 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (a1 h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (a2 h)))))))))

private theorem step267 (s : Fin 60 → Bool)
    (c201 : s 59 ≠ true)
    (c220 : s 37 ≠ true)
    (c262 : s 16 ≠ true)
    (c137 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 47 = true ∨ s 52 = true)
    (c152 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true ∨ s 59 = true)
    (c31 : s 9 ≠ true ∨ s 47 ≠ true)
    (c87 : s 27 ≠ true ∨ s 47 ≠ true)
    (c3 : s 0 ≠ true ∨ s 20 ≠ true)
    (c7 : s 2 ≠ true ∨ s 20 ≠ true)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    (c166 : s 5 ≠ true ∨ s 16 = true ∨ s 0 = true ∨ s 9 = true ∨ s 37 = true)
    (c263 : s 8 ≠ true ∨ s 4 = true ∨ s 2 = true ∨ s 5 = true ∨ s 27 = true ∨ s 52 = true ∨ s 13 = true ∨ s 10 = true)
    : s 52 = true ∨ s 8 ≠ true ∨ s 41 = true ∨ s 43 = true ∨ s 19 = true ∨ s 10 = true ∨ s 13 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6⟩ := hc
  have u0 : s 59 ≠ true := c201
  have u1 : s 37 ≠ true := c220
  have u2 : s 16 ≠ true := c262
  have u3 : s 47 = true := (Or.elim c137 (fun h => (False.elim (a5 h))) (fun h => (Or.elim h (fun h => (False.elim (a6 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a0 h))))))))))
  have u4 : s 20 = true := (Or.elim c152 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u0 h))))))))))
  have u5 : s 9 ≠ true := (Or.elim c31 (fun h => h) (fun h => (False.elim (h u3))))
  have u6 : s 27 ≠ true := (Or.elim c87 (fun h => h) (fun h => (False.elim (h u3))))
  have u7 : s 0 ≠ true := (Or.elim c3 (fun h => h) (fun h => (False.elim (h u4))))
  have u8 : s 2 ≠ true := (Or.elim c7 (fun h => h) (fun h => (False.elim (h u4))))
  have u9 : s 4 ≠ true := (Or.elim c14 (fun h => h) (fun h => (False.elim (h u4))))
  have u10 : s 5 ≠ true := (Or.elim c166 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u1 h))))))))))
  exact (Or.elim c263 (fun h => (h a1)) (fun h => (Or.elim h (fun h => (u9 h)) (fun h => (Or.elim h (fun h => (u8 h)) (fun h => (Or.elim h (fun h => (u10 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (a0 h)) (fun h => (Or.elim h (fun h => (a6 h)) (fun h => (a5 h)))))))))))))))

private theorem step268 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c252 : s 29 ≠ true)
    (c64 : s 19 ≠ true ∨ s 50 ≠ true)
    (c118 : s 43 ≠ true ∨ s 50 ≠ true)
    (c136 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 54 = true ∨ s 55 = true)
    (c107 : s 40 ≠ true ∨ s 54 ≠ true)
    (c110 : s 41 ≠ true ∨ s 54 ≠ true)
    (c115 : s 42 ≠ true ∨ s 54 ≠ true)
    (c266 : s 21 ≠ true ∨ s 43 = true ∨ s 10 = true)
    (c265 : s 21 = true ∨ s 8 = true ∨ s 42 = true ∨ s 41 = true ∨ s 40 = true ∨ s 43 = true ∨ s 13 = true ∨ s 55 = true ∨ s 34 = true)
    (c267 : s 52 = true ∨ s 8 ≠ true ∨ s 41 = true ∨ s 43 = true ∨ s 19 = true ∨ s 10 = true ∨ s 13 = true)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    (c76 : s 23 ≠ true ∨ s 52 ≠ true)
    (c186 : s 52 ≠ true ∨ s 0 = true ∨ s 37 = true ∨ s 34 = true)
    (c194 : s 32 ≠ true ∨ s 20 = true ∨ s 37 = true ∨ s 34 = true)
    (c2 : s 0 ≠ true ∨ s 18 ≠ true)
    (c4 : s 0 ≠ true ∨ s 30 ≠ true)
    (c203 : s 39 ≠ true ∨ s 29 = true ∨ s 32 = true ∨ s 13 = true)
    (c143 : s 18 = true ∨ s 29 = true ∨ s 38 = true ∨ s 39 = true ∨ s 55 = true)
    (c215 : s 35 ≠ true ∨ s 40 = true ∨ s 39 = true ∨ s 18 = true)
    (c139 : s 2 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 41 = true)
    (c82 : s 26 ≠ true ∨ s 38 ≠ true)
    (c102 : s 38 ≠ true ∨ s 58 ≠ true)
    (c6 : s 2 ≠ true ∨ s 45 ≠ true)
    (c156 : s 26 = true ∨ s 29 = true ∨ s 35 = true ∨ s 48 = true ∨ s 58 = true)
    (c129 : s 9 = true ∨ s 23 = true ∨ s 40 = true ∨ s 42 = true ∨ s 45 = true)
    (c33 : s 9 ≠ true ∨ s 48 ≠ true)
    : s 50 ≠ true ∨ s 10 = true ∨ s 13 = true ∨ s 55 = true ∨ s 34 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 29 ≠ true := c252
  have u2 : s 19 ≠ true := (Or.elim c64 (fun h => h) (fun h => (False.elim (h a0))))
  have u3 : s 43 ≠ true := (Or.elim c118 (fun h => h) (fun h => (False.elim (h a0))))
  have u4 : s 54 = true := (Or.elim c136 (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a3 h))))))))))
  have u5 : s 40 ≠ true := (Or.elim c107 (fun h => h) (fun h => (False.elim (h u4))))
  have u6 : s 41 ≠ true := (Or.elim c110 (fun h => h) (fun h => (False.elim (h u4))))
  have u7 : s 42 ≠ true := (Or.elim c115 (fun h => h) (fun h => (False.elim (h u4))))
  have u8 : s 21 ≠ true := (Or.elim c266 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (a1 h))))))
  have u9 : s 8 = true := (Or.elim c265 (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (a4 h))))))))))))))))))
  have u10 : s 52 = true := (Or.elim c267 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h u9))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (a2 h))))))))))))))
  have u11 : s 20 ≠ true := (Or.elim c68 (fun h => h) (fun h => (False.elim (h u10))))
  have u12 : s 23 ≠ true := (Or.elim c76 (fun h => h) (fun h => (False.elim (h u10))))
  have u13 : s 0 = true := (Or.elim c186 (fun h => (False.elim (h u10))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (a4 h))))))))
  have u14 : s 32 ≠ true := (Or.elim c194 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (a4 h))))))))
  have u15 : s 18 ≠ true := (Or.elim c2 (fun h => (False.elim (h u13))) (fun h => h))
  have u16 : s 30 ≠ true := (Or.elim c4 (fun h => (False.elim (h u13))) (fun h => h))
  have u17 : s 39 ≠ true := (Or.elim c203 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (a2 h))))))))
  have u18 : s 38 = true := (Or.elim c143 (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (a3 h))))))))))
  have u19 : s 35 ≠ true := (Or.elim c215 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u15 h))))))))
  have u20 : s 2 = true := (Or.elim c139 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (u6 h))))))))))
  have u21 : s 26 ≠ true := (Or.elim c82 (fun h => h) (fun h => (False.elim (h u18))))
  have u22 : s 58 ≠ true := (Or.elim c102 (fun h => (False.elim (h u18))) (fun h => h))
  have u23 : s 45 ≠ true := (Or.elim c6 (fun h => (False.elim (h u20))) (fun h => h))
  have u24 : s 48 = true := (Or.elim c156 (fun h => (False.elim (u21 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u22 h))))))))))
  have u25 : s 9 = true := (Or.elim c129 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u23 h))))))))))
  exact (Or.elim c33 (fun h => (h u25)) (fun h => (h u24)))

private theorem step269 (s : Fin 60 → Bool)
    (c262 : s 16 ≠ true)
    (c220 : s 37 ≠ true)
    (c252 : s 29 ≠ true)
    (c268 : s 50 ≠ true ∨ s 10 = true ∨ s 13 = true ∨ s 55 = true ∨ s 34 = true)
    (c140 : s 10 = true ∨ s 16 = true ∨ s 43 = true ∨ s 50 = true ∨ s 51 = true)
    (c167 : s 19 ≠ true ∨ s 16 = true ∨ s 43 = true ∨ s 10 = true)
    (c266 : s 21 ≠ true ∨ s 43 = true ∨ s 10 = true)
    (c210 : s 51 ≠ true ∨ s 54 = true ∨ s 13 = true ∨ s 10 = true)
    (c107 : s 40 ≠ true ∨ s 54 ≠ true)
    (c110 : s 41 ≠ true ∨ s 54 ≠ true)
    (c115 : s 42 ≠ true ∨ s 54 ≠ true)
    (c265 : s 21 = true ∨ s 8 = true ∨ s 42 = true ∨ s 41 = true ∨ s 40 = true ∨ s 43 = true ∨ s 13 = true ∨ s 55 = true ∨ s 34 = true)
    (c267 : s 52 = true ∨ s 8 ≠ true ∨ s 41 = true ∨ s 43 = true ∨ s 19 = true ∨ s 10 = true ∨ s 13 = true)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    (c76 : s 23 ≠ true ∨ s 52 ≠ true)
    (c186 : s 52 ≠ true ∨ s 0 = true ∨ s 37 = true ∨ s 34 = true)
    (c194 : s 32 ≠ true ∨ s 20 = true ∨ s 37 = true ∨ s 34 = true)
    (c2 : s 0 ≠ true ∨ s 18 ≠ true)
    (c4 : s 0 ≠ true ∨ s 30 ≠ true)
    (c203 : s 39 ≠ true ∨ s 29 = true ∨ s 32 = true ∨ s 13 = true)
    (c143 : s 18 = true ∨ s 29 = true ∨ s 38 = true ∨ s 39 = true ∨ s 55 = true)
    (c215 : s 35 ≠ true ∨ s 40 = true ∨ s 39 = true ∨ s 18 = true)
    (c139 : s 2 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 41 = true)
    (c82 : s 26 ≠ true ∨ s 38 ≠ true)
    (c102 : s 38 ≠ true ∨ s 58 ≠ true)
    (c6 : s 2 ≠ true ∨ s 45 ≠ true)
    (c156 : s 26 = true ∨ s 29 = true ∨ s 35 = true ∨ s 48 = true ∨ s 58 = true)
    (c129 : s 9 = true ∨ s 23 = true ∨ s 40 = true ∨ s 42 = true ∨ s 45 = true)
    (c33 : s 9 ≠ true ∨ s 48 ≠ true)
    : s 43 = true ∨ s 10 = true ∨ s 13 = true ∨ s 55 = true ∨ s 34 = true := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 16 ≠ true := c262
  have u1 : s 37 ≠ true := c220
  have u2 : s 29 ≠ true := c252
  have u3 : s 50 ≠ true := (Or.elim c268 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (a4 h))))))))))
  have u4 : s 51 = true := (Or.elim c140 (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => h))))))))
  have u5 : s 19 ≠ true := (Or.elim c167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))))
  have u6 : s 21 ≠ true := (Or.elim c266 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))
  have u7 : s 54 = true := (Or.elim c210 (fun h => (False.elim (h u4))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (a1 h))))))))
  have u8 : s 40 ≠ true := (Or.elim c107 (fun h => h) (fun h => (False.elim (h u7))))
  have u9 : s 41 ≠ true := (Or.elim c110 (fun h => h) (fun h => (False.elim (h u7))))
  have u10 : s 42 ≠ true := (Or.elim c115 (fun h => h) (fun h => (False.elim (h u7))))
  have u11 : s 8 = true := (Or.elim c265 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (a4 h))))))))))))))))))
  have u12 : s 52 = true := (Or.elim c267 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h u11))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (a2 h))))))))))))))
  have u13 : s 20 ≠ true := (Or.elim c68 (fun h => h) (fun h => (False.elim (h u12))))
  have u14 : s 23 ≠ true := (Or.elim c76 (fun h => h) (fun h => (False.elim (h u12))))
  have u15 : s 0 = true := (Or.elim c186 (fun h => (False.elim (h u12))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a4 h))))))))
  have u16 : s 32 ≠ true := (Or.elim c194 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a4 h))))))))
  have u17 : s 18 ≠ true := (Or.elim c2 (fun h => (False.elim (h u15))) (fun h => h))
  have u18 : s 30 ≠ true := (Or.elim c4 (fun h => (False.elim (h u15))) (fun h => h))
  have u19 : s 39 ≠ true := (Or.elim c203 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (a2 h))))))))
  have u20 : s 38 = true := (Or.elim c143 (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (a3 h))))))))))
  have u21 : s 35 ≠ true := (Or.elim c215 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u17 h))))))))
  have u22 : s 2 = true := (Or.elim c139 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (False.elim (u9 h))))))))))
  have u23 : s 26 ≠ true := (Or.elim c82 (fun h => h) (fun h => (False.elim (h u20))))
  have u24 : s 58 ≠ true := (Or.elim c102 (fun h => (False.elim (h u20))) (fun h => h))
  have u25 : s 45 ≠ true := (Or.elim c6 (fun h => (False.elim (h u22))) (fun h => h))
  have u26 : s 48 = true := (Or.elim c156 (fun h => (False.elim (u23 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u24 h))))))))))
  have u27 : s 9 = true := (Or.elim c129 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u25 h))))))))))
  exact (Or.elim c33 (fun h => (h u27)) (fun h => (h u26)))

private theorem step270 (s : Fin 60 → Bool)
    (c201 : s 59 ≠ true)
    (c2 : s 0 ≠ true ∨ s 18 ≠ true)
    (c235 : s 31 = true ∨ s 46 = true ∨ s 18 ≠ true ∨ s 50 = true ∨ s 49 = true ∨ s 21 = true ∨ s 8 = true ∨ s 57 = true)
    (c55 : s 14 ≠ true ∨ s 57 ≠ true)
    (c96 : s 33 ≠ true ∨ s 57 ≠ true)
    (c142 : s 11 = true ∨ s 14 = true ∨ s 34 = true ∨ s 50 = true ∨ s 59 = true)
    (c231 : s 11 ≠ true ∨ s 7 = true ∨ s 18 ≠ true)
    (c23 : s 7 ≠ true ∨ s 40 ≠ true)
    (c123 : s 4 = true ∨ s 8 = true ∨ s 40 = true ∨ s 46 = true ∨ s 49 = true)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    (c15 : s 4 ≠ true ∨ s 30 ≠ true)
    (c158 : s 0 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 33 = true)
    : s 21 = true ∨ s 46 = true ∨ s 18 ≠ true ∨ s 49 = true ∨ s 8 = true ∨ s 50 = true ∨ s 34 = true ∨ s 31 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7⟩ := hc
  have u0 : s 59 ≠ true := c201
  have u1 : s 0 ≠ true := (Or.elim c2 (fun h => h) (fun h => (False.elim (h a2))))
  have u2 : s 57 = true := (Or.elim c235 (fun h => (False.elim (a7 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (h a2))) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => h))))))))))))))
  have u3 : s 14 ≠ true := (Or.elim c55 (fun h => h) (fun h => (False.elim (h u2))))
  have u4 : s 33 ≠ true := (Or.elim c96 (fun h => h) (fun h => (False.elim (h u2))))
  have u5 : s 11 = true := (Or.elim c142 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (a6 h))) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => (False.elim (u0 h))))))))))
  have u6 : s 7 = true := (Or.elim c231 (fun h => (False.elim (h u5))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (h a2))))))
  have u7 : s 40 ≠ true := (Or.elim c23 (fun h => (False.elim (h u6))) (fun h => h))
  have u8 : s 4 = true := (Or.elim c123 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (a3 h))))))))))
  have u9 : s 20 ≠ true := (Or.elim c14 (fun h => (False.elim (h u8))) (fun h => h))
  have u10 : s 30 ≠ true := (Or.elim c15 (fun h => (False.elim (h u8))) (fun h => h))
  exact (Or.elim c158 (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u9 h)) (fun h => (Or.elim h (fun h => (a0 h)) (fun h => (Or.elim h (fun h => (u10 h)) (fun h => (u4 h)))))))))

private theorem step271 (s : Fin 60 → Bool)
    (c252 : s 29 ≠ true)
    (c262 : s 16 ≠ true)
    (c264 : s 55 ≠ true ∨ s 34 = true ∨ s 31 = true)
    (c268 : s 50 ≠ true ∨ s 10 = true ∨ s 13 = true ∨ s 55 = true ∨ s 34 = true)
    (c269 : s 43 = true ∨ s 10 = true ∨ s 13 = true ∨ s 55 = true ∨ s 34 = true)
    (c26 : s 8 ≠ true ∨ s 43 ≠ true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    (c119 : s 43 ≠ true ∨ s 51 ≠ true)
    (c208 : s 51 = true ∨ s 55 = true ∨ s 13 = true ∨ s 10 = true ∨ s 18 = true)
    (c132 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 51 = true ∨ s 55 = true)
    (c2 : s 0 ≠ true ∨ s 18 ≠ true)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    (c62 : s 18 ≠ true ∨ s 39 ≠ true)
    (c66 : s 19 ≠ true ∨ s 53 ≠ true)
    (c161 : s 26 = true ∨ s 29 = true ∨ s 39 = true ∨ s 53 = true ∨ s 55 = true)
    (c84 : s 26 ≠ true ∨ s 48 ≠ true)
    (c229 : s 46 ≠ true ∨ s 35 = true ∨ s 8 = true ∨ s 48 = true)
    (c270 : s 21 = true ∨ s 46 = true ∨ s 18 ≠ true ∨ s 49 = true ∨ s 8 = true ∨ s 50 = true ∨ s 34 = true ∨ s 31 = true)
    (c69 : s 21 ≠ true ∨ s 32 ≠ true)
    (c70 : s 21 ≠ true ∨ s 41 ≠ true)
    (c162 : s 13 = true ∨ s 29 = true ∨ s 32 = true ∨ s 55 = true ∨ s 57 = true)
    (c120 : s 0 = true ∨ s 8 = true ∨ s 16 = true ∨ s 20 = true ∨ s 41 = true)
    (c55 : s 14 ≠ true ∨ s 57 ≠ true)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    (c160 : s 6 = true ∨ s 14 = true ∨ s 32 = true ∨ s 34 = true ∨ s 55 = true)
    (c123 : s 4 = true ∨ s 8 = true ∨ s 40 = true ∨ s 46 = true ∨ s 49 = true)
    (c19 : s 6 ≠ true ∨ s 40 ≠ true)
    : s 10 = true ∨ s 13 = true ∨ s 34 = true ∨ s 31 = true := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 29 ≠ true := c252
  have u1 : s 16 ≠ true := c262
  have u2 : s 55 ≠ true := (Or.elim c264 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (a3 h))))))
  have u3 : s 50 ≠ true := (Or.elim c268 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a2 h))))))))))
  have u4 : s 43 = true := (Or.elim c269 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a2 h))))))))))
  have u5 : s 8 ≠ true := (Or.elim c26 (fun h => h) (fun h => (False.elim (h u4))))
  have u6 : s 49 ≠ true := (Or.elim c117 (fun h => (False.elim (h u4))) (fun h => h))
  have u7 : s 51 ≠ true := (Or.elim c119 (fun h => (False.elim (h u4))) (fun h => h))
  have u8 : s 18 = true := (Or.elim c208 (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => h))))))))
  have u9 : s 19 = true := (Or.elim c132 (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u2 h))))))))))
  have u10 : s 0 ≠ true := (Or.elim c2 (fun h => h) (fun h => (False.elim (h u8))))
  have u11 : s 35 ≠ true := (Or.elim c59 (fun h => (False.elim (h u8))) (fun h => h))
  have u12 : s 39 ≠ true := (Or.elim c62 (fun h => (False.elim (h u8))) (fun h => h))
  have u13 : s 53 ≠ true := (Or.elim c66 (fun h => (False.elim (h u9))) (fun h => h))
  have u14 : s 26 = true := (Or.elim c161 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u2 h))))))))))
  have u15 : s 48 ≠ true := (Or.elim c84 (fun h => (False.elim (h u14))) (fun h => h))
  have u16 : s 46 ≠ true := (Or.elim c229 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u15 h))))))))
  have u17 : s 21 = true := (Or.elim c270 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (h u8))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (a3 h))))))))))))))))
  have u18 : s 32 ≠ true := (Or.elim c69 (fun h => (False.elim (h u17))) (fun h => h))
  have u19 : s 41 ≠ true := (Or.elim c70 (fun h => (False.elim (h u17))) (fun h => h))
  have u20 : s 57 = true := (Or.elim c162 (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => h))))))))
  have u21 : s 20 = true := (Or.elim c120 (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u19 h))))))))))
  have u22 : s 14 ≠ true := (Or.elim c55 (fun h => h) (fun h => (False.elim (h u20))))
  have u23 : s 4 ≠ true := (Or.elim c14 (fun h => h) (fun h => (False.elim (h u21))))
  have u24 : s 6 = true := (Or.elim c160 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u2 h))))))))))
  have u25 : s 40 = true := (Or.elim c123 (fun h => (False.elim (u23 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (u6 h))))))))))
  exact (Or.elim c19 (fun h => (h u24)) (fun h => (h u25)))

private theorem step272 (s : Fin 60 → Bool)
    (c252 : s 29 ≠ true)
    (c264 : s 55 ≠ true ∨ s 34 = true ∨ s 31 = true)
    (c271 : s 10 = true ∨ s 13 = true ∨ s 34 = true ∨ s 31 = true)
    (c36 : s 10 ≠ true ∨ s 32 ≠ true)
    (c38 : s 10 ≠ true ∨ s 18 ≠ true)
    (c39 : s 10 ≠ true ∨ s 47 ≠ true)
    (c203 : s 39 ≠ true ∨ s 29 = true ∨ s 32 = true ∨ s 13 = true)
    (c162 : s 13 = true ∨ s 29 = true ∨ s 32 = true ∨ s 55 = true ∨ s 57 = true)
    (c143 : s 18 = true ∨ s 29 = true ∨ s 38 = true ∨ s 39 = true ∨ s 55 = true)
    (c55 : s 14 ≠ true ∨ s 57 ≠ true)
    (c82 : s 26 ≠ true ∨ s 38 ≠ true)
    (c102 : s 38 ≠ true ∨ s 58 ≠ true)
    (c160 : s 6 = true ∨ s 14 = true ∨ s 32 = true ∨ s 34 = true ∨ s 55 = true)
    (c19 : s 6 ≠ true ∨ s 40 ≠ true)
    (c215 : s 35 ≠ true ∨ s 40 = true ∨ s 39 = true ∨ s 18 = true)
    (c163 : s 9 = true ∨ s 14 = true ∨ s 35 = true ∨ s 47 = true ∨ s 58 = true)
    (c156 : s 26 = true ∨ s 29 = true ∨ s 35 = true ∨ s 48 = true ∨ s 58 = true)
    (c33 : s 9 ≠ true ∨ s 48 ≠ true)
    : s 13 = true ∨ s 34 = true ∨ s 31 = true := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 29 ≠ true := c252
  have u1 : s 55 ≠ true := (Or.elim c264 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (a2 h))))))
  have u2 : s 10 = true := (Or.elim c271 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (a2 h))))))))
  have u3 : s 32 ≠ true := (Or.elim c36 (fun h => (False.elim (h u2))) (fun h => h))
  have u4 : s 18 ≠ true := (Or.elim c38 (fun h => (False.elim (h u2))) (fun h => h))
  have u5 : s 47 ≠ true := (Or.elim c39 (fun h => (False.elim (h u2))) (fun h => h))
  have u6 : s 39 ≠ true := (Or.elim c203 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (a0 h))))))))
  have u7 : s 57 = true := (Or.elim c162 (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => h))))))))
  have u8 : s 38 = true := (Or.elim c143 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u1 h))))))))))
  have u9 : s 14 ≠ true := (Or.elim c55 (fun h => h) (fun h => (False.elim (h u7))))
  have u10 : s 26 ≠ true := (Or.elim c82 (fun h => h) (fun h => (False.elim (h u8))))
  have u11 : s 58 ≠ true := (Or.elim c102 (fun h => (False.elim (h u8))) (fun h => h))
  have u12 : s 6 = true := (Or.elim c160 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u1 h))))))))))
  have u13 : s 40 ≠ true := (Or.elim c19 (fun h => (False.elim (h u12))) (fun h => h))
  have u14 : s 35 ≠ true := (Or.elim c215 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u4 h))))))))
  have u15 : s 9 = true := (Or.elim c163 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u11 h))))))))))
  have u16 : s 48 = true := (Or.elim c156 (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u11 h))))))))))
  exact (Or.elim c33 (fun h => (h u15)) (fun h => (h u16)))

private theorem step273 (s : Fin 60 → Bool)
    (c252 : s 29 ≠ true)
    (c161 : s 26 = true ∨ s 29 = true ∨ s 39 = true ∨ s 53 = true ∨ s 55 = true)
    (c143 : s 18 = true ∨ s 29 = true ∨ s 38 = true ∨ s 39 = true ∨ s 55 = true)
    (c82 : s 26 ≠ true ∨ s 38 ≠ true)
    : s 39 = true ∨ s 18 = true ∨ s 53 = true ∨ s 55 = true := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 29 ≠ true := c252
  have u1 : s 26 = true := (Or.elim c161 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (a3 h))))))))))
  have u2 : s 38 = true := (Or.elim c143 (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a3 h))))))))))
  exact (Or.elim c82 (fun h => (h u1)) (fun h => (h u2)))

private theorem step274 (s : Fin 60 → Bool)
    (c201 : s 59 ≠ true)
    (c25 : s 8 ≠ true ∨ s 41 ≠ true)
    (c26 : s 8 ≠ true ∨ s 43 ≠ true)
    (c152 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true ∨ s 59 = true)
    : s 8 ≠ true ∨ s 20 = true ∨ s 52 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 59 ≠ true := c201
  have u1 : s 41 ≠ true := (Or.elim c25 (fun h => (False.elim (h a0))) (fun h => h))
  have u2 : s 43 ≠ true := (Or.elim c26 (fun h => (False.elim (h a0))) (fun h => h))
  exact (Or.elim c152 (fun h => (a1 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (a2 h)) (fun h => (u0 h)))))))))

private theorem step275 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c262 : s 16 ≠ true)
    (c201 : s 59 ≠ true)
    (c272 : s 13 = true ∨ s 34 = true ∨ s 31 = true)
    (c51 : s 13 ≠ true ∨ s 53 ≠ true)
    (c50 : s 13 ≠ true ∨ s 52 ≠ true)
    (c49 : s 13 ≠ true ∨ s 51 ≠ true)
    (c264 : s 55 ≠ true ∨ s 34 = true ∨ s 31 = true)
    (c273 : s 39 = true ∨ s 18 = true ∨ s 53 = true ∨ s 55 = true)
    (c22 : s 7 ≠ true ∨ s 39 ≠ true)
    (c149 : s 0 = true ∨ s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 37 = true)
    (c145 : s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 38 = true ∨ s 51 = true)
    (c1 : s 0 ≠ true ∨ s 17 ≠ true)
    (c3 : s 0 ≠ true ∨ s 20 ≠ true)
    (c86 : s 27 ≠ true ∨ s 38 ≠ true)
    (c274 : s 8 ≠ true ∨ s 20 = true ∨ s 52 = true)
    (c126 : s 8 = true ∨ s 16 = true ∨ s 18 = true ∨ s 35 = true ∨ s 51 = true)
    (c16 : s 5 ≠ true ∨ s 35 ≠ true)
    (c29 : s 9 ≠ true ∨ s 35 ≠ true)
    (c155 : s 5 = true ∨ s 7 = true ∨ s 17 = true ∨ s 31 = true ∨ s 36 = true)
    (c63 : s 19 ≠ true ∨ s 36 ≠ true)
    (c159 : s 5 = true ∨ s 19 = true ∨ s 27 = true ∨ s 46 = true ∨ s 53 = true)
    (c113 : s 42 ≠ true ∨ s 46 ≠ true)
    (c153 : s 8 = true ∨ s 9 = true ∨ s 31 = true ∨ s 42 = true ∨ s 49 = true)
    (c109 : s 41 ≠ true ∨ s 49 ≠ true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    (c152 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true ∨ s 59 = true)
    : s 18 = true ∨ s 34 = true ∨ s 31 = true := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 16 ≠ true := c262
  have u2 : s 59 ≠ true := c201
  have u3 : s 13 = true := (Or.elim c272 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (a2 h))))))
  have u4 : s 53 ≠ true := (Or.elim c51 (fun h => (False.elim (h u3))) (fun h => h))
  have u5 : s 52 ≠ true := (Or.elim c50 (fun h => (False.elim (h u3))) (fun h => h))
  have u6 : s 51 ≠ true := (Or.elim c49 (fun h => (False.elim (h u3))) (fun h => h))
  have u7 : s 55 ≠ true := (Or.elim c264 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (a2 h))))))
  have u8 : s 39 = true := (Or.elim c273 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u7 h))))))))
  have u9 : s 7 ≠ true := (Or.elim c22 (fun h => h) (fun h => (False.elim (h u8))))
  have u10 : s 0 = true := (Or.elim c149 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u0 h))))))))))
  have u11 : s 38 = true := (Or.elim c145 (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u6 h))))))))))
  have u12 : s 17 ≠ true := (Or.elim c1 (fun h => (False.elim (h u10))) (fun h => h))
  have u13 : s 20 ≠ true := (Or.elim c3 (fun h => (False.elim (h u10))) (fun h => h))
  have u14 : s 27 ≠ true := (Or.elim c86 (fun h => h) (fun h => (False.elim (h u11))))
  have u15 : s 8 ≠ true := (Or.elim c274 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u5 h))))))
  have u16 : s 35 = true := (Or.elim c126 (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u6 h))))))))))
  have u17 : s 5 ≠ true := (Or.elim c16 (fun h => h) (fun h => (False.elim (h u16))))
  have u18 : s 9 ≠ true := (Or.elim c29 (fun h => h) (fun h => (False.elim (h u16))))
  have u19 : s 36 = true := (Or.elim c155 (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => h))))))))
  have u20 : s 19 ≠ true := (Or.elim c63 (fun h => h) (fun h => (False.elim (h u19))))
  have u21 : s 46 = true := (Or.elim c159 (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u4 h))))))))))
  have u22 : s 42 ≠ true := (Or.elim c113 (fun h => h) (fun h => (False.elim (h u21))))
  have u23 : s 49 = true := (Or.elim c153 (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => h))))))))
  have u24 : s 41 ≠ true := (Or.elim c109 (fun h => h) (fun h => (False.elim (h u23))))
  have u25 : s 43 ≠ true := (Or.elim c117 (fun h => h) (fun h => (False.elim (h u23))))
  exact (Or.elim c152 (fun h => (u13 h)) (fun h => (Or.elim h (fun h => (u24 h)) (fun h => (Or.elim h (fun h => (u25 h)) (fun h => (Or.elim h (fun h => (u5 h)) (fun h => (u2 h)))))))))

private theorem step276 (s : Fin 60 → Bool)
    (c262 : s 16 ≠ true)
    (c252 : s 29 ≠ true)
    (c264 : s 55 ≠ true ∨ s 34 = true ∨ s 31 = true)
    (c272 : s 13 = true ∨ s 34 = true ∨ s 31 = true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    (c48 : s 13 ≠ true ∨ s 50 ≠ true)
    (c49 : s 13 ≠ true ∨ s 51 ≠ true)
    (c51 : s 13 ≠ true ∨ s 53 ≠ true)
    (c275 : s 18 = true ∨ s 34 = true ∨ s 31 = true)
    (c2 : s 0 ≠ true ∨ s 18 ≠ true)
    (c18 : s 5 ≠ true ∨ s 18 ≠ true)
    (c38 : s 10 ≠ true ∨ s 18 ≠ true)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    (c60 : s 18 ≠ true ∨ s 36 ≠ true)
    (c62 : s 18 ≠ true ∨ s 39 ≠ true)
    (c140 : s 10 = true ∨ s 16 = true ∨ s 43 = true ∨ s 50 = true ∨ s 51 = true)
    (c161 : s 26 = true ∨ s 29 = true ∨ s 39 = true ∨ s 53 = true ∨ s 55 = true)
    (c26 : s 8 ≠ true ∨ s 43 ≠ true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    (c84 : s 26 ≠ true ∨ s 48 ≠ true)
    (c229 : s 46 ≠ true ∨ s 35 = true ∨ s 8 = true ∨ s 48 = true)
    (c270 : s 21 = true ∨ s 46 = true ∨ s 18 ≠ true ∨ s 49 = true ∨ s 8 = true ∨ s 50 = true ∨ s 34 = true ∨ s 31 = true)
    (c70 : s 21 ≠ true ∨ s 41 ≠ true)
    (c120 : s 0 = true ∨ s 8 = true ∨ s 16 = true ∨ s 20 = true ∨ s 41 = true)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    (c123 : s 4 = true ∨ s 8 = true ∨ s 40 = true ∨ s 46 = true ∨ s 49 = true)
    (c19 : s 6 ≠ true ∨ s 40 ≠ true)
    (c23 : s 7 ≠ true ∨ s 40 ≠ true)
    (c160 : s 6 = true ∨ s 14 = true ∨ s 32 = true ∨ s 34 = true ∨ s 55 = true)
    (c155 : s 5 = true ∨ s 7 = true ∨ s 17 = true ∨ s 31 = true ∨ s 36 = true)
    (c53 : s 14 ≠ true ∨ s 17 ≠ true)
    : s 34 = true ∨ s 31 = true := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 16 ≠ true := c262
  have u1 : s 29 ≠ true := c252
  have u2 : s 55 ≠ true := (Or.elim c264 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))
  have u3 : s 13 = true := (Or.elim c272 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))
  have u4 : s 32 ≠ true := (Or.elim c47 (fun h => (False.elim (h u3))) (fun h => h))
  have u5 : s 50 ≠ true := (Or.elim c48 (fun h => (False.elim (h u3))) (fun h => h))
  have u6 : s 51 ≠ true := (Or.elim c49 (fun h => (False.elim (h u3))) (fun h => h))
  have u7 : s 53 ≠ true := (Or.elim c51 (fun h => (False.elim (h u3))) (fun h => h))
  have u8 : s 18 = true := (Or.elim c275 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))
  have u9 : s 0 ≠ true := (Or.elim c2 (fun h => h) (fun h => (False.elim (h u8))))
  have u10 : s 5 ≠ true := (Or.elim c18 (fun h => h) (fun h => (False.elim (h u8))))
  have u11 : s 10 ≠ true := (Or.elim c38 (fun h => h) (fun h => (False.elim (h u8))))
  have u12 : s 35 ≠ true := (Or.elim c59 (fun h => (False.elim (h u8))) (fun h => h))
  have u13 : s 36 ≠ true := (Or.elim c60 (fun h => (False.elim (h u8))) (fun h => h))
  have u14 : s 39 ≠ true := (Or.elim c62 (fun h => (False.elim (h u8))) (fun h => h))
  have u15 : s 43 = true := (Or.elim c140 (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u6 h))))))))))
  have u16 : s 26 = true := (Or.elim c161 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u2 h))))))))))
  have u17 : s 8 ≠ true := (Or.elim c26 (fun h => h) (fun h => (False.elim (h u15))))
  have u18 : s 49 ≠ true := (Or.elim c117 (fun h => (False.elim (h u15))) (fun h => h))
  have u19 : s 48 ≠ true := (Or.elim c84 (fun h => (False.elim (h u16))) (fun h => h))
  have u20 : s 46 ≠ true := (Or.elim c229 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u19 h))))))))
  have u21 : s 21 = true := (Or.elim c270 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => (False.elim (h u8))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))))))))))))
  have u22 : s 41 ≠ true := (Or.elim c70 (fun h => (False.elim (h u21))) (fun h => h))
  have u23 : s 20 = true := (Or.elim c120 (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u22 h))))))))))
  have u24 : s 4 ≠ true := (Or.elim c14 (fun h => h) (fun h => (False.elim (h u23))))
  have u25 : s 40 = true := (Or.elim c123 (fun h => (False.elim (u24 h))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u18 h))))))))))
  have u26 : s 6 ≠ true := (Or.elim c19 (fun h => h) (fun h => (False.elim (h u25))))
  have u27 : s 7 ≠ true := (Or.elim c23 (fun h => h) (fun h => (False.elim (h u25))))
  have u28 : s 14 = true := (Or.elim c160 (fun h => (False.elim (u26 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u2 h))))))))))
  have u29 : s 17 = true := (Or.elim c155 (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u13 h))))))))))
  exact (Or.elim c53 (fun h => (h u28)) (fun h => (h u29)))

private theorem step277 (s : Fin 60 → Bool)
    (c252 : s 29 ≠ true)
    (c262 : s 16 ≠ true)
    (c276 : s 34 = true ∨ s 31 = true)
    (c97 : s 34 ≠ true ∨ s 55 ≠ true)
    (c41 : s 11 ≠ true ∨ s 34 ≠ true)
    (c98 : s 34 ≠ true ∨ s 57 ≠ true)
    (c144 : s 11 = true ∨ s 29 = true ∨ s 32 = true ∨ s 55 = true ∨ s 57 = true)
    (c36 : s 10 ≠ true ∨ s 32 ≠ true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    (c52 : s 14 ≠ true ∨ s 32 ≠ true)
    (c133 : s 11 = true ∨ s 14 = true ∨ s 31 = true ∨ s 50 = true ∨ s 57 = true)
    (c64 : s 19 ≠ true ∨ s 50 ≠ true)
    (c136 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 54 = true ∨ s 55 = true)
    (c110 : s 41 ≠ true ∨ s 54 ≠ true)
    (c118 : s 43 ≠ true ∨ s 50 ≠ true)
    (c69 : s 21 ≠ true ∨ s 32 ≠ true)
    (c122 : s 8 = true ∨ s 21 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true)
    (c120 : s 0 = true ∨ s 8 = true ∨ s 16 = true ∨ s 20 = true ∨ s 41 = true)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    : s 8 = true ∨ s 0 = true ∨ s 31 = true := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 29 ≠ true := c252
  have u1 : s 16 ≠ true := c262
  have u2 : s 34 = true := (Or.elim c276 (fun h => h) (fun h => (False.elim (a2 h))))
  have u3 : s 55 ≠ true := (Or.elim c97 (fun h => (False.elim (h u2))) (fun h => h))
  have u4 : s 11 ≠ true := (Or.elim c41 (fun h => h) (fun h => (False.elim (h u2))))
  have u5 : s 57 ≠ true := (Or.elim c98 (fun h => (False.elim (h u2))) (fun h => h))
  have u6 : s 32 = true := (Or.elim c144 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))))))
  have u7 : s 10 ≠ true := (Or.elim c36 (fun h => h) (fun h => (False.elim (h u6))))
  have u8 : s 13 ≠ true := (Or.elim c47 (fun h => h) (fun h => (False.elim (h u6))))
  have u9 : s 14 ≠ true := (Or.elim c52 (fun h => h) (fun h => (False.elim (h u6))))
  have u10 : s 50 = true := (Or.elim c133 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u5 h))))))))))
  have u11 : s 19 ≠ true := (Or.elim c64 (fun h => h) (fun h => (False.elim (h u10))))
  have u12 : s 54 = true := (Or.elim c136 (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u3 h))))))))))
  have u13 : s 41 ≠ true := (Or.elim c110 (fun h => h) (fun h => (False.elim (h u12))))
  have u14 : s 43 ≠ true := (Or.elim c118 (fun h => h) (fun h => (False.elim (h u10))))
  have u15 : s 21 ≠ true := (Or.elim c69 (fun h => h) (fun h => (False.elim (h u6))))
  have u16 : s 52 = true := (Or.elim c122 (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => h))))))))
  have u17 : s 20 = true := (Or.elim c120 (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u13 h))))))))))
  exact (Or.elim c68 (fun h => (h u17)) (fun h => (h u16)))

private theorem step278 (s : Fin 60 → Bool)
    (c252 : s 29 ≠ true)
    (c276 : s 34 = true ∨ s 31 = true)
    (c97 : s 34 ≠ true ∨ s 55 ≠ true)
    (c41 : s 11 ≠ true ∨ s 34 ≠ true)
    (c98 : s 34 ≠ true ∨ s 57 ≠ true)
    (c144 : s 11 = true ∨ s 29 = true ∨ s 32 = true ∨ s 55 = true ∨ s 57 = true)
    (c36 : s 10 ≠ true ∨ s 32 ≠ true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    (c52 : s 14 ≠ true ∨ s 32 ≠ true)
    (c133 : s 11 = true ∨ s 14 = true ∨ s 31 = true ∨ s 50 = true ∨ s 57 = true)
    (c64 : s 19 ≠ true ∨ s 50 ≠ true)
    (c136 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 54 = true ∨ s 55 = true)
    (c115 : s 42 ≠ true ∨ s 54 ≠ true)
    (c110 : s 41 ≠ true ∨ s 54 ≠ true)
    (c107 : s 40 ≠ true ∨ s 54 ≠ true)
    (c132 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 51 = true ∨ s 55 = true)
    (c58 : s 17 ≠ true ∨ s 51 ≠ true)
    (c118 : s 43 ≠ true ∨ s 50 ≠ true)
    (c69 : s 21 ≠ true ∨ s 32 ≠ true)
    (c99 : s 34 ≠ true ∨ s 58 ≠ true)
    (c2 : s 0 ≠ true ∨ s 18 ≠ true)
    (c18 : s 5 ≠ true ∨ s 18 ≠ true)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    (c148 : s 5 = true ∨ s 13 = true ∨ s 17 = true ∨ s 19 = true ∨ s 53 = true)
    (c80 : s 25 ≠ true ∨ s 53 ≠ true)
    (c85 : s 26 ≠ true ∨ s 53 ≠ true)
    (c156 : s 26 = true ∨ s 29 = true ∨ s 35 = true ∨ s 48 = true ∨ s 58 = true)
    (c33 : s 9 ≠ true ∨ s 48 ≠ true)
    (c88 : s 27 ≠ true ∨ s 48 ≠ true)
    (c277 : s 8 = true ∨ s 0 = true ∨ s 31 = true)
    (c27 : s 8 ≠ true ∨ s 46 ≠ true)
    (c267 : s 52 = true ∨ s 8 ≠ true ∨ s 41 = true ∨ s 43 = true ∨ s 19 = true ∨ s 10 = true ∨ s 13 = true)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    (c76 : s 23 ≠ true ∨ s 52 ≠ true)
    (c129 : s 9 = true ∨ s 23 = true ∨ s 40 = true ∨ s 42 = true ∨ s 45 = true)
    (c6 : s 2 ≠ true ∨ s 45 ≠ true)
    (c139 : s 2 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 41 = true)
    (c131 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 46 = true)
    (c15 : s 4 ≠ true ∨ s 30 ≠ true)
    : s 18 ≠ true ∨ s 31 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 29 ≠ true := c252
  have u1 : s 34 = true := (Or.elim c276 (fun h => h) (fun h => (False.elim (a1 h))))
  have u2 : s 55 ≠ true := (Or.elim c97 (fun h => (False.elim (h u1))) (fun h => h))
  have u3 : s 11 ≠ true := (Or.elim c41 (fun h => h) (fun h => (False.elim (h u1))))
  have u4 : s 57 ≠ true := (Or.elim c98 (fun h => (False.elim (h u1))) (fun h => h))
  have u5 : s 32 = true := (Or.elim c144 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u4 h))))))))))
  have u6 : s 10 ≠ true := (Or.elim c36 (fun h => h) (fun h => (False.elim (h u5))))
  have u7 : s 13 ≠ true := (Or.elim c47 (fun h => h) (fun h => (False.elim (h u5))))
  have u8 : s 14 ≠ true := (Or.elim c52 (fun h => h) (fun h => (False.elim (h u5))))
  have u9 : s 50 = true := (Or.elim c133 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u4 h))))))))))
  have u10 : s 19 ≠ true := (Or.elim c64 (fun h => h) (fun h => (False.elim (h u9))))
  have u11 : s 54 = true := (Or.elim c136 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u2 h))))))))))
  have u12 : s 42 ≠ true := (Or.elim c115 (fun h => h) (fun h => (False.elim (h u11))))
  have u13 : s 41 ≠ true := (Or.elim c110 (fun h => h) (fun h => (False.elim (h u11))))
  have u14 : s 40 ≠ true := (Or.elim c107 (fun h => h) (fun h => (False.elim (h u11))))
  have u15 : s 51 = true := (Or.elim c132 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u2 h))))))))))
  have u16 : s 17 ≠ true := (Or.elim c58 (fun h => h) (fun h => (False.elim (h u15))))
  have u17 : s 43 ≠ true := (Or.elim c118 (fun h => h) (fun h => (False.elim (h u9))))
  have u18 : s 21 ≠ true := (Or.elim c69 (fun h => h) (fun h => (False.elim (h u5))))
  have u19 : s 58 ≠ true := (Or.elim c99 (fun h => (False.elim (h u1))) (fun h => h))
  have u20 : s 0 ≠ true := (Or.elim c2 (fun h => h) (fun h => (False.elim (h a0))))
  have u21 : s 5 ≠ true := (Or.elim c18 (fun h => h) (fun h => (False.elim (h a0))))
  have u22 : s 35 ≠ true := (Or.elim c59 (fun h => (False.elim (h a0))) (fun h => h))
  have u23 : s 53 = true := (Or.elim c148 (fun h => (False.elim (u21 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => h))))))))
  have u24 : s 25 ≠ true := (Or.elim c80 (fun h => h) (fun h => (False.elim (h u23))))
  have u25 : s 26 ≠ true := (Or.elim c85 (fun h => h) (fun h => (False.elim (h u23))))
  have u26 : s 48 = true := (Or.elim c156 (fun h => (False.elim (u25 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u19 h))))))))))
  have u27 : s 9 ≠ true := (Or.elim c33 (fun h => h) (fun h => (False.elim (h u26))))
  have u28 : s 27 ≠ true := (Or.elim c88 (fun h => h) (fun h => (False.elim (h u26))))
  have u29 : s 8 = true := (Or.elim c277 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (a1 h))))))
  have u30 : s 46 ≠ true := (Or.elim c27 (fun h => (False.elim (h u29))) (fun h => h))
  have u31 : s 52 = true := (Or.elim c267 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h u29))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u7 h))))))))))))))
  have u32 : s 20 ≠ true := (Or.elim c68 (fun h => h) (fun h => (False.elim (h u31))))
  have u33 : s 23 ≠ true := (Or.elim c76 (fun h => h) (fun h => (False.elim (h u31))))
  have u34 : s 45 = true := (Or.elim c129 (fun h => (False.elim (u27 h))) (fun h => (Or.elim h (fun h => (False.elim (u33 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => h))))))))
  have u35 : s 2 ≠ true := (Or.elim c6 (fun h => h) (fun h => (False.elim (h u34))))
  have u36 : s 30 = true := (Or.elim c139 (fun h => (False.elim (u35 h))) (fun h => (Or.elim h (fun h => (False.elim (u32 h))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u13 h))))))))))
  have u37 : s 4 = true := (Or.elim c131 (fun h => (False.elim (u35 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (Or.elim h (fun h => (False.elim (u28 h))) (fun h => (False.elim (u30 h))))))))))
  exact (Or.elim c15 (fun h => (h u37)) (fun h => (h u36)))

private theorem step279 (s : Fin 60 → Bool)
    (c262 : s 16 ≠ true)
    (c252 : s 29 ≠ true)
    (c278 : s 18 ≠ true ∨ s 31 = true)
    (c276 : s 34 = true ∨ s 31 = true)
    (c99 : s 34 ≠ true ∨ s 58 ≠ true)
    (c97 : s 34 ≠ true ∨ s 55 ≠ true)
    (c20 : s 7 ≠ true ∨ s 35 ≠ true)
    (c21 : s 7 ≠ true ∨ s 36 ≠ true)
    (c22 : s 7 ≠ true ∨ s 39 ≠ true)
    (c150 : s 9 = true ∨ s 16 = true ∨ s 18 = true ∨ s 35 = true ∨ s 36 = true)
    (c143 : s 18 = true ∨ s 29 = true ∨ s 38 = true ∨ s 39 = true ∨ s 55 = true)
    (c33 : s 9 ≠ true ∨ s 48 ≠ true)
    (c82 : s 26 ≠ true ∨ s 38 ≠ true)
    (c156 : s 26 = true ∨ s 29 = true ∨ s 35 = true ∨ s 48 = true ∨ s 58 = true)
    : s 7 ≠ true ∨ s 31 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 16 ≠ true := c262
  have u1 : s 29 ≠ true := c252
  have u2 : s 18 ≠ true := (Or.elim c278 (fun h => h) (fun h => (False.elim (a1 h))))
  have u3 : s 34 = true := (Or.elim c276 (fun h => h) (fun h => (False.elim (a1 h))))
  have u4 : s 58 ≠ true := (Or.elim c99 (fun h => (False.elim (h u3))) (fun h => h))
  have u5 : s 55 ≠ true := (Or.elim c97 (fun h => (False.elim (h u3))) (fun h => h))
  have u6 : s 35 ≠ true := (Or.elim c20 (fun h => (False.elim (h a0))) (fun h => h))
  have u7 : s 36 ≠ true := (Or.elim c21 (fun h => (False.elim (h a0))) (fun h => h))
  have u8 : s 39 ≠ true := (Or.elim c22 (fun h => (False.elim (h a0))) (fun h => h))
  have u9 : s 9 = true := (Or.elim c150 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u7 h))))))))))
  have u10 : s 38 = true := (Or.elim c143 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u5 h))))))))))
  have u11 : s 48 ≠ true := (Or.elim c33 (fun h => (False.elim (h u9))) (fun h => h))
  have u12 : s 26 ≠ true := (Or.elim c82 (fun h => h) (fun h => (False.elim (h u10))))
  exact (Or.elim c156 (fun h => (u12 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (u11 h)) (fun h => (u4 h)))))))))

private theorem step280 (s : Fin 60 → Bool)
    (c252 : s 29 ≠ true)
    (c278 : s 18 ≠ true ∨ s 31 = true)
    (c276 : s 34 = true ∨ s 31 = true)
    (c97 : s 34 ≠ true ∨ s 55 ≠ true)
    (c82 : s 26 ≠ true ∨ s 38 ≠ true)
    (c83 : s 26 ≠ true ∨ s 39 ≠ true)
    (c143 : s 18 = true ∨ s 29 = true ∨ s 38 = true ∨ s 39 = true ∨ s 55 = true)
    : s 26 ≠ true ∨ s 31 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 29 ≠ true := c252
  have u1 : s 18 ≠ true := (Or.elim c278 (fun h => h) (fun h => (False.elim (a1 h))))
  have u2 : s 34 = true := (Or.elim c276 (fun h => h) (fun h => (False.elim (a1 h))))
  have u3 : s 55 ≠ true := (Or.elim c97 (fun h => (False.elim (h u2))) (fun h => h))
  have u4 : s 38 ≠ true := (Or.elim c82 (fun h => (False.elim (h a0))) (fun h => h))
  have u5 : s 39 ≠ true := (Or.elim c83 (fun h => (False.elim (h a0))) (fun h => h))
  exact (Or.elim c143 (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (Or.elim h (fun h => (u4 h)) (fun h => (Or.elim h (fun h => (u5 h)) (fun h => (u3 h)))))))))

private theorem step281 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c262 : s 16 ≠ true)
    (c201 : s 59 ≠ true)
    (c252 : s 29 ≠ true)
    (c276 : s 34 = true ∨ s 31 = true)
    (c41 : s 11 ≠ true ∨ s 34 ≠ true)
    (c97 : s 34 ≠ true ∨ s 55 ≠ true)
    (c98 : s 34 ≠ true ∨ s 57 ≠ true)
    (c99 : s 34 ≠ true ∨ s 58 ≠ true)
    (c144 : s 11 = true ∨ s 29 = true ∨ s 32 = true ∨ s 55 = true ∨ s 57 = true)
    (c36 : s 10 ≠ true ∨ s 32 ≠ true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    (c52 : s 14 ≠ true ∨ s 32 ≠ true)
    (c69 : s 21 ≠ true ∨ s 32 ≠ true)
    (c133 : s 11 = true ∨ s 14 = true ∨ s 31 = true ∨ s 50 = true ∨ s 57 = true)
    (c64 : s 19 ≠ true ∨ s 50 ≠ true)
    (c118 : s 43 ≠ true ∨ s 50 ≠ true)
    (c136 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 54 = true ∨ s 55 = true)
    (c107 : s 40 ≠ true ∨ s 54 ≠ true)
    (c110 : s 41 ≠ true ∨ s 54 ≠ true)
    (c115 : s 42 ≠ true ∨ s 54 ≠ true)
    (c278 : s 18 ≠ true ∨ s 31 = true)
    (c279 : s 7 ≠ true ∨ s 31 = true)
    (c149 : s 0 = true ∨ s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 37 = true)
    (c4 : s 0 ≠ true ∨ s 30 ≠ true)
    (c280 : s 26 ≠ true ∨ s 31 = true)
    (c3 : s 0 ≠ true ∨ s 20 ≠ true)
    (c139 : s 2 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 41 = true)
    (c152 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true ∨ s 59 = true)
    (c6 : s 2 ≠ true ∨ s 45 ≠ true)
    (c76 : s 23 ≠ true ∨ s 52 ≠ true)
    (c129 : s 9 = true ∨ s 23 = true ∨ s 40 = true ∨ s 42 = true ∨ s 45 = true)
    (c29 : s 9 ≠ true ∨ s 35 ≠ true)
    (c33 : s 9 ≠ true ∨ s 48 ≠ true)
    (c156 : s 26 = true ∨ s 29 = true ∨ s 35 = true ∨ s 48 = true ∨ s 58 = true)
    : s 31 = true := by
  by_contra hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 16 ≠ true := c262
  have u2 : s 59 ≠ true := c201
  have u3 : s 29 ≠ true := c252
  have u4 : s 34 = true := (Or.elim c276 (fun h => h) (fun h => (False.elim (hc h))))
  have u5 : s 11 ≠ true := (Or.elim c41 (fun h => h) (fun h => (False.elim (h u4))))
  have u6 : s 55 ≠ true := (Or.elim c97 (fun h => (False.elim (h u4))) (fun h => h))
  have u7 : s 57 ≠ true := (Or.elim c98 (fun h => (False.elim (h u4))) (fun h => h))
  have u8 : s 58 ≠ true := (Or.elim c99 (fun h => (False.elim (h u4))) (fun h => h))
  have u9 : s 32 = true := (Or.elim c144 (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u7 h))))))))))
  have u10 : s 10 ≠ true := (Or.elim c36 (fun h => h) (fun h => (False.elim (h u9))))
  have u11 : s 13 ≠ true := (Or.elim c47 (fun h => h) (fun h => (False.elim (h u9))))
  have u12 : s 14 ≠ true := (Or.elim c52 (fun h => h) (fun h => (False.elim (h u9))))
  have u13 : s 21 ≠ true := (Or.elim c69 (fun h => h) (fun h => (False.elim (h u9))))
  have u14 : s 50 = true := (Or.elim c133 (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (hc h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u7 h))))))))))
  have u15 : s 19 ≠ true := (Or.elim c64 (fun h => h) (fun h => (False.elim (h u14))))
  have u16 : s 43 ≠ true := (Or.elim c118 (fun h => h) (fun h => (False.elim (h u14))))
  have u17 : s 54 = true := (Or.elim c136 (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u6 h))))))))))
  have u18 : s 40 ≠ true := (Or.elim c107 (fun h => h) (fun h => (False.elim (h u17))))
  have u19 : s 41 ≠ true := (Or.elim c110 (fun h => h) (fun h => (False.elim (h u17))))
  have u20 : s 42 ≠ true := (Or.elim c115 (fun h => h) (fun h => (False.elim (h u17))))
  have u21 : s 18 ≠ true := (Or.elim c278 (fun h => h) (fun h => (False.elim (hc h))))
  have u22 : s 7 ≠ true := (Or.elim c279 (fun h => h) (fun h => (False.elim (hc h))))
  have u23 : s 0 = true := (Or.elim c149 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u0 h))))))))))
  have u24 : s 30 ≠ true := (Or.elim c4 (fun h => (False.elim (h u23))) (fun h => h))
  have u25 : s 26 ≠ true := (Or.elim c280 (fun h => h) (fun h => (False.elim (hc h))))
  have u26 : s 20 ≠ true := (Or.elim c3 (fun h => (False.elim (h u23))) (fun h => h))
  have u27 : s 2 = true := (Or.elim c139 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (False.elim (u19 h))))))))))
  have u28 : s 52 = true := (Or.elim c152 (fun h => (False.elim (u26 h))) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u2 h))))))))))
  have u29 : s 45 ≠ true := (Or.elim c6 (fun h => (False.elim (h u27))) (fun h => h))
  have u30 : s 23 ≠ true := (Or.elim c76 (fun h => h) (fun h => (False.elim (h u28))))
  have u31 : s 9 = true := (Or.elim c129 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u29 h))))))))))
  have u32 : s 35 ≠ true := (Or.elim c29 (fun h => (False.elim (h u31))) (fun h => h))
  have u33 : s 48 ≠ true := (Or.elim c33 (fun h => (False.elim (h u31))) (fun h => h))
  exact (Or.elim c156 (fun h => (u25 h)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (Or.elim h (fun h => (u32 h)) (fun h => (Or.elim h (fun h => (u33 h)) (fun h => (u8 h)))))))))

private theorem step282 (s : Fin 60 → Bool)
    (c281 : s 31 = true)
    (c13 : s 3 ≠ true ∨ s 31 ≠ true)
    : s 3 ≠ true := by
  by_contra hc
  have u0 : s 31 = true := c281
  exact (Or.elim c13 (fun h => (h hc)) (fun h => (h u0)))

private theorem step283 (s : Fin 60 → Bool)
    (c281 : s 31 = true)
    (c35 : s 9 ≠ true ∨ s 31 ≠ true)
    : s 9 ≠ true := by
  by_contra hc
  have u0 : s 31 = true := c281
  exact (Or.elim c35 (fun h => (h hc)) (fun h => (h u0)))

private theorem step284 (s : Fin 60 → Bool)
    (c281 : s 31 = true)
    (c44 : s 11 ≠ true ∨ s 31 ≠ true)
    : s 11 ≠ true := by
  by_contra hc
  have u0 : s 31 = true := c281
  exact (Or.elim c44 (fun h => (h hc)) (fun h => (h u0)))

private theorem step285 (s : Fin 60 → Bool)
    (c281 : s 31 = true)
    (c73 : s 21 ≠ true ∨ s 31 ≠ true)
    : s 21 ≠ true := by
  by_contra hc
  have u0 : s 31 = true := c281
  exact (Or.elim c73 (fun h => (h hc)) (fun h => (h u0)))

private theorem step286 (s : Fin 60 → Bool)
    (c262 : s 16 ≠ true)
    (c220 : s 37 ≠ true)
    (c282 : s 3 ≠ true)
    (c201 : s 59 ≠ true)
    (c285 : s 21 ≠ true)
    (c283 : s 9 ≠ true)
    (c21 : s 7 ≠ true ∨ s 36 ≠ true)
    (c63 : s 19 ≠ true ∨ s 36 ≠ true)
    (c149 : s 0 = true ∨ s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 37 = true)
    (c3 : s 0 ≠ true ∨ s 20 ≠ true)
    (c4 : s 0 ≠ true ∨ s 30 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c128 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 32 = true ∨ s 37 = true)
    (c97 : s 34 ≠ true ∨ s 55 ≠ true)
    (c36 : s 10 ≠ true ∨ s 32 ≠ true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    (c208 : s 51 = true ∨ s 55 = true ∨ s 13 = true ∨ s 10 = true ∨ s 18 = true)
    (c136 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 54 = true ∨ s 55 = true)
    (c119 : s 43 ≠ true ∨ s 51 ≠ true)
    (c107 : s 40 ≠ true ∨ s 54 ≠ true)
    (c110 : s 41 ≠ true ∨ s 54 ≠ true)
    (c115 : s 42 ≠ true ∨ s 54 ≠ true)
    (c152 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true ∨ s 59 = true)
    (c139 : s 2 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 41 = true)
    (c76 : s 23 ≠ true ∨ s 52 ≠ true)
    (c6 : s 2 ≠ true ∨ s 45 ≠ true)
    (c129 : s 9 = true ∨ s 23 = true ∨ s 40 = true ∨ s 42 = true ∨ s 45 = true)
    : s 36 ≠ true ∨ s 18 = true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 16 ≠ true := c262
  have u1 : s 37 ≠ true := c220
  have u2 : s 3 ≠ true := c282
  have u3 : s 59 ≠ true := c201
  have u4 : s 21 ≠ true := c285
  have u5 : s 9 ≠ true := c283
  have u6 : s 7 ≠ true := (Or.elim c21 (fun h => h) (fun h => (False.elim (h a0))))
  have u7 : s 19 ≠ true := (Or.elim c63 (fun h => h) (fun h => (False.elim (h a0))))
  have u8 : s 0 = true := (Or.elim c149 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u1 h))))))))))
  have u9 : s 20 ≠ true := (Or.elim c3 (fun h => (False.elim (h u8))) (fun h => h))
  have u10 : s 30 ≠ true := (Or.elim c4 (fun h => (False.elim (h u8))) (fun h => h))
  have u11 : s 34 = true := (Or.elim c124 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u1 h))))))))))
  have u12 : s 32 = true := (Or.elim c128 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u1 h))))))))))
  have u13 : s 55 ≠ true := (Or.elim c97 (fun h => (False.elim (h u11))) (fun h => h))
  have u14 : s 10 ≠ true := (Or.elim c36 (fun h => h) (fun h => (False.elim (h u12))))
  have u15 : s 13 ≠ true := (Or.elim c47 (fun h => h) (fun h => (False.elim (h u12))))
  have u16 : s 51 = true := (Or.elim c208 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (a1 h))))))))))
  have u17 : s 54 = true := (Or.elim c136 (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u13 h))))))))))
  have u18 : s 43 ≠ true := (Or.elim c119 (fun h => h) (fun h => (False.elim (h u16))))
  have u19 : s 40 ≠ true := (Or.elim c107 (fun h => h) (fun h => (False.elim (h u17))))
  have u20 : s 41 ≠ true := (Or.elim c110 (fun h => h) (fun h => (False.elim (h u17))))
  have u21 : s 42 ≠ true := (Or.elim c115 (fun h => h) (fun h => (False.elim (h u17))))
  have u22 : s 52 = true := (Or.elim c152 (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u3 h))))))))))
  have u23 : s 2 = true := (Or.elim c139 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u20 h))))))))))
  have u24 : s 23 ≠ true := (Or.elim c76 (fun h => h) (fun h => (False.elim (h u22))))
  have u25 : s 45 ≠ true := (Or.elim c6 (fun h => (False.elim (h u23))) (fun h => h))
  exact (Or.elim c129 (fun h => (u5 h)) (fun h => (Or.elim h (fun h => (u24 h)) (fun h => (Or.elim h (fun h => (u19 h)) (fun h => (Or.elim h (fun h => (u21 h)) (fun h => (u25 h)))))))))

private theorem step287 (s : Fin 60 → Bool)
    (c283 : s 9 ≠ true)
    (c285 : s 21 ≠ true)
    (c201 : s 59 ≠ true)
    (c282 : s 3 ≠ true)
    (c220 : s 37 ≠ true)
    (c262 : s 16 ≠ true)
    (c149 : s 0 = true ∨ s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 37 = true)
    (c3 : s 0 ≠ true ∨ s 20 ≠ true)
    (c4 : s 0 ≠ true ∨ s 30 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c128 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 32 = true ∨ s 37 = true)
    (c97 : s 34 ≠ true ∨ s 55 ≠ true)
    (c36 : s 10 ≠ true ∨ s 32 ≠ true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    (c208 : s 51 = true ∨ s 55 = true ∨ s 13 = true ∨ s 10 = true ∨ s 18 = true)
    (c119 : s 43 ≠ true ∨ s 51 ≠ true)
    (c210 : s 51 ≠ true ∨ s 54 = true ∨ s 13 = true ∨ s 10 = true)
    (c107 : s 40 ≠ true ∨ s 54 ≠ true)
    (c110 : s 41 ≠ true ∨ s 54 ≠ true)
    (c115 : s 42 ≠ true ∨ s 54 ≠ true)
    (c152 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true ∨ s 59 = true)
    (c139 : s 2 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 41 = true)
    (c76 : s 23 ≠ true ∨ s 52 ≠ true)
    (c6 : s 2 ≠ true ∨ s 45 ≠ true)
    (c129 : s 9 = true ∨ s 23 = true ∨ s 40 = true ∨ s 42 = true ∨ s 45 = true)
    : s 7 = true ∨ s 18 = true := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 9 ≠ true := c283
  have u1 : s 21 ≠ true := c285
  have u2 : s 59 ≠ true := c201
  have u3 : s 3 ≠ true := c282
  have u4 : s 37 ≠ true := c220
  have u5 : s 16 ≠ true := c262
  have u6 : s 0 = true := (Or.elim c149 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u4 h))))))))))
  have u7 : s 20 ≠ true := (Or.elim c3 (fun h => (False.elim (h u6))) (fun h => h))
  have u8 : s 30 ≠ true := (Or.elim c4 (fun h => (False.elim (h u6))) (fun h => h))
  have u9 : s 34 = true := (Or.elim c124 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u4 h))))))))))
  have u10 : s 32 = true := (Or.elim c128 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u4 h))))))))))
  have u11 : s 55 ≠ true := (Or.elim c97 (fun h => (False.elim (h u9))) (fun h => h))
  have u12 : s 10 ≠ true := (Or.elim c36 (fun h => h) (fun h => (False.elim (h u10))))
  have u13 : s 13 ≠ true := (Or.elim c47 (fun h => h) (fun h => (False.elim (h u10))))
  have u14 : s 51 = true := (Or.elim c208 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (a1 h))))))))))
  have u15 : s 43 ≠ true := (Or.elim c119 (fun h => h) (fun h => (False.elim (h u14))))
  have u16 : s 54 = true := (Or.elim c210 (fun h => (False.elim (h u14))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u12 h))))))))
  have u17 : s 40 ≠ true := (Or.elim c107 (fun h => h) (fun h => (False.elim (h u16))))
  have u18 : s 41 ≠ true := (Or.elim c110 (fun h => h) (fun h => (False.elim (h u16))))
  have u19 : s 42 ≠ true := (Or.elim c115 (fun h => h) (fun h => (False.elim (h u16))))
  have u20 : s 52 = true := (Or.elim c152 (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u2 h))))))))))
  have u21 : s 2 = true := (Or.elim c139 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u18 h))))))))))
  have u22 : s 23 ≠ true := (Or.elim c76 (fun h => h) (fun h => (False.elim (h u20))))
  have u23 : s 45 ≠ true := (Or.elim c6 (fun h => (False.elim (h u21))) (fun h => h))
  exact (Or.elim c129 (fun h => (u0 h)) (fun h => (Or.elim h (fun h => (u22 h)) (fun h => (Or.elim h (fun h => (u17 h)) (fun h => (Or.elim h (fun h => (u19 h)) (fun h => (u23 h)))))))))

private theorem step288 (s : Fin 60 → Bool)
    (c262 : s 16 ≠ true)
    (c283 : s 9 ≠ true)
    (c150 : s 9 = true ∨ s 16 = true ∨ s 18 = true ∨ s 35 = true ∨ s 36 = true)
    (c20 : s 7 ≠ true ∨ s 35 ≠ true)
    (c287 : s 7 = true ∨ s 18 = true)
    : s 36 = true ∨ s 18 = true := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 16 ≠ true := c262
  have u1 : s 9 ≠ true := c283
  have u2 : s 35 = true := (Or.elim c150 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a0 h))))))))))
  have u3 : s 7 ≠ true := (Or.elim c20 (fun h => h) (fun h => (False.elim (h u2))))
  exact (Or.elim c287 (fun h => (u3 h)) (fun h => (a1 h)))

private theorem step289 (s : Fin 60 → Bool)
    (c286 : s 36 ≠ true ∨ s 18 = true)
    (c288 : s 36 = true ∨ s 18 = true)
    : s 18 = true := by
  by_contra hc
  have u0 : s 36 ≠ true := (Or.elim c286 (fun h => h) (fun h => (False.elim (hc h))))
  exact (Or.elim c288 (fun h => (u0 h)) (fun h => (hc h)))

private theorem step290 (s : Fin 60 → Bool)
    (c289 : s 18 = true)
    (c2 : s 0 ≠ true ∨ s 18 ≠ true)
    : s 0 ≠ true := by
  by_contra hc
  have u0 : s 18 = true := c289
  exact (Or.elim c2 (fun h => (h hc)) (fun h => (h u0)))

private theorem step291 (s : Fin 60 → Bool)
    (c289 : s 18 = true)
    (c18 : s 5 ≠ true ∨ s 18 ≠ true)
    : s 5 ≠ true := by
  by_contra hc
  have u0 : s 18 = true := c289
  exact (Or.elim c18 (fun h => (h hc)) (fun h => (h u0)))

private theorem step292 (s : Fin 60 → Bool)
    (c289 : s 18 = true)
    (c38 : s 10 ≠ true ∨ s 18 ≠ true)
    : s 10 ≠ true := by
  by_contra hc
  have u0 : s 18 = true := c289
  exact (Or.elim c38 (fun h => (h hc)) (fun h => (h u0)))

private theorem step293 (s : Fin 60 → Bool)
    (c289 : s 18 = true)
    (c59 : s 18 ≠ true ∨ s 35 ≠ true)
    : s 35 ≠ true := by
  by_contra hc
  have u0 : s 18 = true := c289
  exact (Or.elim c59 (fun h => (h u0)) (fun h => (h hc)))

private theorem step294 (s : Fin 60 → Bool)
    (c289 : s 18 = true)
    (c60 : s 18 ≠ true ∨ s 36 ≠ true)
    : s 36 ≠ true := by
  by_contra hc
  have u0 : s 18 = true := c289
  exact (Or.elim c60 (fun h => (h u0)) (fun h => (h hc)))

private theorem step295 (s : Fin 60 → Bool)
    (c289 : s 18 = true)
    (c62 : s 18 ≠ true ∨ s 39 ≠ true)
    : s 39 ≠ true := by
  by_contra hc
  have u0 : s 18 = true := c289
  exact (Or.elim c62 (fun h => (h u0)) (fun h => (h hc)))

private theorem step296 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c282 : s 3 ≠ true)
    (c292 : s 10 ≠ true)
    (c293 : s 35 ≠ true)
    (c201 : s 59 ≠ true)
    (c290 : s 0 ≠ true)
    (c262 : s 16 ≠ true)
    (c291 : s 5 ≠ true)
    (c283 : s 9 ≠ true)
    (c285 : s 21 ≠ true)
    (c167 : s 19 ≠ true ∨ s 16 = true ∨ s 43 = true ∨ s 10 = true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c128 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 32 = true ∨ s 37 = true)
    (c99 : s 34 ≠ true ∨ s 58 ≠ true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    (c52 : s 14 ≠ true ∨ s 32 ≠ true)
    (c136 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 54 = true ∨ s 55 = true)
    (c132 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 51 = true ∨ s 55 = true)
    (c163 : s 9 = true ∨ s 14 = true ∨ s 35 = true ∨ s 47 = true ∨ s 58 = true)
    (c107 : s 40 ≠ true ∨ s 54 ≠ true)
    (c110 : s 41 ≠ true ∨ s 54 ≠ true)
    (c115 : s 42 ≠ true ∨ s 54 ≠ true)
    (c58 : s 17 ≠ true ∨ s 51 ≠ true)
    (c87 : s 27 ≠ true ∨ s 47 ≠ true)
    (c152 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true ∨ s 59 = true)
    (c120 : s 0 = true ∨ s 8 = true ∨ s 16 = true ∨ s 20 = true ∨ s 41 = true)
    (c148 : s 5 = true ∨ s 13 = true ∨ s 17 = true ∨ s 19 = true ∨ s 53 = true)
    (c76 : s 23 ≠ true ∨ s 52 ≠ true)
    (c27 : s 8 ≠ true ∨ s 46 ≠ true)
    (c80 : s 25 ≠ true ∨ s 53 ≠ true)
    (c129 : s 9 = true ∨ s 23 = true ∨ s 40 = true ∨ s 42 = true ∨ s 45 = true)
    (c6 : s 2 ≠ true ∨ s 45 ≠ true)
    (c139 : s 2 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 41 = true)
    (c131 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 46 = true)
    (c15 : s 4 ≠ true ∨ s 30 ≠ true)
    : s 20 = true ∨ s 43 = true ∨ s 55 = true := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 3 ≠ true := c282
  have u2 : s 10 ≠ true := c292
  have u3 : s 35 ≠ true := c293
  have u4 : s 59 ≠ true := c201
  have u5 : s 0 ≠ true := c290
  have u6 : s 16 ≠ true := c262
  have u7 : s 5 ≠ true := c291
  have u8 : s 9 ≠ true := c283
  have u9 : s 21 ≠ true := c285
  have u10 : s 19 ≠ true := (Or.elim c167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u2 h))))))))
  have u11 : s 34 = true := (Or.elim c124 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))))))
  have u12 : s 32 = true := (Or.elim c128 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))))))
  have u13 : s 58 ≠ true := (Or.elim c99 (fun h => (False.elim (h u11))) (fun h => h))
  have u14 : s 13 ≠ true := (Or.elim c47 (fun h => h) (fun h => (False.elim (h u12))))
  have u15 : s 14 ≠ true := (Or.elim c52 (fun h => h) (fun h => (False.elim (h u12))))
  have u16 : s 54 = true := (Or.elim c136 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a2 h))))))))))
  have u17 : s 51 = true := (Or.elim c132 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a2 h))))))))))
  have u18 : s 47 = true := (Or.elim c163 (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u13 h))))))))))
  have u19 : s 40 ≠ true := (Or.elim c107 (fun h => h) (fun h => (False.elim (h u16))))
  have u20 : s 41 ≠ true := (Or.elim c110 (fun h => h) (fun h => (False.elim (h u16))))
  have u21 : s 42 ≠ true := (Or.elim c115 (fun h => h) (fun h => (False.elim (h u16))))
  have u22 : s 17 ≠ true := (Or.elim c58 (fun h => h) (fun h => (False.elim (h u17))))
  have u23 : s 27 ≠ true := (Or.elim c87 (fun h => h) (fun h => (False.elim (h u18))))
  have u24 : s 52 = true := (Or.elim c152 (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u4 h))))))))))
  have u25 : s 8 = true := (Or.elim c120 (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u20 h))))))))))
  have u26 : s 53 = true := (Or.elim c148 (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => h))))))))
  have u27 : s 23 ≠ true := (Or.elim c76 (fun h => h) (fun h => (False.elim (h u24))))
  have u28 : s 46 ≠ true := (Or.elim c27 (fun h => (False.elim (h u25))) (fun h => h))
  have u29 : s 25 ≠ true := (Or.elim c80 (fun h => h) (fun h => (False.elim (h u26))))
  have u30 : s 45 = true := (Or.elim c129 (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => h))))))))
  have u31 : s 2 ≠ true := (Or.elim c6 (fun h => h) (fun h => (False.elim (h u30))))
  have u32 : s 30 = true := (Or.elim c139 (fun h => (False.elim (u31 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u20 h))))))))))
  have u33 : s 4 = true := (Or.elim c131 (fun h => (False.elim (u31 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u29 h))) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (False.elim (u28 h))))))))))
  exact (Or.elim c15 (fun h => (h u33)) (fun h => (h u32)))

private theorem step297 (s : Fin 60 → Bool)
    (c285 : s 21 ≠ true)
    (c292 : s 10 ≠ true)
    (c267 : s 52 = true ∨ s 8 ≠ true ∨ s 41 = true ∨ s 43 = true ∨ s 19 = true ∨ s 10 = true ∨ s 13 = true)
    (c122 : s 8 = true ∨ s 21 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true)
    : s 41 = true ∨ s 13 = true ∨ s 19 = true ∨ s 43 = true ∨ s 52 = true := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 21 ≠ true := c285
  have u1 : s 10 ≠ true := c292
  have u2 : s 8 ≠ true := (Or.elim c267 (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))))))))))
  exact (Or.elim c122 (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (Or.elim h (fun h => (a0 h)) (fun h => (Or.elim h (fun h => (a3 h)) (fun h => (a4 h)))))))))

private theorem step298 (s : Fin 60 → Bool)
    (c262 : s 16 ≠ true)
    (c292 : s 10 ≠ true)
    (c167 : s 19 ≠ true ∨ s 16 = true ∨ s 43 = true ∨ s 10 = true)
    (c296 : s 20 = true ∨ s 43 = true ∨ s 55 = true)
    (c68 : s 20 ≠ true ∨ s 52 ≠ true)
    (c170 : s 16 = true ∨ s 32 = true ∨ s 43 = true ∨ s 52 = true ∨ s 10 = true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    (c136 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 54 = true ∨ s 55 = true)
    (c110 : s 41 ≠ true ∨ s 54 ≠ true)
    (c297 : s 41 = true ∨ s 13 = true ∨ s 19 = true ∨ s 43 = true ∨ s 52 = true)
    : s 43 = true ∨ s 55 = true := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 16 ≠ true := c262
  have u1 : s 10 ≠ true := c292
  have u2 : s 19 ≠ true := (Or.elim c167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u1 h))))))))
  have u3 : s 20 = true := (Or.elim c296 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))
  have u4 : s 52 ≠ true := (Or.elim c68 (fun h => (False.elim (h u3))) (fun h => h))
  have u5 : s 32 = true := (Or.elim c170 (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))))))
  have u6 : s 13 ≠ true := (Or.elim c47 (fun h => h) (fun h => (False.elim (h u5))))
  have u7 : s 54 = true := (Or.elim c136 (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a1 h))))))))))
  have u8 : s 41 ≠ true := (Or.elim c110 (fun h => h) (fun h => (False.elim (h u7))))
  exact (Or.elim c297 (fun h => (u8 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (a0 h)) (fun h => (u4 h)))))))))

private theorem step299 (s : Fin 60 → Bool)
    (c283 : s 9 ≠ true)
    (c285 : s 21 ≠ true)
    (c289 : s 18 = true)
    (c118 : s 43 ≠ true ∨ s 50 ≠ true)
    (c117 : s 43 ≠ true ∨ s 49 ≠ true)
    (c26 : s 8 ≠ true ∨ s 43 ≠ true)
    (c5 : s 1 ≠ true ∨ s 20 ≠ true)
    (c173 : s 20 ≠ true ∨ s 48 ≠ true ∨ s 49 = true)
    (c233 : s 9 = true ∨ s 1 = true ∨ s 18 ≠ true ∨ s 50 = true ∨ s 49 = true ∨ s 21 = true ∨ s 8 = true ∨ s 48 = true)
    : s 20 ≠ true ∨ s 43 ≠ true := by
  by_contra hc
  simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 9 ≠ true := c283
  have u1 : s 21 ≠ true := c285
  have u2 : s 18 = true := c289
  have u3 : s 50 ≠ true := (Or.elim c118 (fun h => (False.elim (h a1))) (fun h => h))
  have u4 : s 49 ≠ true := (Or.elim c117 (fun h => (False.elim (h a1))) (fun h => h))
  have u5 : s 8 ≠ true := (Or.elim c26 (fun h => h) (fun h => (False.elim (h a1))))
  have u6 : s 1 ≠ true := (Or.elim c5 (fun h => h) (fun h => (False.elim (h a0))))
  have u7 : s 48 ≠ true := (Or.elim c173 (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u4 h))))))
  exact (Or.elim c233 (fun h => (u0 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (h u2)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (Or.elim h (fun h => (u4 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u5 h)) (fun h => (u7 h)))))))))))))))

private theorem step300 (s : Fin 60 → Bool)
    (c220 : s 37 ≠ true)
    (c285 : s 21 ≠ true)
    (c282 : s 3 ≠ true)
    (c292 : s 10 ≠ true)
    (c295 : s 39 ≠ true)
    (c252 : s 29 ≠ true)
    (c283 : s 9 ≠ true)
    (c293 : s 35 ≠ true)
    (c298 : s 43 = true ∨ s 55 = true)
    (c26 : s 8 ≠ true ∨ s 43 ≠ true)
    (c119 : s 43 ≠ true ∨ s 51 ≠ true)
    (c299 : s 20 ≠ true ∨ s 43 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    (c128 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 32 = true ∨ s 37 = true)
    (c99 : s 34 ≠ true ∨ s 58 ≠ true)
    (c47 : s 13 ≠ true ∨ s 32 ≠ true)
    (c52 : s 14 ≠ true ∨ s 32 ≠ true)
    (c132 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 51 = true ∨ s 55 = true)
    (c163 : s 9 = true ∨ s 14 = true ∨ s 35 = true ∨ s 47 = true ∨ s 58 = true)
    (c66 : s 19 ≠ true ∨ s 53 ≠ true)
    (c114 : s 42 ≠ true ∨ s 47 ≠ true)
    (c161 : s 26 = true ∨ s 29 = true ∨ s 39 = true ∨ s 53 = true ∨ s 55 = true)
    (c134 : s 8 = true ∨ s 9 = true ∨ s 35 = true ∨ s 42 = true ∨ s 48 = true)
    (c84 : s 26 ≠ true ∨ s 48 ≠ true)
    : s 55 = true := by
  by_contra hc
  have u0 : s 37 ≠ true := c220
  have u1 : s 21 ≠ true := c285
  have u2 : s 3 ≠ true := c282
  have u3 : s 10 ≠ true := c292
  have u4 : s 39 ≠ true := c295
  have u5 : s 29 ≠ true := c252
  have u6 : s 9 ≠ true := c283
  have u7 : s 35 ≠ true := c293
  have u8 : s 43 = true := (Or.elim c298 (fun h => h) (fun h => (False.elim (hc h))))
  have u9 : s 8 ≠ true := (Or.elim c26 (fun h => h) (fun h => (False.elim (h u8))))
  have u10 : s 51 ≠ true := (Or.elim c119 (fun h => (False.elim (h u8))) (fun h => h))
  have u11 : s 20 ≠ true := (Or.elim c299 (fun h => h) (fun h => (False.elim (h u8))))
  have u12 : s 34 = true := (Or.elim c124 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))))))
  have u13 : s 32 = true := (Or.elim c128 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))))))
  have u14 : s 58 ≠ true := (Or.elim c99 (fun h => (False.elim (h u12))) (fun h => h))
  have u15 : s 13 ≠ true := (Or.elim c47 (fun h => h) (fun h => (False.elim (h u13))))
  have u16 : s 14 ≠ true := (Or.elim c52 (fun h => h) (fun h => (False.elim (h u13))))
  have u17 : s 19 = true := (Or.elim c132 (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (hc h))))))))))
  have u18 : s 47 = true := (Or.elim c163 (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u14 h))))))))))
  have u19 : s 53 ≠ true := (Or.elim c66 (fun h => (False.elim (h u17))) (fun h => h))
  have u20 : s 42 ≠ true := (Or.elim c114 (fun h => h) (fun h => (False.elim (h u18))))
  have u21 : s 26 = true := (Or.elim c161 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (hc h))))))))))
  have u22 : s 48 = true := (Or.elim c134 (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => h))))))))
  exact (Or.elim c84 (fun h => (h u21)) (fun h => (h u22)))

private theorem step301 (s : Fin 60 → Bool)
    (c300 : s 55 = true)
    (c46 : s 12 ≠ true ∨ s 55 ≠ true)
    : s 12 ≠ true := by
  by_contra hc
  have u0 : s 55 = true := c300
  exact (Or.elim c46 (fun h => (h hc)) (fun h => (h u0)))

private theorem step302 (s : Fin 60 → Bool)
    (c300 : s 55 = true)
    (c54 : s 14 ≠ true ∨ s 55 ≠ true)
    : s 14 ≠ true := by
  by_contra hc
  have u0 : s 55 = true := c300
  exact (Or.elim c54 (fun h => (h hc)) (fun h => (h u0)))

private theorem step303 (s : Fin 60 → Bool)
    (c300 : s 55 = true)
    (c97 : s 34 ≠ true ∨ s 55 ≠ true)
    : s 34 ≠ true := by
  by_contra hc
  have u0 : s 55 = true := c300
  exact (Or.elim c97 (fun h => (h hc)) (fun h => (h u0)))

private theorem step304 (s : Fin 60 → Bool)
    (c300 : s 55 = true)
    (c228 : s 55 ≠ true ∨ s 50 = true)
    : s 50 = true := by
  by_contra hc
  have u0 : s 55 = true := c300
  exact (Or.elim c228 (fun h => (h u0)) (fun h => (hc h)))

private theorem step305 (s : Fin 60 → Bool)
    (c303 : s 34 ≠ true)
    (c220 : s 37 ≠ true)
    (c285 : s 21 ≠ true)
    (c282 : s 3 ≠ true)
    (c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true)
    : s 20 = true := by
  by_contra hc
  have u0 : s 34 ≠ true := c303
  have u1 : s 37 ≠ true := c220
  have u2 : s 21 ≠ true := c285
  have u3 : s 3 ≠ true := c282
  exact (Or.elim c124 (fun h => (u3 h)) (fun h => (Or.elim h (fun h => (hc h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))))))

private theorem step306 (s : Fin 60 → Bool)
    (c303 : s 34 ≠ true)
    (c302 : s 14 ≠ true)
    (c284 : s 11 ≠ true)
    (c201 : s 59 ≠ true)
    (c147 : s 11 = true ∨ s 14 = true ∨ s 17 = true ∨ s 34 = true ∨ s 59 = true)
    : s 17 = true := by
  by_contra hc
  have u0 : s 34 ≠ true := c303
  have u1 : s 14 ≠ true := c302
  have u2 : s 11 ≠ true := c284
  have u3 : s 59 ≠ true := c201
  exact (Or.elim c147 (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (hc h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u3 h)))))))))

private theorem step307 (s : Fin 60 → Bool)
    (c303 : s 34 ≠ true)
    (c220 : s 37 ≠ true)
    (c290 : s 0 ≠ true)
    (c186 : s 52 ≠ true ∨ s 0 = true ∨ s 37 = true ∨ s 34 = true)
    : s 52 ≠ true := by
  by_contra hc
  have u0 : s 34 ≠ true := c303
  have u1 : s 37 ≠ true := c220
  have u2 : s 0 ≠ true := c290
  exact (Or.elim c186 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u0 h)))))))

private theorem step308 (s : Fin 60 → Bool)
    (c304 : s 50 = true)
    (c48 : s 13 ≠ true ∨ s 50 ≠ true)
    : s 13 ≠ true := by
  by_contra hc
  have u0 : s 50 = true := c304
  exact (Or.elim c48 (fun h => (h hc)) (fun h => (h u0)))

private theorem step309 (s : Fin 60 → Bool)
    (c304 : s 50 = true)
    (c64 : s 19 ≠ true ∨ s 50 ≠ true)
    : s 19 ≠ true := by
  by_contra hc
  have u0 : s 50 = true := c304
  exact (Or.elim c64 (fun h => (h hc)) (fun h => (h u0)))

private theorem step310 (s : Fin 60 → Bool)
    (c304 : s 50 = true)
    (c89 : s 28 ≠ true ∨ s 50 ≠ true)
    : s 28 ≠ true := by
  by_contra hc
  have u0 : s 50 = true := c304
  exact (Or.elim c89 (fun h => (h hc)) (fun h => (h u0)))

private theorem step311 (s : Fin 60 → Bool)
    (c304 : s 50 = true)
    (c118 : s 43 ≠ true ∨ s 50 ≠ true)
    : s 43 ≠ true := by
  by_contra hc
  have u0 : s 50 = true := c304
  exact (Or.elim c118 (fun h => (h hc)) (fun h => (h u0)))

private theorem step312 (s : Fin 60 → Bool)
    (c305 : s 20 = true)
    (c5 : s 1 ≠ true ∨ s 20 ≠ true)
    : s 1 ≠ true := by
  by_contra hc
  have u0 : s 20 = true := c305
  exact (Or.elim c5 (fun h => (h hc)) (fun h => (h u0)))

private theorem step313 (s : Fin 60 → Bool)
    (c305 : s 20 = true)
    (c7 : s 2 ≠ true ∨ s 20 ≠ true)
    : s 2 ≠ true := by
  by_contra hc
  have u0 : s 20 = true := c305
  exact (Or.elim c7 (fun h => (h hc)) (fun h => (h u0)))

private theorem step314 (s : Fin 60 → Bool)
    (c305 : s 20 = true)
    (c14 : s 4 ≠ true ∨ s 20 ≠ true)
    : s 4 ≠ true := by
  by_contra hc
  have u0 : s 20 = true := c305
  exact (Or.elim c14 (fun h => (h hc)) (fun h => (h u0)))

private theorem step315 (s : Fin 60 → Bool)
    (c306 : s 17 = true)
    (c58 : s 17 ≠ true ∨ s 51 ≠ true)
    : s 51 ≠ true := by
  by_contra hc
  have u0 : s 17 = true := c306
  exact (Or.elim c58 (fun h => (h u0)) (fun h => (h hc)))

private theorem step316 (s : Fin 60 → Bool)
    (c307 : s 52 ≠ true)
    (c292 : s 10 ≠ true)
    (c262 : s 16 ≠ true)
    (c311 : s 43 ≠ true)
    (c170 : s 16 = true ∨ s 32 = true ∨ s 43 = true ∨ s 52 = true ∨ s 10 = true)
    : s 32 = true := by
  by_contra hc
  have u0 : s 52 ≠ true := c307
  have u1 : s 10 ≠ true := c292
  have u2 : s 16 ≠ true := c262
  have u3 : s 43 ≠ true := c311
  exact (Or.elim c170 (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (hc h)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))))))

private theorem step317 (s : Fin 60 → Bool)
    (c307 : s 52 ≠ true)
    (c308 : s 13 ≠ true)
    (c292 : s 10 ≠ true)
    (c309 : s 19 ≠ true)
    (c137 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 47 = true ∨ s 52 = true)
    : s 47 = true := by
  by_contra hc
  have u0 : s 52 ≠ true := c307
  have u1 : s 13 ≠ true := c308
  have u2 : s 10 ≠ true := c292
  have u3 : s 19 ≠ true := c309
  exact (Or.elim c137 (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (Or.elim h (fun h => (hc h)) (fun h => (u0 h)))))))))

private theorem step318 (s : Fin 60 → Bool)
    (c308 : s 13 ≠ true)
    (c309 : s 19 ≠ true)
    (c311 : s 43 ≠ true)
    (c307 : s 52 ≠ true)
    (c297 : s 41 = true ∨ s 13 = true ∨ s 19 = true ∨ s 43 = true ∨ s 52 = true)
    : s 41 = true := by
  by_contra hc
  have u0 : s 13 ≠ true := c308
  have u1 : s 19 ≠ true := c309
  have u2 : s 43 ≠ true := c311
  have u3 : s 52 ≠ true := c307
  exact (Or.elim c297 (fun h => (hc h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (u3 h)))))))))

private theorem step319 (s : Fin 60 → Bool)
    (c317 : s 47 = true)
    (c87 : s 27 ≠ true ∨ s 47 ≠ true)
    : s 27 ≠ true := by
  by_contra hc
  have u0 : s 47 = true := c317
  exact (Or.elim c87 (fun h => (h hc)) (fun h => (h u0)))

private theorem step320 (s : Fin 60 → Bool)
    (c317 : s 47 = true)
    (c114 : s 42 ≠ true ∨ s 47 ≠ true)
    : s 42 ≠ true := by
  by_contra hc
  have u0 : s 47 = true := c317
  exact (Or.elim c114 (fun h => (h hc)) (fun h => (h u0)))

private theorem step321 (s : Fin 60 → Bool)
    (c318 : s 41 = true)
    (c25 : s 8 ≠ true ∨ s 41 ≠ true)
    : s 8 ≠ true := by
  by_contra hc
  have u0 : s 41 = true := c318
  exact (Or.elim c25 (fun h => (h hc)) (fun h => (h u0)))

private theorem step322 (s : Fin 60 → Bool)
    (c318 : s 41 = true)
    (c75 : s 23 ≠ true ∨ s 41 ≠ true)
    : s 23 ≠ true := by
  by_contra hc
  have u0 : s 41 = true := c318
  exact (Or.elim c75 (fun h => (h hc)) (fun h => (h u0)))

private theorem step323 (s : Fin 60 → Bool)
    (c318 : s 41 = true)
    (c78 : s 24 ≠ true ∨ s 41 ≠ true)
    : s 24 ≠ true := by
  by_contra hc
  have u0 : s 41 = true := c318
  exact (Or.elim c78 (fun h => (h hc)) (fun h => (h u0)))

private theorem step324 (s : Fin 60 → Bool)
    (c318 : s 41 = true)
    (c109 : s 41 ≠ true ∨ s 49 ≠ true)
    : s 49 ≠ true := by
  by_contra hc
  have u0 : s 41 = true := c318
  exact (Or.elim c109 (fun h => (h u0)) (fun h => (h hc)))

private theorem step325 (s : Fin 60 → Bool)
    (c318 : s 41 = true)
    (c110 : s 41 ≠ true ∨ s 54 ≠ true)
    : s 54 ≠ true := by
  by_contra hc
  have u0 : s 41 = true := c318
  exact (Or.elim c110 (fun h => (h u0)) (fun h => (h hc)))

private theorem step326 (s : Fin 60 → Bool)
    (c319 : s 27 ≠ true)
    (c324 : s 49 ≠ true)
    (c314 : s 4 ≠ true)
    (c313 : s 2 ≠ true)
    (c135 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 49 = true)
    : s 25 = true := by
  by_contra hc
  have u0 : s 27 ≠ true := c319
  have u1 : s 49 ≠ true := c324
  have u2 : s 4 ≠ true := c314
  have u3 : s 2 ≠ true := c313
  exact (Or.elim c135 (fun h => (u3 h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (hc h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))))))

private theorem step327 (s : Fin 60 → Bool)
    (c320 : s 42 ≠ true)
    (c321 : s 8 ≠ true)
    (c293 : s 35 ≠ true)
    (c283 : s 9 ≠ true)
    (c134 : s 8 = true ∨ s 9 = true ∨ s 35 = true ∨ s 42 = true ∨ s 48 = true)
    : s 48 = true := by
  by_contra hc
  have u0 : s 42 ≠ true := c320
  have u1 : s 8 ≠ true := c321
  have u2 : s 35 ≠ true := c293
  have u3 : s 9 ≠ true := c283
  exact (Or.elim c134 (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (hc h)))))))))

private theorem step328 (s : Fin 60 → Bool)
    (c323 : s 24 ≠ true)
    (c220 : s 37 ≠ true)
    (c322 : s 23 ≠ true)
    (c311 : s 43 ≠ true)
    (c130 : s 23 = true ∨ s 24 = true ∨ s 37 = true ∨ s 43 = true ∨ s 53 = true)
    : s 53 = true := by
  by_contra hc
  have u0 : s 24 ≠ true := c323
  have u1 : s 37 ≠ true := c220
  have u2 : s 23 ≠ true := c322
  have u3 : s 43 ≠ true := c311
  exact (Or.elim c130 (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (hc h)))))))))

private theorem step329 (s : Fin 60 → Bool)
    (c327 : s 48 = true)
    (c324 : s 49 ≠ true)
    (c305 : s 20 = true)
    (c173 : s 20 ≠ true ∨ s 48 ≠ true ∨ s 49 = true)
    : False := by
  have u0 : s 48 = true := c327
  have u1 : s 49 ≠ true := c324
  have u2 : s 20 = true := c305
  exact (Or.elim c173 (fun h => (h u2)) (fun h => (Or.elim h (fun h => (h u0)) (fun h => (u1 h)))))

/-- No independent set hits these 44 five-cycles. The certificate is proved
using explicit propositional case analysis, without compiler-trust axioms. -/
private theorem no_selector (s : Fin 60 → Bool)
    (hn : ∀ i : Fin 119, ¬(s (excluded i).1 = true ∧ s (excluded i).2 = true))
    (hp : ∀ i : Fin 44, s (cycles i 0) = true ∨ s (cycles i 1) = true ∨
      s (cycles i 2) = true ∨ s (cycles i 3) = true ∨ s (cycles i 4) = true) : False := by
  have c1 : s 0 ≠ true ∨ s 17 ≠ true := by
    have n : ¬(s 0 = true ∧ s 17 = true) := hn 0
    by_cases ha : s 0 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c2 : s 0 ≠ true ∨ s 18 ≠ true := by
    have n : ¬(s 0 = true ∧ s 18 = true) := hn 1
    by_cases ha : s 0 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c3 : s 0 ≠ true ∨ s 20 ≠ true := by
    have n : ¬(s 0 = true ∧ s 20 = true) := hn 2
    by_cases ha : s 0 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c4 : s 0 ≠ true ∨ s 30 ≠ true := by
    have n : ¬(s 0 = true ∧ s 30 = true) := hn 3
    by_cases ha : s 0 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c5 : s 1 ≠ true ∨ s 20 ≠ true := by
    have n : ¬(s 1 = true ∧ s 20 = true) := hn 4
    by_cases ha : s 1 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c6 : s 2 ≠ true ∨ s 45 ≠ true := by
    have n : ¬(s 2 = true ∧ s 45 = true) := hn 5
    by_cases ha : s 2 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c7 : s 2 ≠ true ∨ s 20 ≠ true := by
    have n : ¬(s 2 = true ∧ s 20 = true) := hn 6
    by_cases ha : s 2 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c8 : s 2 ≠ true ∨ s 29 ≠ true := by
    have n : ¬(s 2 = true ∧ s 29 = true) := hn 7
    by_cases ha : s 2 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c9 : s 2 ≠ true ∨ s 30 ≠ true := by
    have n : ¬(s 2 = true ∧ s 30 = true) := hn 8
    by_cases ha : s 2 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c10 : s 3 ≠ true ∨ s 32 ≠ true := by
    have n : ¬(s 3 = true ∧ s 32 = true) := hn 9
    by_cases ha : s 3 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c11 : s 3 ≠ true ∨ s 33 ≠ true := by
    have n : ¬(s 3 = true ∧ s 33 = true) := hn 10
    by_cases ha : s 3 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c12 : s 3 ≠ true ∨ s 30 ≠ true := by
    have n : ¬(s 3 = true ∧ s 30 = true) := hn 11
    by_cases ha : s 3 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c13 : s 3 ≠ true ∨ s 31 ≠ true := by
    have n : ¬(s 3 = true ∧ s 31 = true) := hn 12
    by_cases ha : s 3 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c14 : s 4 ≠ true ∨ s 20 ≠ true := by
    have n : ¬(s 4 = true ∧ s 20 = true) := hn 13
    by_cases ha : s 4 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c15 : s 4 ≠ true ∨ s 30 ≠ true := by
    have n : ¬(s 4 = true ∧ s 30 = true) := hn 14
    by_cases ha : s 4 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c16 : s 5 ≠ true ∨ s 35 ≠ true := by
    have n : ¬(s 5 = true ∧ s 35 = true) := hn 15
    by_cases ha : s 5 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c17 : s 5 ≠ true ∨ s 16 ≠ true := by
    have n : ¬(s 5 = true ∧ s 16 = true) := hn 16
    by_cases ha : s 5 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c18 : s 5 ≠ true ∨ s 18 ≠ true := by
    have n : ¬(s 5 = true ∧ s 18 = true) := hn 17
    by_cases ha : s 5 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c19 : s 6 ≠ true ∨ s 40 ≠ true := by
    have n : ¬(s 6 = true ∧ s 40 = true) := hn 18
    by_cases ha : s 6 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c20 : s 7 ≠ true ∨ s 35 ≠ true := by
    have n : ¬(s 7 = true ∧ s 35 = true) := hn 19
    by_cases ha : s 7 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c21 : s 7 ≠ true ∨ s 36 ≠ true := by
    have n : ¬(s 7 = true ∧ s 36 = true) := hn 20
    by_cases ha : s 7 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c22 : s 7 ≠ true ∨ s 39 ≠ true := by
    have n : ¬(s 7 = true ∧ s 39 = true) := hn 21
    by_cases ha : s 7 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c23 : s 7 ≠ true ∨ s 40 ≠ true := by
    have n : ¬(s 7 = true ∧ s 40 = true) := hn 22
    by_cases ha : s 7 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c24 : s 7 ≠ true ∨ s 16 ≠ true := by
    have n : ¬(s 7 = true ∧ s 16 = true) := hn 23
    by_cases ha : s 7 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c25 : s 8 ≠ true ∨ s 41 ≠ true := by
    have n : ¬(s 8 = true ∧ s 41 = true) := hn 24
    by_cases ha : s 8 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c26 : s 8 ≠ true ∨ s 43 ≠ true := by
    have n : ¬(s 8 = true ∧ s 43 = true) := hn 25
    by_cases ha : s 8 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c27 : s 8 ≠ true ∨ s 46 ≠ true := by
    have n : ¬(s 8 = true ∧ s 46 = true) := hn 26
    by_cases ha : s 8 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c28 : s 8 ≠ true ∨ s 16 ≠ true := by
    have n : ¬(s 8 = true ∧ s 16 = true) := hn 27
    by_cases ha : s 8 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c29 : s 9 ≠ true ∨ s 35 ≠ true := by
    have n : ¬(s 9 = true ∧ s 35 = true) := hn 28
    by_cases ha : s 9 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c30 : s 9 ≠ true ∨ s 46 ≠ true := by
    have n : ¬(s 9 = true ∧ s 46 = true) := hn 29
    by_cases ha : s 9 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c31 : s 9 ≠ true ∨ s 47 ≠ true := by
    have n : ¬(s 9 = true ∧ s 47 = true) := hn 30
    by_cases ha : s 9 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c32 : s 9 ≠ true ∨ s 16 ≠ true := by
    have n : ¬(s 9 = true ∧ s 16 = true) := hn 31
    by_cases ha : s 9 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c33 : s 9 ≠ true ∨ s 48 ≠ true := by
    have n : ¬(s 9 = true ∧ s 48 = true) := hn 32
    by_cases ha : s 9 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c34 : s 9 ≠ true ∨ s 49 ≠ true := by
    have n : ¬(s 9 = true ∧ s 49 = true) := hn 33
    by_cases ha : s 9 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c35 : s 9 ≠ true ∨ s 31 ≠ true := by
    have n : ¬(s 9 = true ∧ s 31 = true) := hn 34
    by_cases ha : s 9 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c36 : s 10 ≠ true ∨ s 32 ≠ true := by
    have n : ¬(s 10 = true ∧ s 32 = true) := hn 35
    by_cases ha : s 10 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c37 : s 10 ≠ true ∨ s 16 ≠ true := by
    have n : ¬(s 10 = true ∧ s 16 = true) := hn 36
    by_cases ha : s 10 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c38 : s 10 ≠ true ∨ s 18 ≠ true := by
    have n : ¬(s 10 = true ∧ s 18 = true) := hn 37
    by_cases ha : s 10 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c39 : s 10 ≠ true ∨ s 47 ≠ true := by
    have n : ¬(s 10 = true ∧ s 47 = true) := hn 38
    by_cases ha : s 10 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c40 : s 10 ≠ true ∨ s 55 ≠ true := by
    have n : ¬(s 10 = true ∧ s 55 = true) := hn 39
    by_cases ha : s 10 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c41 : s 11 ≠ true ∨ s 34 ≠ true := by
    have n : ¬(s 11 = true ∧ s 34 = true) := hn 40
    by_cases ha : s 11 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c42 : s 11 ≠ true ∨ s 17 ≠ true := by
    have n : ¬(s 11 = true ∧ s 17 = true) := hn 41
    by_cases ha : s 11 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c43 : s 11 ≠ true ∨ s 55 ≠ true := by
    have n : ¬(s 11 = true ∧ s 55 = true) := hn 42
    by_cases ha : s 11 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c44 : s 11 ≠ true ∨ s 31 ≠ true := by
    have n : ¬(s 11 = true ∧ s 31 = true) := hn 43
    by_cases ha : s 11 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c45 : s 12 ≠ true ∨ s 45 ≠ true := by
    have n : ¬(s 12 = true ∧ s 45 = true) := hn 44
    by_cases ha : s 12 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c46 : s 12 ≠ true ∨ s 55 ≠ true := by
    have n : ¬(s 12 = true ∧ s 55 = true) := hn 45
    by_cases ha : s 12 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c47 : s 13 ≠ true ∨ s 32 ≠ true := by
    have n : ¬(s 13 = true ∧ s 32 = true) := hn 46
    by_cases ha : s 13 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c48 : s 13 ≠ true ∨ s 50 ≠ true := by
    have n : ¬(s 13 = true ∧ s 50 = true) := hn 47
    by_cases ha : s 13 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c49 : s 13 ≠ true ∨ s 51 ≠ true := by
    have n : ¬(s 13 = true ∧ s 51 = true) := hn 48
    by_cases ha : s 13 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c50 : s 13 ≠ true ∨ s 52 ≠ true := by
    have n : ¬(s 13 = true ∧ s 52 = true) := hn 49
    by_cases ha : s 13 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c51 : s 13 ≠ true ∨ s 53 ≠ true := by
    have n : ¬(s 13 = true ∧ s 53 = true) := hn 50
    by_cases ha : s 13 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c52 : s 14 ≠ true ∨ s 32 ≠ true := by
    have n : ¬(s 14 = true ∧ s 32 = true) := hn 51
    by_cases ha : s 14 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c53 : s 14 ≠ true ∨ s 17 ≠ true := by
    have n : ¬(s 14 = true ∧ s 17 = true) := hn 52
    by_cases ha : s 14 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c54 : s 14 ≠ true ∨ s 55 ≠ true := by
    have n : ¬(s 14 = true ∧ s 55 = true) := hn 53
    by_cases ha : s 14 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c55 : s 14 ≠ true ∨ s 57 ≠ true := by
    have n : ¬(s 14 = true ∧ s 57 = true) := hn 54
    by_cases ha : s 14 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c56 : s 16 ≠ true ∨ s 36 ≠ true := by
    have n : ¬(s 16 = true ∧ s 36 = true) := hn 55
    by_cases ha : s 16 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c57 : s 16 ≠ true ∨ s 51 ≠ true := by
    have n : ¬(s 16 = true ∧ s 51 = true) := hn 56
    by_cases ha : s 16 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c58 : s 17 ≠ true ∨ s 51 ≠ true := by
    have n : ¬(s 17 = true ∧ s 51 = true) := hn 57
    by_cases ha : s 17 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c59 : s 18 ≠ true ∨ s 35 ≠ true := by
    have n : ¬(s 18 = true ∧ s 35 = true) := hn 58
    by_cases ha : s 18 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c60 : s 18 ≠ true ∨ s 36 ≠ true := by
    have n : ¬(s 18 = true ∧ s 36 = true) := hn 59
    by_cases ha : s 18 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c61 : s 18 ≠ true ∨ s 37 ≠ true := by
    have n : ¬(s 18 = true ∧ s 37 = true) := hn 60
    by_cases ha : s 18 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c62 : s 18 ≠ true ∨ s 39 ≠ true := by
    have n : ¬(s 18 = true ∧ s 39 = true) := hn 61
    by_cases ha : s 18 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c63 : s 19 ≠ true ∨ s 36 ≠ true := by
    have n : ¬(s 19 = true ∧ s 36 = true) := hn 62
    by_cases ha : s 19 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c64 : s 19 ≠ true ∨ s 50 ≠ true := by
    have n : ¬(s 19 = true ∧ s 50 = true) := hn 63
    by_cases ha : s 19 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c65 : s 19 ≠ true ∨ s 51 ≠ true := by
    have n : ¬(s 19 = true ∧ s 51 = true) := hn 64
    by_cases ha : s 19 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c66 : s 19 ≠ true ∨ s 53 ≠ true := by
    have n : ¬(s 19 = true ∧ s 53 = true) := hn 65
    by_cases ha : s 19 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c67 : s 20 ≠ true ∨ s 37 ≠ true := by
    have n : ¬(s 20 = true ∧ s 37 = true) := hn 66
    by_cases ha : s 20 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c68 : s 20 ≠ true ∨ s 52 ≠ true := by
    have n : ¬(s 20 = true ∧ s 52 = true) := hn 67
    by_cases ha : s 20 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c69 : s 21 ≠ true ∨ s 32 ≠ true := by
    have n : ¬(s 21 = true ∧ s 32 = true) := hn 68
    by_cases ha : s 21 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c70 : s 21 ≠ true ∨ s 41 ≠ true := by
    have n : ¬(s 21 = true ∧ s 41 = true) := hn 69
    by_cases ha : s 21 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c71 : s 21 ≠ true ∨ s 52 ≠ true := by
    have n : ¬(s 21 = true ∧ s 52 = true) := hn 70
    by_cases ha : s 21 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c72 : s 21 ≠ true ∨ s 30 ≠ true := by
    have n : ¬(s 21 = true ∧ s 30 = true) := hn 71
    by_cases ha : s 21 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c73 : s 21 ≠ true ∨ s 31 ≠ true := by
    have n : ¬(s 21 = true ∧ s 31 = true) := hn 72
    by_cases ha : s 21 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c74 : s 23 ≠ true ∨ s 37 ≠ true := by
    have n : ¬(s 23 = true ∧ s 37 = true) := hn 73
    by_cases ha : s 23 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c75 : s 23 ≠ true ∨ s 41 ≠ true := by
    have n : ¬(s 23 = true ∧ s 41 = true) := hn 74
    by_cases ha : s 23 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c76 : s 23 ≠ true ∨ s 52 ≠ true := by
    have n : ¬(s 23 = true ∧ s 52 = true) := hn 75
    by_cases ha : s 23 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c77 : s 24 ≠ true ∨ s 37 ≠ true := by
    have n : ¬(s 24 = true ∧ s 37 = true) := hn 76
    by_cases ha : s 24 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c78 : s 24 ≠ true ∨ s 41 ≠ true := by
    have n : ¬(s 24 = true ∧ s 41 = true) := hn 77
    by_cases ha : s 24 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c79 : s 25 ≠ true ∨ s 48 ≠ true := by
    have n : ¬(s 25 = true ∧ s 48 = true) := hn 78
    by_cases ha : s 25 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c80 : s 25 ≠ true ∨ s 53 ≠ true := by
    have n : ¬(s 25 = true ∧ s 53 = true) := hn 79
    by_cases ha : s 25 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c81 : s 26 ≠ true ∨ s 37 ≠ true := by
    have n : ¬(s 26 = true ∧ s 37 = true) := hn 80
    by_cases ha : s 26 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c82 : s 26 ≠ true ∨ s 38 ≠ true := by
    have n : ¬(s 26 = true ∧ s 38 = true) := hn 81
    by_cases ha : s 26 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c83 : s 26 ≠ true ∨ s 39 ≠ true := by
    have n : ¬(s 26 = true ∧ s 39 = true) := hn 82
    by_cases ha : s 26 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c84 : s 26 ≠ true ∨ s 48 ≠ true := by
    have n : ¬(s 26 = true ∧ s 48 = true) := hn 83
    by_cases ha : s 26 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c85 : s 26 ≠ true ∨ s 53 ≠ true := by
    have n : ¬(s 26 = true ∧ s 53 = true) := hn 84
    by_cases ha : s 26 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c86 : s 27 ≠ true ∨ s 38 ≠ true := by
    have n : ¬(s 27 = true ∧ s 38 = true) := hn 85
    by_cases ha : s 27 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c87 : s 27 ≠ true ∨ s 47 ≠ true := by
    have n : ¬(s 27 = true ∧ s 47 = true) := hn 86
    by_cases ha : s 27 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c88 : s 27 ≠ true ∨ s 48 ≠ true := by
    have n : ¬(s 27 = true ∧ s 48 = true) := hn 87
    by_cases ha : s 27 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c89 : s 28 ≠ true ∨ s 50 ≠ true := by
    have n : ¬(s 28 = true ∧ s 50 = true) := hn 88
    by_cases ha : s 28 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c90 : s 28 ≠ true ∨ s 52 ≠ true := by
    have n : ¬(s 28 = true ∧ s 52 = true) := hn 89
    by_cases ha : s 28 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c91 : s 29 ≠ true ∨ s 38 ≠ true := by
    have n : ¬(s 29 = true ∧ s 38 = true) := hn 90
    by_cases ha : s 29 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c92 : s 29 ≠ true ∨ s 48 ≠ true := by
    have n : ¬(s 29 = true ∧ s 48 = true) := hn 91
    by_cases ha : s 29 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c93 : s 29 ≠ true ∨ s 53 ≠ true := by
    have n : ¬(s 29 = true ∧ s 53 = true) := hn 92
    by_cases ha : s 29 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c94 : s 29 ≠ true ∨ s 57 ≠ true := by
    have n : ¬(s 29 = true ∧ s 57 = true) := hn 93
    by_cases ha : s 29 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c95 : s 29 ≠ true ∨ s 59 ≠ true := by
    have n : ¬(s 29 = true ∧ s 59 = true) := hn 94
    by_cases ha : s 29 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c96 : s 33 ≠ true ∨ s 57 ≠ true := by
    have n : ¬(s 33 = true ∧ s 57 = true) := hn 95
    by_cases ha : s 33 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c97 : s 34 ≠ true ∨ s 55 ≠ true := by
    have n : ¬(s 34 = true ∧ s 55 = true) := hn 96
    by_cases ha : s 34 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c98 : s 34 ≠ true ∨ s 57 ≠ true := by
    have n : ¬(s 34 = true ∧ s 57 = true) := hn 97
    by_cases ha : s 34 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c99 : s 34 ≠ true ∨ s 58 ≠ true := by
    have n : ¬(s 34 = true ∧ s 58 = true) := hn 98
    by_cases ha : s 34 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c100 : s 34 ≠ true ∨ s 59 ≠ true := by
    have n : ¬(s 34 = true ∧ s 59 = true) := hn 99
    by_cases ha : s 34 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c101 : s 37 ≠ true ∨ s 58 ≠ true := by
    have n : ¬(s 37 = true ∧ s 58 = true) := hn 100
    by_cases ha : s 37 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c102 : s 38 ≠ true ∨ s 58 ≠ true := by
    have n : ¬(s 38 = true ∧ s 58 = true) := hn 101
    by_cases ha : s 38 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c103 : s 39 ≠ true ∨ s 55 ≠ true := by
    have n : ¬(s 39 = true ∧ s 55 = true) := hn 102
    by_cases ha : s 39 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c104 : s 39 ≠ true ∨ s 57 ≠ true := by
    have n : ¬(s 39 = true ∧ s 57 = true) := hn 103
    by_cases ha : s 39 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c105 : s 39 ≠ true ∨ s 59 ≠ true := by
    have n : ¬(s 39 = true ∧ s 59 = true) := hn 104
    by_cases ha : s 39 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c106 : s 40 ≠ true ∨ s 49 ≠ true := by
    have n : ¬(s 40 = true ∧ s 49 = true) := hn 105
    by_cases ha : s 40 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c107 : s 40 ≠ true ∨ s 54 ≠ true := by
    have n : ¬(s 40 = true ∧ s 54 = true) := hn 106
    by_cases ha : s 40 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c108 : s 40 ≠ true ∨ s 59 ≠ true := by
    have n : ¬(s 40 = true ∧ s 59 = true) := hn 107
    by_cases ha : s 40 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c109 : s 41 ≠ true ∨ s 49 ≠ true := by
    have n : ¬(s 41 = true ∧ s 49 = true) := hn 108
    by_cases ha : s 41 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c110 : s 41 ≠ true ∨ s 54 ≠ true := by
    have n : ¬(s 41 = true ∧ s 54 = true) := hn 109
    by_cases ha : s 41 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c111 : s 41 ≠ true ∨ s 59 ≠ true := by
    have n : ¬(s 41 = true ∧ s 59 = true) := hn 110
    by_cases ha : s 41 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c112 : s 42 ≠ true ∨ s 45 ≠ true := by
    have n : ¬(s 42 = true ∧ s 45 = true) := hn 111
    by_cases ha : s 42 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c113 : s 42 ≠ true ∨ s 46 ≠ true := by
    have n : ¬(s 42 = true ∧ s 46 = true) := hn 112
    by_cases ha : s 42 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c114 : s 42 ≠ true ∨ s 47 ≠ true := by
    have n : ¬(s 42 = true ∧ s 47 = true) := hn 113
    by_cases ha : s 42 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c115 : s 42 ≠ true ∨ s 54 ≠ true := by
    have n : ¬(s 42 = true ∧ s 54 = true) := hn 114
    by_cases ha : s 42 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c116 : s 42 ≠ true ∨ s 59 ≠ true := by
    have n : ¬(s 42 = true ∧ s 59 = true) := hn 115
    by_cases ha : s 42 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c117 : s 43 ≠ true ∨ s 49 ≠ true := by
    have n : ¬(s 43 = true ∧ s 49 = true) := hn 116
    by_cases ha : s 43 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c118 : s 43 ≠ true ∨ s 50 ≠ true := by
    have n : ¬(s 43 = true ∧ s 50 = true) := hn 117
    by_cases ha : s 43 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c119 : s 43 ≠ true ∨ s 51 ≠ true := by
    have n : ¬(s 43 = true ∧ s 51 = true) := hn 118
    by_cases ha : s 43 = true
    · exact Or.inr (fun hb => n ⟨ha,hb⟩)
    · exact Or.inl ha
  have c120 : s 0 = true ∨ s 8 = true ∨ s 16 = true ∨ s 20 = true ∨ s 41 = true := by
    have h : s 0 = true ∨ s 16 = true ∨ s 8 = true ∨ s 41 = true ∨ s 20 = true := hp 0
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c121 : s 12 = true ∨ s 21 = true ∨ s 32 = true ∨ s 41 = true ∨ s 49 = true := by
    have h : s 12 = true ∨ s 32 = true ∨ s 21 = true ∨ s 41 = true ∨ s 49 = true := hp 1
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))
  have c122 : s 8 = true ∨ s 21 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true := by
    have h : s 8 = true ∨ s 41 = true ∨ s 21 = true ∨ s 52 = true ∨ s 43 = true := hp 2
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c123 : s 4 = true ∨ s 8 = true ∨ s 40 = true ∨ s 46 = true ∨ s 49 = true := by
    have h : s 4 = true ∨ s 46 = true ∨ s 8 = true ∨ s 40 = true ∨ s 49 = true := hp 3
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))
  have c124 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 34 = true ∨ s 37 = true := by
    have h : s 3 = true ∨ s 20 = true ∨ s 37 = true ∨ s 21 = true ∨ s 34 = true := hp 4
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c125 : s 5 = true ∨ s 7 = true ∨ s 18 = true ∨ s 39 = true ∨ s 40 = true := by
    have h : s 5 = true ∨ s 18 = true ∨ s 39 = true ∨ s 7 = true ∨ s 40 = true := hp 5
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))
  have c126 : s 8 = true ∨ s 16 = true ∨ s 18 = true ∨ s 35 = true ∨ s 51 = true := by
    have h : s 8 = true ∨ s 16 = true ∨ s 51 = true ∨ s 18 = true ∨ s 35 = true := hp 6
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c127 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 32 = true ∨ s 52 = true := by
    have h : s 10 = true ∨ s 19 = true ∨ s 52 = true ∨ s 13 = true ∨ s 32 = true := hp 7
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c128 : s 3 = true ∨ s 20 = true ∨ s 21 = true ∨ s 32 = true ∨ s 37 = true := by
    have h : s 3 = true ∨ s 20 = true ∨ s 37 = true ∨ s 21 = true ∨ s 32 = true := hp 8
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c129 : s 9 = true ∨ s 23 = true ∨ s 40 = true ∨ s 42 = true ∨ s 45 = true := by
    have h : s 9 = true ∨ s 40 = true ∨ s 23 = true ∨ s 42 = true ∨ s 45 = true := hp 9
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))
  have c130 : s 23 = true ∨ s 24 = true ∨ s 37 = true ∨ s 43 = true ∨ s 53 = true := by
    have h : s 23 = true ∨ s 37 = true ∨ s 24 = true ∨ s 53 = true ∨ s 43 = true := hp 10
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c131 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 46 = true := by
    have h : s 2 = true ∨ s 25 = true ∨ s 4 = true ∨ s 46 = true ∨ s 27 = true := hp 11
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c132 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 51 = true ∨ s 55 = true := by
    have h : s 10 = true ∨ s 19 = true ∨ s 51 = true ∨ s 13 = true ∨ s 55 = true := hp 12
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))
  have c133 : s 11 = true ∨ s 14 = true ∨ s 31 = true ∨ s 50 = true ∨ s 57 = true := by
    have h : s 11 = true ∨ s 31 = true ∨ s 57 = true ∨ s 14 = true ∨ s 50 = true := hp 13
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c134 : s 8 = true ∨ s 9 = true ∨ s 35 = true ∨ s 42 = true ∨ s 48 = true := by
    have h : s 8 = true ∨ s 35 = true ∨ s 9 = true ∨ s 48 = true ∨ s 42 = true := hp 14
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c135 : s 2 = true ∨ s 4 = true ∨ s 25 = true ∨ s 27 = true ∨ s 49 = true := by
    have h : s 2 = true ∨ s 25 = true ∨ s 4 = true ∨ s 49 = true ∨ s 27 = true := hp 15
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c136 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 54 = true ∨ s 55 = true := by
    have h : s 10 = true ∨ s 19 = true ∨ s 54 = true ∨ s 13 = true ∨ s 55 = true := hp 16
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))
  have c137 : s 10 = true ∨ s 13 = true ∨ s 19 = true ∨ s 47 = true ∨ s 52 = true := by
    have h : s 10 = true ∨ s 19 = true ∨ s 52 = true ∨ s 13 = true ∨ s 47 = true := hp 17
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c138 : s 1 = true ∨ s 3 = true ∨ s 21 = true ∨ s 32 = true ∨ s 45 = true := by
    have h : s 1 = true ∨ s 21 = true ∨ s 32 = true ∨ s 3 = true ∨ s 45 = true := hp 18
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))
  have c139 : s 2 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 41 = true := by
    have h : s 2 = true ∨ s 20 = true ∨ s 41 = true ∨ s 21 = true ∨ s 30 = true := hp 19
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c140 : s 10 = true ∨ s 16 = true ∨ s 43 = true ∨ s 50 = true ∨ s 51 = true := by
    have h : s 10 = true ∨ s 16 = true ∨ s 51 = true ∨ s 43 = true ∨ s 50 = true := hp 20
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c141 : s 10 = true ∨ s 18 = true ∨ s 24 = true ∨ s 50 = true ∨ s 51 = true := by
    have h : s 10 = true ∨ s 18 = true ∨ s 51 = true ∨ s 24 = true ∨ s 50 = true := hp 21
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c142 : s 11 = true ∨ s 14 = true ∨ s 34 = true ∨ s 50 = true ∨ s 59 = true := by
    have h : s 11 = true ∨ s 34 = true ∨ s 59 = true ∨ s 14 = true ∨ s 50 = true := hp 22
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c143 : s 18 = true ∨ s 29 = true ∨ s 38 = true ∨ s 39 = true ∨ s 55 = true := by
    have h : s 18 = true ∨ s 38 = true ∨ s 29 = true ∨ s 55 = true ∨ s 39 = true := hp 23
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c144 : s 11 = true ∨ s 29 = true ∨ s 32 = true ∨ s 55 = true ∨ s 57 = true := by
    have h : s 11 = true ∨ s 32 = true ∨ s 57 = true ∨ s 29 = true ∨ s 55 = true := hp 24
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c145 : s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 38 = true ∨ s 51 = true := by
    have h : s 7 = true ∨ s 16 = true ∨ s 51 = true ∨ s 18 = true ∨ s 38 = true := hp 25
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c146 : s 2 = true ∨ s 4 = true ∨ s 20 = true ∨ s 28 = true ∨ s 48 = true := by
    have h : s 2 = true ∨ s 20 = true ∨ s 4 = true ∨ s 48 = true ∨ s 28 = true := hp 26
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c147 : s 11 = true ∨ s 14 = true ∨ s 17 = true ∨ s 34 = true ∨ s 59 = true := by
    have h : s 11 = true ∨ s 17 = true ∨ s 14 = true ∨ s 59 = true ∨ s 34 = true := hp 27
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c148 : s 5 = true ∨ s 13 = true ∨ s 17 = true ∨ s 19 = true ∨ s 53 = true := by
    have h : s 5 = true ∨ s 17 = true ∨ s 13 = true ∨ s 53 = true ∨ s 19 = true := hp 28
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c149 : s 0 = true ∨ s 7 = true ∨ s 16 = true ∨ s 18 = true ∨ s 37 = true := by
    have h : s 0 = true ∨ s 16 = true ∨ s 7 = true ∨ s 37 = true ∨ s 18 = true := hp 29
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c150 : s 9 = true ∨ s 16 = true ∨ s 18 = true ∨ s 35 = true ∨ s 36 = true := by
    have h : s 9 = true ∨ s 16 = true ∨ s 36 = true ∨ s 18 = true ∨ s 35 = true := hp 30
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c151 : s 8 = true ∨ s 26 = true ∨ s 35 = true ∨ s 43 = true ∨ s 53 = true := by
    have h : s 8 = true ∨ s 35 = true ∨ s 26 = true ∨ s 53 = true ∨ s 43 = true := hp 31
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c152 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 52 = true ∨ s 59 = true := by
    have h : s 20 = true ∨ s 41 = true ∨ s 59 = true ∨ s 43 = true ∨ s 52 = true := hp 32
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c153 : s 8 = true ∨ s 9 = true ∨ s 31 = true ∨ s 42 = true ∨ s 49 = true := by
    have h : s 8 = true ∨ s 31 = true ∨ s 9 = true ∨ s 49 = true ∨ s 42 = true := hp 33
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c154 : s 10 = true ∨ s 13 = true ∨ s 18 = true ∨ s 50 = true ∨ s 51 = true := by
    have h : s 10 = true ∨ s 18 = true ∨ s 51 = true ∨ s 13 = true ∨ s 50 = true := hp 34
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c155 : s 5 = true ∨ s 7 = true ∨ s 17 = true ∨ s 31 = true ∨ s 36 = true := by
    have h : s 5 = true ∨ s 17 = true ∨ s 36 = true ∨ s 7 = true ∨ s 31 = true := hp 35
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c156 : s 26 = true ∨ s 29 = true ∨ s 35 = true ∨ s 48 = true ∨ s 58 = true := by
    have h : s 26 = true ∨ s 35 = true ∨ s 58 = true ∨ s 29 = true ∨ s 48 = true := hp 36
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c157 : s 0 = true ∨ s 18 = true ∨ s 30 = true ∨ s 39 = true ∨ s 57 = true := by
    have h : s 0 = true ∨ s 18 = true ∨ s 39 = true ∨ s 57 = true ∨ s 30 = true := hp 37
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.inr (Or.inr (Or.inl h)))))))))))
  have c158 : s 0 = true ∨ s 20 = true ∨ s 21 = true ∨ s 30 = true ∨ s 33 = true := by
    have h : s 0 = true ∨ s 20 = true ∨ s 33 = true ∨ s 21 = true ∨ s 30 = true := hp 38
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c159 : s 5 = true ∨ s 19 = true ∨ s 27 = true ∨ s 46 = true ∨ s 53 = true := by
    have h : s 5 = true ∨ s 19 = true ∨ s 53 = true ∨ s 27 = true ∨ s 46 = true := hp 39
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c160 : s 6 = true ∨ s 14 = true ∨ s 32 = true ∨ s 34 = true ∨ s 55 = true := by
    have h : s 6 = true ∨ s 32 = true ∨ s 14 = true ∨ s 55 = true ∨ s 34 = true := hp 40
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c161 : s 26 = true ∨ s 29 = true ∨ s 39 = true ∨ s 53 = true ∨ s 55 = true := by
    have h : s 26 = true ∨ s 39 = true ∨ s 55 = true ∨ s 29 = true ∨ s 53 = true := hp 41
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c162 : s 13 = true ∨ s 29 = true ∨ s 32 = true ∨ s 55 = true ∨ s 57 = true := by
    have h : s 13 = true ∨ s 32 = true ∨ s 57 = true ∨ s 29 = true ∨ s 55 = true := hp 42
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c163 : s 9 = true ∨ s 14 = true ∨ s 35 = true ∨ s 47 = true ∨ s 58 = true := by
    have h : s 9 = true ∨ s 35 = true ∨ s 58 = true ∨ s 14 = true ∨ s 47 = true := hp 43
    exact (Or.elim h (fun h => (Or.inl h)) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inr (Or.inr (Or.inr h))))) (fun h => (Or.elim h (fun h => (Or.inr (Or.inl h))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  have c164 : s 52 ≠ true ∨ s 12 = true ∨ s 37 = true ∨ s 59 ≠ true := step164 s c116 c111 c108 c100 c68 c71 c76 c124 c10 c12 c121 c139 c34 c6 c129
  have c165 : s 53 ≠ true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true := step165 s c46 c164 c40 c111 c100 c51 c66 c80 c127 c137 c10 c69 c87 c124 c7 c14 c131 c135 c27 c117 c122
  have c166 : s 5 ≠ true ∨ s 16 = true ∨ s 0 = true ∨ s 9 = true ∨ s 37 = true := step166 s c16 c18 c150 c149 c21
  have c167 : s 19 ≠ true ∨ s 16 = true ∨ s 43 = true ∨ s 10 = true := step167 s c64 c65 c140
  have c168 : s 32 ≠ true ∨ s 49 ≠ true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true := step168 s c117 c34 c165 c46 c164 c40 c111 c100 c10 c47 c69 c124 c122 c3 c27 c28 c166 c167 c137 c159 c87
  have c169 : s 16 ≠ true ∨ s 48 = true ∨ s 9 = true ∨ s 59 ≠ true := step169 s c116 c108 c105 c17 c24 c28 c125 c134 c59
  have c170 : s 16 = true ∨ s 32 = true ∨ s 43 = true ∨ s 52 = true ∨ s 10 = true := step170 s c167 c127 c48 c49 c140
  have c171 : s 49 ≠ true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true := step171 s c165 c46 c164 c40 c108 c105 c34 c117 c168 c170 c17 c24 c28 c169 c125 c84 c59 c151
  have c172 : s 16 ≠ true ∨ s 49 = true ∨ s 37 = true ∨ s 59 ≠ true := step172 s c116 c100 c28 c32 c169 c153 c79 c88 c13 c73 c124 c7 c14 c135
  have c173 : s 20 ≠ true ∨ s 48 ≠ true ∨ s 49 = true := step173 s c88 c79 c7 c14 c135
  have c174 : s 21 = true ∨ s 20 = true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true := step174 s c171 c46 c111 c100 c124 c121 c10
  have c175 : s 21 ≠ true ∨ s 9 = true ∨ s 16 = true ∨ s 49 = true ∨ s 52 = true ∨ s 10 = true ∨ s 42 = true := step175 s c69 c73 c170 c153 c26
  have c176 : s 8 ≠ true ∨ s 5 = true ∨ s 13 = true ∨ s 16 = true ∨ s 53 = true ∨ s 52 = true ∨ s 10 = true := step176 s c26 c27 c167 c137 c159 c87
  have c177 : s 9 = true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true := step177 s c171 c172 c165 c46 c164 c40 c116 c111 c175 c121 c174 c47 c3 c173 c166 c176 c134 c20 c59 c149
  have c178 : s 32 ≠ true ∨ s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true := step178 s c177 c31 c30 c171 c172 c46 c164 c40 c108 c100 c10 c47 c69 c124 c137 c14 c167 c123 c26
  have c179 : s 55 ≠ true ∨ s 37 = true ∨ s 59 ≠ true := step179 s c111 c108 c40 c46 c164 c171 c172 c177 c29 c30 c178 c170 c26 c119 c123 c126 c14 c2 c120
  have c180 : s 8 = true ∨ s 16 = true ∨ s 49 = true ∨ s 18 ≠ true ∨ s 59 ≠ true := step180 s c59 c2 c116 c111 c108 c120 c14 c173 c123 c134 c30
  have c181 : s 52 ≠ true ∨ s 33 = true ∨ s 0 = true ∨ s 37 = true ∨ s 34 = true := step181 s c68 c71 c124 c158 c12
  have c182 : s 49 = true ∨ s 52 = true ∨ s 58 ≠ true ∨ s 59 ≠ true := step182 s c95 c105 c102 c101 c179 c143 c38 c18 c100 c172 c180 c26 c167 c170 c10 c47 c69 c124 c137 c176 c7 c14 c87 c80 c135
  have c183 : s 16 = true ∨ s 52 = true ∨ s 58 ≠ true ∨ s 59 ≠ true := step183 s c182 c117 c95 c105 c102 c101 c179 c143 c38 c18 c111 c100 c167 c170 c10 c47 c69 c124 c137 c122 c7 c14 c87 c27 c176 c131 c80
  have c184 : s 52 = true ∨ s 58 ≠ true ∨ s 59 ≠ true := step184 s c95 c105 c102 c101 c179 c143 c38 c111 c182 c34 c117 c183 c28 c169 c122 c84 c69 c161 c51 c66 c127
  have c185 : s 58 ≠ true ∨ s 59 ≠ true := step185 s c105 c100 c95 c101 c102 c179 c143 c2 c184 c68 c71 c181 c124 c11
  have c186 : s 52 ≠ true ∨ s 0 = true ∨ s 37 = true ∨ s 34 = true := step186 s c68 c71 c181 c124 c11
  have c187 : s 16 ≠ true ∨ s 21 = true ∨ s 52 = true ∨ s 37 = true ∨ s 59 ≠ true := step187 s c111 c28 c172 c122 c117
  have c188 : s 43 ≠ true ∨ s 18 ≠ true ∨ s 16 = true ∨ s 59 ≠ true := step188 s c26 c117 c180
  have c189 : s 18 ≠ true ∨ s 20 ≠ true ∨ s 16 = true ∨ s 21 = true ∨ s 52 = true ∨ s 59 ≠ true := step189 s c14 c7 c111 c18 c38 c188 c122 c167 c170 c27 c47 c137 c176 c87 c80 c131
  have c190 : s 18 = true ∨ s 16 = true ∨ s 0 = true ∨ s 37 = true ∨ s 59 ≠ true := step190 s c179 c185 c105 c95 c149 c143 c20 c21 c82 c150 c156 c33
  have c191 : s 21 = true ∨ s 0 = true ∨ s 37 = true ∨ s 59 ≠ true := step191 s c100 c186 c187 c190 c38 c188 c189 c170 c124 c10
  have c192 : s 16 = true ∨ s 0 = true ∨ s 37 = true ∨ s 59 ≠ true := step192 s c191 c69 c100 c186 c190 c38 c188 c170
  have c193 : s 16 ≠ true ∨ s 55 = true ∨ s 59 ≠ true := step193 s c105 c95 c32 c37 c57 c169 c84 c161 c51 c66 c132
  have c194 : s 32 ≠ true ∨ s 20 = true ∨ s 37 = true ∨ s 34 = true := step194 s c10 c69 c124
  have c195 : s 9 ≠ true ∨ s 26 = true ∨ s 59 ≠ true := step195 s c185 c95 c29 c33 c156
  have c196 : s 35 ≠ true ∨ s 18 = true ∨ s 59 ≠ true := step196 s c108 c105 c16 c20 c125
  have c197 : s 37 = true ∨ s 59 ≠ true := step197 s c185 c116 c108 c105 c100 c95 c179 c193 c192 c2 c3 c143 c82 c161 c51 c66 c194 c162 c55 c195 c196 c163 c39 c127 c76 c164 c129 c45
  have c198 : s 13 = true ∨ s 10 = true ∨ s 21 ≠ true ∨ s 18 = true := step198 s c71 c69 c127 c64 c65 c154
  have c199 : s 10 = true ∨ s 21 ≠ true ∨ s 37 ≠ true := step199 s c77 c61 c198 c48 c49 c141
  have c200 : s 21 ≠ true ∨ s 59 ≠ true := step200 s c197 c81 c195 c61 c196 c185 c105 c95 c69 c199 c39 c40 c163 c161 c55 c51 c162
  have c201 : s 59 ≠ true := step201 s c95 c105 c108 c111 c116 c185 c197 c61 c67 c74 c81 c196 c195 c156 c129 c79 c88 c6 c200 c139 c4 c15 c131 c27 c120 c17 c24 c125
  have c202 : s 35 = true ∨ s 29 = true ∨ s 2 = true ∨ s 41 = true ∨ s 13 = true ∨ s 10 = true ∨ s 37 ≠ true := step202 s c67 c199 c139 c15 c4 c101 c81 c61 c156 c79 c88 c131 c135 c27 c106 c117 c120 c151 c17 c24 c57 c66 c125 c132 c103
  have c203 : s 39 ≠ true ∨ s 29 = true ∨ s 32 = true ∨ s 13 = true := step203 s c103 c104 c162
  have c204 : s 29 = true ∨ s 32 = true ∨ s 2 = true ∨ s 41 = true ∨ s 13 = true ∨ s 10 = true ∨ s 37 ≠ true := step204 s c199 c81 c61 c202 c16 c20 c203 c125 c106 c107 c121 c46 c161 c136 c66
  have c205 : s 28 ≠ true ∨ s 41 = true ∨ s 13 = true ∨ s 10 = true ∨ s 37 ≠ true := step205 s c201 c67 c61 c89 c90 c154 c152 c119
  have c206 : s 2 = true ∨ s 41 = true ∨ s 13 = true ∨ s 10 = true ∨ s 37 ≠ true := step206 s c205 c199 c67 c61 c139 c4 c15 c146 c79 c88 c92 c131 c135 c202 c27 c106 c16 c20 c120 c125 c57 c103 c154 c132 c64
  have c207 : s 55 ≠ true ∨ s 30 = true ∨ s 21 = true ∨ s 37 ≠ true := step207 s c201 c67 c61 c43 c54 c97 c103 c147 c1 c157 c158 c96
  have c208 : s 51 = true ∨ s 55 = true ∨ s 13 = true ∨ s 10 = true ∨ s 18 = true := step208 s c154 c132 c64
  have c209 : s 2 ≠ true ∨ s 13 = true ∨ s 10 = true ∨ s 37 ≠ true := step209 s c199 c101 c81 c74 c61 c6 c8 c9 c207 c208 c65 c136 c107 c115 c129 c29 c33 c156
  have c210 : s 51 ≠ true ∨ s 54 = true ∨ s 13 = true ∨ s 10 = true := step210 s c201 c58 c65 c136 c43 c54 c97 c147
  have c211 : s 13 = true ∨ s 10 = true ∨ s 37 ≠ true := step211 s c199 c67 c61 c209 c206 c109 c110 c210 c154 c208 c89 c207 c15 c146 c79 c88 c135
  have c212 : s 10 = true ∨ s 37 ≠ true := step212 s c77 c61 c211 c48 c49 c141
  have c213 : s 41 ≠ true ∨ s 13 ≠ true ∨ s 37 ≠ true := step213 s c51 c49 c212 c40 c37 c36 c81 c61 c25 c109 c126 c16 c20 c29 c145 c86 c91 c161 c104 c144 c42 c44 c155 c153 c63 c113 c159
  have c214 : s 13 ≠ true ∨ s 37 ≠ true := step214 s c201 c212 c40 c37 c36 c81 c67 c61 c49 c50 c51 c213 c152 c26 c117 c126 c120 c16 c20 c29 c1 c145 c86 c91 c161 c104 c144 c44 c155 c153 c63 c113 c159
  have c215 : s 35 ≠ true ∨ s 40 = true ∨ s 39 = true ∨ s 18 = true := step215 s c16 c20 c125
  have c216 : s 29 = true ∨ s 34 = true ∨ s 37 ≠ true := step216 s c214 c212 c40 c39 c36 c101 c81 c61 c203 c162 c55 c160 c19 c215 c156 c163 c33
  have c217 : s 29 ≠ true ∨ s 41 = true ∨ s 51 = true ∨ s 37 ≠ true := step217 s c201 c212 c37 c67 c61 c8 c91 c92 c145 c20 c126 c26 c152 c71 c90 c139 c146 c15
  have c218 : s 29 = true ∨ s 37 ≠ true := step218 s c214 c212 c40 c36 c162 c216 c98
  have c219 : s 51 = true ∨ s 37 ≠ true := step219 s c218 c91 c212 c37 c61 c217 c145 c25 c20 c126
  have c220 : s 37 ≠ true := step220 s c201 c67 c81 c214 c218 c8 c92 c93 c219 c58 c65 c119 c148 c16 c151 c25 c152 c71 c90 c139 c146 c15
  have c221 : s 20 = true ∨ s 41 = true ∨ s 43 = true ∨ s 29 ≠ true := step221 s c201 c92 c8 c152 c71 c90 c139 c146 c15
  have c222 : s 32 = true ∨ s 21 = true ∨ s 3 = true ∨ s 49 = true ∨ s 1 = true ∨ s 41 = true := step222 s c138 c121 c45
  have c223 : s 7 ≠ true ∨ s 52 = true ∨ s 1 = true ∨ s 0 = true ∨ s 41 = true ∨ s 18 = true ∨ s 35 = true ∨ s 19 = true ∨ s 16 = true ∨ s 13 = true ∨ s 57 = true := step223 s c21 c22 c150 c31 c34 c157 c12 c72 c222 c137 c36
  have c224 : s 52 = true ∨ s 1 = true ∨ s 57 = true ∨ s 0 = true ∨ s 41 = true ∨ s 18 = true ∨ s 35 = true ∨ s 19 = true ∨ s 16 = true ∨ s 13 = true := step224 s c220 c223 c149
  have c225 : s 41 = true ∨ s 51 ≠ true ∨ s 29 ≠ true := step225 s c93 c65 c49 c58 c148 c18 c16 c119 c57 c94 c221 c3 c5 c68 c224
  have c226 : s 51 ≠ true ∨ s 29 ≠ true := step226 s c220 c93 c119 c225 c75 c78 c130
  have c227 : s 18 = true ∨ s 41 ≠ true ∨ s 29 ≠ true := step227 s c220 c75 c93 c78 c130 c118 c25 c226 c91 c141 c37 c145 c126 c20
  have c228 : s 55 ≠ true ∨ s 50 = true := step228 s c201 c43 c54 c97 c142
  have c229 : s 46 ≠ true ∨ s 35 = true ∨ s 8 = true ∨ s 48 = true := step229 s c30 c113 c134
  have c230 : s 14 ≠ true ∨ s 7 = true ∨ s 45 = true ∨ s 1 = true ∨ s 36 = true ∨ s 5 = true ∨ s 21 = true := step230 s c52 c53 c138 c155 c13
  have c231 : s 11 ≠ true ∨ s 7 = true ∨ s 18 ≠ true := step231 s c60 c18 c42 c44 c155
  have c232 : s 7 = true ∨ s 47 = true ∨ s 45 = true ∨ s 9 = true ∨ s 1 = true ∨ s 18 ≠ true ∨ s 50 = true ∨ s 21 = true := step232 s c201 c60 c59 c18 c230 c163 c231 c99 c142
  have c233 : s 9 = true ∨ s 1 = true ∨ s 18 ≠ true ∨ s 50 = true ∨ s 49 = true ∨ s 21 = true ∨ s 8 = true ∨ s 48 = true := step233 s c220 c59 c229 c2 c134 c112 c114 c232 c23 c123 c14 c15 c158 c11 c124 c128 c99 c52 c163
  have c234 : s 4 ≠ true ∨ s 31 = true ∨ s 0 = true ∨ s 50 = true ∨ s 21 = true ∨ s 57 = true := step234 s c220 c14 c15 c158 c11 c124 c128 c41 c52 c133
  have c235 : s 31 = true ∨ s 46 = true ∨ s 18 ≠ true ∨ s 50 = true ∨ s 49 = true ∨ s 21 = true ∨ s 8 = true ∨ s 57 = true := step235 s c60 c18 c2 c234 c123 c23 c231 c155 c133 c53
  have c236 : s 41 ≠ true ∨ s 29 ≠ true := step236 s c220 c94 c93 c92 c25 c70 c75 c78 c109 c130 c118 c227 c59 c229 c235 c13 c35 c134 c233 c114 c5 c124 c128 c99 c52 c163
  have c237 : s 43 ≠ true ∨ s 9 = true ∨ s 21 = true ∨ s 14 = true ∨ s 50 = true ∨ s 18 ≠ true ∨ s 29 ≠ true := step237 s c220 c59 c94 c92 c26 c117 c229 c134 c233 c235 c114 c5 c13 c163 c124 c99
  have c238 : s 43 = true ∨ s 21 = true ∨ s 50 = true ∨ s 10 = true ∨ s 29 ≠ true := step238 s c236 c226 c221 c140 c68 c28 c122
  have c239 : s 21 = true ∨ s 14 = true ∨ s 50 = true ∨ s 18 ≠ true ∨ s 29 ≠ true := step239 s c59 c38 c94 c92 c238 c26 c117 c237 c229 c35 c235
  have c240 : s 7 ≠ true ∨ s 50 = true ∨ s 18 ≠ true ∨ s 29 ≠ true := step240 s c59 c38 c2 c236 c226 c92 c23 c24 c140 c26 c117 c229 c120 c123 c14
  have c241 : s 14 = true ∨ s 50 = true ∨ s 18 ≠ true ∨ s 29 ≠ true := step241 s c240 c231 c94 c239 c133 c73
  have c242 : s 50 = true ∨ s 18 ≠ true ∨ s 29 ≠ true := step242 s c220 c60 c38 c18 c236 c240 c241 c52 c53 c155 c13 c73 c128 c5 c238 c222 c117
  have c243 : s 18 ≠ true ∨ s 29 ≠ true := step243 s c236 c93 c92 c18 c38 c59 c242 c48 c64 c118 c221 c68 c137 c31 c87 c114 c159 c134 c27
  have c244 : s 10 = true ∨ s 50 ≠ true ∨ s 29 ≠ true := step244 s c220 c236 c118 c221 c68 c3 c64 c48 c243 c93 c198 c137 c122 c31 c87 c27 c28 c166 c159
  have c245 : s 50 ≠ true ∨ s 29 ≠ true := step245 s c243 c236 c226 c94 c91 c48 c64 c118 c221 c3 c5 c68 c244 c37 c145 c224 c20
  have c246 : s 10 ≠ true ∨ s 20 ≠ true ∨ s 29 ≠ true := step246 s c5 c3 c243 c236 c226 c94 c91 c36 c37 c145 c20 c21 c22 c150 c157 c34 c12 c72 c222
  have c247 : s 43 = true ∨ s 29 ≠ true := step247 s c245 c236 c226 c94 c221 c246 c140 c238 c17 c24 c56 c73 c155 c42 c53 c133
  have c248 : s 31 = true ∨ s 16 ≠ true ∨ s 29 ≠ true := step248 s c56 c24 c17 c245 c94 c155 c42 c53 c133
  have c249 : s 3 = true ∨ s 21 = true ∨ s 41 = true ∨ s 49 = true ∨ s 32 = true := step249 s c220 c222 c128 c5
  have c250 : s 31 ≠ true ∨ s 32 = true ∨ s 29 ≠ true := step250 s c247 c117 c236 c13 c73 c249
  have c251 : s 16 = true ∨ s 29 ≠ true := step251 s c247 c26 c243 c226 c91 c145 c126 c20
  have c252 : s 29 ≠ true := step252 s c226 c243 c245 c251 c37 c248 c154 c250 c47
  have c253 : s 32 ≠ true ∨ s 41 = true ∨ s 18 = true ∨ s 21 = true ∨ s 16 ≠ true := step253 s c220 c57 c37 c28 c47 c154 c208 c118 c97 c122 c194 c68
  have c254 : s 41 = true ∨ s 18 = true ∨ s 31 ≠ true ∨ s 16 ≠ true := step254 s c220 c73 c13 c28 c253 c128 c249 c68 c117 c122
  have c255 : s 18 = true ∨ s 31 ≠ true ∨ s 16 ≠ true := step255 s c220 c73 c13 c57 c37 c254 c75 c78 c109 c141 c48 c64 c118 c208 c130 c97 c80 c124 c7 c14 c68 c135 c137 c87
  have c256 : s 53 ≠ true ∨ s 49 = true ∨ s 31 ≠ true ∨ s 16 ≠ true := step256 s c220 c255 c59 c2 c73 c13 c57 c37 c32 c28 c51 c66 c132 c97 c124 c186 c173 c137 c134 c114
  have c257 : s 41 ≠ true ∨ s 31 ≠ true ∨ s 16 ≠ true := step257 s c252 c220 c255 c62 c59 c73 c13 c32 c28 c75 c78 c109 c256 c130 c118 c228 c161 c84 c134 c233 c114 c5 c124 c128 c99 c52 c163
  have c258 : s 50 = true ∨ s 49 = true ∨ s 31 ≠ true ∨ s 16 ≠ true := step258 s c201 c252 c13 c257 c73 c249 c52 c256 c255 c62 c59 c44 c32 c28 c228 c142 c161 c99 c84 c163 c134 c114
  have c259 : s 49 = true ∨ s 31 ≠ true ∨ s 16 ≠ true := step259 s c220 c257 c255 c2 c73 c13 c57 c37 c28 c249 c47 c258 c64 c118 c132 c122 c97 c186
  have c260 : s 31 ≠ true ∨ s 16 ≠ true := step260 s c220 c57 c37 c32 c28 c13 c73 c255 c2 c59 c257 c259 c117 c122 c50 c68 c186 c128 c97 c99 c52 c132 c163 c66 c114 c151 c134 c84
  have c261 : s 34 ≠ true ∨ s 16 ≠ true := step261 s c252 c17 c24 c56 c260 c155 c53 c42 c57 c37 c97 c98 c144 c133 c47 c64 c132
  have c262 : s 16 ≠ true := step262 s c201 c220 c17 c24 c28 c32 c37 c56 c260 c155 c1 c42 c53 c261 c142 c186 c48 c64 c137 c127 c69 c118 c114 c122 c153 c109
  have c263 : s 8 ≠ true ∨ s 4 = true ∨ s 2 = true ∨ s 5 = true ∨ s 27 = true ∨ s 52 = true ∨ s 13 = true ∨ s 10 = true := step263 s c262 c27 c176 c131 c80
  have c264 : s 55 ≠ true ∨ s 34 = true ∨ s 31 = true := step264 s c201 c220 c262 c40 c43 c54 c228 c147 c48 c64 c118 c1 c186 c137 c127 c31 c87 c114 c69 c194 c166 c7 c14 c263 c153 c122 c109
  have c265 : s 21 = true ∨ s 8 = true ∨ s 42 = true ∨ s 41 = true ∨ s 40 = true ∨ s 43 = true ∨ s 13 = true ∨ s 55 = true ∨ s 34 = true := step265 s c220 c252 c122 c68 c76 c186 c194 c2 c4 c203 c143 c215 c139 c82 c102 c6 c156 c129 c33
  have c266 : s 21 ≠ true ∨ s 43 = true ∨ s 10 = true := step266 s c262 c69 c71 c170
  have c267 : s 52 = true ∨ s 8 ≠ true ∨ s 41 = true ∨ s 43 = true ∨ s 19 = true ∨ s 10 = true ∨ s 13 = true := step267 s c201 c220 c262 c137 c152 c31 c87 c3 c7 c14 c166 c263
  have c268 : s 50 ≠ true ∨ s 10 = true ∨ s 13 = true ∨ s 55 = true ∨ s 34 = true := step268 s c220 c252 c64 c118 c136 c107 c110 c115 c266 c265 c267 c68 c76 c186 c194 c2 c4 c203 c143 c215 c139 c82 c102 c6 c156 c129 c33
  have c269 : s 43 = true ∨ s 10 = true ∨ s 13 = true ∨ s 55 = true ∨ s 34 = true := step269 s c262 c220 c252 c268 c140 c167 c266 c210 c107 c110 c115 c265 c267 c68 c76 c186 c194 c2 c4 c203 c143 c215 c139 c82 c102 c6 c156 c129 c33
  have c270 : s 21 = true ∨ s 46 = true ∨ s 18 ≠ true ∨ s 49 = true ∨ s 8 = true ∨ s 50 = true ∨ s 34 = true ∨ s 31 = true := step270 s c201 c2 c235 c55 c96 c142 c231 c23 c123 c14 c15 c158
  have c271 : s 10 = true ∨ s 13 = true ∨ s 34 = true ∨ s 31 = true := step271 s c252 c262 c264 c268 c269 c26 c117 c119 c208 c132 c2 c59 c62 c66 c161 c84 c229 c270 c69 c70 c162 c120 c55 c14 c160 c123 c19
  have c272 : s 13 = true ∨ s 34 = true ∨ s 31 = true := step272 s c252 c264 c271 c36 c38 c39 c203 c162 c143 c55 c82 c102 c160 c19 c215 c163 c156 c33
  have c273 : s 39 = true ∨ s 18 = true ∨ s 53 = true ∨ s 55 = true := step273 s c252 c161 c143 c82
  have c274 : s 8 ≠ true ∨ s 20 = true ∨ s 52 = true := step274 s c201 c25 c26 c152
  have c275 : s 18 = true ∨ s 34 = true ∨ s 31 = true := step275 s c220 c262 c201 c272 c51 c50 c49 c264 c273 c22 c149 c145 c1 c3 c86 c274 c126 c16 c29 c155 c63 c159 c113 c153 c109 c117 c152
  have c276 : s 34 = true ∨ s 31 = true := step276 s c262 c252 c264 c272 c47 c48 c49 c51 c275 c2 c18 c38 c59 c60 c62 c140 c161 c26 c117 c84 c229 c270 c70 c120 c14 c123 c19 c23 c160 c155 c53
  have c277 : s 8 = true ∨ s 0 = true ∨ s 31 = true := step277 s c252 c262 c276 c97 c41 c98 c144 c36 c47 c52 c133 c64 c136 c110 c118 c69 c122 c120 c68
  have c278 : s 18 ≠ true ∨ s 31 = true := step278 s c252 c276 c97 c41 c98 c144 c36 c47 c52 c133 c64 c136 c115 c110 c107 c132 c58 c118 c69 c99 c2 c18 c59 c148 c80 c85 c156 c33 c88 c277 c27 c267 c68 c76 c129 c6 c139 c131 c15
  have c279 : s 7 ≠ true ∨ s 31 = true := step279 s c262 c252 c278 c276 c99 c97 c20 c21 c22 c150 c143 c33 c82 c156
  have c280 : s 26 ≠ true ∨ s 31 = true := step280 s c252 c278 c276 c97 c82 c83 c143
  have c281 : s 31 = true := step281 s c220 c262 c201 c252 c276 c41 c97 c98 c99 c144 c36 c47 c52 c69 c133 c64 c118 c136 c107 c110 c115 c278 c279 c149 c4 c280 c3 c139 c152 c6 c76 c129 c29 c33 c156
  have c282 : s 3 ≠ true := step282 s c281 c13
  have c283 : s 9 ≠ true := step283 s c281 c35
  have c284 : s 11 ≠ true := step284 s c281 c44
  have c285 : s 21 ≠ true := step285 s c281 c73
  have c286 : s 36 ≠ true ∨ s 18 = true := step286 s c262 c220 c282 c201 c285 c283 c21 c63 c149 c3 c4 c124 c128 c97 c36 c47 c208 c136 c119 c107 c110 c115 c152 c139 c76 c6 c129
  have c287 : s 7 = true ∨ s 18 = true := step287 s c283 c285 c201 c282 c220 c262 c149 c3 c4 c124 c128 c97 c36 c47 c208 c119 c210 c107 c110 c115 c152 c139 c76 c6 c129
  have c288 : s 36 = true ∨ s 18 = true := step288 s c262 c283 c150 c20 c287
  have c289 : s 18 = true := step289 s c286 c288
  have c290 : s 0 ≠ true := step290 s c289 c2
  have c291 : s 5 ≠ true := step291 s c289 c18
  have c292 : s 10 ≠ true := step292 s c289 c38
  have c293 : s 35 ≠ true := step293 s c289 c59
  have c294 : s 36 ≠ true := step294 s c289 c60
  have c295 : s 39 ≠ true := step295 s c289 c62
  have c296 : s 20 = true ∨ s 43 = true ∨ s 55 = true := step296 s c220 c282 c292 c293 c201 c290 c262 c291 c283 c285 c167 c124 c128 c99 c47 c52 c136 c132 c163 c107 c110 c115 c58 c87 c152 c120 c148 c76 c27 c80 c129 c6 c139 c131 c15
  have c297 : s 41 = true ∨ s 13 = true ∨ s 19 = true ∨ s 43 = true ∨ s 52 = true := step297 s c285 c292 c267 c122
  have c298 : s 43 = true ∨ s 55 = true := step298 s c262 c292 c167 c296 c68 c170 c47 c136 c110 c297
  have c299 : s 20 ≠ true ∨ s 43 ≠ true := step299 s c283 c285 c289 c118 c117 c26 c5 c173 c233
  have c300 : s 55 = true := step300 s c220 c285 c282 c292 c295 c252 c283 c293 c298 c26 c119 c299 c124 c128 c99 c47 c52 c132 c163 c66 c114 c161 c134 c84
  have c301 : s 12 ≠ true := step301 s c300 c46
  have c302 : s 14 ≠ true := step302 s c300 c54
  have c303 : s 34 ≠ true := step303 s c300 c97
  have c304 : s 50 = true := step304 s c300 c228
  have c305 : s 20 = true := step305 s c303 c220 c285 c282 c124
  have c306 : s 17 = true := step306 s c303 c302 c284 c201 c147
  have c307 : s 52 ≠ true := step307 s c303 c220 c290 c186
  have c308 : s 13 ≠ true := step308 s c304 c48
  have c309 : s 19 ≠ true := step309 s c304 c64
  have c310 : s 28 ≠ true := step310 s c304 c89
  have c311 : s 43 ≠ true := step311 s c304 c118
  have c312 : s 1 ≠ true := step312 s c305 c5
  have c313 : s 2 ≠ true := step313 s c305 c7
  have c314 : s 4 ≠ true := step314 s c305 c14
  have c315 : s 51 ≠ true := step315 s c306 c58
  have c316 : s 32 = true := step316 s c307 c292 c262 c311 c170
  have c317 : s 47 = true := step317 s c307 c308 c292 c309 c137
  have c318 : s 41 = true := step318 s c308 c309 c311 c307 c297
  have c319 : s 27 ≠ true := step319 s c317 c87
  have c320 : s 42 ≠ true := step320 s c317 c114
  have c321 : s 8 ≠ true := step321 s c318 c25
  have c322 : s 23 ≠ true := step322 s c318 c75
  have c323 : s 24 ≠ true := step323 s c318 c78
  have c324 : s 49 ≠ true := step324 s c318 c109
  have c325 : s 54 ≠ true := step325 s c318 c110
  have c326 : s 25 = true := step326 s c319 c324 c314 c313 c135
  have c327 : s 48 = true := step327 s c320 c321 c293 c283 c134
  have c328 : s 53 = true := step328 s c323 c220 c322 c311 c130
  have c329 : False := step329 s c327 c324 c305 c173
  exact c329

variable {V : Type*} (G : SimpleGraph V)

lemma five_has_apex (h : NoFive G) (a b c d e : Option V)
    (hab : (coneGraph G).Adj a b) (hbc : (coneGraph G).Adj b c)
    (hcd : (coneGraph G).Adj c d) (hde : (coneGraph G).Adj d e)
    (hea : (coneGraph G).Adj e a) :
    a = none ∨ b = none ∨ c = none ∨ d = none ∨ e = none := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;>
    simp_all only [coneGraph, reduceCtorEq, or_true, or_false]
  exact h _ _ _ _ _ hab hbc hcd hde hea

/-- A graph with no closed five-step walk cannot receive the second arc
four-clique after adjoining one universal vertex. -/
theorem no_hom (h : NoFive G) (f : A2 →g coneGraph G) : False := by
  classical
  let s : Fin 60 → Bool := fun i => decide (f (point i) = none)
  apply no_selector s
  · intro i hi
    have hx : f (point (excluded i).1) = none := of_decide_eq_true hi.1
    have hy : f (point (excluded i).2) = none := of_decide_eq_true hi.2
    have ha := f.map_adj (excluded_adj i)
    rw [hx,hy] at ha
    exact ha
  · intro i
    have ha := five_has_apex G h
      (f (point (cycles i 0))) (f (point (cycles i 1)))
      (f (point (cycles i 2))) (f (point (cycles i 3))) (f (point (cycles i 4)))
      (f.map_adj (cycles_adj i 0)) (f.map_adj (cycles_adj i 1))
      (f.map_adj (cycles_adj i 2)) (f.map_adj (cycles_adj i 3)) (f.map_adj (cycles_adj i 4))
    simpa only [s,decide_eq_true_eq] using ha

theorem cliqueFree_of_noFive (h : NoFive G) :
    (right (right (coneGraph G))).CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  exact no_hom G h (fromRight (fromRight e.toHom))

theorem cliqueFree_iff_noFive :
    (right (right (coneGraph G))).CliqueFree 4 ↔ NoFive G :=
  ⟨Erdos595SecondConeClique.noFive_of_cliqueFree G,cliqueFree_of_noFive G⟩

#print axioms no_selector
#print axioms no_hom
#print axioms cliqueFree_iff_noFive
end Erdos595SecondConeCriterion
