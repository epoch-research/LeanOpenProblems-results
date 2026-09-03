import Submission.ArcAdjoint

/-!
A finite structural property of the second arc graph of K4: a map into a
five-state template cannot use either of the two private-leaf states.
The LRAT search is reconstructed with ordinary propositional proofs; there
is no SAT, native-evaluation, or compiler-trust axiom in the result.
-/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open SimpleGraph Set
namespace Erdos595PrivateTriangleCertificate
open Erdos595ArcAdjoint
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

private lemma point_surjective : Function.Surjective point := by decide +kernel

/-- 0 is the attachment vertex, 1 and 2 its private triangle vertices,
3 its other neighbors (independent), and 4 the remaining vertices.
State 4 deliberately permits loops, so this is a relation, not a simple graph. -/
def Allowed (a b : Fin 5) : Prop :=
  (a = 0 ∧ (b = 1 ∨ b = 2 ∨ b = 3)) ∨
  (a = 1 ∧ (b = 0 ∨ b = 2)) ∨
  (a = 2 ∧ (b = 0 ∨ b = 1)) ∨
  (a = 3 ∧ (b = 0 ∨ b = 4)) ∨
  (a = 4 ∧ (b = 3 ∨ b = 4))
instance (a b : Fin 5) : Decidable (Allowed a b) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _))

private lemma five_cases : ∀ a : Fin 5, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by decide +kernel
private lemma row0 (b : Fin 5) : Allowed 0 b ↔ b = 1 ∨ b = 2 ∨ b = 3 := by
  fin_cases b <;> decide +kernel
private lemma row1 (b : Fin 5) : Allowed 1 b ↔ b = 0 ∨ b = 2 := by
  fin_cases b <;> decide +kernel
private lemma row2 (b : Fin 5) : Allowed 2 b ↔ b = 0 ∨ b = 1 := by
  fin_cases b <;> decide +kernel
private lemma row3 (b : Fin 5) : Allowed 3 b ↔ b = 0 ∨ b = 4 := by
  fin_cases b <;> decide +kernel
private lemma row4 (b : Fin 5) : Allowed 4 b ↔ b = 3 ∨ b = 4 := by
  fin_cases b <;> decide +kernel


private theorem step3362 (s : Fin 60 → Fin 5)
    (c660 : s 59 ≠ 3 ∨ s 59 ≠ 4)
    (c659 : s 59 ≠ 2 ∨ s 59 ≠ 4)
    (c657 : s 59 ≠ 1 ∨ s 59 ≠ 4)
    (c2006 : s 29 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c654 : s 59 ≠ 0 ∨ s 59 ≠ 4)
    (c2008 : s 29 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c2412 : s 38 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2)
    (c1331 : s 14 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c1333 : s 14 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c3307 : s 58 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c1332 : s 14 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c3308 : s 58 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c649 : s 58 ≠ 3 ∨ s 58 ≠ 4)
    (c2371 : s 38 ≠ 0 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 58 = 3)
    (c1928 : s 28 ≠ 2 ∨ s 38 = 0 ∨ s 38 = 1)
    (c1883 : s 27 ≠ 2 ∨ s 38 = 0 ∨ s 38 = 1)
    (c2007 : s 29 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c2413 : s 38 ≠ 2 ∨ s 29 = 0 ∨ s 29 = 1)
    (c1927 : s 28 ≠ 1 ∨ s 38 = 0 ∨ s 38 = 2)
    (c1882 : s 27 ≠ 1 ∨ s 38 = 0 ∨ s 38 = 2)
    (c1813 : s 25 ≠ 2 ∨ s 38 = 0 ∨ s 38 = 1)
    (c1812 : s 25 ≠ 1 ∨ s 38 = 0 ∨ s 38 = 2)
    (c2281 : s 36 ≠ 0 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 58 = 3)
    (c643 : s 58 ≠ 0 ∨ s 58 ≠ 4)
    (c2283 : s 36 ≠ 2 ∨ s 58 = 0 ∨ s 58 = 1)
    (c1522 : s 19 ≠ 1 ∨ s 36 = 0 ∨ s 36 = 2)
    (c1387 : s 16 ≠ 1 ∨ s 36 = 0 ∨ s 36 = 2)
    (c1367 : s 15 ≠ 1 ∨ s 36 = 0 ∨ s 36 = 2)
    (c2282 : s 36 ≠ 1 ∨ s 58 = 0 ∨ s 58 = 2)
    (c1523 : s 19 ≠ 2 ∨ s 36 = 0 ∨ s 36 = 1)
    (c1388 : s 16 ≠ 2 ∨ s 36 = 0 ∨ s 36 = 1)
    (c1368 : s 15 ≠ 2 ∨ s 36 = 0 ∨ s 36 = 1)
    (c2328 : s 37 ≠ 2 ∨ s 58 = 0 ∨ s 58 = 1)
    (c2238 : s 35 ≠ 2 ∨ s 58 = 0 ∨ s 58 = 1)
    (c2327 : s 37 ≠ 1 ∨ s 58 = 0 ∨ s 58 = 2)
    (c2237 : s 35 ≠ 1 ∨ s 58 = 0 ∨ s 58 = 2)
    (c2636 : s 43 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2638 : s 43 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c3002 : s 52 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c2591 : s 42 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2593 : s 42 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c2762 : s 46 ≠ 1 ∨ s 42 = 0 ∨ s 42 = 2)
    (c2717 : s 45 ≠ 1 ∨ s 42 = 0 ∨ s 42 = 2)
    (c2546 : s 41 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2548 : s 41 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c1757 : s 24 ≠ 1 ∨ s 41 = 0 ∨ s 41 = 2)
    (c1597 : s 20 ≠ 1 ∨ s 41 = 0 ∨ s 41 = 2)
    (c2501 : s 40 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2503 : s 40 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c892 : s 5 ≠ 1 ∨ s 40 = 0 ∨ s 40 = 2)
    (c1072 : s 9 ≠ 1 ∨ s 40 = 0 ∨ s 40 = 2)
    (c2456 : s 39 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2458 : s 39 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c1857 : s 26 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    (c1682 : s 22 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    (c997 : s 7 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    (c1502 : s 18 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    (c2231 : s 34 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2233 : s 34 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c807 : s 3 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c1622 : s 21 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c1167 : s 11 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c942 : s 6 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c787 : s 2 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2)
    (c2862 : s 48 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2)
    (c2897 : s 49 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c1042 : s 8 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c3107 : s 54 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c3047 : s 53 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c2957 : s 51 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c1727 : s 23 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c2637 : s 43 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c3003 : s 52 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c2502 : s 40 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c893 : s 5 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c1073 : s 9 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c788 : s 2 ≠ 2 ∨ s 29 = 0 ∨ s 29 = 1)
    (c2133 : s 32 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c1463 : s 17 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c3252 : s 57 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3048 : s 53 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c2958 : s 51 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c2938 : s 50 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c2592 : s 42 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c2813 : s 47 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1)
    (c2763 : s 46 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1)
    (c2833 : s 48 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1)
    (c2718 : s 45 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1)
    (c2547 : s 41 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c1758 : s 24 ≠ 2 ∨ s 41 = 0 ∨ s 41 = 1)
    (c1598 : s 20 ≠ 2 ∨ s 41 = 0 ∨ s 41 = 1)
    (c2873 : s 49 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c3093 : s 54 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c1713 : s 23 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c1028 : s 8 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c2457 : s 39 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c3143 : s 55 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c1858 : s 26 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c1683 : s 22 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c998 : s 7 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c3188 : s 56 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c1503 : s 18 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c2232 : s 34 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c808 : s 3 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c1623 : s 21 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c1168 : s 11 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c943 : s 6 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c3197 : s 56 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3167 : s 55 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c2932 : s 50 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c2807 : s 47 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c2132 : s 32 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c1462 : s 17 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3253 : s 57 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c2683 : s 44 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c2682 : s 44 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c632 : s 57 ≠ 0 ∨ s 57 ≠ 4)
    (c638 : s 57 ≠ 3 ∨ s 57 ≠ 4)
    (c2097 : s 31 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2052 : s 30 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2187 : s 33 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2053 : s 30 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2098 : s 31 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2188 : s 33 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2051 : s 30 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c2141 : s 32 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c703 : s 0 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1)
    (c747 : s 1 ≠ 1 ∨ s 30 = 0 ∨ s 30 = 2)
    (c882 : s 4 ≠ 1 ∨ s 30 = 0 ∨ s 30 = 2)
    (c702 : s 0 ≠ 1 ∨ s 30 = 0 ∨ s 30 = 2)
    (c748 : s 1 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1)
    (c883 : s 4 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1)
    (c1112 : s 10 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1202 : s 12 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1247 : s 13 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1113 : s 10 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1203 : s 12 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1248 : s 13 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c3361 : s 0 = 1 ∨ s 0 = 2 ∨ s 1 = 1 ∨ s 1 = 2 ∨ s 2 = 1 ∨ s 2 = 2 ∨ s 3 = 1 ∨ s 3 = 2 ∨ s 4 = 1 ∨ s 4 = 2 ∨ s 5 = 1 ∨ s 5 = 2 ∨ s 6 = 1 ∨ s 6 = 2 ∨ s 7 = 1 ∨ s 7 = 2 ∨ s 8 = 1 ∨ s 8 = 2 ∨ s 9 = 1 ∨ s 9 = 2 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 11 = 1 ∨ s 11 = 2 ∨ s 12 = 1 ∨ s 12 = 2 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 15 = 1 ∨ s 15 = 2 ∨ s 16 = 1 ∨ s 16 = 2 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 18 = 1 ∨ s 18 = 2 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 20 = 1 ∨ s 20 = 2 ∨ s 21 = 1 ∨ s 21 = 2 ∨ s 22 = 1 ∨ s 22 = 2 ∨ s 23 = 1 ∨ s 23 = 2 ∨ s 24 = 1 ∨ s 24 = 2 ∨ s 25 = 1 ∨ s 25 = 2 ∨ s 26 = 1 ∨ s 26 = 2 ∨ s 27 = 1 ∨ s 27 = 2 ∨ s 28 = 1 ∨ s 28 = 2 ∨ s 29 = 1 ∨ s 29 = 2 ∨ s 30 = 1 ∨ s 30 = 2 ∨ s 31 = 1 ∨ s 31 = 2 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 33 = 1 ∨ s 33 = 2 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 35 = 1 ∨ s 35 = 2 ∨ s 36 = 1 ∨ s 36 = 2 ∨ s 37 = 1 ∨ s 37 = 2 ∨ s 38 = 1 ∨ s 38 = 2 ∨ s 39 = 1 ∨ s 39 = 2 ∨ s 40 = 1 ∨ s 40 = 2 ∨ s 41 = 1 ∨ s 41 = 2 ∨ s 42 = 1 ∨ s 42 = 2 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 44 = 1 ∨ s 44 = 2 ∨ s 45 = 1 ∨ s 45 = 2 ∨ s 46 = 1 ∨ s 46 = 2 ∨ s 47 = 1 ∨ s 47 = 2 ∨ s 48 = 1 ∨ s 48 = 2 ∨ s 49 = 1 ∨ s 49 = 2 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 52 = 1 ∨ s 52 = 2 ∨ s 53 = 1 ∨ s 53 = 2 ∨ s 54 = 1 ∨ s 54 = 2 ∨ s 55 = 1 ∨ s 55 = 2 ∨ s 56 = 1 ∨ s 56 = 2 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 59 = 1 ∨ s 59 = 2)
    : s 57 ≠ 4 ∨ s 58 ≠ 4 ∨ s 59 ≠ 4 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 59 ≠ 3 := (Or.elim c660 (fun h => h) (fun h => (False.elim (h a2))))
  have u1 : s 59 ≠ 2 := (Or.elim c659 (fun h => h) (fun h => (False.elim (h a2))))
  have u2 : s 59 ≠ 1 := (Or.elim c657 (fun h => h) (fun h => (False.elim (h a2))))
  have u3 : s 29 ≠ 0 := (Or.elim c2006 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u4 : s 59 ≠ 0 := (Or.elim c654 (fun h => h) (fun h => (False.elim (h a2))))
  have u5 : s 29 ≠ 2 := (Or.elim c2008 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u6 : s 38 ≠ 1 := (Or.elim c2412 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u7 : s 14 ≠ 0 := (Or.elim c1331 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u8 : s 14 ≠ 2 := (Or.elim c1333 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u9 : s 58 ≠ 1 := (Or.elim c3307 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u8 h))))))
  have u10 : s 14 ≠ 1 := (Or.elim c1332 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u11 : s 58 ≠ 2 := (Or.elim c3308 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u10 h))))))
  have u12 : s 58 ≠ 3 := (Or.elim c649 (fun h => h) (fun h => (False.elim (h a1))))
  have u13 : s 38 ≠ 0 := (Or.elim c2371 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u12 h))))))))
  have u14 : s 28 ≠ 2 := (Or.elim c1928 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u6 h))))))
  have u15 : s 27 ≠ 2 := (Or.elim c1883 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u6 h))))))
  have u16 : s 29 ≠ 1 := (Or.elim c2007 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u17 : s 38 ≠ 2 := (Or.elim c2413 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u16 h))))))
  have u18 : s 28 ≠ 1 := (Or.elim c1927 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u17 h))))))
  have u19 : s 27 ≠ 1 := (Or.elim c1882 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u17 h))))))
  have u20 : s 25 ≠ 2 := (Or.elim c1813 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u6 h))))))
  have u21 : s 25 ≠ 1 := (Or.elim c1812 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u17 h))))))
  have u22 : s 36 ≠ 0 := (Or.elim c2281 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u12 h))))))))
  have u23 : s 58 ≠ 0 := (Or.elim c643 (fun h => h) (fun h => (False.elim (h a1))))
  have u24 : s 36 ≠ 2 := (Or.elim c2283 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (False.elim (u9 h))))))
  have u25 : s 19 ≠ 1 := (Or.elim c1522 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u24 h))))))
  have u26 : s 16 ≠ 1 := (Or.elim c1387 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u24 h))))))
  have u27 : s 15 ≠ 1 := (Or.elim c1367 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u24 h))))))
  have u28 : s 36 ≠ 1 := (Or.elim c2282 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (False.elim (u11 h))))))
  have u29 : s 19 ≠ 2 := (Or.elim c1523 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u28 h))))))
  have u30 : s 16 ≠ 2 := (Or.elim c1388 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u28 h))))))
  have u31 : s 15 ≠ 2 := (Or.elim c1368 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u28 h))))))
  have u32 : s 37 ≠ 2 := (Or.elim c2328 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (False.elim (u9 h))))))
  have u33 : s 35 ≠ 2 := (Or.elim c2238 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (False.elim (u9 h))))))
  have u34 : s 37 ≠ 1 := (Or.elim c2327 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (False.elim (u11 h))))))
  have u35 : s 35 ≠ 1 := (Or.elim c2237 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (False.elim (u11 h))))))
  have u36 : s 43 ≠ 0 := (Or.elim c2636 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u37 : s 43 ≠ 2 := (Or.elim c2638 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u38 : s 52 ≠ 1 := (Or.elim c3002 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u37 h))))))
  have u39 : s 42 ≠ 0 := (Or.elim c2591 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u40 : s 42 ≠ 2 := (Or.elim c2593 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u41 : s 46 ≠ 1 := (Or.elim c2762 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (False.elim (u40 h))))))
  have u42 : s 45 ≠ 1 := (Or.elim c2717 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (False.elim (u40 h))))))
  have u43 : s 41 ≠ 0 := (Or.elim c2546 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u44 : s 41 ≠ 2 := (Or.elim c2548 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u45 : s 24 ≠ 1 := (Or.elim c1757 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u43 h))) (fun h => (False.elim (u44 h))))))
  have u46 : s 20 ≠ 1 := (Or.elim c1597 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u43 h))) (fun h => (False.elim (u44 h))))))
  have u47 : s 40 ≠ 0 := (Or.elim c2501 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u48 : s 40 ≠ 2 := (Or.elim c2503 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u49 : s 5 ≠ 1 := (Or.elim c892 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u47 h))) (fun h => (False.elim (u48 h))))))
  have u50 : s 9 ≠ 1 := (Or.elim c1072 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u47 h))) (fun h => (False.elim (u48 h))))))
  have u51 : s 39 ≠ 0 := (Or.elim c2456 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u52 : s 39 ≠ 2 := (Or.elim c2458 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u53 : s 26 ≠ 1 := (Or.elim c1857 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u52 h))))))
  have u54 : s 22 ≠ 1 := (Or.elim c1682 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u52 h))))))
  have u55 : s 7 ≠ 1 := (Or.elim c997 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u52 h))))))
  have u56 : s 18 ≠ 1 := (Or.elim c1502 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u52 h))))))
  have u57 : s 34 ≠ 0 := (Or.elim c2231 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u58 : s 34 ≠ 2 := (Or.elim c2233 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u59 : s 3 ≠ 1 := (Or.elim c807 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u57 h))) (fun h => (False.elim (u58 h))))))
  have u60 : s 21 ≠ 1 := (Or.elim c1622 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u57 h))) (fun h => (False.elim (u58 h))))))
  have u61 : s 11 ≠ 1 := (Or.elim c1167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u57 h))) (fun h => (False.elim (u58 h))))))
  have u62 : s 6 ≠ 1 := (Or.elim c942 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u57 h))) (fun h => (False.elim (u58 h))))))
  have u63 : s 2 ≠ 1 := (Or.elim c787 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u64 : s 48 ≠ 1 := (Or.elim c2862 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u65 : s 49 ≠ 1 := (Or.elim c2897 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u37 h))))))
  have u66 : s 8 ≠ 1 := (Or.elim c1042 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u37 h))))))
  have u67 : s 54 ≠ 1 := (Or.elim c3107 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u37 h))))))
  have u68 : s 53 ≠ 1 := (Or.elim c3047 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u37 h))))))
  have u69 : s 51 ≠ 1 := (Or.elim c2957 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u37 h))))))
  have u70 : s 23 ≠ 1 := (Or.elim c1727 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u37 h))))))
  have u71 : s 43 ≠ 1 := (Or.elim c2637 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u72 : s 52 ≠ 2 := (Or.elim c3003 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u71 h))))))
  have u73 : s 40 ≠ 1 := (Or.elim c2502 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u74 : s 5 ≠ 2 := (Or.elim c893 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u47 h))) (fun h => (False.elim (u73 h))))))
  have u75 : s 9 ≠ 2 := (Or.elim c1073 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u47 h))) (fun h => (False.elim (u73 h))))))
  have u76 : s 2 ≠ 2 := (Or.elim c788 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u16 h))))))
  have u77 : s 32 ≠ 2 := (Or.elim c2133 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u10 h))))))
  have u78 : s 17 ≠ 2 := (Or.elim c1463 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u10 h))))))
  have u79 : s 57 ≠ 1 := (Or.elim c3252 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u8 h))))))
  have u80 : s 53 ≠ 2 := (Or.elim c3048 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u71 h))))))
  have u81 : s 51 ≠ 2 := (Or.elim c2958 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u71 h))))))
  have u82 : s 50 ≠ 2 := (Or.elim c2938 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u71 h))))))
  have u83 : s 42 ≠ 1 := (Or.elim c2592 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u84 : s 47 ≠ 2 := (Or.elim c2813 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (False.elim (u83 h))))))
  have u85 : s 46 ≠ 2 := (Or.elim c2763 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (False.elim (u83 h))))))
  have u86 : s 48 ≠ 2 := (Or.elim c2833 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (False.elim (u83 h))))))
  have u87 : s 45 ≠ 2 := (Or.elim c2718 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (False.elim (u83 h))))))
  have u88 : s 41 ≠ 1 := (Or.elim c2547 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u89 : s 24 ≠ 2 := (Or.elim c1758 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u43 h))) (fun h => (False.elim (u88 h))))))
  have u90 : s 20 ≠ 2 := (Or.elim c1598 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u43 h))) (fun h => (False.elim (u88 h))))))
  have u91 : s 49 ≠ 2 := (Or.elim c2873 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u47 h))) (fun h => (False.elim (u73 h))))))
  have u92 : s 54 ≠ 2 := (Or.elim c3093 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u47 h))) (fun h => (False.elim (u73 h))))))
  have u93 : s 23 ≠ 2 := (Or.elim c1713 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u47 h))) (fun h => (False.elim (u73 h))))))
  have u94 : s 8 ≠ 2 := (Or.elim c1028 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u47 h))) (fun h => (False.elim (u73 h))))))
  have u95 : s 39 ≠ 1 := (Or.elim c2457 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u96 : s 55 ≠ 2 := (Or.elim c3143 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u95 h))))))
  have u97 : s 26 ≠ 2 := (Or.elim c1858 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u95 h))))))
  have u98 : s 22 ≠ 2 := (Or.elim c1683 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u95 h))))))
  have u99 : s 7 ≠ 2 := (Or.elim c998 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u95 h))))))
  have u100 : s 56 ≠ 2 := (Or.elim c3188 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u95 h))))))
  have u101 : s 18 ≠ 2 := (Or.elim c1503 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u95 h))))))
  have u102 : s 34 ≠ 1 := (Or.elim c2232 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u103 : s 3 ≠ 2 := (Or.elim c808 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u57 h))) (fun h => (False.elim (u102 h))))))
  have u104 : s 21 ≠ 2 := (Or.elim c1623 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u57 h))) (fun h => (False.elim (u102 h))))))
  have u105 : s 11 ≠ 2 := (Or.elim c1168 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u57 h))) (fun h => (False.elim (u102 h))))))
  have u106 : s 6 ≠ 2 := (Or.elim c943 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u57 h))) (fun h => (False.elim (u102 h))))))
  have u107 : s 56 ≠ 1 := (Or.elim c3197 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u8 h))))))
  have u108 : s 55 ≠ 1 := (Or.elim c3167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u8 h))))))
  have u109 : s 50 ≠ 1 := (Or.elim c2932 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u8 h))))))
  have u110 : s 47 ≠ 1 := (Or.elim c2807 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u8 h))))))
  have u111 : s 32 ≠ 1 := (Or.elim c2132 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u8 h))))))
  have u112 : s 17 ≠ 1 := (Or.elim c1462 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u8 h))))))
  have u113 : s 57 ≠ 2 := (Or.elim c3253 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u10 h))))))
  have u114 : s 44 ≠ 2 := (Or.elim c2683 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u115 : s 44 ≠ 1 := (Or.elim c2682 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u116 : s 57 ≠ 0 := (Or.elim c632 (fun h => h) (fun h => (False.elim (h a0))))
  have u117 : s 57 ≠ 3 := (Or.elim c638 (fun h => h) (fun h => (False.elim (h a0))))
  have u118 : s 31 ≠ 1 := (Or.elim c2097 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u116 h))) (fun h => (False.elim (u113 h))))))
  have u119 : s 30 ≠ 1 := (Or.elim c2052 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u116 h))) (fun h => (False.elim (u113 h))))))
  have u120 : s 33 ≠ 1 := (Or.elim c2187 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u116 h))) (fun h => (False.elim (u113 h))))))
  have u121 : s 30 ≠ 2 := (Or.elim c2053 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u116 h))) (fun h => (False.elim (u79 h))))))
  have u122 : s 31 ≠ 2 := (Or.elim c2098 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u116 h))) (fun h => (False.elim (u79 h))))))
  have u123 : s 33 ≠ 2 := (Or.elim c2188 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u116 h))) (fun h => (False.elim (u79 h))))))
  have u124 : s 30 ≠ 0 := (Or.elim c2051 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u79 h))) (fun h => (Or.elim h (fun h => (False.elim (u113 h))) (fun h => (False.elim (u117 h))))))))
  have u125 : s 32 ≠ 0 := (Or.elim c2141 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u79 h))) (fun h => (Or.elim h (fun h => (False.elim (u113 h))) (fun h => (False.elim (u117 h))))))))
  have u126 : s 0 ≠ 2 := (Or.elim c703 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u124 h))) (fun h => (False.elim (u119 h))))))
  have u127 : s 1 ≠ 1 := (Or.elim c747 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u124 h))) (fun h => (False.elim (u121 h))))))
  have u128 : s 4 ≠ 1 := (Or.elim c882 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u124 h))) (fun h => (False.elim (u121 h))))))
  have u129 : s 0 ≠ 1 := (Or.elim c702 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u124 h))) (fun h => (False.elim (u121 h))))))
  have u130 : s 1 ≠ 2 := (Or.elim c748 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u124 h))) (fun h => (False.elim (u119 h))))))
  have u131 : s 4 ≠ 2 := (Or.elim c883 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u124 h))) (fun h => (False.elim (u119 h))))))
  have u132 : s 10 ≠ 1 := (Or.elim c1112 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u125 h))) (fun h => (False.elim (u77 h))))))
  have u133 : s 12 ≠ 1 := (Or.elim c1202 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u125 h))) (fun h => (False.elim (u77 h))))))
  have u134 : s 13 ≠ 1 := (Or.elim c1247 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u125 h))) (fun h => (False.elim (u77 h))))))
  have u135 : s 10 ≠ 2 := (Or.elim c1113 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u125 h))) (fun h => (False.elim (u111 h))))))
  have u136 : s 12 ≠ 2 := (Or.elim c1203 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u125 h))) (fun h => (False.elim (u111 h))))))
  have u137 : s 13 ≠ 2 := (Or.elim c1248 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u125 h))) (fun h => (False.elim (u111 h))))))
  exact (Or.elim c3361 (fun h => (u129 h)) (fun h => (Or.elim h (fun h => (u126 h)) (fun h => (Or.elim h (fun h => (u127 h)) (fun h => (Or.elim h (fun h => (u130 h)) (fun h => (Or.elim h (fun h => (u63 h)) (fun h => (Or.elim h (fun h => (u76 h)) (fun h => (Or.elim h (fun h => (u59 h)) (fun h => (Or.elim h (fun h => (u103 h)) (fun h => (Or.elim h (fun h => (u128 h)) (fun h => (Or.elim h (fun h => (u131 h)) (fun h => (Or.elim h (fun h => (u49 h)) (fun h => (Or.elim h (fun h => (u74 h)) (fun h => (Or.elim h (fun h => (u62 h)) (fun h => (Or.elim h (fun h => (u106 h)) (fun h => (Or.elim h (fun h => (u55 h)) (fun h => (Or.elim h (fun h => (u99 h)) (fun h => (Or.elim h (fun h => (u66 h)) (fun h => (Or.elim h (fun h => (u94 h)) (fun h => (Or.elim h (fun h => (u50 h)) (fun h => (Or.elim h (fun h => (u75 h)) (fun h => (Or.elim h (fun h => (u132 h)) (fun h => (Or.elim h (fun h => (u135 h)) (fun h => (Or.elim h (fun h => (u61 h)) (fun h => (Or.elim h (fun h => (u105 h)) (fun h => (Or.elim h (fun h => (u133 h)) (fun h => (Or.elim h (fun h => (u136 h)) (fun h => (Or.elim h (fun h => (u134 h)) (fun h => (Or.elim h (fun h => (u137 h)) (fun h => (Or.elim h (fun h => (u10 h)) (fun h => (Or.elim h (fun h => (u8 h)) (fun h => (Or.elim h (fun h => (u27 h)) (fun h => (Or.elim h (fun h => (u31 h)) (fun h => (Or.elim h (fun h => (u26 h)) (fun h => (Or.elim h (fun h => (u30 h)) (fun h => (Or.elim h (fun h => (u112 h)) (fun h => (Or.elim h (fun h => (u78 h)) (fun h => (Or.elim h (fun h => (u56 h)) (fun h => (Or.elim h (fun h => (u101 h)) (fun h => (Or.elim h (fun h => (u25 h)) (fun h => (Or.elim h (fun h => (u29 h)) (fun h => (Or.elim h (fun h => (u46 h)) (fun h => (Or.elim h (fun h => (u90 h)) (fun h => (Or.elim h (fun h => (u60 h)) (fun h => (Or.elim h (fun h => (u104 h)) (fun h => (Or.elim h (fun h => (u54 h)) (fun h => (Or.elim h (fun h => (u98 h)) (fun h => (Or.elim h (fun h => (u70 h)) (fun h => (Or.elim h (fun h => (u93 h)) (fun h => (Or.elim h (fun h => (u45 h)) (fun h => (Or.elim h (fun h => (u89 h)) (fun h => (Or.elim h (fun h => (u21 h)) (fun h => (Or.elim h (fun h => (u20 h)) (fun h => (Or.elim h (fun h => (u53 h)) (fun h => (Or.elim h (fun h => (u97 h)) (fun h => (Or.elim h (fun h => (u19 h)) (fun h => (Or.elim h (fun h => (u15 h)) (fun h => (Or.elim h (fun h => (u18 h)) (fun h => (Or.elim h (fun h => (u14 h)) (fun h => (Or.elim h (fun h => (u16 h)) (fun h => (Or.elim h (fun h => (u5 h)) (fun h => (Or.elim h (fun h => (u119 h)) (fun h => (Or.elim h (fun h => (u121 h)) (fun h => (Or.elim h (fun h => (u118 h)) (fun h => (Or.elim h (fun h => (u122 h)) (fun h => (Or.elim h (fun h => (u111 h)) (fun h => (Or.elim h (fun h => (u77 h)) (fun h => (Or.elim h (fun h => (u120 h)) (fun h => (Or.elim h (fun h => (u123 h)) (fun h => (Or.elim h (fun h => (u102 h)) (fun h => (Or.elim h (fun h => (u58 h)) (fun h => (Or.elim h (fun h => (u35 h)) (fun h => (Or.elim h (fun h => (u33 h)) (fun h => (Or.elim h (fun h => (u28 h)) (fun h => (Or.elim h (fun h => (u24 h)) (fun h => (Or.elim h (fun h => (u34 h)) (fun h => (Or.elim h (fun h => (u32 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (u17 h)) (fun h => (Or.elim h (fun h => (u95 h)) (fun h => (Or.elim h (fun h => (u52 h)) (fun h => (Or.elim h (fun h => (u73 h)) (fun h => (Or.elim h (fun h => (u48 h)) (fun h => (Or.elim h (fun h => (u88 h)) (fun h => (Or.elim h (fun h => (u44 h)) (fun h => (Or.elim h (fun h => (u83 h)) (fun h => (Or.elim h (fun h => (u40 h)) (fun h => (Or.elim h (fun h => (u71 h)) (fun h => (Or.elim h (fun h => (u37 h)) (fun h => (Or.elim h (fun h => (u115 h)) (fun h => (Or.elim h (fun h => (u114 h)) (fun h => (Or.elim h (fun h => (u42 h)) (fun h => (Or.elim h (fun h => (u87 h)) (fun h => (Or.elim h (fun h => (u41 h)) (fun h => (Or.elim h (fun h => (u85 h)) (fun h => (Or.elim h (fun h => (u110 h)) (fun h => (Or.elim h (fun h => (u84 h)) (fun h => (Or.elim h (fun h => (u64 h)) (fun h => (Or.elim h (fun h => (u86 h)) (fun h => (Or.elim h (fun h => (u65 h)) (fun h => (Or.elim h (fun h => (u91 h)) (fun h => (Or.elim h (fun h => (u109 h)) (fun h => (Or.elim h (fun h => (u82 h)) (fun h => (Or.elim h (fun h => (u69 h)) (fun h => (Or.elim h (fun h => (u81 h)) (fun h => (Or.elim h (fun h => (u38 h)) (fun h => (Or.elim h (fun h => (u72 h)) (fun h => (Or.elim h (fun h => (u68 h)) (fun h => (Or.elim h (fun h => (u80 h)) (fun h => (Or.elim h (fun h => (u67 h)) (fun h => (Or.elim h (fun h => (u92 h)) (fun h => (Or.elim h (fun h => (u108 h)) (fun h => (Or.elim h (fun h => (u96 h)) (fun h => (Or.elim h (fun h => (u107 h)) (fun h => (Or.elim h (fun h => (u100 h)) (fun h => (Or.elim h (fun h => (u79 h)) (fun h => (Or.elim h (fun h => (u113 h)) (fun h => (Or.elim h (fun h => (u9 h)) (fun h => (Or.elim h (fun h => (u11 h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (u1 h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem step3363 (s : Fin 60 → Fin 5)
    (c657 : s 59 ≠ 1 ∨ s 59 ≠ 4)
    (c654 : s 59 ≠ 0 ∨ s 59 ≠ 4)
    (c1333 : s 14 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c660 : s 59 ≠ 3 ∨ s 59 ≠ 4)
    (c659 : s 59 ≠ 2 ∨ s 59 ≠ 4)
    (c1331 : s 14 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c3252 : s 57 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c1332 : s 14 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c3253 : s 57 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c2141 : s 32 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c628 : s 57 = 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3 ∨ s 57 = 4)
    (c2145 : s 32 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c3251 : s 57 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c1294 : s 14 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4)
    : s 57 = 3 ∨ s 57 = 4 ∨ s 59 ≠ 4 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 59 ≠ 1 := (Or.elim c657 (fun h => h) (fun h => (False.elim (h a2))))
  have u1 : s 59 ≠ 0 := (Or.elim c654 (fun h => h) (fun h => (False.elim (h a2))))
  have u2 : s 14 ≠ 2 := (Or.elim c1333 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))
  have u3 : s 59 ≠ 3 := (Or.elim c660 (fun h => h) (fun h => (False.elim (h a2))))
  have u4 : s 59 ≠ 2 := (Or.elim c659 (fun h => h) (fun h => (False.elim (h a2))))
  have u5 : s 14 ≠ 0 := (Or.elim c1331 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u3 h))))))))
  have u6 : s 57 ≠ 1 := (Or.elim c3252 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u2 h))))))
  have u7 : s 14 ≠ 1 := (Or.elim c1332 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u4 h))))))
  have u8 : s 57 ≠ 2 := (Or.elim c3253 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u7 h))))))
  have u9 : s 32 ≠ 0 := (Or.elim c2141 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (a0 h))))))))
  have u10 : s 57 = 0 := (Or.elim c628 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))))))
  have u11 : s 32 ≠ 4 := (Or.elim c2145 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))
  have u12 : s 14 = 3 := (Or.elim c3251 (fun h => (False.elim (h u10))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => h))))))
  exact (Or.elim c1294 (fun h => (h u12)) (fun h => (Or.elim h (fun h => (u9 h)) (fun h => (u11 h)))))

private theorem step3364 (s : Fin 60 → Fin 5)
    (c660 : s 59 ≠ 3 ∨ s 59 ≠ 4)
    (c659 : s 59 ≠ 2 ∨ s 59 ≠ 4)
    (c657 : s 59 ≠ 1 ∨ s 59 ≠ 4)
    (c2636 : s 43 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c654 : s 59 ≠ 0 ∨ s 59 ≠ 4)
    (c2638 : s 43 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c3002 : s 52 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c2591 : s 42 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2593 : s 42 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c2762 : s 46 ≠ 1 ∨ s 42 = 0 ∨ s 42 = 2)
    (c2717 : s 45 ≠ 1 ∨ s 42 = 0 ∨ s 42 = 2)
    (c2546 : s 41 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2548 : s 41 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c1757 : s 24 ≠ 1 ∨ s 41 = 0 ∨ s 41 = 2)
    (c1597 : s 20 ≠ 1 ∨ s 41 = 0 ∨ s 41 = 2)
    (c2501 : s 40 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2503 : s 40 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c892 : s 5 ≠ 1 ∨ s 40 = 0 ∨ s 40 = 2)
    (c1072 : s 9 ≠ 1 ∨ s 40 = 0 ∨ s 40 = 2)
    (c2456 : s 39 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2458 : s 39 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c1857 : s 26 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    (c1682 : s 22 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    (c997 : s 7 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    (c1502 : s 18 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    (c2231 : s 34 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2233 : s 34 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c807 : s 3 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c1622 : s 21 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c1167 : s 11 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c942 : s 6 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c2006 : s 29 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2008 : s 29 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c787 : s 2 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2)
    (c2862 : s 48 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2)
    (c2412 : s 38 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2)
    (c2897 : s 49 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c1042 : s 8 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c3107 : s 54 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c3047 : s 53 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c2957 : s 51 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c1727 : s 23 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c2637 : s 43 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c3003 : s 52 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c2502 : s 40 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c893 : s 5 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c1073 : s 9 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c2007 : s 29 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c788 : s 2 ≠ 2 ∨ s 29 = 0 ∨ s 29 = 1)
    (c2413 : s 38 ≠ 2 ∨ s 29 = 0 ∨ s 29 = 1)
    (c1332 : s 14 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c1331 : s 14 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2133 : s 32 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c1463 : s 17 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c1333 : s 14 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c3252 : s 57 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3048 : s 53 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c2958 : s 51 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c2938 : s 50 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c2592 : s 42 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c2813 : s 47 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1)
    (c2763 : s 46 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1)
    (c2833 : s 48 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1)
    (c2718 : s 45 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1)
    (c2547 : s 41 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c1758 : s 24 ≠ 2 ∨ s 41 = 0 ∨ s 41 = 1)
    (c1598 : s 20 ≠ 2 ∨ s 41 = 0 ∨ s 41 = 1)
    (c2873 : s 49 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c3093 : s 54 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c1713 : s 23 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c1028 : s 8 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c2457 : s 39 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c3143 : s 55 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c1858 : s 26 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c1683 : s 22 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c998 : s 7 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c3188 : s 56 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c1503 : s 18 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c2232 : s 34 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c808 : s 3 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c1623 : s 21 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c1168 : s 11 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c943 : s 6 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c3307 : s 58 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3197 : s 56 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3167 : s 55 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c2932 : s 50 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c2807 : s 47 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c2132 : s 32 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c1462 : s 17 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3308 : s 58 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c3253 : s 57 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c2683 : s 44 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c2682 : s 44 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c643 : s 58 ≠ 0 ∨ s 58 ≠ 4)
    (c649 : s 58 ≠ 3 ∨ s 58 ≠ 4)
    (c2237 : s 35 ≠ 1 ∨ s 58 = 0 ∨ s 58 = 2)
    (c2282 : s 36 ≠ 1 ∨ s 58 = 0 ∨ s 58 = 2)
    (c2327 : s 37 ≠ 1 ∨ s 58 = 0 ∨ s 58 = 2)
    (c2238 : s 35 ≠ 2 ∨ s 58 = 0 ∨ s 58 = 1)
    (c2283 : s 36 ≠ 2 ∨ s 58 = 0 ∨ s 58 = 1)
    (c2328 : s 37 ≠ 2 ∨ s 58 = 0 ∨ s 58 = 1)
    (c2281 : s 36 ≠ 0 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 58 = 3)
    (c2371 : s 38 ≠ 0 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 58 = 3)
    (c1368 : s 15 ≠ 2 ∨ s 36 = 0 ∨ s 36 = 1)
    (c1388 : s 16 ≠ 2 ∨ s 36 = 0 ∨ s 36 = 1)
    (c1523 : s 19 ≠ 2 ∨ s 36 = 0 ∨ s 36 = 1)
    (c1367 : s 15 ≠ 1 ∨ s 36 = 0 ∨ s 36 = 2)
    (c1387 : s 16 ≠ 1 ∨ s 36 = 0 ∨ s 36 = 2)
    (c1522 : s 19 ≠ 1 ∨ s 36 = 0 ∨ s 36 = 2)
    (c1812 : s 25 ≠ 1 ∨ s 38 = 0 ∨ s 38 = 2)
    (c1813 : s 25 ≠ 2 ∨ s 38 = 0 ∨ s 38 = 1)
    (c1882 : s 27 ≠ 1 ∨ s 38 = 0 ∨ s 38 = 2)
    (c1927 : s 28 ≠ 1 ∨ s 38 = 0 ∨ s 38 = 2)
    (c1883 : s 27 ≠ 2 ∨ s 38 = 0 ∨ s 38 = 1)
    (c1928 : s 28 ≠ 2 ∨ s 38 = 0 ∨ s 38 = 1)
    (c3362 : s 57 ≠ 4 ∨ s 58 ≠ 4 ∨ s 59 ≠ 4)
    (c3363 : s 57 = 3 ∨ s 57 = 4 ∨ s 59 ≠ 4)
    (c631 : s 57 ≠ 0 ∨ s 57 ≠ 3)
    (c1324 : s 14 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c2054 : s 30 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c2097 : s 31 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2052 : s 30 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2187 : s 33 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2053 : s 30 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2098 : s 31 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2188 : s 33 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c3166 : s 55 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2806 : s 47 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c1461 : s 17 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c1641 : s 21 ≠ 0 ∨ s 30 = 1 ∨ s 30 = 2 ∨ s 30 = 3)
    (c1152 : s 10 ≠ 1 ∨ s 55 = 0 ∨ s 55 = 2)
    (c1153 : s 10 ≠ 2 ∨ s 55 = 0 ∨ s 55 = 1)
    (c1242 : s 12 ≠ 1 ∨ s 55 = 0 ∨ s 55 = 2)
    (c1287 : s 13 ≠ 1 ∨ s 55 = 0 ∨ s 55 = 2)
    (c1243 : s 12 ≠ 2 ∨ s 55 = 0 ∨ s 55 = 1)
    (c1288 : s 13 ≠ 2 ∨ s 55 = 0 ∨ s 55 = 1)
    (c857 : s 4 ≠ 1 ∨ s 47 = 0 ∨ s 47 = 2)
    (c858 : s 4 ≠ 2 ∨ s 47 = 0 ∨ s 47 = 1)
    (c677 : s 0 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2)
    (c678 : s 0 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1)
    (c722 : s 1 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2)
    (c723 : s 1 ≠ 2 ∨ s 21 = 0 ∨ s 21 = 1)
    (c3361 : s 0 = 1 ∨ s 0 = 2 ∨ s 1 = 1 ∨ s 1 = 2 ∨ s 2 = 1 ∨ s 2 = 2 ∨ s 3 = 1 ∨ s 3 = 2 ∨ s 4 = 1 ∨ s 4 = 2 ∨ s 5 = 1 ∨ s 5 = 2 ∨ s 6 = 1 ∨ s 6 = 2 ∨ s 7 = 1 ∨ s 7 = 2 ∨ s 8 = 1 ∨ s 8 = 2 ∨ s 9 = 1 ∨ s 9 = 2 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 11 = 1 ∨ s 11 = 2 ∨ s 12 = 1 ∨ s 12 = 2 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 15 = 1 ∨ s 15 = 2 ∨ s 16 = 1 ∨ s 16 = 2 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 18 = 1 ∨ s 18 = 2 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 20 = 1 ∨ s 20 = 2 ∨ s 21 = 1 ∨ s 21 = 2 ∨ s 22 = 1 ∨ s 22 = 2 ∨ s 23 = 1 ∨ s 23 = 2 ∨ s 24 = 1 ∨ s 24 = 2 ∨ s 25 = 1 ∨ s 25 = 2 ∨ s 26 = 1 ∨ s 26 = 2 ∨ s 27 = 1 ∨ s 27 = 2 ∨ s 28 = 1 ∨ s 28 = 2 ∨ s 29 = 1 ∨ s 29 = 2 ∨ s 30 = 1 ∨ s 30 = 2 ∨ s 31 = 1 ∨ s 31 = 2 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 33 = 1 ∨ s 33 = 2 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 35 = 1 ∨ s 35 = 2 ∨ s 36 = 1 ∨ s 36 = 2 ∨ s 37 = 1 ∨ s 37 = 2 ∨ s 38 = 1 ∨ s 38 = 2 ∨ s 39 = 1 ∨ s 39 = 2 ∨ s 40 = 1 ∨ s 40 = 2 ∨ s 41 = 1 ∨ s 41 = 2 ∨ s 42 = 1 ∨ s 42 = 2 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 44 = 1 ∨ s 44 = 2 ∨ s 45 = 1 ∨ s 45 = 2 ∨ s 46 = 1 ∨ s 46 = 2 ∨ s 47 = 1 ∨ s 47 = 2 ∨ s 48 = 1 ∨ s 48 = 2 ∨ s 49 = 1 ∨ s 49 = 2 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 52 = 1 ∨ s 52 = 2 ∨ s 53 = 1 ∨ s 53 = 2 ∨ s 54 = 1 ∨ s 54 = 2 ∨ s 55 = 1 ∨ s 55 = 2 ∨ s 56 = 1 ∨ s 56 = 2 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 59 = 1 ∨ s 59 = 2)
    : s 58 ≠ 4 ∨ s 59 ≠ 4 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 59 ≠ 3 := (Or.elim c660 (fun h => h) (fun h => (False.elim (h a1))))
  have u1 : s 59 ≠ 2 := (Or.elim c659 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 59 ≠ 1 := (Or.elim c657 (fun h => h) (fun h => (False.elim (h a1))))
  have u3 : s 43 ≠ 0 := (Or.elim c2636 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u4 : s 59 ≠ 0 := (Or.elim c654 (fun h => h) (fun h => (False.elim (h a1))))
  have u5 : s 43 ≠ 2 := (Or.elim c2638 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u6 : s 52 ≠ 1 := (Or.elim c3002 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u7 : s 42 ≠ 0 := (Or.elim c2591 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u8 : s 42 ≠ 2 := (Or.elim c2593 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u9 : s 46 ≠ 1 := (Or.elim c2762 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u8 h))))))
  have u10 : s 45 ≠ 1 := (Or.elim c2717 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u8 h))))))
  have u11 : s 41 ≠ 0 := (Or.elim c2546 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u12 : s 41 ≠ 2 := (Or.elim c2548 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u13 : s 24 ≠ 1 := (Or.elim c1757 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u12 h))))))
  have u14 : s 20 ≠ 1 := (Or.elim c1597 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u12 h))))))
  have u15 : s 40 ≠ 0 := (Or.elim c2501 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u16 : s 40 ≠ 2 := (Or.elim c2503 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u17 : s 5 ≠ 1 := (Or.elim c892 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u16 h))))))
  have u18 : s 9 ≠ 1 := (Or.elim c1072 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u16 h))))))
  have u19 : s 39 ≠ 0 := (Or.elim c2456 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u20 : s 39 ≠ 2 := (Or.elim c2458 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u21 : s 26 ≠ 1 := (Or.elim c1857 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u20 h))))))
  have u22 : s 22 ≠ 1 := (Or.elim c1682 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u20 h))))))
  have u23 : s 7 ≠ 1 := (Or.elim c997 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u20 h))))))
  have u24 : s 18 ≠ 1 := (Or.elim c1502 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u20 h))))))
  have u25 : s 34 ≠ 0 := (Or.elim c2231 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u26 : s 34 ≠ 2 := (Or.elim c2233 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u27 : s 3 ≠ 1 := (Or.elim c807 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u26 h))))))
  have u28 : s 21 ≠ 1 := (Or.elim c1622 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u26 h))))))
  have u29 : s 11 ≠ 1 := (Or.elim c1167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u26 h))))))
  have u30 : s 6 ≠ 1 := (Or.elim c942 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u26 h))))))
  have u31 : s 29 ≠ 0 := (Or.elim c2006 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u32 : s 29 ≠ 2 := (Or.elim c2008 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u33 : s 2 ≠ 1 := (Or.elim c787 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u32 h))))))
  have u34 : s 48 ≠ 1 := (Or.elim c2862 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u32 h))))))
  have u35 : s 38 ≠ 1 := (Or.elim c2412 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u32 h))))))
  have u36 : s 49 ≠ 1 := (Or.elim c2897 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u37 : s 8 ≠ 1 := (Or.elim c1042 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u38 : s 54 ≠ 1 := (Or.elim c3107 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u39 : s 53 ≠ 1 := (Or.elim c3047 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u40 : s 51 ≠ 1 := (Or.elim c2957 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u41 : s 23 ≠ 1 := (Or.elim c1727 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u42 : s 43 ≠ 1 := (Or.elim c2637 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u43 : s 52 ≠ 2 := (Or.elim c3003 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u42 h))))))
  have u44 : s 40 ≠ 1 := (Or.elim c2502 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u45 : s 5 ≠ 2 := (Or.elim c893 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u44 h))))))
  have u46 : s 9 ≠ 2 := (Or.elim c1073 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u44 h))))))
  have u47 : s 29 ≠ 1 := (Or.elim c2007 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u48 : s 2 ≠ 2 := (Or.elim c788 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u47 h))))))
  have u49 : s 38 ≠ 2 := (Or.elim c2413 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u47 h))))))
  have u50 : s 14 ≠ 1 := (Or.elim c1332 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u51 : s 14 ≠ 0 := (Or.elim c1331 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u52 : s 32 ≠ 2 := (Or.elim c2133 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u50 h))))))
  have u53 : s 17 ≠ 2 := (Or.elim c1463 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u50 h))))))
  have u54 : s 14 ≠ 2 := (Or.elim c1333 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u55 : s 57 ≠ 1 := (Or.elim c3252 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u54 h))))))
  have u56 : s 53 ≠ 2 := (Or.elim c3048 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u42 h))))))
  have u57 : s 51 ≠ 2 := (Or.elim c2958 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u42 h))))))
  have u58 : s 50 ≠ 2 := (Or.elim c2938 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u42 h))))))
  have u59 : s 42 ≠ 1 := (Or.elim c2592 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u60 : s 47 ≠ 2 := (Or.elim c2813 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u59 h))))))
  have u61 : s 46 ≠ 2 := (Or.elim c2763 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u59 h))))))
  have u62 : s 48 ≠ 2 := (Or.elim c2833 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u59 h))))))
  have u63 : s 45 ≠ 2 := (Or.elim c2718 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u59 h))))))
  have u64 : s 41 ≠ 1 := (Or.elim c2547 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u65 : s 24 ≠ 2 := (Or.elim c1758 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u64 h))))))
  have u66 : s 20 ≠ 2 := (Or.elim c1598 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u64 h))))))
  have u67 : s 49 ≠ 2 := (Or.elim c2873 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u44 h))))))
  have u68 : s 54 ≠ 2 := (Or.elim c3093 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u44 h))))))
  have u69 : s 23 ≠ 2 := (Or.elim c1713 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u44 h))))))
  have u70 : s 8 ≠ 2 := (Or.elim c1028 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u44 h))))))
  have u71 : s 39 ≠ 1 := (Or.elim c2457 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u72 : s 55 ≠ 2 := (Or.elim c3143 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u71 h))))))
  have u73 : s 26 ≠ 2 := (Or.elim c1858 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u71 h))))))
  have u74 : s 22 ≠ 2 := (Or.elim c1683 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u71 h))))))
  have u75 : s 7 ≠ 2 := (Or.elim c998 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u71 h))))))
  have u76 : s 56 ≠ 2 := (Or.elim c3188 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u71 h))))))
  have u77 : s 18 ≠ 2 := (Or.elim c1503 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u71 h))))))
  have u78 : s 34 ≠ 1 := (Or.elim c2232 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u79 : s 3 ≠ 2 := (Or.elim c808 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u78 h))))))
  have u80 : s 21 ≠ 2 := (Or.elim c1623 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u78 h))))))
  have u81 : s 11 ≠ 2 := (Or.elim c1168 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u78 h))))))
  have u82 : s 6 ≠ 2 := (Or.elim c943 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u78 h))))))
  have u83 : s 58 ≠ 1 := (Or.elim c3307 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u54 h))))))
  have u84 : s 56 ≠ 1 := (Or.elim c3197 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u54 h))))))
  have u85 : s 55 ≠ 1 := (Or.elim c3167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u54 h))))))
  have u86 : s 50 ≠ 1 := (Or.elim c2932 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u54 h))))))
  have u87 : s 47 ≠ 1 := (Or.elim c2807 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u54 h))))))
  have u88 : s 32 ≠ 1 := (Or.elim c2132 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u54 h))))))
  have u89 : s 17 ≠ 1 := (Or.elim c1462 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u54 h))))))
  have u90 : s 58 ≠ 2 := (Or.elim c3308 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u50 h))))))
  have u91 : s 57 ≠ 2 := (Or.elim c3253 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u50 h))))))
  have u92 : s 44 ≠ 2 := (Or.elim c2683 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u93 : s 44 ≠ 1 := (Or.elim c2682 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u94 : s 58 ≠ 0 := (Or.elim c643 (fun h => h) (fun h => (False.elim (h a0))))
  have u95 : s 58 ≠ 3 := (Or.elim c649 (fun h => h) (fun h => (False.elim (h a0))))
  have u96 : s 35 ≠ 1 := (Or.elim c2237 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u94 h))) (fun h => (False.elim (u90 h))))))
  have u97 : s 36 ≠ 1 := (Or.elim c2282 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u94 h))) (fun h => (False.elim (u90 h))))))
  have u98 : s 37 ≠ 1 := (Or.elim c2327 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u94 h))) (fun h => (False.elim (u90 h))))))
  have u99 : s 35 ≠ 2 := (Or.elim c2238 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u94 h))) (fun h => (False.elim (u83 h))))))
  have u100 : s 36 ≠ 2 := (Or.elim c2283 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u94 h))) (fun h => (False.elim (u83 h))))))
  have u101 : s 37 ≠ 2 := (Or.elim c2328 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u94 h))) (fun h => (False.elim (u83 h))))))
  have u102 : s 36 ≠ 0 := (Or.elim c2281 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u83 h))) (fun h => (Or.elim h (fun h => (False.elim (u90 h))) (fun h => (False.elim (u95 h))))))))
  have u103 : s 38 ≠ 0 := (Or.elim c2371 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u83 h))) (fun h => (Or.elim h (fun h => (False.elim (u90 h))) (fun h => (False.elim (u95 h))))))))
  have u104 : s 15 ≠ 2 := (Or.elim c1368 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u102 h))) (fun h => (False.elim (u97 h))))))
  have u105 : s 16 ≠ 2 := (Or.elim c1388 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u102 h))) (fun h => (False.elim (u97 h))))))
  have u106 : s 19 ≠ 2 := (Or.elim c1523 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u102 h))) (fun h => (False.elim (u97 h))))))
  have u107 : s 15 ≠ 1 := (Or.elim c1367 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u102 h))) (fun h => (False.elim (u100 h))))))
  have u108 : s 16 ≠ 1 := (Or.elim c1387 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u102 h))) (fun h => (False.elim (u100 h))))))
  have u109 : s 19 ≠ 1 := (Or.elim c1522 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u102 h))) (fun h => (False.elim (u100 h))))))
  have u110 : s 25 ≠ 1 := (Or.elim c1812 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u103 h))) (fun h => (False.elim (u49 h))))))
  have u111 : s 25 ≠ 2 := (Or.elim c1813 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u103 h))) (fun h => (False.elim (u35 h))))))
  have u112 : s 27 ≠ 1 := (Or.elim c1882 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u103 h))) (fun h => (False.elim (u49 h))))))
  have u113 : s 28 ≠ 1 := (Or.elim c1927 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u103 h))) (fun h => (False.elim (u49 h))))))
  have u114 : s 27 ≠ 2 := (Or.elim c1883 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u103 h))) (fun h => (False.elim (u35 h))))))
  have u115 : s 28 ≠ 2 := (Or.elim c1928 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u103 h))) (fun h => (False.elim (u35 h))))))
  have u116 : s 57 ≠ 4 := (Or.elim c3362 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (False.elim (h a1))))))
  have u117 : s 57 = 3 := (Or.elim c3363 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u116 h))) (fun h => (False.elim (h a1))))))
  have u118 : s 57 ≠ 0 := (Or.elim c631 (fun h => h) (fun h => (False.elim (h u117))))
  have u119 : s 14 ≠ 3 := (Or.elim c1324 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u118 h))) (fun h => (False.elim (u116 h))))))
  have u120 : s 30 ≠ 3 := (Or.elim c2054 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u118 h))) (fun h => (False.elim (u116 h))))))
  have u121 : s 31 ≠ 1 := (Or.elim c2097 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u118 h))) (fun h => (False.elim (u91 h))))))
  have u122 : s 30 ≠ 1 := (Or.elim c2052 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u118 h))) (fun h => (False.elim (u91 h))))))
  have u123 : s 33 ≠ 1 := (Or.elim c2187 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u118 h))) (fun h => (False.elim (u91 h))))))
  have u124 : s 30 ≠ 2 := (Or.elim c2053 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u118 h))) (fun h => (False.elim (u55 h))))))
  have u125 : s 31 ≠ 2 := (Or.elim c2098 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u118 h))) (fun h => (False.elim (u55 h))))))
  have u126 : s 33 ≠ 2 := (Or.elim c2188 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u118 h))) (fun h => (False.elim (u55 h))))))
  have u127 : s 55 ≠ 0 := (Or.elim c3166 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (Or.elim h (fun h => (False.elim (u54 h))) (fun h => (False.elim (u119 h))))))))
  have u128 : s 47 ≠ 0 := (Or.elim c2806 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (Or.elim h (fun h => (False.elim (u54 h))) (fun h => (False.elim (u119 h))))))))
  have u129 : s 17 ≠ 0 := (Or.elim c1461 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (Or.elim h (fun h => (False.elim (u54 h))) (fun h => (False.elim (u119 h))))))))
  have u130 : s 21 ≠ 0 := (Or.elim c1641 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u122 h))) (fun h => (Or.elim h (fun h => (False.elim (u124 h))) (fun h => (False.elim (u120 h))))))))
  have u131 : s 10 ≠ 1 := (Or.elim c1152 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u127 h))) (fun h => (False.elim (u72 h))))))
  have u132 : s 10 ≠ 2 := (Or.elim c1153 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u127 h))) (fun h => (False.elim (u85 h))))))
  have u133 : s 12 ≠ 1 := (Or.elim c1242 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u127 h))) (fun h => (False.elim (u72 h))))))
  have u134 : s 13 ≠ 1 := (Or.elim c1287 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u127 h))) (fun h => (False.elim (u72 h))))))
  have u135 : s 12 ≠ 2 := (Or.elim c1243 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u127 h))) (fun h => (False.elim (u85 h))))))
  have u136 : s 13 ≠ 2 := (Or.elim c1288 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u127 h))) (fun h => (False.elim (u85 h))))))
  have u137 : s 4 ≠ 1 := (Or.elim c857 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u128 h))) (fun h => (False.elim (u60 h))))))
  have u138 : s 4 ≠ 2 := (Or.elim c858 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u128 h))) (fun h => (False.elim (u87 h))))))
  have u139 : s 0 ≠ 1 := (Or.elim c677 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u129 h))) (fun h => (False.elim (u53 h))))))
  have u140 : s 0 ≠ 2 := (Or.elim c678 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u129 h))) (fun h => (False.elim (u89 h))))))
  have u141 : s 1 ≠ 1 := (Or.elim c722 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u130 h))) (fun h => (False.elim (u80 h))))))
  have u142 : s 1 ≠ 2 := (Or.elim c723 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u130 h))) (fun h => (False.elim (u28 h))))))
  exact (Or.elim c3361 (fun h => (u139 h)) (fun h => (Or.elim h (fun h => (u140 h)) (fun h => (Or.elim h (fun h => (u141 h)) (fun h => (Or.elim h (fun h => (u142 h)) (fun h => (Or.elim h (fun h => (u33 h)) (fun h => (Or.elim h (fun h => (u48 h)) (fun h => (Or.elim h (fun h => (u27 h)) (fun h => (Or.elim h (fun h => (u79 h)) (fun h => (Or.elim h (fun h => (u137 h)) (fun h => (Or.elim h (fun h => (u138 h)) (fun h => (Or.elim h (fun h => (u17 h)) (fun h => (Or.elim h (fun h => (u45 h)) (fun h => (Or.elim h (fun h => (u30 h)) (fun h => (Or.elim h (fun h => (u82 h)) (fun h => (Or.elim h (fun h => (u23 h)) (fun h => (Or.elim h (fun h => (u75 h)) (fun h => (Or.elim h (fun h => (u37 h)) (fun h => (Or.elim h (fun h => (u70 h)) (fun h => (Or.elim h (fun h => (u18 h)) (fun h => (Or.elim h (fun h => (u46 h)) (fun h => (Or.elim h (fun h => (u131 h)) (fun h => (Or.elim h (fun h => (u132 h)) (fun h => (Or.elim h (fun h => (u29 h)) (fun h => (Or.elim h (fun h => (u81 h)) (fun h => (Or.elim h (fun h => (u133 h)) (fun h => (Or.elim h (fun h => (u135 h)) (fun h => (Or.elim h (fun h => (u134 h)) (fun h => (Or.elim h (fun h => (u136 h)) (fun h => (Or.elim h (fun h => (u50 h)) (fun h => (Or.elim h (fun h => (u54 h)) (fun h => (Or.elim h (fun h => (u107 h)) (fun h => (Or.elim h (fun h => (u104 h)) (fun h => (Or.elim h (fun h => (u108 h)) (fun h => (Or.elim h (fun h => (u105 h)) (fun h => (Or.elim h (fun h => (u89 h)) (fun h => (Or.elim h (fun h => (u53 h)) (fun h => (Or.elim h (fun h => (u24 h)) (fun h => (Or.elim h (fun h => (u77 h)) (fun h => (Or.elim h (fun h => (u109 h)) (fun h => (Or.elim h (fun h => (u106 h)) (fun h => (Or.elim h (fun h => (u14 h)) (fun h => (Or.elim h (fun h => (u66 h)) (fun h => (Or.elim h (fun h => (u28 h)) (fun h => (Or.elim h (fun h => (u80 h)) (fun h => (Or.elim h (fun h => (u22 h)) (fun h => (Or.elim h (fun h => (u74 h)) (fun h => (Or.elim h (fun h => (u41 h)) (fun h => (Or.elim h (fun h => (u69 h)) (fun h => (Or.elim h (fun h => (u13 h)) (fun h => (Or.elim h (fun h => (u65 h)) (fun h => (Or.elim h (fun h => (u110 h)) (fun h => (Or.elim h (fun h => (u111 h)) (fun h => (Or.elim h (fun h => (u21 h)) (fun h => (Or.elim h (fun h => (u73 h)) (fun h => (Or.elim h (fun h => (u112 h)) (fun h => (Or.elim h (fun h => (u114 h)) (fun h => (Or.elim h (fun h => (u113 h)) (fun h => (Or.elim h (fun h => (u115 h)) (fun h => (Or.elim h (fun h => (u47 h)) (fun h => (Or.elim h (fun h => (u32 h)) (fun h => (Or.elim h (fun h => (u122 h)) (fun h => (Or.elim h (fun h => (u124 h)) (fun h => (Or.elim h (fun h => (u121 h)) (fun h => (Or.elim h (fun h => (u125 h)) (fun h => (Or.elim h (fun h => (u88 h)) (fun h => (Or.elim h (fun h => (u52 h)) (fun h => (Or.elim h (fun h => (u123 h)) (fun h => (Or.elim h (fun h => (u126 h)) (fun h => (Or.elim h (fun h => (u78 h)) (fun h => (Or.elim h (fun h => (u26 h)) (fun h => (Or.elim h (fun h => (u96 h)) (fun h => (Or.elim h (fun h => (u99 h)) (fun h => (Or.elim h (fun h => (u97 h)) (fun h => (Or.elim h (fun h => (u100 h)) (fun h => (Or.elim h (fun h => (u98 h)) (fun h => (Or.elim h (fun h => (u101 h)) (fun h => (Or.elim h (fun h => (u35 h)) (fun h => (Or.elim h (fun h => (u49 h)) (fun h => (Or.elim h (fun h => (u71 h)) (fun h => (Or.elim h (fun h => (u20 h)) (fun h => (Or.elim h (fun h => (u44 h)) (fun h => (Or.elim h (fun h => (u16 h)) (fun h => (Or.elim h (fun h => (u64 h)) (fun h => (Or.elim h (fun h => (u12 h)) (fun h => (Or.elim h (fun h => (u59 h)) (fun h => (Or.elim h (fun h => (u8 h)) (fun h => (Or.elim h (fun h => (u42 h)) (fun h => (Or.elim h (fun h => (u5 h)) (fun h => (Or.elim h (fun h => (u93 h)) (fun h => (Or.elim h (fun h => (u92 h)) (fun h => (Or.elim h (fun h => (u10 h)) (fun h => (Or.elim h (fun h => (u63 h)) (fun h => (Or.elim h (fun h => (u9 h)) (fun h => (Or.elim h (fun h => (u61 h)) (fun h => (Or.elim h (fun h => (u87 h)) (fun h => (Or.elim h (fun h => (u60 h)) (fun h => (Or.elim h (fun h => (u34 h)) (fun h => (Or.elim h (fun h => (u62 h)) (fun h => (Or.elim h (fun h => (u36 h)) (fun h => (Or.elim h (fun h => (u67 h)) (fun h => (Or.elim h (fun h => (u86 h)) (fun h => (Or.elim h (fun h => (u58 h)) (fun h => (Or.elim h (fun h => (u40 h)) (fun h => (Or.elim h (fun h => (u57 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (u43 h)) (fun h => (Or.elim h (fun h => (u39 h)) (fun h => (Or.elim h (fun h => (u56 h)) (fun h => (Or.elim h (fun h => (u38 h)) (fun h => (Or.elim h (fun h => (u68 h)) (fun h => (Or.elim h (fun h => (u85 h)) (fun h => (Or.elim h (fun h => (u72 h)) (fun h => (Or.elim h (fun h => (u84 h)) (fun h => (Or.elim h (fun h => (u76 h)) (fun h => (Or.elim h (fun h => (u55 h)) (fun h => (Or.elim h (fun h => (u91 h)) (fun h => (Or.elim h (fun h => (u83 h)) (fun h => (Or.elim h (fun h => (u90 h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (u1 h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem step3365 (s : Fin 60 → Fin 5)
    (c660 : s 59 ≠ 3 ∨ s 59 ≠ 4)
    (c659 : s 59 ≠ 2 ∨ s 59 ≠ 4)
    (c657 : s 59 ≠ 1 ∨ s 59 ≠ 4)
    (c2636 : s 43 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c654 : s 59 ≠ 0 ∨ s 59 ≠ 4)
    (c2638 : s 43 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c3002 : s 52 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c2591 : s 42 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2593 : s 42 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c2762 : s 46 ≠ 1 ∨ s 42 = 0 ∨ s 42 = 2)
    (c2717 : s 45 ≠ 1 ∨ s 42 = 0 ∨ s 42 = 2)
    (c2546 : s 41 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2548 : s 41 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c1757 : s 24 ≠ 1 ∨ s 41 = 0 ∨ s 41 = 2)
    (c1597 : s 20 ≠ 1 ∨ s 41 = 0 ∨ s 41 = 2)
    (c2501 : s 40 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2503 : s 40 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c892 : s 5 ≠ 1 ∨ s 40 = 0 ∨ s 40 = 2)
    (c1072 : s 9 ≠ 1 ∨ s 40 = 0 ∨ s 40 = 2)
    (c2456 : s 39 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2458 : s 39 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c1857 : s 26 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    (c1682 : s 22 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    (c997 : s 7 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    (c1502 : s 18 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    (c2231 : s 34 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2233 : s 34 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c807 : s 3 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c1622 : s 21 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c1167 : s 11 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c942 : s 6 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c2006 : s 29 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2008 : s 29 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c787 : s 2 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2)
    (c2862 : s 48 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2)
    (c2412 : s 38 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2)
    (c2897 : s 49 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c1042 : s 8 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c3107 : s 54 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c3047 : s 53 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c2957 : s 51 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c1727 : s 23 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c2637 : s 43 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c3003 : s 52 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c2502 : s 40 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c893 : s 5 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c1073 : s 9 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c2007 : s 29 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c788 : s 2 ≠ 2 ∨ s 29 = 0 ∨ s 29 = 1)
    (c2413 : s 38 ≠ 2 ∨ s 29 = 0 ∨ s 29 = 1)
    (c1332 : s 14 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c1331 : s 14 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2133 : s 32 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c1463 : s 17 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c1333 : s 14 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c3252 : s 57 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3048 : s 53 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c2958 : s 51 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c2938 : s 50 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c2592 : s 42 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c2813 : s 47 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1)
    (c2763 : s 46 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1)
    (c2833 : s 48 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1)
    (c2718 : s 45 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1)
    (c2547 : s 41 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c1758 : s 24 ≠ 2 ∨ s 41 = 0 ∨ s 41 = 1)
    (c1598 : s 20 ≠ 2 ∨ s 41 = 0 ∨ s 41 = 1)
    (c2873 : s 49 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c3093 : s 54 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c1713 : s 23 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c1028 : s 8 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c2457 : s 39 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c3143 : s 55 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c1858 : s 26 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c1683 : s 22 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c998 : s 7 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c3188 : s 56 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c1503 : s 18 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c2232 : s 34 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c808 : s 3 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c1623 : s 21 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c1168 : s 11 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c943 : s 6 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c3307 : s 58 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3197 : s 56 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3167 : s 55 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c2932 : s 50 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c2807 : s 47 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c2132 : s 32 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c1462 : s 17 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3308 : s 58 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c3253 : s 57 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c2683 : s 44 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c2682 : s 44 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c3363 : s 57 = 3 ∨ s 57 = 4 ∨ s 59 ≠ 4)
    (c631 : s 57 ≠ 0 ∨ s 57 ≠ 3)
    (c1324 : s 14 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c1999 : s 29 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c2054 : s 30 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c2097 : s 31 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2052 : s 30 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2187 : s 33 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2053 : s 30 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2098 : s 31 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2188 : s 33 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c3196 : s 56 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c3306 : s 58 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c3166 : s 55 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2931 : s 50 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2806 : s 47 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c1461 : s 17 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c786 : s 2 ≠ 0 ∨ s 29 = 1 ∨ s 29 = 2 ∨ s 29 = 3)
    (c966 : s 6 ≠ 0 ∨ s 30 = 1 ∨ s 30 = 2 ∨ s 30 = 3)
    (c1641 : s 21 ≠ 0 ∨ s 30 = 1 ∨ s 30 = 2 ∨ s 30 = 3)
    (c1827 : s 25 ≠ 1 ∨ s 56 = 0 ∨ s 56 = 2)
    (c1828 : s 25 ≠ 2 ∨ s 56 = 0 ∨ s 56 = 1)
    (c1963 : s 28 ≠ 2 ∨ s 56 = 0 ∨ s 56 = 1)
    (c1918 : s 27 ≠ 2 ∨ s 56 = 0 ∨ s 56 = 1)
    (c1962 : s 28 ≠ 1 ∨ s 56 = 0 ∨ s 56 = 2)
    (c1917 : s 27 ≠ 1 ∨ s 56 = 0 ∨ s 56 = 2)
    (c2237 : s 35 ≠ 1 ∨ s 58 = 0 ∨ s 58 = 2)
    (c2282 : s 36 ≠ 1 ∨ s 58 = 0 ∨ s 58 = 2)
    (c2327 : s 37 ≠ 1 ∨ s 58 = 0 ∨ s 58 = 2)
    (c2238 : s 35 ≠ 2 ∨ s 58 = 0 ∨ s 58 = 1)
    (c2283 : s 36 ≠ 2 ∨ s 58 = 0 ∨ s 58 = 1)
    (c2328 : s 37 ≠ 2 ∨ s 58 = 0 ∨ s 58 = 1)
    (c1152 : s 10 ≠ 1 ∨ s 55 = 0 ∨ s 55 = 2)
    (c1153 : s 10 ≠ 2 ∨ s 55 = 0 ∨ s 55 = 1)
    (c1242 : s 12 ≠ 1 ∨ s 55 = 0 ∨ s 55 = 2)
    (c1287 : s 13 ≠ 1 ∨ s 55 = 0 ∨ s 55 = 2)
    (c1243 : s 12 ≠ 2 ∨ s 55 = 0 ∨ s 55 = 1)
    (c1288 : s 13 ≠ 2 ∨ s 55 = 0 ∨ s 55 = 1)
    (c1537 : s 19 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2)
    (c1538 : s 19 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1)
    (c857 : s 4 ≠ 1 ∨ s 47 = 0 ∨ s 47 = 2)
    (c858 : s 4 ≠ 2 ∨ s 47 = 0 ∨ s 47 = 1)
    (c677 : s 0 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2)
    (c678 : s 0 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1)
    (c1347 : s 15 ≠ 1 ∨ s 2 = 0 ∨ s 2 = 2)
    (c1348 : s 15 ≠ 2 ∨ s 2 = 0 ∨ s 2 = 1)
    (c1397 : s 16 ≠ 1 ∨ s 6 = 0 ∨ s 6 = 2)
    (c1398 : s 16 ≠ 2 ∨ s 6 = 0 ∨ s 6 = 1)
    (c722 : s 1 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2)
    (c723 : s 1 ≠ 2 ∨ s 21 = 0 ∨ s 21 = 1)
    (c3361 : s 0 = 1 ∨ s 0 = 2 ∨ s 1 = 1 ∨ s 1 = 2 ∨ s 2 = 1 ∨ s 2 = 2 ∨ s 3 = 1 ∨ s 3 = 2 ∨ s 4 = 1 ∨ s 4 = 2 ∨ s 5 = 1 ∨ s 5 = 2 ∨ s 6 = 1 ∨ s 6 = 2 ∨ s 7 = 1 ∨ s 7 = 2 ∨ s 8 = 1 ∨ s 8 = 2 ∨ s 9 = 1 ∨ s 9 = 2 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 11 = 1 ∨ s 11 = 2 ∨ s 12 = 1 ∨ s 12 = 2 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 15 = 1 ∨ s 15 = 2 ∨ s 16 = 1 ∨ s 16 = 2 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 18 = 1 ∨ s 18 = 2 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 20 = 1 ∨ s 20 = 2 ∨ s 21 = 1 ∨ s 21 = 2 ∨ s 22 = 1 ∨ s 22 = 2 ∨ s 23 = 1 ∨ s 23 = 2 ∨ s 24 = 1 ∨ s 24 = 2 ∨ s 25 = 1 ∨ s 25 = 2 ∨ s 26 = 1 ∨ s 26 = 2 ∨ s 27 = 1 ∨ s 27 = 2 ∨ s 28 = 1 ∨ s 28 = 2 ∨ s 29 = 1 ∨ s 29 = 2 ∨ s 30 = 1 ∨ s 30 = 2 ∨ s 31 = 1 ∨ s 31 = 2 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 33 = 1 ∨ s 33 = 2 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 35 = 1 ∨ s 35 = 2 ∨ s 36 = 1 ∨ s 36 = 2 ∨ s 37 = 1 ∨ s 37 = 2 ∨ s 38 = 1 ∨ s 38 = 2 ∨ s 39 = 1 ∨ s 39 = 2 ∨ s 40 = 1 ∨ s 40 = 2 ∨ s 41 = 1 ∨ s 41 = 2 ∨ s 42 = 1 ∨ s 42 = 2 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 44 = 1 ∨ s 44 = 2 ∨ s 45 = 1 ∨ s 45 = 2 ∨ s 46 = 1 ∨ s 46 = 2 ∨ s 47 = 1 ∨ s 47 = 2 ∨ s 48 = 1 ∨ s 48 = 2 ∨ s 49 = 1 ∨ s 49 = 2 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 52 = 1 ∨ s 52 = 2 ∨ s 53 = 1 ∨ s 53 = 2 ∨ s 54 = 1 ∨ s 54 = 2 ∨ s 55 = 1 ∨ s 55 = 2 ∨ s 56 = 1 ∨ s 56 = 2 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 59 = 1 ∨ s 59 = 2)
    : s 57 = 4 ∨ s 59 ≠ 4 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 59 ≠ 3 := (Or.elim c660 (fun h => h) (fun h => (False.elim (h a1))))
  have u1 : s 59 ≠ 2 := (Or.elim c659 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 59 ≠ 1 := (Or.elim c657 (fun h => h) (fun h => (False.elim (h a1))))
  have u3 : s 43 ≠ 0 := (Or.elim c2636 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u4 : s 59 ≠ 0 := (Or.elim c654 (fun h => h) (fun h => (False.elim (h a1))))
  have u5 : s 43 ≠ 2 := (Or.elim c2638 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u6 : s 52 ≠ 1 := (Or.elim c3002 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u7 : s 42 ≠ 0 := (Or.elim c2591 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u8 : s 42 ≠ 2 := (Or.elim c2593 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u9 : s 46 ≠ 1 := (Or.elim c2762 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u8 h))))))
  have u10 : s 45 ≠ 1 := (Or.elim c2717 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u8 h))))))
  have u11 : s 41 ≠ 0 := (Or.elim c2546 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u12 : s 41 ≠ 2 := (Or.elim c2548 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u13 : s 24 ≠ 1 := (Or.elim c1757 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u12 h))))))
  have u14 : s 20 ≠ 1 := (Or.elim c1597 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u12 h))))))
  have u15 : s 40 ≠ 0 := (Or.elim c2501 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u16 : s 40 ≠ 2 := (Or.elim c2503 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u17 : s 5 ≠ 1 := (Or.elim c892 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u16 h))))))
  have u18 : s 9 ≠ 1 := (Or.elim c1072 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u16 h))))))
  have u19 : s 39 ≠ 0 := (Or.elim c2456 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u20 : s 39 ≠ 2 := (Or.elim c2458 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u21 : s 26 ≠ 1 := (Or.elim c1857 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u20 h))))))
  have u22 : s 22 ≠ 1 := (Or.elim c1682 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u20 h))))))
  have u23 : s 7 ≠ 1 := (Or.elim c997 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u20 h))))))
  have u24 : s 18 ≠ 1 := (Or.elim c1502 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u20 h))))))
  have u25 : s 34 ≠ 0 := (Or.elim c2231 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u26 : s 34 ≠ 2 := (Or.elim c2233 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u27 : s 3 ≠ 1 := (Or.elim c807 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u26 h))))))
  have u28 : s 21 ≠ 1 := (Or.elim c1622 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u26 h))))))
  have u29 : s 11 ≠ 1 := (Or.elim c1167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u26 h))))))
  have u30 : s 6 ≠ 1 := (Or.elim c942 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u26 h))))))
  have u31 : s 29 ≠ 0 := (Or.elim c2006 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u32 : s 29 ≠ 2 := (Or.elim c2008 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u33 : s 2 ≠ 1 := (Or.elim c787 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u32 h))))))
  have u34 : s 48 ≠ 1 := (Or.elim c2862 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u32 h))))))
  have u35 : s 38 ≠ 1 := (Or.elim c2412 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u32 h))))))
  have u36 : s 49 ≠ 1 := (Or.elim c2897 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u37 : s 8 ≠ 1 := (Or.elim c1042 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u38 : s 54 ≠ 1 := (Or.elim c3107 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u39 : s 53 ≠ 1 := (Or.elim c3047 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u40 : s 51 ≠ 1 := (Or.elim c2957 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u41 : s 23 ≠ 1 := (Or.elim c1727 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u42 : s 43 ≠ 1 := (Or.elim c2637 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u43 : s 52 ≠ 2 := (Or.elim c3003 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u42 h))))))
  have u44 : s 40 ≠ 1 := (Or.elim c2502 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u45 : s 5 ≠ 2 := (Or.elim c893 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u44 h))))))
  have u46 : s 9 ≠ 2 := (Or.elim c1073 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u44 h))))))
  have u47 : s 29 ≠ 1 := (Or.elim c2007 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u48 : s 2 ≠ 2 := (Or.elim c788 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u47 h))))))
  have u49 : s 38 ≠ 2 := (Or.elim c2413 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u47 h))))))
  have u50 : s 14 ≠ 1 := (Or.elim c1332 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u51 : s 14 ≠ 0 := (Or.elim c1331 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u52 : s 32 ≠ 2 := (Or.elim c2133 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u50 h))))))
  have u53 : s 17 ≠ 2 := (Or.elim c1463 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u50 h))))))
  have u54 : s 14 ≠ 2 := (Or.elim c1333 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u55 : s 57 ≠ 1 := (Or.elim c3252 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u54 h))))))
  have u56 : s 53 ≠ 2 := (Or.elim c3048 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u42 h))))))
  have u57 : s 51 ≠ 2 := (Or.elim c2958 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u42 h))))))
  have u58 : s 50 ≠ 2 := (Or.elim c2938 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u42 h))))))
  have u59 : s 42 ≠ 1 := (Or.elim c2592 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u60 : s 47 ≠ 2 := (Or.elim c2813 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u59 h))))))
  have u61 : s 46 ≠ 2 := (Or.elim c2763 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u59 h))))))
  have u62 : s 48 ≠ 2 := (Or.elim c2833 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u59 h))))))
  have u63 : s 45 ≠ 2 := (Or.elim c2718 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u59 h))))))
  have u64 : s 41 ≠ 1 := (Or.elim c2547 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u65 : s 24 ≠ 2 := (Or.elim c1758 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u64 h))))))
  have u66 : s 20 ≠ 2 := (Or.elim c1598 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u64 h))))))
  have u67 : s 49 ≠ 2 := (Or.elim c2873 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u44 h))))))
  have u68 : s 54 ≠ 2 := (Or.elim c3093 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u44 h))))))
  have u69 : s 23 ≠ 2 := (Or.elim c1713 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u44 h))))))
  have u70 : s 8 ≠ 2 := (Or.elim c1028 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u44 h))))))
  have u71 : s 39 ≠ 1 := (Or.elim c2457 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u72 : s 55 ≠ 2 := (Or.elim c3143 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u71 h))))))
  have u73 : s 26 ≠ 2 := (Or.elim c1858 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u71 h))))))
  have u74 : s 22 ≠ 2 := (Or.elim c1683 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u71 h))))))
  have u75 : s 7 ≠ 2 := (Or.elim c998 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u71 h))))))
  have u76 : s 56 ≠ 2 := (Or.elim c3188 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u71 h))))))
  have u77 : s 18 ≠ 2 := (Or.elim c1503 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u71 h))))))
  have u78 : s 34 ≠ 1 := (Or.elim c2232 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u79 : s 3 ≠ 2 := (Or.elim c808 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u78 h))))))
  have u80 : s 21 ≠ 2 := (Or.elim c1623 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u78 h))))))
  have u81 : s 11 ≠ 2 := (Or.elim c1168 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u78 h))))))
  have u82 : s 6 ≠ 2 := (Or.elim c943 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u78 h))))))
  have u83 : s 58 ≠ 1 := (Or.elim c3307 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u54 h))))))
  have u84 : s 56 ≠ 1 := (Or.elim c3197 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u54 h))))))
  have u85 : s 55 ≠ 1 := (Or.elim c3167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u54 h))))))
  have u86 : s 50 ≠ 1 := (Or.elim c2932 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u54 h))))))
  have u87 : s 47 ≠ 1 := (Or.elim c2807 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u54 h))))))
  have u88 : s 32 ≠ 1 := (Or.elim c2132 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u54 h))))))
  have u89 : s 17 ≠ 1 := (Or.elim c1462 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u54 h))))))
  have u90 : s 58 ≠ 2 := (Or.elim c3308 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u50 h))))))
  have u91 : s 57 ≠ 2 := (Or.elim c3253 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u50 h))))))
  have u92 : s 44 ≠ 2 := (Or.elim c2683 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u93 : s 44 ≠ 1 := (Or.elim c2682 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u94 : s 57 = 3 := (Or.elim c3363 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (h a1))))))
  have u95 : s 57 ≠ 0 := (Or.elim c631 (fun h => h) (fun h => (False.elim (h u94))))
  have u96 : s 14 ≠ 3 := (Or.elim c1324 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u95 h))) (fun h => (False.elim (a0 h))))))
  have u97 : s 29 ≠ 3 := (Or.elim c1999 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u95 h))) (fun h => (False.elim (a0 h))))))
  have u98 : s 30 ≠ 3 := (Or.elim c2054 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u95 h))) (fun h => (False.elim (a0 h))))))
  have u99 : s 31 ≠ 1 := (Or.elim c2097 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u95 h))) (fun h => (False.elim (u91 h))))))
  have u100 : s 30 ≠ 1 := (Or.elim c2052 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u95 h))) (fun h => (False.elim (u91 h))))))
  have u101 : s 33 ≠ 1 := (Or.elim c2187 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u95 h))) (fun h => (False.elim (u91 h))))))
  have u102 : s 30 ≠ 2 := (Or.elim c2053 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u95 h))) (fun h => (False.elim (u55 h))))))
  have u103 : s 31 ≠ 2 := (Or.elim c2098 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u95 h))) (fun h => (False.elim (u55 h))))))
  have u104 : s 33 ≠ 2 := (Or.elim c2188 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u95 h))) (fun h => (False.elim (u55 h))))))
  have u105 : s 56 ≠ 0 := (Or.elim c3196 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (Or.elim h (fun h => (False.elim (u54 h))) (fun h => (False.elim (u96 h))))))))
  have u106 : s 58 ≠ 0 := (Or.elim c3306 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (Or.elim h (fun h => (False.elim (u54 h))) (fun h => (False.elim (u96 h))))))))
  have u107 : s 55 ≠ 0 := (Or.elim c3166 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (Or.elim h (fun h => (False.elim (u54 h))) (fun h => (False.elim (u96 h))))))))
  have u108 : s 50 ≠ 0 := (Or.elim c2931 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (Or.elim h (fun h => (False.elim (u54 h))) (fun h => (False.elim (u96 h))))))))
  have u109 : s 47 ≠ 0 := (Or.elim c2806 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (Or.elim h (fun h => (False.elim (u54 h))) (fun h => (False.elim (u96 h))))))))
  have u110 : s 17 ≠ 0 := (Or.elim c1461 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (Or.elim h (fun h => (False.elim (u54 h))) (fun h => (False.elim (u96 h))))))))
  have u111 : s 2 ≠ 0 := (Or.elim c786 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u47 h))) (fun h => (Or.elim h (fun h => (False.elim (u32 h))) (fun h => (False.elim (u97 h))))))))
  have u112 : s 6 ≠ 0 := (Or.elim c966 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u100 h))) (fun h => (Or.elim h (fun h => (False.elim (u102 h))) (fun h => (False.elim (u98 h))))))))
  have u113 : s 21 ≠ 0 := (Or.elim c1641 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u100 h))) (fun h => (Or.elim h (fun h => (False.elim (u102 h))) (fun h => (False.elim (u98 h))))))))
  have u114 : s 25 ≠ 1 := (Or.elim c1827 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u105 h))) (fun h => (False.elim (u76 h))))))
  have u115 : s 25 ≠ 2 := (Or.elim c1828 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u105 h))) (fun h => (False.elim (u84 h))))))
  have u116 : s 28 ≠ 2 := (Or.elim c1963 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u105 h))) (fun h => (False.elim (u84 h))))))
  have u117 : s 27 ≠ 2 := (Or.elim c1918 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u105 h))) (fun h => (False.elim (u84 h))))))
  have u118 : s 28 ≠ 1 := (Or.elim c1962 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u105 h))) (fun h => (False.elim (u76 h))))))
  have u119 : s 27 ≠ 1 := (Or.elim c1917 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u105 h))) (fun h => (False.elim (u76 h))))))
  have u120 : s 35 ≠ 1 := (Or.elim c2237 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u106 h))) (fun h => (False.elim (u90 h))))))
  have u121 : s 36 ≠ 1 := (Or.elim c2282 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u106 h))) (fun h => (False.elim (u90 h))))))
  have u122 : s 37 ≠ 1 := (Or.elim c2327 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u106 h))) (fun h => (False.elim (u90 h))))))
  have u123 : s 35 ≠ 2 := (Or.elim c2238 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u106 h))) (fun h => (False.elim (u83 h))))))
  have u124 : s 36 ≠ 2 := (Or.elim c2283 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u106 h))) (fun h => (False.elim (u83 h))))))
  have u125 : s 37 ≠ 2 := (Or.elim c2328 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u106 h))) (fun h => (False.elim (u83 h))))))
  have u126 : s 10 ≠ 1 := (Or.elim c1152 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u107 h))) (fun h => (False.elim (u72 h))))))
  have u127 : s 10 ≠ 2 := (Or.elim c1153 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u107 h))) (fun h => (False.elim (u85 h))))))
  have u128 : s 12 ≠ 1 := (Or.elim c1242 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u107 h))) (fun h => (False.elim (u72 h))))))
  have u129 : s 13 ≠ 1 := (Or.elim c1287 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u107 h))) (fun h => (False.elim (u72 h))))))
  have u130 : s 12 ≠ 2 := (Or.elim c1243 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u107 h))) (fun h => (False.elim (u85 h))))))
  have u131 : s 13 ≠ 2 := (Or.elim c1288 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u107 h))) (fun h => (False.elim (u85 h))))))
  have u132 : s 19 ≠ 1 := (Or.elim c1537 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u108 h))) (fun h => (False.elim (u58 h))))))
  have u133 : s 19 ≠ 2 := (Or.elim c1538 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u108 h))) (fun h => (False.elim (u86 h))))))
  have u134 : s 4 ≠ 1 := (Or.elim c857 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u109 h))) (fun h => (False.elim (u60 h))))))
  have u135 : s 4 ≠ 2 := (Or.elim c858 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u109 h))) (fun h => (False.elim (u87 h))))))
  have u136 : s 0 ≠ 1 := (Or.elim c677 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u110 h))) (fun h => (False.elim (u53 h))))))
  have u137 : s 0 ≠ 2 := (Or.elim c678 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u110 h))) (fun h => (False.elim (u89 h))))))
  have u138 : s 15 ≠ 1 := (Or.elim c1347 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u111 h))) (fun h => (False.elim (u48 h))))))
  have u139 : s 15 ≠ 2 := (Or.elim c1348 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u111 h))) (fun h => (False.elim (u33 h))))))
  have u140 : s 16 ≠ 1 := (Or.elim c1397 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u112 h))) (fun h => (False.elim (u82 h))))))
  have u141 : s 16 ≠ 2 := (Or.elim c1398 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u112 h))) (fun h => (False.elim (u30 h))))))
  have u142 : s 1 ≠ 1 := (Or.elim c722 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u113 h))) (fun h => (False.elim (u80 h))))))
  have u143 : s 1 ≠ 2 := (Or.elim c723 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u113 h))) (fun h => (False.elim (u28 h))))))
  exact (Or.elim c3361 (fun h => (u136 h)) (fun h => (Or.elim h (fun h => (u137 h)) (fun h => (Or.elim h (fun h => (u142 h)) (fun h => (Or.elim h (fun h => (u143 h)) (fun h => (Or.elim h (fun h => (u33 h)) (fun h => (Or.elim h (fun h => (u48 h)) (fun h => (Or.elim h (fun h => (u27 h)) (fun h => (Or.elim h (fun h => (u79 h)) (fun h => (Or.elim h (fun h => (u134 h)) (fun h => (Or.elim h (fun h => (u135 h)) (fun h => (Or.elim h (fun h => (u17 h)) (fun h => (Or.elim h (fun h => (u45 h)) (fun h => (Or.elim h (fun h => (u30 h)) (fun h => (Or.elim h (fun h => (u82 h)) (fun h => (Or.elim h (fun h => (u23 h)) (fun h => (Or.elim h (fun h => (u75 h)) (fun h => (Or.elim h (fun h => (u37 h)) (fun h => (Or.elim h (fun h => (u70 h)) (fun h => (Or.elim h (fun h => (u18 h)) (fun h => (Or.elim h (fun h => (u46 h)) (fun h => (Or.elim h (fun h => (u126 h)) (fun h => (Or.elim h (fun h => (u127 h)) (fun h => (Or.elim h (fun h => (u29 h)) (fun h => (Or.elim h (fun h => (u81 h)) (fun h => (Or.elim h (fun h => (u128 h)) (fun h => (Or.elim h (fun h => (u130 h)) (fun h => (Or.elim h (fun h => (u129 h)) (fun h => (Or.elim h (fun h => (u131 h)) (fun h => (Or.elim h (fun h => (u50 h)) (fun h => (Or.elim h (fun h => (u54 h)) (fun h => (Or.elim h (fun h => (u138 h)) (fun h => (Or.elim h (fun h => (u139 h)) (fun h => (Or.elim h (fun h => (u140 h)) (fun h => (Or.elim h (fun h => (u141 h)) (fun h => (Or.elim h (fun h => (u89 h)) (fun h => (Or.elim h (fun h => (u53 h)) (fun h => (Or.elim h (fun h => (u24 h)) (fun h => (Or.elim h (fun h => (u77 h)) (fun h => (Or.elim h (fun h => (u132 h)) (fun h => (Or.elim h (fun h => (u133 h)) (fun h => (Or.elim h (fun h => (u14 h)) (fun h => (Or.elim h (fun h => (u66 h)) (fun h => (Or.elim h (fun h => (u28 h)) (fun h => (Or.elim h (fun h => (u80 h)) (fun h => (Or.elim h (fun h => (u22 h)) (fun h => (Or.elim h (fun h => (u74 h)) (fun h => (Or.elim h (fun h => (u41 h)) (fun h => (Or.elim h (fun h => (u69 h)) (fun h => (Or.elim h (fun h => (u13 h)) (fun h => (Or.elim h (fun h => (u65 h)) (fun h => (Or.elim h (fun h => (u114 h)) (fun h => (Or.elim h (fun h => (u115 h)) (fun h => (Or.elim h (fun h => (u21 h)) (fun h => (Or.elim h (fun h => (u73 h)) (fun h => (Or.elim h (fun h => (u119 h)) (fun h => (Or.elim h (fun h => (u117 h)) (fun h => (Or.elim h (fun h => (u118 h)) (fun h => (Or.elim h (fun h => (u116 h)) (fun h => (Or.elim h (fun h => (u47 h)) (fun h => (Or.elim h (fun h => (u32 h)) (fun h => (Or.elim h (fun h => (u100 h)) (fun h => (Or.elim h (fun h => (u102 h)) (fun h => (Or.elim h (fun h => (u99 h)) (fun h => (Or.elim h (fun h => (u103 h)) (fun h => (Or.elim h (fun h => (u88 h)) (fun h => (Or.elim h (fun h => (u52 h)) (fun h => (Or.elim h (fun h => (u101 h)) (fun h => (Or.elim h (fun h => (u104 h)) (fun h => (Or.elim h (fun h => (u78 h)) (fun h => (Or.elim h (fun h => (u26 h)) (fun h => (Or.elim h (fun h => (u120 h)) (fun h => (Or.elim h (fun h => (u123 h)) (fun h => (Or.elim h (fun h => (u121 h)) (fun h => (Or.elim h (fun h => (u124 h)) (fun h => (Or.elim h (fun h => (u122 h)) (fun h => (Or.elim h (fun h => (u125 h)) (fun h => (Or.elim h (fun h => (u35 h)) (fun h => (Or.elim h (fun h => (u49 h)) (fun h => (Or.elim h (fun h => (u71 h)) (fun h => (Or.elim h (fun h => (u20 h)) (fun h => (Or.elim h (fun h => (u44 h)) (fun h => (Or.elim h (fun h => (u16 h)) (fun h => (Or.elim h (fun h => (u64 h)) (fun h => (Or.elim h (fun h => (u12 h)) (fun h => (Or.elim h (fun h => (u59 h)) (fun h => (Or.elim h (fun h => (u8 h)) (fun h => (Or.elim h (fun h => (u42 h)) (fun h => (Or.elim h (fun h => (u5 h)) (fun h => (Or.elim h (fun h => (u93 h)) (fun h => (Or.elim h (fun h => (u92 h)) (fun h => (Or.elim h (fun h => (u10 h)) (fun h => (Or.elim h (fun h => (u63 h)) (fun h => (Or.elim h (fun h => (u9 h)) (fun h => (Or.elim h (fun h => (u61 h)) (fun h => (Or.elim h (fun h => (u87 h)) (fun h => (Or.elim h (fun h => (u60 h)) (fun h => (Or.elim h (fun h => (u34 h)) (fun h => (Or.elim h (fun h => (u62 h)) (fun h => (Or.elim h (fun h => (u36 h)) (fun h => (Or.elim h (fun h => (u67 h)) (fun h => (Or.elim h (fun h => (u86 h)) (fun h => (Or.elim h (fun h => (u58 h)) (fun h => (Or.elim h (fun h => (u40 h)) (fun h => (Or.elim h (fun h => (u57 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (u43 h)) (fun h => (Or.elim h (fun h => (u39 h)) (fun h => (Or.elim h (fun h => (u56 h)) (fun h => (Or.elim h (fun h => (u38 h)) (fun h => (Or.elim h (fun h => (u68 h)) (fun h => (Or.elim h (fun h => (u85 h)) (fun h => (Or.elim h (fun h => (u72 h)) (fun h => (Or.elim h (fun h => (u84 h)) (fun h => (Or.elim h (fun h => (u76 h)) (fun h => (Or.elim h (fun h => (u55 h)) (fun h => (Or.elim h (fun h => (u91 h)) (fun h => (Or.elim h (fun h => (u83 h)) (fun h => (Or.elim h (fun h => (u90 h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (u1 h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem step3366 (s : Fin 60 → Fin 5)
    (c660 : s 59 ≠ 3 ∨ s 59 ≠ 4)
    (c659 : s 59 ≠ 2 ∨ s 59 ≠ 4)
    (c657 : s 59 ≠ 1 ∨ s 59 ≠ 4)
    (c1331 : s 14 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c654 : s 59 ≠ 0 ∨ s 59 ≠ 4)
    (c1333 : s 14 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c2132 : s 32 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3252 : s 57 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c1332 : s 14 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c3253 : s 57 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c3365 : s 57 = 4 ∨ s 59 ≠ 4)
    (c638 : s 57 ≠ 3 ∨ s 57 ≠ 4)
    (c2141 : s 32 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c1248 : s 13 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1203 : s 12 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1113 : s 10 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c2133 : s 32 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c1247 : s 13 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1202 : s 12 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1112 : s 10 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c632 : s 57 ≠ 0 ∨ s 57 ≠ 4)
    (c2053 : s 30 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2051 : s 30 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c702 : s 0 ≠ 1 ∨ s 30 = 0 ∨ s 30 = 2)
    (c882 : s 4 ≠ 1 ∨ s 30 = 0 ∨ s 30 = 2)
    (c747 : s 1 ≠ 1 ∨ s 30 = 0 ∨ s 30 = 2)
    (c2052 : s 30 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c883 : s 4 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1)
    (c748 : s 1 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1)
    (c703 : s 0 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1)
    (c2188 : s 33 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2098 : s 31 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2187 : s 33 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2097 : s 31 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c3364 : s 58 ≠ 4 ∨ s 59 ≠ 4)
    (c2636 : s 43 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2638 : s 43 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c3002 : s 52 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c2591 : s 42 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2593 : s 42 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c2762 : s 46 ≠ 1 ∨ s 42 = 0 ∨ s 42 = 2)
    (c2717 : s 45 ≠ 1 ∨ s 42 = 0 ∨ s 42 = 2)
    (c2546 : s 41 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2548 : s 41 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c1757 : s 24 ≠ 1 ∨ s 41 = 0 ∨ s 41 = 2)
    (c1597 : s 20 ≠ 1 ∨ s 41 = 0 ∨ s 41 = 2)
    (c2501 : s 40 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2503 : s 40 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c892 : s 5 ≠ 1 ∨ s 40 = 0 ∨ s 40 = 2)
    (c1072 : s 9 ≠ 1 ∨ s 40 = 0 ∨ s 40 = 2)
    (c2456 : s 39 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2458 : s 39 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c1857 : s 26 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    (c1682 : s 22 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    (c997 : s 7 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    (c1502 : s 18 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    (c2231 : s 34 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2233 : s 34 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c807 : s 3 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c1622 : s 21 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c1167 : s 11 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c942 : s 6 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c2006 : s 29 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2008 : s 29 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c787 : s 2 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2)
    (c2862 : s 48 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2)
    (c2412 : s 38 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2)
    (c2897 : s 49 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c1042 : s 8 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c3107 : s 54 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c3047 : s 53 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c2957 : s 51 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c1727 : s 23 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c2637 : s 43 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c3003 : s 52 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c2502 : s 40 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c893 : s 5 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c1073 : s 9 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c2007 : s 29 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c788 : s 2 ≠ 2 ∨ s 29 = 0 ∨ s 29 = 1)
    (c2413 : s 38 ≠ 2 ∨ s 29 = 0 ∨ s 29 = 1)
    (c1463 : s 17 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c3048 : s 53 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c2958 : s 51 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c2938 : s 50 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c2592 : s 42 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c2813 : s 47 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1)
    (c2763 : s 46 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1)
    (c2833 : s 48 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1)
    (c2718 : s 45 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1)
    (c2547 : s 41 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c1758 : s 24 ≠ 2 ∨ s 41 = 0 ∨ s 41 = 1)
    (c1598 : s 20 ≠ 2 ∨ s 41 = 0 ∨ s 41 = 1)
    (c2873 : s 49 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c3093 : s 54 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c1713 : s 23 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c1028 : s 8 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1)
    (c2457 : s 39 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c3143 : s 55 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c1858 : s 26 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c1683 : s 22 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c998 : s 7 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c3188 : s 56 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c1503 : s 18 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c2232 : s 34 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c808 : s 3 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c1623 : s 21 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c1168 : s 11 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c943 : s 6 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c3307 : s 58 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3197 : s 56 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3167 : s 55 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c2932 : s 50 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c2807 : s 47 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c1462 : s 17 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3308 : s 58 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c2683 : s 44 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c2682 : s 44 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c3196 : s 56 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c3306 : s 58 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2931 : s 50 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c1827 : s 25 ≠ 1 ∨ s 56 = 0 ∨ s 56 = 2)
    (c1828 : s 25 ≠ 2 ∨ s 56 = 0 ∨ s 56 = 1)
    (c1963 : s 28 ≠ 2 ∨ s 56 = 0 ∨ s 56 = 1)
    (c1918 : s 27 ≠ 2 ∨ s 56 = 0 ∨ s 56 = 1)
    (c1962 : s 28 ≠ 1 ∨ s 56 = 0 ∨ s 56 = 2)
    (c1917 : s 27 ≠ 1 ∨ s 56 = 0 ∨ s 56 = 2)
    (c2004 : s 29 ≠ 3 ∨ s 58 = 0 ∨ s 58 = 4)
    (c2229 : s 34 ≠ 3 ∨ s 58 = 0 ∨ s 58 = 4)
    (c2237 : s 35 ≠ 1 ∨ s 58 = 0 ∨ s 58 = 2)
    (c2282 : s 36 ≠ 1 ∨ s 58 = 0 ∨ s 58 = 2)
    (c2327 : s 37 ≠ 1 ∨ s 58 = 0 ∨ s 58 = 2)
    (c2238 : s 35 ≠ 2 ∨ s 58 = 0 ∨ s 58 = 1)
    (c2283 : s 36 ≠ 2 ∨ s 58 = 0 ∨ s 58 = 1)
    (c2328 : s 37 ≠ 2 ∨ s 58 = 0 ∨ s 58 = 1)
    (c1537 : s 19 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2)
    (c1538 : s 19 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1)
    (c786 : s 2 ≠ 0 ∨ s 29 = 1 ∨ s 29 = 2 ∨ s 29 = 3)
    (c941 : s 6 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3)
    (c1347 : s 15 ≠ 1 ∨ s 2 = 0 ∨ s 2 = 2)
    (c1348 : s 15 ≠ 2 ∨ s 2 = 0 ∨ s 2 = 1)
    (c1397 : s 16 ≠ 1 ∨ s 6 = 0 ∨ s 6 = 2)
    (c1398 : s 16 ≠ 2 ∨ s 6 = 0 ∨ s 6 = 1)
    (c3361 : s 0 = 1 ∨ s 0 = 2 ∨ s 1 = 1 ∨ s 1 = 2 ∨ s 2 = 1 ∨ s 2 = 2 ∨ s 3 = 1 ∨ s 3 = 2 ∨ s 4 = 1 ∨ s 4 = 2 ∨ s 5 = 1 ∨ s 5 = 2 ∨ s 6 = 1 ∨ s 6 = 2 ∨ s 7 = 1 ∨ s 7 = 2 ∨ s 8 = 1 ∨ s 8 = 2 ∨ s 9 = 1 ∨ s 9 = 2 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 11 = 1 ∨ s 11 = 2 ∨ s 12 = 1 ∨ s 12 = 2 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 15 = 1 ∨ s 15 = 2 ∨ s 16 = 1 ∨ s 16 = 2 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 18 = 1 ∨ s 18 = 2 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 20 = 1 ∨ s 20 = 2 ∨ s 21 = 1 ∨ s 21 = 2 ∨ s 22 = 1 ∨ s 22 = 2 ∨ s 23 = 1 ∨ s 23 = 2 ∨ s 24 = 1 ∨ s 24 = 2 ∨ s 25 = 1 ∨ s 25 = 2 ∨ s 26 = 1 ∨ s 26 = 2 ∨ s 27 = 1 ∨ s 27 = 2 ∨ s 28 = 1 ∨ s 28 = 2 ∨ s 29 = 1 ∨ s 29 = 2 ∨ s 30 = 1 ∨ s 30 = 2 ∨ s 31 = 1 ∨ s 31 = 2 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 33 = 1 ∨ s 33 = 2 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 35 = 1 ∨ s 35 = 2 ∨ s 36 = 1 ∨ s 36 = 2 ∨ s 37 = 1 ∨ s 37 = 2 ∨ s 38 = 1 ∨ s 38 = 2 ∨ s 39 = 1 ∨ s 39 = 2 ∨ s 40 = 1 ∨ s 40 = 2 ∨ s 41 = 1 ∨ s 41 = 2 ∨ s 42 = 1 ∨ s 42 = 2 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 44 = 1 ∨ s 44 = 2 ∨ s 45 = 1 ∨ s 45 = 2 ∨ s 46 = 1 ∨ s 46 = 2 ∨ s 47 = 1 ∨ s 47 = 2 ∨ s 48 = 1 ∨ s 48 = 2 ∨ s 49 = 1 ∨ s 49 = 2 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 52 = 1 ∨ s 52 = 2 ∨ s 53 = 1 ∨ s 53 = 2 ∨ s 54 = 1 ∨ s 54 = 2 ∨ s 55 = 1 ∨ s 55 = 2 ∨ s 56 = 1 ∨ s 56 = 2 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 59 = 1 ∨ s 59 = 2)
    : s 14 = 3 ∨ s 59 ≠ 4 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 59 ≠ 3 := (Or.elim c660 (fun h => h) (fun h => (False.elim (h a1))))
  have u1 : s 59 ≠ 2 := (Or.elim c659 (fun h => h) (fun h => (False.elim (h a1))))
  have u2 : s 59 ≠ 1 := (Or.elim c657 (fun h => h) (fun h => (False.elim (h a1))))
  have u3 : s 14 ≠ 0 := (Or.elim c1331 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u4 : s 59 ≠ 0 := (Or.elim c654 (fun h => h) (fun h => (False.elim (h a1))))
  have u5 : s 14 ≠ 2 := (Or.elim c1333 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u6 : s 32 ≠ 1 := (Or.elim c2132 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u7 : s 57 ≠ 1 := (Or.elim c3252 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u8 : s 14 ≠ 1 := (Or.elim c1332 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u9 : s 57 ≠ 2 := (Or.elim c3253 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u8 h))))))
  have u10 : s 57 = 4 := (Or.elim c3365 (fun h => h) (fun h => (False.elim (h a1))))
  have u11 : s 57 ≠ 3 := (Or.elim c638 (fun h => h) (fun h => (False.elim (h u10))))
  have u12 : s 32 ≠ 0 := (Or.elim c2141 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u11 h))))))))
  have u13 : s 13 ≠ 2 := (Or.elim c1248 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u6 h))))))
  have u14 : s 12 ≠ 2 := (Or.elim c1203 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u6 h))))))
  have u15 : s 10 ≠ 2 := (Or.elim c1113 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u6 h))))))
  have u16 : s 32 ≠ 2 := (Or.elim c2133 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u8 h))))))
  have u17 : s 13 ≠ 1 := (Or.elim c1247 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u16 h))))))
  have u18 : s 12 ≠ 1 := (Or.elim c1202 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u16 h))))))
  have u19 : s 10 ≠ 1 := (Or.elim c1112 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u16 h))))))
  have u20 : s 57 ≠ 0 := (Or.elim c632 (fun h => h) (fun h => (False.elim (h u10))))
  have u21 : s 30 ≠ 2 := (Or.elim c2053 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u7 h))))))
  have u22 : s 30 ≠ 0 := (Or.elim c2051 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u11 h))))))))
  have u23 : s 0 ≠ 1 := (Or.elim c702 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u21 h))))))
  have u24 : s 4 ≠ 1 := (Or.elim c882 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u21 h))))))
  have u25 : s 1 ≠ 1 := (Or.elim c747 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u21 h))))))
  have u26 : s 30 ≠ 1 := (Or.elim c2052 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u9 h))))))
  have u27 : s 4 ≠ 2 := (Or.elim c883 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u26 h))))))
  have u28 : s 1 ≠ 2 := (Or.elim c748 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u26 h))))))
  have u29 : s 0 ≠ 2 := (Or.elim c703 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u26 h))))))
  have u30 : s 33 ≠ 2 := (Or.elim c2188 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u7 h))))))
  have u31 : s 31 ≠ 2 := (Or.elim c2098 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u7 h))))))
  have u32 : s 33 ≠ 1 := (Or.elim c2187 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u9 h))))))
  have u33 : s 31 ≠ 1 := (Or.elim c2097 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u9 h))))))
  have u34 : s 58 ≠ 4 := (Or.elim c3364 (fun h => h) (fun h => (False.elim (h a1))))
  have u35 : s 43 ≠ 0 := (Or.elim c2636 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u36 : s 43 ≠ 2 := (Or.elim c2638 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u37 : s 52 ≠ 1 := (Or.elim c3002 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u36 h))))))
  have u38 : s 42 ≠ 0 := (Or.elim c2591 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u39 : s 42 ≠ 2 := (Or.elim c2593 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u40 : s 46 ≠ 1 := (Or.elim c2762 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u39 h))))))
  have u41 : s 45 ≠ 1 := (Or.elim c2717 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u39 h))))))
  have u42 : s 41 ≠ 0 := (Or.elim c2546 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u43 : s 41 ≠ 2 := (Or.elim c2548 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u44 : s 24 ≠ 1 := (Or.elim c1757 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u42 h))) (fun h => (False.elim (u43 h))))))
  have u45 : s 20 ≠ 1 := (Or.elim c1597 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u42 h))) (fun h => (False.elim (u43 h))))))
  have u46 : s 40 ≠ 0 := (Or.elim c2501 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u47 : s 40 ≠ 2 := (Or.elim c2503 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u48 : s 5 ≠ 1 := (Or.elim c892 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u46 h))) (fun h => (False.elim (u47 h))))))
  have u49 : s 9 ≠ 1 := (Or.elim c1072 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u46 h))) (fun h => (False.elim (u47 h))))))
  have u50 : s 39 ≠ 0 := (Or.elim c2456 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u51 : s 39 ≠ 2 := (Or.elim c2458 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u52 : s 26 ≠ 1 := (Or.elim c1857 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u51 h))))))
  have u53 : s 22 ≠ 1 := (Or.elim c1682 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u51 h))))))
  have u54 : s 7 ≠ 1 := (Or.elim c997 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u51 h))))))
  have u55 : s 18 ≠ 1 := (Or.elim c1502 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u51 h))))))
  have u56 : s 34 ≠ 0 := (Or.elim c2231 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u57 : s 34 ≠ 2 := (Or.elim c2233 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u58 : s 3 ≠ 1 := (Or.elim c807 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u56 h))) (fun h => (False.elim (u57 h))))))
  have u59 : s 21 ≠ 1 := (Or.elim c1622 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u56 h))) (fun h => (False.elim (u57 h))))))
  have u60 : s 11 ≠ 1 := (Or.elim c1167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u56 h))) (fun h => (False.elim (u57 h))))))
  have u61 : s 6 ≠ 1 := (Or.elim c942 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u56 h))) (fun h => (False.elim (u57 h))))))
  have u62 : s 29 ≠ 0 := (Or.elim c2006 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  have u63 : s 29 ≠ 2 := (Or.elim c2008 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u64 : s 2 ≠ 1 := (Or.elim c787 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u62 h))) (fun h => (False.elim (u63 h))))))
  have u65 : s 48 ≠ 1 := (Or.elim c2862 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u62 h))) (fun h => (False.elim (u63 h))))))
  have u66 : s 38 ≠ 1 := (Or.elim c2412 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u62 h))) (fun h => (False.elim (u63 h))))))
  have u67 : s 49 ≠ 1 := (Or.elim c2897 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u36 h))))))
  have u68 : s 8 ≠ 1 := (Or.elim c1042 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u36 h))))))
  have u69 : s 54 ≠ 1 := (Or.elim c3107 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u36 h))))))
  have u70 : s 53 ≠ 1 := (Or.elim c3047 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u36 h))))))
  have u71 : s 51 ≠ 1 := (Or.elim c2957 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u36 h))))))
  have u72 : s 23 ≠ 1 := (Or.elim c1727 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u36 h))))))
  have u73 : s 43 ≠ 1 := (Or.elim c2637 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u74 : s 52 ≠ 2 := (Or.elim c3003 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u73 h))))))
  have u75 : s 40 ≠ 1 := (Or.elim c2502 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u76 : s 5 ≠ 2 := (Or.elim c893 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u46 h))) (fun h => (False.elim (u75 h))))))
  have u77 : s 9 ≠ 2 := (Or.elim c1073 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u46 h))) (fun h => (False.elim (u75 h))))))
  have u78 : s 29 ≠ 1 := (Or.elim c2007 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u79 : s 2 ≠ 2 := (Or.elim c788 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u62 h))) (fun h => (False.elim (u78 h))))))
  have u80 : s 38 ≠ 2 := (Or.elim c2413 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u62 h))) (fun h => (False.elim (u78 h))))))
  have u81 : s 17 ≠ 2 := (Or.elim c1463 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u8 h))))))
  have u82 : s 53 ≠ 2 := (Or.elim c3048 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u73 h))))))
  have u83 : s 51 ≠ 2 := (Or.elim c2958 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u73 h))))))
  have u84 : s 50 ≠ 2 := (Or.elim c2938 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u73 h))))))
  have u85 : s 42 ≠ 1 := (Or.elim c2592 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u86 : s 47 ≠ 2 := (Or.elim c2813 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u85 h))))))
  have u87 : s 46 ≠ 2 := (Or.elim c2763 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u85 h))))))
  have u88 : s 48 ≠ 2 := (Or.elim c2833 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u85 h))))))
  have u89 : s 45 ≠ 2 := (Or.elim c2718 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u85 h))))))
  have u90 : s 41 ≠ 1 := (Or.elim c2547 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u91 : s 24 ≠ 2 := (Or.elim c1758 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u42 h))) (fun h => (False.elim (u90 h))))))
  have u92 : s 20 ≠ 2 := (Or.elim c1598 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u42 h))) (fun h => (False.elim (u90 h))))))
  have u93 : s 49 ≠ 2 := (Or.elim c2873 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u46 h))) (fun h => (False.elim (u75 h))))))
  have u94 : s 54 ≠ 2 := (Or.elim c3093 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u46 h))) (fun h => (False.elim (u75 h))))))
  have u95 : s 23 ≠ 2 := (Or.elim c1713 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u46 h))) (fun h => (False.elim (u75 h))))))
  have u96 : s 8 ≠ 2 := (Or.elim c1028 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u46 h))) (fun h => (False.elim (u75 h))))))
  have u97 : s 39 ≠ 1 := (Or.elim c2457 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u98 : s 55 ≠ 2 := (Or.elim c3143 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u97 h))))))
  have u99 : s 26 ≠ 2 := (Or.elim c1858 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u97 h))))))
  have u100 : s 22 ≠ 2 := (Or.elim c1683 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u97 h))))))
  have u101 : s 7 ≠ 2 := (Or.elim c998 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u97 h))))))
  have u102 : s 56 ≠ 2 := (Or.elim c3188 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u97 h))))))
  have u103 : s 18 ≠ 2 := (Or.elim c1503 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u97 h))))))
  have u104 : s 34 ≠ 1 := (Or.elim c2232 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u105 : s 3 ≠ 2 := (Or.elim c808 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u56 h))) (fun h => (False.elim (u104 h))))))
  have u106 : s 21 ≠ 2 := (Or.elim c1623 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u56 h))) (fun h => (False.elim (u104 h))))))
  have u107 : s 11 ≠ 2 := (Or.elim c1168 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u56 h))) (fun h => (False.elim (u104 h))))))
  have u108 : s 6 ≠ 2 := (Or.elim c943 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u56 h))) (fun h => (False.elim (u104 h))))))
  have u109 : s 58 ≠ 1 := (Or.elim c3307 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u110 : s 56 ≠ 1 := (Or.elim c3197 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u111 : s 55 ≠ 1 := (Or.elim c3167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u112 : s 50 ≠ 1 := (Or.elim c2932 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u113 : s 47 ≠ 1 := (Or.elim c2807 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u114 : s 17 ≠ 1 := (Or.elim c1462 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u115 : s 58 ≠ 2 := (Or.elim c3308 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u8 h))))))
  have u116 : s 44 ≠ 2 := (Or.elim c2683 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u117 : s 44 ≠ 1 := (Or.elim c2682 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u1 h))))))
  have u118 : s 56 ≠ 0 := (Or.elim c3196 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (a0 h))))))))
  have u119 : s 58 ≠ 0 := (Or.elim c3306 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (a0 h))))))))
  have u120 : s 50 ≠ 0 := (Or.elim c2931 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (a0 h))))))))
  have u121 : s 25 ≠ 1 := (Or.elim c1827 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u118 h))) (fun h => (False.elim (u102 h))))))
  have u122 : s 25 ≠ 2 := (Or.elim c1828 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u118 h))) (fun h => (False.elim (u110 h))))))
  have u123 : s 28 ≠ 2 := (Or.elim c1963 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u118 h))) (fun h => (False.elim (u110 h))))))
  have u124 : s 27 ≠ 2 := (Or.elim c1918 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u118 h))) (fun h => (False.elim (u110 h))))))
  have u125 : s 28 ≠ 1 := (Or.elim c1962 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u118 h))) (fun h => (False.elim (u102 h))))))
  have u126 : s 27 ≠ 1 := (Or.elim c1917 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u118 h))) (fun h => (False.elim (u102 h))))))
  have u127 : s 29 ≠ 3 := (Or.elim c2004 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u119 h))) (fun h => (False.elim (u34 h))))))
  have u128 : s 34 ≠ 3 := (Or.elim c2229 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u119 h))) (fun h => (False.elim (u34 h))))))
  have u129 : s 35 ≠ 1 := (Or.elim c2237 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u119 h))) (fun h => (False.elim (u115 h))))))
  have u130 : s 36 ≠ 1 := (Or.elim c2282 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u119 h))) (fun h => (False.elim (u115 h))))))
  have u131 : s 37 ≠ 1 := (Or.elim c2327 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u119 h))) (fun h => (False.elim (u115 h))))))
  have u132 : s 35 ≠ 2 := (Or.elim c2238 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u119 h))) (fun h => (False.elim (u109 h))))))
  have u133 : s 36 ≠ 2 := (Or.elim c2283 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u119 h))) (fun h => (False.elim (u109 h))))))
  have u134 : s 37 ≠ 2 := (Or.elim c2328 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u119 h))) (fun h => (False.elim (u109 h))))))
  have u135 : s 19 ≠ 1 := (Or.elim c1537 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u120 h))) (fun h => (False.elim (u84 h))))))
  have u136 : s 19 ≠ 2 := (Or.elim c1538 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u120 h))) (fun h => (False.elim (u112 h))))))
  have u137 : s 2 ≠ 0 := (Or.elim c786 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u78 h))) (fun h => (Or.elim h (fun h => (False.elim (u63 h))) (fun h => (False.elim (u127 h))))))))
  have u138 : s 6 ≠ 0 := (Or.elim c941 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u104 h))) (fun h => (Or.elim h (fun h => (False.elim (u57 h))) (fun h => (False.elim (u128 h))))))))
  have u139 : s 15 ≠ 1 := (Or.elim c1347 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u137 h))) (fun h => (False.elim (u79 h))))))
  have u140 : s 15 ≠ 2 := (Or.elim c1348 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u137 h))) (fun h => (False.elim (u64 h))))))
  have u141 : s 16 ≠ 1 := (Or.elim c1397 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u138 h))) (fun h => (False.elim (u108 h))))))
  have u142 : s 16 ≠ 2 := (Or.elim c1398 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u138 h))) (fun h => (False.elim (u61 h))))))
  exact (Or.elim c3361 (fun h => (u23 h)) (fun h => (Or.elim h (fun h => (u29 h)) (fun h => (Or.elim h (fun h => (u25 h)) (fun h => (Or.elim h (fun h => (u28 h)) (fun h => (Or.elim h (fun h => (u64 h)) (fun h => (Or.elim h (fun h => (u79 h)) (fun h => (Or.elim h (fun h => (u58 h)) (fun h => (Or.elim h (fun h => (u105 h)) (fun h => (Or.elim h (fun h => (u24 h)) (fun h => (Or.elim h (fun h => (u27 h)) (fun h => (Or.elim h (fun h => (u48 h)) (fun h => (Or.elim h (fun h => (u76 h)) (fun h => (Or.elim h (fun h => (u61 h)) (fun h => (Or.elim h (fun h => (u108 h)) (fun h => (Or.elim h (fun h => (u54 h)) (fun h => (Or.elim h (fun h => (u101 h)) (fun h => (Or.elim h (fun h => (u68 h)) (fun h => (Or.elim h (fun h => (u96 h)) (fun h => (Or.elim h (fun h => (u49 h)) (fun h => (Or.elim h (fun h => (u77 h)) (fun h => (Or.elim h (fun h => (u19 h)) (fun h => (Or.elim h (fun h => (u15 h)) (fun h => (Or.elim h (fun h => (u60 h)) (fun h => (Or.elim h (fun h => (u107 h)) (fun h => (Or.elim h (fun h => (u18 h)) (fun h => (Or.elim h (fun h => (u14 h)) (fun h => (Or.elim h (fun h => (u17 h)) (fun h => (Or.elim h (fun h => (u13 h)) (fun h => (Or.elim h (fun h => (u8 h)) (fun h => (Or.elim h (fun h => (u5 h)) (fun h => (Or.elim h (fun h => (u139 h)) (fun h => (Or.elim h (fun h => (u140 h)) (fun h => (Or.elim h (fun h => (u141 h)) (fun h => (Or.elim h (fun h => (u142 h)) (fun h => (Or.elim h (fun h => (u114 h)) (fun h => (Or.elim h (fun h => (u81 h)) (fun h => (Or.elim h (fun h => (u55 h)) (fun h => (Or.elim h (fun h => (u103 h)) (fun h => (Or.elim h (fun h => (u135 h)) (fun h => (Or.elim h (fun h => (u136 h)) (fun h => (Or.elim h (fun h => (u45 h)) (fun h => (Or.elim h (fun h => (u92 h)) (fun h => (Or.elim h (fun h => (u59 h)) (fun h => (Or.elim h (fun h => (u106 h)) (fun h => (Or.elim h (fun h => (u53 h)) (fun h => (Or.elim h (fun h => (u100 h)) (fun h => (Or.elim h (fun h => (u72 h)) (fun h => (Or.elim h (fun h => (u95 h)) (fun h => (Or.elim h (fun h => (u44 h)) (fun h => (Or.elim h (fun h => (u91 h)) (fun h => (Or.elim h (fun h => (u121 h)) (fun h => (Or.elim h (fun h => (u122 h)) (fun h => (Or.elim h (fun h => (u52 h)) (fun h => (Or.elim h (fun h => (u99 h)) (fun h => (Or.elim h (fun h => (u126 h)) (fun h => (Or.elim h (fun h => (u124 h)) (fun h => (Or.elim h (fun h => (u125 h)) (fun h => (Or.elim h (fun h => (u123 h)) (fun h => (Or.elim h (fun h => (u78 h)) (fun h => (Or.elim h (fun h => (u63 h)) (fun h => (Or.elim h (fun h => (u26 h)) (fun h => (Or.elim h (fun h => (u21 h)) (fun h => (Or.elim h (fun h => (u33 h)) (fun h => (Or.elim h (fun h => (u31 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (u16 h)) (fun h => (Or.elim h (fun h => (u32 h)) (fun h => (Or.elim h (fun h => (u30 h)) (fun h => (Or.elim h (fun h => (u104 h)) (fun h => (Or.elim h (fun h => (u57 h)) (fun h => (Or.elim h (fun h => (u129 h)) (fun h => (Or.elim h (fun h => (u132 h)) (fun h => (Or.elim h (fun h => (u130 h)) (fun h => (Or.elim h (fun h => (u133 h)) (fun h => (Or.elim h (fun h => (u131 h)) (fun h => (Or.elim h (fun h => (u134 h)) (fun h => (Or.elim h (fun h => (u66 h)) (fun h => (Or.elim h (fun h => (u80 h)) (fun h => (Or.elim h (fun h => (u97 h)) (fun h => (Or.elim h (fun h => (u51 h)) (fun h => (Or.elim h (fun h => (u75 h)) (fun h => (Or.elim h (fun h => (u47 h)) (fun h => (Or.elim h (fun h => (u90 h)) (fun h => (Or.elim h (fun h => (u43 h)) (fun h => (Or.elim h (fun h => (u85 h)) (fun h => (Or.elim h (fun h => (u39 h)) (fun h => (Or.elim h (fun h => (u73 h)) (fun h => (Or.elim h (fun h => (u36 h)) (fun h => (Or.elim h (fun h => (u117 h)) (fun h => (Or.elim h (fun h => (u116 h)) (fun h => (Or.elim h (fun h => (u41 h)) (fun h => (Or.elim h (fun h => (u89 h)) (fun h => (Or.elim h (fun h => (u40 h)) (fun h => (Or.elim h (fun h => (u87 h)) (fun h => (Or.elim h (fun h => (u113 h)) (fun h => (Or.elim h (fun h => (u86 h)) (fun h => (Or.elim h (fun h => (u65 h)) (fun h => (Or.elim h (fun h => (u88 h)) (fun h => (Or.elim h (fun h => (u67 h)) (fun h => (Or.elim h (fun h => (u93 h)) (fun h => (Or.elim h (fun h => (u112 h)) (fun h => (Or.elim h (fun h => (u84 h)) (fun h => (Or.elim h (fun h => (u71 h)) (fun h => (Or.elim h (fun h => (u83 h)) (fun h => (Or.elim h (fun h => (u37 h)) (fun h => (Or.elim h (fun h => (u74 h)) (fun h => (Or.elim h (fun h => (u70 h)) (fun h => (Or.elim h (fun h => (u82 h)) (fun h => (Or.elim h (fun h => (u69 h)) (fun h => (Or.elim h (fun h => (u94 h)) (fun h => (Or.elim h (fun h => (u111 h)) (fun h => (Or.elim h (fun h => (u98 h)) (fun h => (Or.elim h (fun h => (u110 h)) (fun h => (Or.elim h (fun h => (u102 h)) (fun h => (Or.elim h (fun h => (u7 h)) (fun h => (Or.elim h (fun h => (u9 h)) (fun h => (Or.elim h (fun h => (u109 h)) (fun h => (Or.elim h (fun h => (u115 h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (u1 h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem step3367 (s : Fin 60 → Fin 5)
    (c654 : s 59 ≠ 0 ∨ s 59 ≠ 4)
    (c657 : s 59 ≠ 1 ∨ s 59 ≠ 4)
    (c659 : s 59 ≠ 2 ∨ s 59 ≠ 4)
    (c660 : s 59 ≠ 3 ∨ s 59 ≠ 4)
    (c1332 : s 14 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c1333 : s 14 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c2007 : s 29 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c1331 : s 14 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2008 : s 29 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c3308 : s 58 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c3307 : s 58 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3364 : s 58 ≠ 4 ∨ s 59 ≠ 4)
    (c3366 : s 14 = 3 ∨ s 59 ≠ 4)
    (c165 : s 14 ≠ 3 ∨ s 14 ≠ 4)
    (c1329 : s 14 ≠ 3 ∨ s 58 = 0 ∨ s 58 = 4)
    (c3309 : s 58 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c3311 : s 58 ≠ 0 ∨ s 29 = 1 ∨ s 29 = 2 ∨ s 29 = 3)
    (c2371 : s 38 ≠ 0 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 58 = 3)
    (c2375 : s 38 ≠ 4 ∨ s 58 = 3 ∨ s 58 = 4)
    (c1974 : s 29 ≠ 3 ∨ s 38 = 0 ∨ s 38 = 4)
    : s 59 ≠ 4 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 59 ≠ 0 := (Or.elim c654 (fun h => h) (fun h => (False.elim (h hc))))
  have u1 : s 59 ≠ 1 := (Or.elim c657 (fun h => h) (fun h => (False.elim (h hc))))
  have u2 : s 59 ≠ 2 := (Or.elim c659 (fun h => h) (fun h => (False.elim (h hc))))
  have u3 : s 59 ≠ 3 := (Or.elim c660 (fun h => h) (fun h => (False.elim (h hc))))
  have u4 : s 14 ≠ 1 := (Or.elim c1332 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (u2 h))))))
  have u5 : s 14 ≠ 2 := (Or.elim c1333 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (u1 h))))))
  have u6 : s 29 ≠ 1 := (Or.elim c2007 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (u2 h))))))
  have u7 : s 14 ≠ 0 := (Or.elim c1331 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u3 h))))))))
  have u8 : s 29 ≠ 2 := (Or.elim c2008 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (u1 h))))))
  have u9 : s 58 ≠ 2 := (Or.elim c3308 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u4 h))))))
  have u10 : s 58 ≠ 1 := (Or.elim c3307 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u5 h))))))
  have u11 : s 58 ≠ 4 := (Or.elim c3364 (fun h => h) (fun h => (False.elim (h hc))))
  have u12 : s 14 = 3 := (Or.elim c3366 (fun h => h) (fun h => (False.elim (h hc))))
  have u13 : s 14 ≠ 4 := (Or.elim c165 (fun h => (False.elim (h u12))) (fun h => h))
  have u14 : s 58 = 0 := (Or.elim c1329 (fun h => (False.elim (h u12))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u11 h))))))
  have u15 : s 58 ≠ 3 := (Or.elim c3309 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u13 h))))))
  have u16 : s 29 = 3 := (Or.elim c3311 (fun h => (False.elim (h u14))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => h))))))
  have u17 : s 38 ≠ 0 := (Or.elim c2371 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u15 h))))))))
  have u18 : s 38 ≠ 4 := (Or.elim c2375 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u11 h))))))
  exact (Or.elim c1974 (fun h => (h u16)) (fun h => (Or.elim h (fun h => (u17 h)) (fun h => (u18 h)))))

private theorem step3368 (s : Fin 60 → Fin 5)
    (c3367 : s 59 ≠ 4)
    (c158 : s 14 ≠ 0 ∨ s 14 ≠ 3)
    (c165 : s 14 ≠ 3 ∨ s 14 ≠ 4)
    (c3352 : s 59 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3353 : s 59 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c3354 : s 59 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c1463 : s 17 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c2133 : s 32 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c2808 : s 47 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c2933 : s 50 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c3168 : s 55 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c3198 : s 56 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c1462 : s 17 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c2132 : s 32 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c2807 : s 47 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c2932 : s 50 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3167 : s 55 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3197 : s 56 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3307 : s 58 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3308 : s 58 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c1464 : s 17 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c2134 : s 32 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c2809 : s 47 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c3254 : s 57 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c2006 : s 29 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2231 : s 34 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2456 : s 39 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2681 : s 44 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2235 : s 34 ≠ 4 ∨ s 59 = 3 ∨ s 59 = 4)
    (c676 : s 0 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c1256 : s 13 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c1606 : s 21 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c796 : s 3 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c931 : s 6 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c3226 : s 57 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c856 : s 4 ≠ 0 ∨ s 47 = 1 ∨ s 47 = 2 ∨ s 47 = 3)
    (c2051 : s 30 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c2096 : s 31 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c2141 : s 32 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c2186 : s 33 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c1624 : s 21 ≠ 3 ∨ s 34 = 0 ∨ s 34 = 4)
    (c809 : s 3 ≠ 3 ∨ s 34 = 0 ∨ s 34 = 4)
    (c1169 : s 11 ≠ 3 ∨ s 34 = 0 ∨ s 34 = 4)
    (c2097 : s 31 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2222 : s 34 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2052 : s 30 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2187 : s 33 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2053 : s 30 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2098 : s 31 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2188 : s 33 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c1997 : s 29 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2672 : s 44 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2447 : s 39 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c1998 : s 29 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2223 : s 34 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2673 : s 44 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2448 : s 39 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c793 : s 2 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1)
    (c833 : s 3 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1)
    (c968 : s 6 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1)
    (c1193 : s 11 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1)
    (c1643 : s 21 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1)
    (c703 : s 0 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1)
    (c748 : s 1 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1)
    (c883 : s 4 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1)
    (c747 : s 1 ≠ 1 ∨ s 30 = 0 ∨ s 30 = 2)
    (c882 : s 4 ≠ 1 ∨ s 30 = 0 ∨ s 30 = 2)
    (c702 : s 0 ≠ 1 ∨ s 30 = 0 ∨ s 30 = 2)
    (c928 : s 5 ≠ 2 ∨ s 31 = 0 ∨ s 31 = 1)
    (c1063 : s 8 ≠ 2 ∨ s 31 = 0 ∨ s 31 = 1)
    (c1108 : s 9 ≠ 2 ∨ s 31 = 0 ∨ s 31 = 1)
    (c1112 : s 10 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1202 : s 12 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1247 : s 13 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1113 : s 10 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1203 : s 12 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1248 : s 13 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1607 : s 21 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c797 : s 3 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c932 : s 6 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1157 : s 11 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c3021 : s 52 ≠ 0 ∨ s 21 = 1 ∨ s 21 = 2 ∨ s 21 = 3)
    (c1351 : s 15 ≠ 0 ∨ s 3 = 1 ∨ s 3 = 2 ∨ s 3 = 3)
    (c2701 : s 45 ≠ 0 ∨ s 3 = 1 ∨ s 3 = 2 ∨ s 3 = 3)
    (c1446 : s 17 ≠ 0 ∨ s 11 = 1 ∨ s 11 = 2 ∨ s 11 = 3)
    (c2916 : s 50 ≠ 0 ∨ s 11 = 1 ∨ s 11 = 2 ∨ s 11 = 3)
    (c1018 : s 7 ≠ 2 ∨ s 31 = 0 ∨ s 31 = 1)
    (c1588 : s 20 ≠ 2 ∨ s 33 = 0 ∨ s 33 = 1)
    (c1658 : s 22 ≠ 2 ∨ s 33 = 0 ∨ s 33 = 1)
    (c1703 : s 23 ≠ 2 ∨ s 33 = 0 ∨ s 33 = 1)
    (c1748 : s 24 ≠ 2 ∨ s 33 = 0 ∨ s 33 = 1)
    (c792 : s 2 ≠ 1 ∨ s 30 = 0 ∨ s 30 = 2)
    (c927 : s 5 ≠ 1 ∨ s 31 = 0 ∨ s 31 = 2)
    (c1017 : s 7 ≠ 1 ∨ s 31 = 0 ∨ s 31 = 2)
    (c1062 : s 8 ≠ 1 ∨ s 31 = 0 ∨ s 31 = 2)
    (c1107 : s 9 ≠ 1 ∨ s 31 = 0 ∨ s 31 = 2)
    (c1587 : s 20 ≠ 1 ∨ s 33 = 0 ∨ s 33 = 2)
    (c1657 : s 22 ≠ 1 ∨ s 33 = 0 ∨ s 33 = 2)
    (c1702 : s 23 ≠ 1 ∨ s 33 = 0 ∨ s 33 = 2)
    (c1747 : s 24 ≠ 1 ∨ s 33 = 0 ∨ s 33 = 2)
    (c2413 : s 38 ≠ 2 ∨ s 29 = 0 ∨ s 29 = 1)
    (c2863 : s 48 ≠ 2 ∨ s 29 = 0 ∨ s 29 = 1)
    (c3088 : s 53 ≠ 2 ∨ s 29 = 0 ∨ s 29 = 1)
    (c3113 : s 54 ≠ 2 ∨ s 44 = 0 ∨ s 44 = 1)
    (c2903 : s 49 ≠ 2 ∨ s 44 = 0 ∨ s 44 = 1)
    (c1503 : s 18 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c1858 : s 26 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c2412 : s 38 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2)
    (c2862 : s 48 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2)
    (c3087 : s 53 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2)
    (c3112 : s 54 ≠ 1 ∨ s 44 = 0 ∨ s 44 = 2)
    (c2902 : s 49 ≠ 1 ∨ s 44 = 0 ∨ s 44 = 2)
    (c1502 : s 18 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    (c1857 : s 26 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    (c2702 : s 45 ≠ 1 ∨ s 3 = 0 ∨ s 3 = 2)
    (c1352 : s 15 ≠ 1 ∨ s 3 = 0 ∨ s 3 = 2)
    (c1802 : s 25 ≠ 1 ∨ s 3 = 0 ∨ s 3 = 2)
    (c2467 : s 40 ≠ 1 ∨ s 6 = 0 ∨ s 6 = 2)
    (c2742 : s 46 ≠ 1 ∨ s 6 = 0 ∨ s 6 = 2)
    (c1397 : s 16 ≠ 1 ∨ s 6 = 0 ∨ s 6 = 2)
    (c2247 : s 35 ≠ 1 ∨ s 6 = 0 ∨ s 6 = 2)
    (c2347 : s 37 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2)
    (c2522 : s 41 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2)
    (c3022 : s 52 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2)
    (c1517 : s 19 ≠ 1 ∨ s 0 = 0 ∨ s 0 = 2)
    (c2708 : s 45 ≠ 2 ∨ s 4 = 0 ∨ s 4 = 1)
    (c2733 : s 46 ≠ 2 ∨ s 4 = 0 ∨ s 4 = 1)
    (c1358 : s 15 ≠ 2 ∨ s 4 = 0 ∨ s 4 = 1)
    (c1808 : s 25 ≠ 2 ∨ s 4 = 0 ∨ s 4 = 1)
    (c1383 : s 16 ≠ 2 ∨ s 0 = 0 ∨ s 0 = 1)
    (c1518 : s 19 ≠ 2 ∨ s 0 = 0 ∨ s 0 = 1)
    (c2963 : s 51 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1)
    (c3008 : s 52 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1)
    (c2962 : s 51 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2)
    (c2523 : s 41 ≠ 2 ∨ s 21 = 0 ∨ s 21 = 1)
    (c2348 : s 37 ≠ 2 ∨ s 21 = 0 ∨ s 21 = 1)
    (c2468 : s 40 ≠ 2 ∨ s 6 = 0 ∨ s 6 = 1)
    (c2248 : s 35 ≠ 2 ∨ s 6 = 0 ∨ s 6 = 1)
    (c1947 : s 28 ≠ 1 ∨ s 52 = 0 ∨ s 52 = 2)
    (c1948 : s 28 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1)
    (c2293 : s 36 ≠ 2 ∨ s 15 = 0 ∨ s 15 = 1)
    (c1887 : s 27 ≠ 1 ∨ s 45 = 0 ∨ s 45 = 2)
    (c2557 : s 42 ≠ 1 ∨ s 45 = 0 ∨ s 45 = 2)
    (c1888 : s 27 ≠ 2 ∨ s 45 = 0 ∨ s 45 = 1)
    (c2558 : s 42 ≠ 2 ∨ s 45 = 0 ∨ s 45 = 1)
    (c2302 : s 36 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2)
    (c2608 : s 43 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1)
    (c2607 : s 43 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2)
    (c3361 : s 0 = 1 ∨ s 0 = 2 ∨ s 1 = 1 ∨ s 1 = 2 ∨ s 2 = 1 ∨ s 2 = 2 ∨ s 3 = 1 ∨ s 3 = 2 ∨ s 4 = 1 ∨ s 4 = 2 ∨ s 5 = 1 ∨ s 5 = 2 ∨ s 6 = 1 ∨ s 6 = 2 ∨ s 7 = 1 ∨ s 7 = 2 ∨ s 8 = 1 ∨ s 8 = 2 ∨ s 9 = 1 ∨ s 9 = 2 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 11 = 1 ∨ s 11 = 2 ∨ s 12 = 1 ∨ s 12 = 2 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 15 = 1 ∨ s 15 = 2 ∨ s 16 = 1 ∨ s 16 = 2 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 18 = 1 ∨ s 18 = 2 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 20 = 1 ∨ s 20 = 2 ∨ s 21 = 1 ∨ s 21 = 2 ∨ s 22 = 1 ∨ s 22 = 2 ∨ s 23 = 1 ∨ s 23 = 2 ∨ s 24 = 1 ∨ s 24 = 2 ∨ s 25 = 1 ∨ s 25 = 2 ∨ s 26 = 1 ∨ s 26 = 2 ∨ s 27 = 1 ∨ s 27 = 2 ∨ s 28 = 1 ∨ s 28 = 2 ∨ s 29 = 1 ∨ s 29 = 2 ∨ s 30 = 1 ∨ s 30 = 2 ∨ s 31 = 1 ∨ s 31 = 2 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 33 = 1 ∨ s 33 = 2 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 35 = 1 ∨ s 35 = 2 ∨ s 36 = 1 ∨ s 36 = 2 ∨ s 37 = 1 ∨ s 37 = 2 ∨ s 38 = 1 ∨ s 38 = 2 ∨ s 39 = 1 ∨ s 39 = 2 ∨ s 40 = 1 ∨ s 40 = 2 ∨ s 41 = 1 ∨ s 41 = 2 ∨ s 42 = 1 ∨ s 42 = 2 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 44 = 1 ∨ s 44 = 2 ∨ s 45 = 1 ∨ s 45 = 2 ∨ s 46 = 1 ∨ s 46 = 2 ∨ s 47 = 1 ∨ s 47 = 2 ∨ s 48 = 1 ∨ s 48 = 2 ∨ s 49 = 1 ∨ s 49 = 2 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 52 = 1 ∨ s 52 = 2 ∨ s 53 = 1 ∨ s 53 = 2 ∨ s 54 = 1 ∨ s 54 = 2 ∨ s 55 = 1 ∨ s 55 = 2 ∨ s 56 = 1 ∨ s 56 = 2 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 59 = 1 ∨ s 59 = 2)
    : s 14 ≠ 3 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 57 = 1 ∨ s 57 = 2 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 59 ≠ 4 := c3367
  have u1 : s 14 ≠ 0 := (Or.elim c158 (fun h => h) (fun h => (False.elim (h a0))))
  have u2 : s 14 ≠ 4 := (Or.elim c165 (fun h => (False.elim (h a0))) (fun h => h))
  have u3 : s 59 ≠ 1 := (Or.elim c3352 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a2 h))))))
  have u4 : s 59 ≠ 2 := (Or.elim c3353 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u5 : s 59 ≠ 3 := (Or.elim c3354 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u6 : s 17 ≠ 2 := (Or.elim c1463 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u7 : s 32 ≠ 2 := (Or.elim c2133 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u8 : s 47 ≠ 2 := (Or.elim c2808 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u9 : s 50 ≠ 2 := (Or.elim c2933 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u10 : s 55 ≠ 2 := (Or.elim c3168 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u11 : s 56 ≠ 2 := (Or.elim c3198 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u12 : s 17 ≠ 1 := (Or.elim c1462 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a2 h))))))
  have u13 : s 32 ≠ 1 := (Or.elim c2132 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a2 h))))))
  have u14 : s 47 ≠ 1 := (Or.elim c2807 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a2 h))))))
  have u15 : s 50 ≠ 1 := (Or.elim c2932 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a2 h))))))
  have u16 : s 55 ≠ 1 := (Or.elim c3167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a2 h))))))
  have u17 : s 56 ≠ 1 := (Or.elim c3197 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a2 h))))))
  have u18 : s 58 ≠ 1 := (Or.elim c3307 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a2 h))))))
  have u19 : s 58 ≠ 2 := (Or.elim c3308 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u20 : s 17 ≠ 3 := (Or.elim c1464 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u21 : s 32 ≠ 3 := (Or.elim c2134 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u22 : s 47 ≠ 3 := (Or.elim c2809 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u23 : s 57 ≠ 3 := (Or.elim c3254 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u24 : s 29 ≠ 0 := (Or.elim c2006 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u5 h))))))))
  have u25 : s 34 ≠ 0 := (Or.elim c2231 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u5 h))))))))
  have u26 : s 39 ≠ 0 := (Or.elim c2456 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u5 h))))))))
  have u27 : s 44 ≠ 0 := (Or.elim c2681 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u5 h))))))))
  have u28 : s 34 ≠ 4 := (Or.elim c2235 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u0 h))))))
  have u29 : s 0 ≠ 0 := (Or.elim c676 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u20 h))))))))
  have u30 : s 13 ≠ 0 := (Or.elim c1256 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u20 h))))))))
  have u31 : s 21 ≠ 0 := (Or.elim c1606 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u21 h))))))))
  have u32 : s 3 ≠ 0 := (Or.elim c796 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u21 h))))))))
  have u33 : s 6 ≠ 0 := (Or.elim c931 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u21 h))))))))
  have u34 : s 57 ≠ 0 := (Or.elim c3226 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u21 h))))))))
  have u35 : s 4 ≠ 0 := (Or.elim c856 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u22 h))))))))
  have u36 : s 30 ≠ 0 := (Or.elim c2051 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (False.elim (u23 h))))))))
  have u37 : s 31 ≠ 0 := (Or.elim c2096 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (False.elim (u23 h))))))))
  have u38 : s 32 ≠ 0 := (Or.elim c2141 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (False.elim (u23 h))))))))
  have u39 : s 33 ≠ 0 := (Or.elim c2186 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (False.elim (u23 h))))))))
  have u40 : s 21 ≠ 3 := (Or.elim c1624 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u28 h))))))
  have u41 : s 3 ≠ 3 := (Or.elim c809 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u28 h))))))
  have u42 : s 11 ≠ 3 := (Or.elim c1169 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u28 h))))))
  have u43 : s 31 ≠ 1 := (Or.elim c2097 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (a4 h))))))
  have u44 : s 34 ≠ 1 := (Or.elim c2222 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (a4 h))))))
  have u45 : s 30 ≠ 1 := (Or.elim c2052 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (a4 h))))))
  have u46 : s 33 ≠ 1 := (Or.elim c2187 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (a4 h))))))
  have u47 : s 30 ≠ 2 := (Or.elim c2053 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (a3 h))))))
  have u48 : s 31 ≠ 2 := (Or.elim c2098 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (a3 h))))))
  have u49 : s 33 ≠ 2 := (Or.elim c2188 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (a3 h))))))
  have u50 : s 29 ≠ 1 := (Or.elim c1997 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (a4 h))))))
  have u51 : s 44 ≠ 1 := (Or.elim c2672 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (a4 h))))))
  have u52 : s 39 ≠ 1 := (Or.elim c2447 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (a4 h))))))
  have u53 : s 29 ≠ 2 := (Or.elim c1998 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (a3 h))))))
  have u54 : s 34 ≠ 2 := (Or.elim c2223 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (a3 h))))))
  have u55 : s 44 ≠ 2 := (Or.elim c2673 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (a3 h))))))
  have u56 : s 39 ≠ 2 := (Or.elim c2448 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (a3 h))))))
  have u57 : s 2 ≠ 2 := (Or.elim c793 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u45 h))))))
  have u58 : s 3 ≠ 2 := (Or.elim c833 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u45 h))))))
  have u59 : s 6 ≠ 2 := (Or.elim c968 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u45 h))))))
  have u60 : s 11 ≠ 2 := (Or.elim c1193 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u45 h))))))
  have u61 : s 21 ≠ 2 := (Or.elim c1643 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u45 h))))))
  have u62 : s 0 ≠ 2 := (Or.elim c703 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u45 h))))))
  have u63 : s 1 ≠ 2 := (Or.elim c748 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u45 h))))))
  have u64 : s 4 ≠ 2 := (Or.elim c883 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u45 h))))))
  have u65 : s 1 ≠ 1 := (Or.elim c747 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u47 h))))))
  have u66 : s 4 ≠ 1 := (Or.elim c882 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u47 h))))))
  have u67 : s 0 ≠ 1 := (Or.elim c702 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u47 h))))))
  have u68 : s 5 ≠ 2 := (Or.elim c928 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => (False.elim (u43 h))))))
  have u69 : s 8 ≠ 2 := (Or.elim c1063 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => (False.elim (u43 h))))))
  have u70 : s 9 ≠ 2 := (Or.elim c1108 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => (False.elim (u43 h))))))
  have u71 : s 10 ≠ 1 := (Or.elim c1112 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u7 h))))))
  have u72 : s 12 ≠ 1 := (Or.elim c1202 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u7 h))))))
  have u73 : s 13 ≠ 1 := (Or.elim c1247 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u7 h))))))
  have u74 : s 10 ≠ 2 := (Or.elim c1113 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u13 h))))))
  have u75 : s 12 ≠ 2 := (Or.elim c1203 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u13 h))))))
  have u76 : s 13 ≠ 2 := (Or.elim c1248 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u13 h))))))
  have u77 : s 21 ≠ 1 := (Or.elim c1607 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u7 h))))))
  have u78 : s 3 ≠ 1 := (Or.elim c797 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u7 h))))))
  have u79 : s 6 ≠ 1 := (Or.elim c932 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u7 h))))))
  have u80 : s 11 ≠ 1 := (Or.elim c1157 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u7 h))))))
  have u81 : s 52 ≠ 0 := (Or.elim c3021 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u77 h))) (fun h => (Or.elim h (fun h => (False.elim (u61 h))) (fun h => (False.elim (u40 h))))))))
  have u82 : s 15 ≠ 0 := (Or.elim c1351 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u78 h))) (fun h => (Or.elim h (fun h => (False.elim (u58 h))) (fun h => (False.elim (u41 h))))))))
  have u83 : s 45 ≠ 0 := (Or.elim c2701 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u78 h))) (fun h => (Or.elim h (fun h => (False.elim (u58 h))) (fun h => (False.elim (u41 h))))))))
  have u84 : s 17 ≠ 0 := (Or.elim c1446 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u80 h))) (fun h => (Or.elim h (fun h => (False.elim (u60 h))) (fun h => (False.elim (u42 h))))))))
  have u85 : s 50 ≠ 0 := (Or.elim c2916 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u80 h))) (fun h => (Or.elim h (fun h => (False.elim (u60 h))) (fun h => (False.elim (u42 h))))))))
  have u86 : s 7 ≠ 2 := (Or.elim c1018 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => (False.elim (u43 h))))))
  have u87 : s 20 ≠ 2 := (Or.elim c1588 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (False.elim (u46 h))))))
  have u88 : s 22 ≠ 2 := (Or.elim c1658 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (False.elim (u46 h))))))
  have u89 : s 23 ≠ 2 := (Or.elim c1703 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (False.elim (u46 h))))))
  have u90 : s 24 ≠ 2 := (Or.elim c1748 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (False.elim (u46 h))))))
  have u91 : s 2 ≠ 1 := (Or.elim c792 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u47 h))))))
  have u92 : s 5 ≠ 1 := (Or.elim c927 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => (False.elim (u48 h))))))
  have u93 : s 7 ≠ 1 := (Or.elim c1017 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => (False.elim (u48 h))))))
  have u94 : s 8 ≠ 1 := (Or.elim c1062 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => (False.elim (u48 h))))))
  have u95 : s 9 ≠ 1 := (Or.elim c1107 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => (False.elim (u48 h))))))
  have u96 : s 20 ≠ 1 := (Or.elim c1587 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (False.elim (u49 h))))))
  have u97 : s 22 ≠ 1 := (Or.elim c1657 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (False.elim (u49 h))))))
  have u98 : s 23 ≠ 1 := (Or.elim c1702 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (False.elim (u49 h))))))
  have u99 : s 24 ≠ 1 := (Or.elim c1747 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (False.elim (u49 h))))))
  have u100 : s 38 ≠ 2 := (Or.elim c2413 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (False.elim (u50 h))))))
  have u101 : s 48 ≠ 2 := (Or.elim c2863 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (False.elim (u50 h))))))
  have u102 : s 53 ≠ 2 := (Or.elim c3088 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (False.elim (u50 h))))))
  have u103 : s 54 ≠ 2 := (Or.elim c3113 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (False.elim (u51 h))))))
  have u104 : s 49 ≠ 2 := (Or.elim c2903 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (False.elim (u51 h))))))
  have u105 : s 18 ≠ 2 := (Or.elim c1503 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (False.elim (u52 h))))))
  have u106 : s 26 ≠ 2 := (Or.elim c1858 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (False.elim (u52 h))))))
  have u107 : s 38 ≠ 1 := (Or.elim c2412 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (False.elim (u53 h))))))
  have u108 : s 48 ≠ 1 := (Or.elim c2862 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (False.elim (u53 h))))))
  have u109 : s 53 ≠ 1 := (Or.elim c3087 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (False.elim (u53 h))))))
  have u110 : s 54 ≠ 1 := (Or.elim c3112 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (False.elim (u55 h))))))
  have u111 : s 49 ≠ 1 := (Or.elim c2902 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (False.elim (u55 h))))))
  have u112 : s 18 ≠ 1 := (Or.elim c1502 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (False.elim (u56 h))))))
  have u113 : s 26 ≠ 1 := (Or.elim c1857 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (False.elim (u56 h))))))
  have u114 : s 45 ≠ 1 := (Or.elim c2702 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u32 h))) (fun h => (False.elim (u58 h))))))
  have u115 : s 15 ≠ 1 := (Or.elim c1352 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u32 h))) (fun h => (False.elim (u58 h))))))
  have u116 : s 25 ≠ 1 := (Or.elim c1802 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u32 h))) (fun h => (False.elim (u58 h))))))
  have u117 : s 40 ≠ 1 := (Or.elim c2467 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u33 h))) (fun h => (False.elim (u59 h))))))
  have u118 : s 46 ≠ 1 := (Or.elim c2742 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u33 h))) (fun h => (False.elim (u59 h))))))
  have u119 : s 16 ≠ 1 := (Or.elim c1397 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u33 h))) (fun h => (False.elim (u59 h))))))
  have u120 : s 35 ≠ 1 := (Or.elim c2247 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u33 h))) (fun h => (False.elim (u59 h))))))
  have u121 : s 37 ≠ 1 := (Or.elim c2347 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u61 h))))))
  have u122 : s 41 ≠ 1 := (Or.elim c2522 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u61 h))))))
  have u123 : s 52 ≠ 1 := (Or.elim c3022 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u61 h))))))
  have u124 : s 19 ≠ 1 := (Or.elim c1517 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u29 h))) (fun h => (False.elim (u62 h))))))
  have u125 : s 45 ≠ 2 := (Or.elim c2708 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u66 h))))))
  have u126 : s 46 ≠ 2 := (Or.elim c2733 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u66 h))))))
  have u127 : s 15 ≠ 2 := (Or.elim c1358 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u66 h))))))
  have u128 : s 25 ≠ 2 := (Or.elim c1808 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u66 h))))))
  have u129 : s 16 ≠ 2 := (Or.elim c1383 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u29 h))) (fun h => (False.elim (u67 h))))))
  have u130 : s 19 ≠ 2 := (Or.elim c1518 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u29 h))) (fun h => (False.elim (u67 h))))))
  have u131 : s 51 ≠ 2 := (Or.elim c2963 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => (False.elim (u73 h))))))
  have u132 : s 52 ≠ 2 := (Or.elim c3008 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => (False.elim (u73 h))))))
  have u133 : s 51 ≠ 1 := (Or.elim c2962 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => (False.elim (u76 h))))))
  have u134 : s 41 ≠ 2 := (Or.elim c2523 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u77 h))))))
  have u135 : s 37 ≠ 2 := (Or.elim c2348 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u77 h))))))
  have u136 : s 40 ≠ 2 := (Or.elim c2468 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u33 h))) (fun h => (False.elim (u79 h))))))
  have u137 : s 35 ≠ 2 := (Or.elim c2248 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u33 h))) (fun h => (False.elim (u79 h))))))
  have u138 : s 28 ≠ 1 := (Or.elim c1947 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u81 h))) (fun h => (False.elim (u132 h))))))
  have u139 : s 28 ≠ 2 := (Or.elim c1948 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u81 h))) (fun h => (False.elim (u123 h))))))
  have u140 : s 36 ≠ 2 := (Or.elim c2293 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u82 h))) (fun h => (False.elim (u115 h))))))
  have u141 : s 27 ≠ 1 := (Or.elim c1887 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u83 h))) (fun h => (False.elim (u125 h))))))
  have u142 : s 42 ≠ 1 := (Or.elim c2557 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u83 h))) (fun h => (False.elim (u125 h))))))
  have u143 : s 27 ≠ 2 := (Or.elim c1888 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u83 h))) (fun h => (False.elim (u114 h))))))
  have u144 : s 42 ≠ 2 := (Or.elim c2558 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u83 h))) (fun h => (False.elim (u114 h))))))
  have u145 : s 36 ≠ 1 := (Or.elim c2302 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u84 h))) (fun h => (False.elim (u6 h))))))
  have u146 : s 43 ≠ 2 := (Or.elim c2608 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u85 h))) (fun h => (False.elim (u15 h))))))
  have u147 : s 43 ≠ 1 := (Or.elim c2607 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u85 h))) (fun h => (False.elim (u9 h))))))
  exact (Or.elim c3361 (fun h => (u67 h)) (fun h => (Or.elim h (fun h => (u62 h)) (fun h => (Or.elim h (fun h => (u65 h)) (fun h => (Or.elim h (fun h => (u63 h)) (fun h => (Or.elim h (fun h => (u91 h)) (fun h => (Or.elim h (fun h => (u57 h)) (fun h => (Or.elim h (fun h => (u78 h)) (fun h => (Or.elim h (fun h => (u58 h)) (fun h => (Or.elim h (fun h => (u66 h)) (fun h => (Or.elim h (fun h => (u64 h)) (fun h => (Or.elim h (fun h => (u92 h)) (fun h => (Or.elim h (fun h => (u68 h)) (fun h => (Or.elim h (fun h => (u79 h)) (fun h => (Or.elim h (fun h => (u59 h)) (fun h => (Or.elim h (fun h => (u93 h)) (fun h => (Or.elim h (fun h => (u86 h)) (fun h => (Or.elim h (fun h => (u94 h)) (fun h => (Or.elim h (fun h => (u69 h)) (fun h => (Or.elim h (fun h => (u95 h)) (fun h => (Or.elim h (fun h => (u70 h)) (fun h => (Or.elim h (fun h => (u71 h)) (fun h => (Or.elim h (fun h => (u74 h)) (fun h => (Or.elim h (fun h => (u80 h)) (fun h => (Or.elim h (fun h => (u60 h)) (fun h => (Or.elim h (fun h => (u72 h)) (fun h => (Or.elim h (fun h => (u75 h)) (fun h => (Or.elim h (fun h => (u73 h)) (fun h => (Or.elim h (fun h => (u76 h)) (fun h => (Or.elim h (fun h => (a1 h)) (fun h => (Or.elim h (fun h => (a2 h)) (fun h => (Or.elim h (fun h => (u115 h)) (fun h => (Or.elim h (fun h => (u127 h)) (fun h => (Or.elim h (fun h => (u119 h)) (fun h => (Or.elim h (fun h => (u129 h)) (fun h => (Or.elim h (fun h => (u12 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (Or.elim h (fun h => (u112 h)) (fun h => (Or.elim h (fun h => (u105 h)) (fun h => (Or.elim h (fun h => (u124 h)) (fun h => (Or.elim h (fun h => (u130 h)) (fun h => (Or.elim h (fun h => (u96 h)) (fun h => (Or.elim h (fun h => (u87 h)) (fun h => (Or.elim h (fun h => (u77 h)) (fun h => (Or.elim h (fun h => (u61 h)) (fun h => (Or.elim h (fun h => (u97 h)) (fun h => (Or.elim h (fun h => (u88 h)) (fun h => (Or.elim h (fun h => (u98 h)) (fun h => (Or.elim h (fun h => (u89 h)) (fun h => (Or.elim h (fun h => (u99 h)) (fun h => (Or.elim h (fun h => (u90 h)) (fun h => (Or.elim h (fun h => (u116 h)) (fun h => (Or.elim h (fun h => (u128 h)) (fun h => (Or.elim h (fun h => (u113 h)) (fun h => (Or.elim h (fun h => (u106 h)) (fun h => (Or.elim h (fun h => (u141 h)) (fun h => (Or.elim h (fun h => (u143 h)) (fun h => (Or.elim h (fun h => (u138 h)) (fun h => (Or.elim h (fun h => (u139 h)) (fun h => (Or.elim h (fun h => (u50 h)) (fun h => (Or.elim h (fun h => (u53 h)) (fun h => (Or.elim h (fun h => (u45 h)) (fun h => (Or.elim h (fun h => (u47 h)) (fun h => (Or.elim h (fun h => (u43 h)) (fun h => (Or.elim h (fun h => (u48 h)) (fun h => (Or.elim h (fun h => (u13 h)) (fun h => (Or.elim h (fun h => (u7 h)) (fun h => (Or.elim h (fun h => (u46 h)) (fun h => (Or.elim h (fun h => (u49 h)) (fun h => (Or.elim h (fun h => (u44 h)) (fun h => (Or.elim h (fun h => (u54 h)) (fun h => (Or.elim h (fun h => (u120 h)) (fun h => (Or.elim h (fun h => (u137 h)) (fun h => (Or.elim h (fun h => (u145 h)) (fun h => (Or.elim h (fun h => (u140 h)) (fun h => (Or.elim h (fun h => (u121 h)) (fun h => (Or.elim h (fun h => (u135 h)) (fun h => (Or.elim h (fun h => (u107 h)) (fun h => (Or.elim h (fun h => (u100 h)) (fun h => (Or.elim h (fun h => (u52 h)) (fun h => (Or.elim h (fun h => (u56 h)) (fun h => (Or.elim h (fun h => (u117 h)) (fun h => (Or.elim h (fun h => (u136 h)) (fun h => (Or.elim h (fun h => (u122 h)) (fun h => (Or.elim h (fun h => (u134 h)) (fun h => (Or.elim h (fun h => (u142 h)) (fun h => (Or.elim h (fun h => (u144 h)) (fun h => (Or.elim h (fun h => (u147 h)) (fun h => (Or.elim h (fun h => (u146 h)) (fun h => (Or.elim h (fun h => (u51 h)) (fun h => (Or.elim h (fun h => (u55 h)) (fun h => (Or.elim h (fun h => (u114 h)) (fun h => (Or.elim h (fun h => (u125 h)) (fun h => (Or.elim h (fun h => (u118 h)) (fun h => (Or.elim h (fun h => (u126 h)) (fun h => (Or.elim h (fun h => (u14 h)) (fun h => (Or.elim h (fun h => (u8 h)) (fun h => (Or.elim h (fun h => (u108 h)) (fun h => (Or.elim h (fun h => (u101 h)) (fun h => (Or.elim h (fun h => (u111 h)) (fun h => (Or.elim h (fun h => (u104 h)) (fun h => (Or.elim h (fun h => (u15 h)) (fun h => (Or.elim h (fun h => (u9 h)) (fun h => (Or.elim h (fun h => (u133 h)) (fun h => (Or.elim h (fun h => (u131 h)) (fun h => (Or.elim h (fun h => (u123 h)) (fun h => (Or.elim h (fun h => (u132 h)) (fun h => (Or.elim h (fun h => (u109 h)) (fun h => (Or.elim h (fun h => (u102 h)) (fun h => (Or.elim h (fun h => (u110 h)) (fun h => (Or.elim h (fun h => (u103 h)) (fun h => (Or.elim h (fun h => (u16 h)) (fun h => (Or.elim h (fun h => (u10 h)) (fun h => (Or.elim h (fun h => (u17 h)) (fun h => (Or.elim h (fun h => (u11 h)) (fun h => (Or.elim h (fun h => (a3 h)) (fun h => (Or.elim h (fun h => (a4 h)) (fun h => (Or.elim h (fun h => (u18 h)) (fun h => (Or.elim h (fun h => (u19 h)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (u4 h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem step3369 (s : Fin 60 → Fin 5)
    (c3367 : s 59 ≠ 4)
    (c656 : s 59 ≠ 1 ∨ s 59 ≠ 3)
    (c3317 : s 59 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c1335 : s 14 ≠ 4 ∨ s 59 = 3 ∨ s 59 = 4)
    (c2191 : s 34 ≠ 0 ∨ s 3 = 1 ∨ s 3 = 2 ∨ s 3 = 3)
    (c2135 : s 32 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4)
    (c799 : s 3 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4)
    : s 59 ≠ 1 ∨ s 3 = 2 ∨ s 3 = 1 ∨ s 34 = 2 ∨ s 32 = 0 ∨ s 14 = 3 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5⟩ := hc
  have u0 : s 59 ≠ 4 := c3367
  have u1 : s 59 ≠ 3 := (Or.elim c656 (fun h => (False.elim (h a0))) (fun h => h))
  have u2 : s 34 = 0 := (Or.elim c3317 (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a3 h))))))
  have u3 : s 14 ≠ 4 := (Or.elim c1335 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))
  have u4 : s 3 = 3 := (Or.elim c2191 (fun h => (False.elim (h u2))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => h))))))
  have u5 : s 32 ≠ 4 := (Or.elim c2135 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => (False.elim (u3 h))))))
  exact (Or.elim c799 (fun h => (h u4)) (fun h => (Or.elim h (fun h => (a4 h)) (fun h => (u5 h)))))

private theorem step3370 (s : Fin 60 → Fin 5)
    (c3367 : s 59 ≠ 4)
    (c3368 : s 14 ≠ 3 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 57 = 1 ∨ s 57 = 2)
    (c3251 : s 57 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2931 : s 50 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2806 : s 47 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2131 : s 32 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c1461 : s 17 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c3351 : s 59 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2097 : s 31 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2142 : s 32 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2222 : s 34 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2052 : s 30 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2187 : s 33 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2053 : s 30 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2098 : s 31 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2188 : s 33 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c1997 : s 29 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2672 : s 44 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2447 : s 39 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c1998 : s 29 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2143 : s 32 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2223 : s 34 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2673 : s 44 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c2448 : s 39 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    (c1112 : s 10 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1202 : s 12 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1247 : s 13 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1113 : s 10 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1203 : s 12 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1248 : s 13 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1607 : s 21 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c797 : s 3 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c932 : s 6 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1157 : s 11 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c933 : s 6 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1158 : s 11 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1608 : s 21 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c798 : s 3 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c2009 : s 29 ≠ 3 ∨ s 59 = 0 ∨ s 59 = 4)
    (c2234 : s 34 ≠ 3 ∨ s 59 = 0 ∨ s 59 = 4)
    (c2459 : s 39 ≠ 3 ∨ s 59 = 0 ∨ s 59 = 4)
    (c2504 : s 40 ≠ 3 ∨ s 59 = 0 ∨ s 59 = 4)
    (c2549 : s 41 ≠ 3 ∨ s 59 = 0 ∨ s 59 = 4)
    (c2594 : s 42 ≠ 3 ∨ s 59 = 0 ∨ s 59 = 4)
    (c2639 : s 43 ≠ 3 ∨ s 59 = 0 ∨ s 59 = 4)
    (c2411 : s 38 ≠ 0 ∨ s 29 = 1 ∨ s 29 = 2 ∨ s 29 = 3)
    (c786 : s 2 ≠ 0 ∨ s 29 = 1 ∨ s 29 = 2 ∨ s 29 = 3)
    (c2861 : s 48 ≠ 0 ∨ s 29 = 1 ∨ s 29 = 2 ∨ s 29 = 3)
    (c1166 : s 11 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3)
    (c1621 : s 21 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3)
    (c806 : s 3 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3)
    (c941 : s 6 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3)
    (c1501 : s 18 ≠ 0 ∨ s 39 = 1 ∨ s 39 = 2 ∨ s 39 = 3)
    (c1856 : s 26 ≠ 0 ∨ s 39 = 1 ∨ s 39 = 2 ∨ s 39 = 3)
    (c1448 : s 17 ≠ 2 ∨ s 11 = 0 ∨ s 11 = 1)
    (c2793 : s 47 ≠ 2 ∨ s 11 = 0 ∨ s 11 = 1)
    (c2918 : s 50 ≠ 2 ∨ s 11 = 0 ∨ s 11 = 1)
    (c3153 : s 55 ≠ 2 ∨ s 11 = 0 ∨ s 11 = 1)
    (c1447 : s 17 ≠ 1 ∨ s 11 = 0 ∨ s 11 = 2)
    (c2792 : s 47 ≠ 1 ∨ s 11 = 0 ∨ s 11 = 2)
    (c2917 : s 50 ≠ 1 ∨ s 11 = 0 ∨ s 11 = 2)
    (c3152 : s 55 ≠ 1 ∨ s 11 = 0 ∨ s 11 = 2)
    (c2523 : s 41 ≠ 2 ∨ s 21 = 0 ∨ s 21 = 1)
    (c3023 : s 52 ≠ 2 ∨ s 21 = 0 ∨ s 21 = 1)
    (c2348 : s 37 ≠ 2 ∨ s 21 = 0 ∨ s 21 = 1)
    (c723 : s 1 ≠ 2 ∨ s 21 = 0 ∨ s 21 = 1)
    (c2347 : s 37 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2)
    (c722 : s 1 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2)
    (c2522 : s 41 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2)
    (c3022 : s 52 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2)
    (c1578 : s 20 ≠ 2 ∨ s 3 = 0 ∨ s 3 = 1)
    (c2703 : s 45 ≠ 2 ∨ s 3 = 0 ∨ s 3 = 1)
    (c1353 : s 15 ≠ 2 ∨ s 3 = 0 ∨ s 3 = 1)
    (c1803 : s 25 ≠ 2 ∨ s 3 = 0 ∨ s 3 = 1)
    (c1577 : s 20 ≠ 1 ∨ s 3 = 0 ∨ s 3 = 2)
    (c2702 : s 45 ≠ 1 ∨ s 3 = 0 ∨ s 3 = 2)
    (c1352 : s 15 ≠ 1 ∨ s 3 = 0 ∨ s 3 = 2)
    (c1802 : s 25 ≠ 1 ∨ s 3 = 0 ∨ s 3 = 2)
    (c2468 : s 40 ≠ 2 ∨ s 6 = 0 ∨ s 6 = 1)
    (c2743 : s 46 ≠ 2 ∨ s 6 = 0 ∨ s 6 = 1)
    (c1398 : s 16 ≠ 2 ∨ s 6 = 0 ∨ s 6 = 1)
    (c2248 : s 35 ≠ 2 ∨ s 6 = 0 ∨ s 6 = 1)
    (c2467 : s 40 ≠ 1 ∨ s 6 = 0 ∨ s 6 = 2)
    (c2742 : s 46 ≠ 1 ∨ s 6 = 0 ∨ s 6 = 2)
    (c1397 : s 16 ≠ 1 ∨ s 6 = 0 ∨ s 6 = 2)
    (c2247 : s 35 ≠ 1 ∨ s 6 = 0 ∨ s 6 = 2)
    (c2977 : s 51 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2)
    (c677 : s 0 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2)
    (c2302 : s 36 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2)
    (c912 : s 5 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2)
    (c857 : s 4 ≠ 1 ∨ s 47 = 0 ∨ s 47 = 2)
    (c1087 : s 9 ≠ 1 ∨ s 47 = 0 ∨ s 47 = 2)
    (c1897 : s 27 ≠ 1 ∨ s 47 = 0 ∨ s 47 = 2)
    (c2567 : s 42 ≠ 1 ∨ s 47 = 0 ∨ s 47 = 2)
    (c1762 : s 24 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2)
    (c1937 : s 28 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2)
    (c2607 : s 43 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2)
    (c1537 : s 19 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2)
    (c2978 : s 51 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1)
    (c678 : s 0 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1)
    (c2303 : s 36 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1)
    (c913 : s 5 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1)
    (c858 : s 4 ≠ 2 ∨ s 47 = 0 ∨ s 47 = 1)
    (c1898 : s 27 ≠ 2 ∨ s 47 = 0 ∨ s 47 = 1)
    (c2568 : s 42 ≠ 2 ∨ s 47 = 0 ∨ s 47 = 1)
    (c1088 : s 9 ≠ 2 ∨ s 47 = 0 ∨ s 47 = 1)
    (c1763 : s 24 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1)
    (c1938 : s 28 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1)
    (c2608 : s 43 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1)
    (c1538 : s 19 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1)
    (c1756 : s 24 ≠ 0 ∨ s 41 = 1 ∨ s 41 = 2 ∨ s 41 = 3)
    (c1596 : s 20 ≠ 0 ∨ s 41 = 1 ∨ s 41 = 2 ∨ s 41 = 3)
    (c762 : s 2 ≠ 1 ∨ s 20 = 0 ∨ s 20 = 2)
    (c891 : s 5 ≠ 0 ∨ s 40 = 1 ∨ s 40 = 2 ∨ s 40 = 3)
    (c1071 : s 9 ≠ 0 ∨ s 40 = 1 ∨ s 40 = 2 ∨ s 40 = 3)
    (c1488 : s 18 ≠ 2 ∨ s 5 = 0 ∨ s 5 = 1)
    (c2828 : s 48 ≠ 2 ∨ s 9 = 0 ∨ s 9 = 1)
    (c2878 : s 49 ≠ 2 ∨ s 9 = 0 ∨ s 9 = 1)
    (c3063 : s 53 ≠ 2 ∨ s 24 = 0 ∨ s 24 = 1)
    (c3128 : s 54 ≠ 2 ∨ s 24 = 0 ∨ s 24 = 1)
    (c1487 : s 18 ≠ 1 ∨ s 5 = 0 ∨ s 5 = 2)
    (c2761 : s 46 ≠ 0 ∨ s 42 = 1 ∨ s 42 = 2 ∨ s 42 = 3)
    (c2827 : s 48 ≠ 1 ∨ s 9 = 0 ∨ s 9 = 2)
    (c2877 : s 49 ≠ 1 ∨ s 9 = 0 ∨ s 9 = 2)
    (c3062 : s 53 ≠ 1 ∨ s 24 = 0 ∨ s 24 = 2)
    (c3127 : s 54 ≠ 1 ∨ s 24 = 0 ∨ s 24 = 2)
    (c3001 : s 52 ≠ 0 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 43 = 3)
    (c763 : s 2 ≠ 2 ∨ s 20 = 0 ∨ s 20 = 1)
    (c1833 : s 26 ≠ 2 ∨ s 2 = 0 ∨ s 2 = 1)
    (c2382 : s 38 ≠ 1 ∨ s 18 = 0 ∨ s 18 = 2)
    (c1862 : s 26 ≠ 1 ∨ s 48 = 0 ∨ s 48 = 2)
    (c2383 : s 38 ≠ 2 ∨ s 18 = 0 ∨ s 18 = 1)
    (c1007 : s 7 ≠ 1 ∨ s 46 = 0 ∨ s 46 = 2)
    (c1052 : s 8 ≠ 1 ∨ s 46 = 0 ∨ s 46 = 2)
    (c1008 : s 7 ≠ 2 ∨ s 46 = 0 ∨ s 46 = 1)
    (c1053 : s 8 ≠ 2 ∨ s 46 = 0 ∨ s 46 = 1)
    (c1693 : s 22 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1)
    (c1738 : s 23 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1)
    (c1692 : s 22 ≠ 1 ∨ s 52 = 0 ∨ s 52 = 2)
    (c1737 : s 23 ≠ 1 ∨ s 52 = 0 ∨ s 52 = 2)
    (c3207 : s 56 ≠ 1 ∨ s 26 = 0 ∨ s 26 = 2)
    (c3293 : s 58 ≠ 2 ∨ s 38 = 0 ∨ s 38 = 1)
    (c3208 : s 56 ≠ 2 ∨ s 26 = 0 ∨ s 26 = 1)
    (c3292 : s 58 ≠ 1 ∨ s 38 = 0 ∨ s 38 = 2)
    (c3369 : s 59 ≠ 1 ∨ s 3 = 2 ∨ s 3 = 1 ∨ s 34 = 2 ∨ s 32 = 0 ∨ s 14 = 3)
    (c3361 : s 0 = 1 ∨ s 0 = 2 ∨ s 1 = 1 ∨ s 1 = 2 ∨ s 2 = 1 ∨ s 2 = 2 ∨ s 3 = 1 ∨ s 3 = 2 ∨ s 4 = 1 ∨ s 4 = 2 ∨ s 5 = 1 ∨ s 5 = 2 ∨ s 6 = 1 ∨ s 6 = 2 ∨ s 7 = 1 ∨ s 7 = 2 ∨ s 8 = 1 ∨ s 8 = 2 ∨ s 9 = 1 ∨ s 9 = 2 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 11 = 1 ∨ s 11 = 2 ∨ s 12 = 1 ∨ s 12 = 2 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 15 = 1 ∨ s 15 = 2 ∨ s 16 = 1 ∨ s 16 = 2 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 18 = 1 ∨ s 18 = 2 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 20 = 1 ∨ s 20 = 2 ∨ s 21 = 1 ∨ s 21 = 2 ∨ s 22 = 1 ∨ s 22 = 2 ∨ s 23 = 1 ∨ s 23 = 2 ∨ s 24 = 1 ∨ s 24 = 2 ∨ s 25 = 1 ∨ s 25 = 2 ∨ s 26 = 1 ∨ s 26 = 2 ∨ s 27 = 1 ∨ s 27 = 2 ∨ s 28 = 1 ∨ s 28 = 2 ∨ s 29 = 1 ∨ s 29 = 2 ∨ s 30 = 1 ∨ s 30 = 2 ∨ s 31 = 1 ∨ s 31 = 2 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 33 = 1 ∨ s 33 = 2 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 35 = 1 ∨ s 35 = 2 ∨ s 36 = 1 ∨ s 36 = 2 ∨ s 37 = 1 ∨ s 37 = 2 ∨ s 38 = 1 ∨ s 38 = 2 ∨ s 39 = 1 ∨ s 39 = 2 ∨ s 40 = 1 ∨ s 40 = 2 ∨ s 41 = 1 ∨ s 41 = 2 ∨ s 42 = 1 ∨ s 42 = 2 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 44 = 1 ∨ s 44 = 2 ∨ s 45 = 1 ∨ s 45 = 2 ∨ s 46 = 1 ∨ s 46 = 2 ∨ s 47 = 1 ∨ s 47 = 2 ∨ s 48 = 1 ∨ s 48 = 2 ∨ s 49 = 1 ∨ s 49 = 2 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 52 = 1 ∨ s 52 = 2 ∨ s 53 = 1 ∨ s 53 = 2 ∨ s 54 = 1 ∨ s 54 = 2 ∨ s 55 = 1 ∨ s 55 = 2 ∨ s 56 = 1 ∨ s 56 = 2 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 59 = 1 ∨ s 59 = 2)
    (c658 : s 59 ≠ 2 ∨ s 59 ≠ 3)
    (c3318 : s 59 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c1335 : s 14 ≠ 4 ∨ s 59 = 3 ∨ s 59 = 4)
    (c2191 : s 34 ≠ 0 ∨ s 3 = 1 ∨ s 3 = 2 ∨ s 3 = 3)
    (c2135 : s 32 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4)
    (c799 : s 3 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4)
    : s 14 = 1 ∨ s 14 = 2 ∨ s 57 = 2 ∨ s 57 = 1 := by
  by_contra hc
  try simp only [not_or] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 59 ≠ 4 := c3367
  have u1 : s 14 ≠ 3 := (Or.elim c3368 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (a2 h))))))))))
  have u2 : s 57 ≠ 0 := (Or.elim c3251 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u1 h))))))))
  have u3 : s 50 ≠ 0 := (Or.elim c2931 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u1 h))))))))
  have u4 : s 47 ≠ 0 := (Or.elim c2806 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u1 h))))))))
  have u5 : s 32 ≠ 0 := (Or.elim c2131 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u1 h))))))))
  have u6 : s 17 ≠ 0 := (Or.elim c1461 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u1 h))))))))
  have u7 : s 59 ≠ 0 := (Or.elim c3351 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u1 h))))))))
  have u8 : s 31 ≠ 1 := (Or.elim c2097 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a2 h))))))
  have u9 : s 32 ≠ 1 := (Or.elim c2142 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a2 h))))))
  have u10 : s 34 ≠ 1 := (Or.elim c2222 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a2 h))))))
  have u11 : s 30 ≠ 1 := (Or.elim c2052 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a2 h))))))
  have u12 : s 33 ≠ 1 := (Or.elim c2187 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a2 h))))))
  have u13 : s 30 ≠ 2 := (Or.elim c2053 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a3 h))))))
  have u14 : s 31 ≠ 2 := (Or.elim c2098 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a3 h))))))
  have u15 : s 33 ≠ 2 := (Or.elim c2188 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a3 h))))))
  have u16 : s 29 ≠ 1 := (Or.elim c1997 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a2 h))))))
  have u17 : s 44 ≠ 1 := (Or.elim c2672 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a2 h))))))
  have u18 : s 39 ≠ 1 := (Or.elim c2447 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a2 h))))))
  have u19 : s 29 ≠ 2 := (Or.elim c1998 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a3 h))))))
  have u20 : s 32 ≠ 2 := (Or.elim c2143 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a3 h))))))
  have u21 : s 34 ≠ 2 := (Or.elim c2223 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a3 h))))))
  have u22 : s 44 ≠ 2 := (Or.elim c2673 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a3 h))))))
  have u23 : s 39 ≠ 2 := (Or.elim c2448 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a3 h))))))
  have u24 : s 10 ≠ 1 := (Or.elim c1112 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u20 h))))))
  have u25 : s 12 ≠ 1 := (Or.elim c1202 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u20 h))))))
  have u26 : s 13 ≠ 1 := (Or.elim c1247 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u20 h))))))
  have u27 : s 10 ≠ 2 := (Or.elim c1113 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u9 h))))))
  have u28 : s 12 ≠ 2 := (Or.elim c1203 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u9 h))))))
  have u29 : s 13 ≠ 2 := (Or.elim c1248 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u9 h))))))
  have u30 : s 21 ≠ 1 := (Or.elim c1607 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u20 h))))))
  have u31 : s 3 ≠ 1 := (Or.elim c797 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u20 h))))))
  have u32 : s 6 ≠ 1 := (Or.elim c932 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u20 h))))))
  have u33 : s 11 ≠ 1 := (Or.elim c1157 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u20 h))))))
  have u34 : s 6 ≠ 2 := (Or.elim c933 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u9 h))))))
  have u35 : s 11 ≠ 2 := (Or.elim c1158 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u9 h))))))
  have u36 : s 21 ≠ 2 := (Or.elim c1608 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u9 h))))))
  have u37 : s 3 ≠ 2 := (Or.elim c798 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u9 h))))))
  have u38 : s 29 ≠ 3 := (Or.elim c2009 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u0 h))))))
  have u39 : s 34 ≠ 3 := (Or.elim c2234 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u0 h))))))
  have u40 : s 39 ≠ 3 := (Or.elim c2459 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u0 h))))))
  have u41 : s 40 ≠ 3 := (Or.elim c2504 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u0 h))))))
  have u42 : s 41 ≠ 3 := (Or.elim c2549 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u0 h))))))
  have u43 : s 42 ≠ 3 := (Or.elim c2594 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u0 h))))))
  have u44 : s 43 ≠ 3 := (Or.elim c2639 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u0 h))))))
  have u45 : s 38 ≠ 0 := (Or.elim c2411 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u38 h))))))))
  have u46 : s 2 ≠ 0 := (Or.elim c786 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u38 h))))))))
  have u47 : s 48 ≠ 0 := (Or.elim c2861 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u38 h))))))))
  have u48 : s 11 ≠ 0 := (Or.elim c1166 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u39 h))))))))
  have u49 : s 21 ≠ 0 := (Or.elim c1621 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u39 h))))))))
  have u50 : s 3 ≠ 0 := (Or.elim c806 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u39 h))))))))
  have u51 : s 6 ≠ 0 := (Or.elim c941 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u39 h))))))))
  have u52 : s 18 ≠ 0 := (Or.elim c1501 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (False.elim (u40 h))))))))
  have u53 : s 26 ≠ 0 := (Or.elim c1856 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (False.elim (u40 h))))))))
  have u54 : s 17 ≠ 2 := (Or.elim c1448 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u48 h))) (fun h => (False.elim (u33 h))))))
  have u55 : s 47 ≠ 2 := (Or.elim c2793 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u48 h))) (fun h => (False.elim (u33 h))))))
  have u56 : s 50 ≠ 2 := (Or.elim c2918 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u48 h))) (fun h => (False.elim (u33 h))))))
  have u57 : s 55 ≠ 2 := (Or.elim c3153 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u48 h))) (fun h => (False.elim (u33 h))))))
  have u58 : s 17 ≠ 1 := (Or.elim c1447 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u48 h))) (fun h => (False.elim (u35 h))))))
  have u59 : s 47 ≠ 1 := (Or.elim c2792 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u48 h))) (fun h => (False.elim (u35 h))))))
  have u60 : s 50 ≠ 1 := (Or.elim c2917 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u48 h))) (fun h => (False.elim (u35 h))))))
  have u61 : s 55 ≠ 1 := (Or.elim c3152 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u48 h))) (fun h => (False.elim (u35 h))))))
  have u62 : s 41 ≠ 2 := (Or.elim c2523 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u49 h))) (fun h => (False.elim (u30 h))))))
  have u63 : s 52 ≠ 2 := (Or.elim c3023 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u49 h))) (fun h => (False.elim (u30 h))))))
  have u64 : s 37 ≠ 2 := (Or.elim c2348 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u49 h))) (fun h => (False.elim (u30 h))))))
  have u65 : s 1 ≠ 2 := (Or.elim c723 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u49 h))) (fun h => (False.elim (u30 h))))))
  have u66 : s 37 ≠ 1 := (Or.elim c2347 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u49 h))) (fun h => (False.elim (u36 h))))))
  have u67 : s 1 ≠ 1 := (Or.elim c722 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u49 h))) (fun h => (False.elim (u36 h))))))
  have u68 : s 41 ≠ 1 := (Or.elim c2522 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u49 h))) (fun h => (False.elim (u36 h))))))
  have u69 : s 52 ≠ 1 := (Or.elim c3022 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u49 h))) (fun h => (False.elim (u36 h))))))
  have u70 : s 20 ≠ 2 := (Or.elim c1578 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u31 h))))))
  have u71 : s 45 ≠ 2 := (Or.elim c2703 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u31 h))))))
  have u72 : s 15 ≠ 2 := (Or.elim c1353 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u31 h))))))
  have u73 : s 25 ≠ 2 := (Or.elim c1803 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u31 h))))))
  have u74 : s 20 ≠ 1 := (Or.elim c1577 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u37 h))))))
  have u75 : s 45 ≠ 1 := (Or.elim c2702 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u37 h))))))
  have u76 : s 15 ≠ 1 := (Or.elim c1352 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u37 h))))))
  have u77 : s 25 ≠ 1 := (Or.elim c1802 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u37 h))))))
  have u78 : s 40 ≠ 2 := (Or.elim c2468 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u32 h))))))
  have u79 : s 46 ≠ 2 := (Or.elim c2743 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u32 h))))))
  have u80 : s 16 ≠ 2 := (Or.elim c1398 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u32 h))))))
  have u81 : s 35 ≠ 2 := (Or.elim c2248 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u32 h))))))
  have u82 : s 40 ≠ 1 := (Or.elim c2467 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u34 h))))))
  have u83 : s 46 ≠ 1 := (Or.elim c2742 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u34 h))))))
  have u84 : s 16 ≠ 1 := (Or.elim c1397 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u34 h))))))
  have u85 : s 35 ≠ 1 := (Or.elim c2247 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => (False.elim (u34 h))))))
  have u86 : s 51 ≠ 1 := (Or.elim c2977 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u54 h))))))
  have u87 : s 0 ≠ 1 := (Or.elim c677 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u54 h))))))
  have u88 : s 36 ≠ 1 := (Or.elim c2302 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u54 h))))))
  have u89 : s 5 ≠ 1 := (Or.elim c912 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u54 h))))))
  have u90 : s 4 ≠ 1 := (Or.elim c857 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u55 h))))))
  have u91 : s 9 ≠ 1 := (Or.elim c1087 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u55 h))))))
  have u92 : s 27 ≠ 1 := (Or.elim c1897 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u55 h))))))
  have u93 : s 42 ≠ 1 := (Or.elim c2567 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u55 h))))))
  have u94 : s 24 ≠ 1 := (Or.elim c1762 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u56 h))))))
  have u95 : s 28 ≠ 1 := (Or.elim c1937 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u56 h))))))
  have u96 : s 43 ≠ 1 := (Or.elim c2607 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u56 h))))))
  have u97 : s 19 ≠ 1 := (Or.elim c1537 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u56 h))))))
  have u98 : s 51 ≠ 2 := (Or.elim c2978 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u58 h))))))
  have u99 : s 0 ≠ 2 := (Or.elim c678 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u58 h))))))
  have u100 : s 36 ≠ 2 := (Or.elim c2303 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u58 h))))))
  have u101 : s 5 ≠ 2 := (Or.elim c913 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u58 h))))))
  have u102 : s 4 ≠ 2 := (Or.elim c858 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u59 h))))))
  have u103 : s 27 ≠ 2 := (Or.elim c1898 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u59 h))))))
  have u104 : s 42 ≠ 2 := (Or.elim c2568 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u59 h))))))
  have u105 : s 9 ≠ 2 := (Or.elim c1088 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u59 h))))))
  have u106 : s 24 ≠ 2 := (Or.elim c1763 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u60 h))))))
  have u107 : s 28 ≠ 2 := (Or.elim c1938 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u60 h))))))
  have u108 : s 43 ≠ 2 := (Or.elim c2608 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u60 h))))))
  have u109 : s 19 ≠ 2 := (Or.elim c1538 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u60 h))))))
  have u110 : s 24 ≠ 0 := (Or.elim c1756 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u68 h))) (fun h => (Or.elim h (fun h => (False.elim (u62 h))) (fun h => (False.elim (u42 h))))))))
  have u111 : s 20 ≠ 0 := (Or.elim c1596 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u68 h))) (fun h => (Or.elim h (fun h => (False.elim (u62 h))) (fun h => (False.elim (u42 h))))))))
  have u112 : s 2 ≠ 1 := (Or.elim c762 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u111 h))) (fun h => (False.elim (u70 h))))))
  have u113 : s 5 ≠ 0 := (Or.elim c891 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u82 h))) (fun h => (Or.elim h (fun h => (False.elim (u78 h))) (fun h => (False.elim (u41 h))))))))
  have u114 : s 9 ≠ 0 := (Or.elim c1071 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u82 h))) (fun h => (Or.elim h (fun h => (False.elim (u78 h))) (fun h => (False.elim (u41 h))))))))
  have u115 : s 18 ≠ 2 := (Or.elim c1488 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u113 h))) (fun h => (False.elim (u89 h))))))
  have u116 : s 48 ≠ 2 := (Or.elim c2828 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u114 h))) (fun h => (False.elim (u91 h))))))
  have u117 : s 49 ≠ 2 := (Or.elim c2878 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u114 h))) (fun h => (False.elim (u91 h))))))
  have u118 : s 53 ≠ 2 := (Or.elim c3063 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u110 h))) (fun h => (False.elim (u94 h))))))
  have u119 : s 54 ≠ 2 := (Or.elim c3128 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u110 h))) (fun h => (False.elim (u94 h))))))
  have u120 : s 18 ≠ 1 := (Or.elim c1487 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u113 h))) (fun h => (False.elim (u101 h))))))
  have u121 : s 46 ≠ 0 := (Or.elim c2761 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u93 h))) (fun h => (Or.elim h (fun h => (False.elim (u104 h))) (fun h => (False.elim (u43 h))))))))
  have u122 : s 48 ≠ 1 := (Or.elim c2827 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u114 h))) (fun h => (False.elim (u105 h))))))
  have u123 : s 49 ≠ 1 := (Or.elim c2877 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u114 h))) (fun h => (False.elim (u105 h))))))
  have u124 : s 53 ≠ 1 := (Or.elim c3062 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u110 h))) (fun h => (False.elim (u106 h))))))
  have u125 : s 54 ≠ 1 := (Or.elim c3127 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u110 h))) (fun h => (False.elim (u106 h))))))
  have u126 : s 52 ≠ 0 := (Or.elim c3001 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u96 h))) (fun h => (Or.elim h (fun h => (False.elim (u108 h))) (fun h => (False.elim (u44 h))))))))
  have u127 : s 2 ≠ 2 := (Or.elim c763 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u111 h))) (fun h => (False.elim (u74 h))))))
  have u128 : s 26 ≠ 2 := (Or.elim c1833 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u46 h))) (fun h => (False.elim (u112 h))))))
  have u129 : s 38 ≠ 1 := (Or.elim c2382 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u52 h))) (fun h => (False.elim (u115 h))))))
  have u130 : s 26 ≠ 1 := (Or.elim c1862 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u47 h))) (fun h => (False.elim (u116 h))))))
  have u131 : s 38 ≠ 2 := (Or.elim c2383 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u52 h))) (fun h => (False.elim (u120 h))))))
  have u132 : s 7 ≠ 1 := (Or.elim c1007 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u121 h))) (fun h => (False.elim (u79 h))))))
  have u133 : s 8 ≠ 1 := (Or.elim c1052 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u121 h))) (fun h => (False.elim (u79 h))))))
  have u134 : s 7 ≠ 2 := (Or.elim c1008 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u121 h))) (fun h => (False.elim (u83 h))))))
  have u135 : s 8 ≠ 2 := (Or.elim c1053 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u121 h))) (fun h => (False.elim (u83 h))))))
  have u136 : s 22 ≠ 2 := (Or.elim c1693 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u126 h))) (fun h => (False.elim (u69 h))))))
  have u137 : s 23 ≠ 2 := (Or.elim c1738 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u126 h))) (fun h => (False.elim (u69 h))))))
  have u138 : s 22 ≠ 1 := (Or.elim c1692 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u126 h))) (fun h => (False.elim (u63 h))))))
  have u139 : s 23 ≠ 1 := (Or.elim c1737 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u126 h))) (fun h => (False.elim (u63 h))))))
  have u140 : s 56 ≠ 1 := (Or.elim c3207 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u53 h))) (fun h => (False.elim (u128 h))))))
  have u141 : s 58 ≠ 2 := (Or.elim c3293 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u45 h))) (fun h => (False.elim (u129 h))))))
  have u142 : s 56 ≠ 2 := (Or.elim c3208 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u53 h))) (fun h => (False.elim (u130 h))))))
  have u143 : s 58 ≠ 1 := (Or.elim c3292 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u45 h))) (fun h => (False.elim (u131 h))))))
  have u144 : s 59 ≠ 1 := (Or.elim c3369 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u1 h))))))))))))
  have u145 : s 59 = 2 := (Or.elim c3361 (fun h => (False.elim (u87 h))) (fun h => (Or.elim h (fun h => (False.elim (u99 h))) (fun h => (Or.elim h (fun h => (False.elim (u67 h))) (fun h => (Or.elim h (fun h => (False.elim (u65 h))) (fun h => (Or.elim h (fun h => (False.elim (u112 h))) (fun h => (Or.elim h (fun h => (False.elim (u127 h))) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => (Or.elim h (fun h => (False.elim (u90 h))) (fun h => (Or.elim h (fun h => (False.elim (u102 h))) (fun h => (Or.elim h (fun h => (False.elim (u89 h))) (fun h => (Or.elim h (fun h => (False.elim (u101 h))) (fun h => (Or.elim h (fun h => (False.elim (u32 h))) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (Or.elim h (fun h => (False.elim (u132 h))) (fun h => (Or.elim h (fun h => (False.elim (u134 h))) (fun h => (Or.elim h (fun h => (False.elim (u133 h))) (fun h => (Or.elim h (fun h => (False.elim (u135 h))) (fun h => (Or.elim h (fun h => (False.elim (u91 h))) (fun h => (Or.elim h (fun h => (False.elim (u105 h))) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (Or.elim h (fun h => (False.elim (u33 h))) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (Or.elim h (fun h => (False.elim (u28 h))) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (Or.elim h (fun h => (False.elim (u29 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u76 h))) (fun h => (Or.elim h (fun h => (False.elim (u72 h))) (fun h => (Or.elim h (fun h => (False.elim (u84 h))) (fun h => (Or.elim h (fun h => (False.elim (u80 h))) (fun h => (Or.elim h (fun h => (False.elim (u58 h))) (fun h => (Or.elim h (fun h => (False.elim (u54 h))) (fun h => (Or.elim h (fun h => (False.elim (u120 h))) (fun h => (Or.elim h (fun h => (False.elim (u115 h))) (fun h => (Or.elim h (fun h => (False.elim (u97 h))) (fun h => (Or.elim h (fun h => (False.elim (u109 h))) (fun h => (Or.elim h (fun h => (False.elim (u74 h))) (fun h => (Or.elim h (fun h => (False.elim (u70 h))) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (Or.elim h (fun h => (False.elim (u138 h))) (fun h => (Or.elim h (fun h => (False.elim (u136 h))) (fun h => (Or.elim h (fun h => (False.elim (u139 h))) (fun h => (Or.elim h (fun h => (False.elim (u137 h))) (fun h => (Or.elim h (fun h => (False.elim (u94 h))) (fun h => (Or.elim h (fun h => (False.elim (u106 h))) (fun h => (Or.elim h (fun h => (False.elim (u77 h))) (fun h => (Or.elim h (fun h => (False.elim (u73 h))) (fun h => (Or.elim h (fun h => (False.elim (u130 h))) (fun h => (Or.elim h (fun h => (False.elim (u128 h))) (fun h => (Or.elim h (fun h => (False.elim (u92 h))) (fun h => (Or.elim h (fun h => (False.elim (u103 h))) (fun h => (Or.elim h (fun h => (False.elim (u95 h))) (fun h => (Or.elim h (fun h => (False.elim (u107 h))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (Or.elim h (fun h => (False.elim (u85 h))) (fun h => (Or.elim h (fun h => (False.elim (u81 h))) (fun h => (Or.elim h (fun h => (False.elim (u88 h))) (fun h => (Or.elim h (fun h => (False.elim (u100 h))) (fun h => (Or.elim h (fun h => (False.elim (u66 h))) (fun h => (Or.elim h (fun h => (False.elim (u64 h))) (fun h => (Or.elim h (fun h => (False.elim (u129 h))) (fun h => (Or.elim h (fun h => (False.elim (u131 h))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (Or.elim h (fun h => (False.elim (u82 h))) (fun h => (Or.elim h (fun h => (False.elim (u78 h))) (fun h => (Or.elim h (fun h => (False.elim (u68 h))) (fun h => (Or.elim h (fun h => (False.elim (u62 h))) (fun h => (Or.elim h (fun h => (False.elim (u93 h))) (fun h => (Or.elim h (fun h => (False.elim (u104 h))) (fun h => (Or.elim h (fun h => (False.elim (u96 h))) (fun h => (Or.elim h (fun h => (False.elim (u108 h))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (Or.elim h (fun h => (False.elim (u75 h))) (fun h => (Or.elim h (fun h => (False.elim (u71 h))) (fun h => (Or.elim h (fun h => (False.elim (u83 h))) (fun h => (Or.elim h (fun h => (False.elim (u79 h))) (fun h => (Or.elim h (fun h => (False.elim (u59 h))) (fun h => (Or.elim h (fun h => (False.elim (u55 h))) (fun h => (Or.elim h (fun h => (False.elim (u122 h))) (fun h => (Or.elim h (fun h => (False.elim (u116 h))) (fun h => (Or.elim h (fun h => (False.elim (u123 h))) (fun h => (Or.elim h (fun h => (False.elim (u117 h))) (fun h => (Or.elim h (fun h => (False.elim (u60 h))) (fun h => (Or.elim h (fun h => (False.elim (u56 h))) (fun h => (Or.elim h (fun h => (False.elim (u86 h))) (fun h => (Or.elim h (fun h => (False.elim (u98 h))) (fun h => (Or.elim h (fun h => (False.elim (u69 h))) (fun h => (Or.elim h (fun h => (False.elim (u63 h))) (fun h => (Or.elim h (fun h => (False.elim (u124 h))) (fun h => (Or.elim h (fun h => (False.elim (u118 h))) (fun h => (Or.elim h (fun h => (False.elim (u125 h))) (fun h => (Or.elim h (fun h => (False.elim (u119 h))) (fun h => (Or.elim h (fun h => (False.elim (u61 h))) (fun h => (Or.elim h (fun h => (False.elim (u57 h))) (fun h => (Or.elim h (fun h => (False.elim (u140 h))) (fun h => (Or.elim h (fun h => (False.elim (u142 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u143 h))) (fun h => (Or.elim h (fun h => (False.elim (u141 h))) (fun h => (Or.elim h (fun h => (False.elim (u144 h))) (fun h => h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  have u146 : s 59 ≠ 3 := (Or.elim c658 (fun h => (False.elim (h u145))) (fun h => h))
  have u147 : s 34 = 0 := (Or.elim c3318 (fun h => (False.elim (h u145))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u10 h))))))
  have u148 : s 14 ≠ 4 := (Or.elim c1335 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u146 h))) (fun h => (False.elim (u0 h))))))
  have u149 : s 3 = 3 := (Or.elim c2191 (fun h => (False.elim (h u147))) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => h))))))
  have u150 : s 32 ≠ 4 := (Or.elim c2135 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u148 h))))))
  exact (Or.elim c799 (fun h => (h u149)) (fun h => (Or.elim h (fun h => (u5 h)) (fun h => (u150 h)))))

private theorem step3371 (s : Fin 60 → Fin 5)
    (c3367 : s 59 ≠ 4)
    (c652 : s 59 ≠ 0 ∨ s 59 ≠ 2)
    (c3318 : s 59 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c2549 : s 41 ≠ 3 ∨ s 59 = 0 ∨ s 59 = 4)
    (c2233 : s 34 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c2503 : s 40 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c2548 : s 41 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c2207 : s 34 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2)
    (c942 : s 6 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c1167 : s 11 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c1622 : s 21 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c807 : s 3 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c1631 : s 21 ≠ 0 ∨ s 41 = 1 ∨ s 41 = 2 ∨ s 41 = 3)
    (c2466 : s 40 ≠ 0 ∨ s 6 = 1 ∨ s 6 = 2 ∨ s 6 = 3)
    (c1446 : s 17 ≠ 0 ∨ s 11 = 1 ∨ s 11 = 2 ∨ s 11 = 3)
    (c2916 : s 50 ≠ 0 ∨ s 11 = 1 ∨ s 11 = 2 ∨ s 11 = 3)
    (c3021 : s 52 ≠ 0 ∨ s 21 = 1 ∨ s 21 = 2 ∨ s 21 = 3)
    (c1576 : s 20 ≠ 0 ∨ s 3 = 1 ∨ s 3 = 2 ∨ s 3 = 3)
    (c2517 : s 41 ≠ 1 ∨ s 20 = 0 ∨ s 20 = 2)
    (c892 : s 5 ≠ 1 ∨ s 40 = 0 ∨ s 40 = 2)
    (c913 : s 5 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1)
    (c1538 : s 19 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1)
    (c1603 : s 20 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1)
    (c1526 : s 19 ≠ 0 ∨ s 5 = 1 ∨ s 5 = 2 ∨ s 5 = 3)
    (c3012 : s 52 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2)
    : s 59 ≠ 2 ∨ s 3 = 2 ∨ s 21 = 2 ∨ s 11 = 2 ∨ s 6 = 2 ∨ s 5 = 3 ∨ s 11 = 3 ∨ s 6 = 3 ∨ s 3 = 3 ∨ s 21 = 3 ∨ s 34 = 0 ∨ s 50 = 1 ∨ s 17 = 1 ∨ s 59 = 1 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13⟩ := hc
  have u0 : s 59 ≠ 4 := c3367
  have u1 : s 59 ≠ 0 := (Or.elim c652 (fun h => h) (fun h => (False.elim (h a0))))
  have u2 : s 34 = 1 := (Or.elim c3318 (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => (False.elim (a10 h))) (fun h => h))))
  have u3 : s 41 ≠ 3 := (Or.elim c2549 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))
  have u4 : s 34 ≠ 2 := (Or.elim c2233 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a13 h))))))
  have u5 : s 40 ≠ 2 := (Or.elim c2503 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a13 h))))))
  have u6 : s 41 ≠ 2 := (Or.elim c2548 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a13 h))))))
  have u7 : s 21 = 0 := (Or.elim c2207 (fun h => (False.elim (h u2))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a2 h))))))
  have u8 : s 6 ≠ 1 := (Or.elim c942 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a10 h))) (fun h => (False.elim (u4 h))))))
  have u9 : s 11 ≠ 1 := (Or.elim c1167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a10 h))) (fun h => (False.elim (u4 h))))))
  have u10 : s 21 ≠ 1 := (Or.elim c1622 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a10 h))) (fun h => (False.elim (u4 h))))))
  have u11 : s 3 ≠ 1 := (Or.elim c807 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a10 h))) (fun h => (False.elim (u4 h))))))
  have u12 : s 41 = 1 := (Or.elim c1631 (fun h => (False.elim (h u7))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u3 h))))))))
  have u13 : s 40 ≠ 0 := (Or.elim c2466 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (False.elim (a7 h))))))))
  have u14 : s 17 ≠ 0 := (Or.elim c1446 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (a6 h))))))))
  have u15 : s 50 ≠ 0 := (Or.elim c2916 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (a6 h))))))))
  have u16 : s 52 ≠ 0 := (Or.elim c3021 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (a9 h))))))))
  have u17 : s 20 ≠ 0 := (Or.elim c1576 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (a8 h))))))))
  have u18 : s 20 = 2 := (Or.elim c2517 (fun h => (False.elim (h u12))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => h))))
  have u19 : s 5 ≠ 1 := (Or.elim c892 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u5 h))))))
  have u20 : s 5 ≠ 2 := (Or.elim c913 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (a12 h))))))
  have u21 : s 19 ≠ 2 := (Or.elim c1538 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (a11 h))))))
  have u22 : s 52 = 1 := (Or.elim c1603 (fun h => (False.elim (h u18))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => h))))
  have u23 : s 19 ≠ 0 := (Or.elim c1526 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (a5 h))))))))
  exact (Or.elim c3012 (fun h => (h u22)) (fun h => (Or.elim h (fun h => (u23 h)) (fun h => (u21 h)))))

private theorem step3372 (s : Fin 60 → Fin 5)
    (c574 : s 52 ≠ 0 ∨ s 52 ≠ 1)
    (c578 : s 52 ≠ 1 ∨ s 52 ≠ 2)
    (c3007 : s 52 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2)
    (c2617 : s 43 ≠ 1 ∨ s 52 = 0 ∨ s 52 = 2)
    (c1261 : s 13 ≠ 0 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 50 = 3)
    (c2938 : s 50 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    : s 52 ≠ 1 ∨ s 43 = 0 ∨ s 13 = 2 ∨ s 50 = 3 ∨ s 50 = 1 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4⟩ := hc
  have u0 : s 52 ≠ 0 := (Or.elim c574 (fun h => h) (fun h => (False.elim (h a0))))
  have u1 : s 52 ≠ 2 := (Or.elim c578 (fun h => (False.elim (h a0))) (fun h => h))
  have u2 : s 13 = 0 := (Or.elim c3007 (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a2 h))))))
  have u3 : s 43 ≠ 1 := (Or.elim c2617 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (u1 h))))))
  have u4 : s 50 = 2 := (Or.elim c1261 (fun h => (False.elim (h u2))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a3 h))))))))
  exact (Or.elim c2938 (fun h => (h u4)) (fun h => (Or.elim h (fun h => (a1 h)) (fun h => (u3 h)))))

private theorem step3374 (s : Fin 60 → Fin 5)
    (c190 : s 17 ≠ 0 ∨ s 17 ≠ 2)
    (c1468 : s 17 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c2978 : s 51 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1)
    (c2303 : s 36 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1)
    (c2986 : s 51 ≠ 0 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 19 = 3)
    (c1766 : s 24 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3)
    (c1522 : s 19 ≠ 1 ∨ s 36 = 0 ∨ s 36 = 2)
    (c2362 : s 37 ≠ 1 ∨ s 24 = 0 ∨ s 24 = 2)
    (c2281 : s 36 ≠ 0 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 58 = 3)
    (c3288 : s 58 ≠ 2 ∨ s 37 = 0 ∨ s 37 = 1)
    : s 17 ≠ 2 ∨ s 37 = 0 ∨ s 51 = 1 ∨ s 19 = 3 ∨ s 19 = 2 ∨ s 24 = 2 ∨ s 51 = 3 ∨ s 58 = 3 ∨ s 58 = 1 ∨ s 17 = 1 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9⟩ := hc
  have u0 : s 17 ≠ 0 := (Or.elim c190 (fun h => h) (fun h => (False.elim (h a0))))
  have u1 : s 51 = 0 := (Or.elim c1468 (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a2 h))))))
  have u2 : s 51 ≠ 2 := (Or.elim c2978 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (a9 h))))))
  have u3 : s 36 ≠ 2 := (Or.elim c2303 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (a9 h))))))
  have u4 : s 19 = 1 := (Or.elim c2986 (fun h => (False.elim (h u1))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (False.elim (a3 h))))))))
  have u5 : s 24 ≠ 0 := (Or.elim c1766 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a6 h))))))))
  have u6 : s 36 = 0 := (Or.elim c1522 (fun h => (False.elim (h u4))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u3 h))))))
  have u7 : s 37 ≠ 1 := (Or.elim c2362 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (a5 h))))))
  have u8 : s 58 = 2 := (Or.elim c2281 (fun h => (False.elim (h u6))) (fun h => (Or.elim h (fun h => (False.elim (a8 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a7 h))))))))
  exact (Or.elim c3288 (fun h => (h u8)) (fun h => (Or.elim h (fun h => (a1 h)) (fun h => (u7 h)))))

private theorem step3375 (s : Fin 60 → Fin 5)
    (c3367 : s 59 ≠ 4)
    (c162 : s 14 ≠ 1 ∨ s 14 ≠ 4)
    (c156 : s 14 ≠ 0 ∨ s 14 ≠ 1)
    (c3354 : s 59 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c2640 : s 43 ≠ 4 ∨ s 59 = 3 ∨ s 59 = 4)
    (c2959 : s 51 ≠ 3 ∨ s 43 = 0 ∨ s 43 = 4)
    (c1464 : s 17 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c161 : s 14 ≠ 1 ∨ s 14 ≠ 3)
    (c1465 : s 17 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4)
    (c680 : s 0 ≠ 4 ∨ s 17 = 3 ∨ s 17 = 4)
    (c3309 : s 58 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c1773 : s 24 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1)
    (c1548 : s 19 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1)
    (c1549 : s 19 ≠ 3 ∨ s 52 = 0 ∨ s 52 = 4)
    (c2618 : s 43 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1)
    (c1738 : s 23 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1)
    (c1727 : s 23 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c1042 : s 8 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c2957 : s 51 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c2356 : s 37 ≠ 0 ∨ s 23 = 1 ∨ s 23 = 2 ∨ s 23 = 3)
    (c3374 : s 17 ≠ 2 ∨ s 37 = 0 ∨ s 51 = 1 ∨ s 19 = 3 ∨ s 19 = 2 ∨ s 24 = 2 ∨ s 51 = 3 ∨ s 58 = 3 ∨ s 58 = 1 ∨ s 17 = 1)
    (c1302 : s 14 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2)
    (c676 : s 0 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c1126 : s 10 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c2976 : s 51 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c1446 : s 17 ≠ 0 ∨ s 11 = 1 ∨ s 11 = 2 ∨ s 11 = 3)
    (c1384 : s 16 ≠ 3 ∨ s 0 = 0 ∨ s 0 = 4)
    (c1417 : s 16 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2)
    (c1423 : s 16 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c1197 : s 11 ≠ 1 ∨ s 31 = 0 ∨ s 31 = 2)
    (c1056 : s 8 ≠ 0 ∨ s 16 = 1 ∨ s 16 = 2 ∨ s 16 = 3)
    (c2078 : s 31 ≠ 2 ∨ s 8 = 0 ∨ s 8 = 1)
    : s 52 = 0 ∨ s 52 = 1 ∨ s 43 = 0 ∨ s 52 = 4 ∨ s 11 = 2 ∨ s 10 = 2 ∨ s 23 = 3 ∨ s 11 = 3 ∨ s 31 = 0 ∨ s 58 = 1 ∨ s 17 = 1 ∨ s 14 ≠ 1 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11⟩ := hc
  have u0 : s 59 ≠ 4 := c3367
  have u1 : s 14 ≠ 4 := (Or.elim c162 (fun h => (False.elim (h a11))) (fun h => h))
  have u2 : s 14 ≠ 0 := (Or.elim c156 (fun h => h) (fun h => (False.elim (h a11))))
  have u3 : s 59 ≠ 3 := (Or.elim c3354 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u1 h))))))
  have u4 : s 43 ≠ 4 := (Or.elim c2640 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u0 h))))))
  have u5 : s 51 ≠ 3 := (Or.elim c2959 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u4 h))))))
  have u6 : s 17 ≠ 3 := (Or.elim c1464 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u1 h))))))
  have u7 : s 14 ≠ 3 := (Or.elim c161 (fun h => (False.elim (h a11))) (fun h => h))
  have u8 : s 17 ≠ 4 := (Or.elim c1465 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u1 h))))))
  have u9 : s 0 ≠ 4 := (Or.elim c680 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u8 h))))))
  have u10 : s 58 ≠ 3 := (Or.elim c3309 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u1 h))))))
  have u11 : s 24 ≠ 2 := (Or.elim c1773 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))
  have u12 : s 19 ≠ 2 := (Or.elim c1548 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))
  have u13 : s 19 ≠ 3 := (Or.elim c1549 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a3 h))))))
  have u14 : s 43 ≠ 2 := (Or.elim c2618 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))
  have u15 : s 23 ≠ 2 := (Or.elim c1738 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))
  have u16 : s 23 ≠ 1 := (Or.elim c1727 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u14 h))))))
  have u17 : s 8 ≠ 1 := (Or.elim c1042 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u14 h))))))
  have u18 : s 51 ≠ 1 := (Or.elim c2957 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u14 h))))))
  have u19 : s 37 ≠ 0 := (Or.elim c2356 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (a6 h))))))))
  have u20 : s 17 ≠ 2 := (Or.elim c3374 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (a9 h))) (fun h => (False.elim (a10 h))))))))))))))))))))
  have u21 : s 17 = 0 := (Or.elim c1302 (fun h => (False.elim (h a11))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u20 h))))))
  have u22 : s 0 ≠ 0 := (Or.elim c676 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a10 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u6 h))))))))
  have u23 : s 10 ≠ 0 := (Or.elim c1126 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a10 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u6 h))))))))
  have u24 : s 51 ≠ 0 := (Or.elim c2976 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a10 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u6 h))))))))
  have u25 : s 11 = 1 := (Or.elim c1446 (fun h => (False.elim (h u21))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (False.elim (a7 h))))))))
  have u26 : s 16 ≠ 3 := (Or.elim c1384 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u9 h))))))
  have u27 : s 16 ≠ 1 := (Or.elim c1417 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (False.elim (a5 h))))))
  have u28 : s 16 ≠ 2 := (Or.elim c1423 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (False.elim (u18 h))))))
  have u29 : s 31 = 2 := (Or.elim c1197 (fun h => (False.elim (h u25))) (fun h => (Or.elim h (fun h => (False.elim (a8 h))) (fun h => h))))
  have u30 : s 8 ≠ 0 := (Or.elim c1056 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (Or.elim h (fun h => (False.elim (u28 h))) (fun h => (False.elim (u26 h))))))))
  exact (Or.elim c2078 (fun h => (h u29)) (fun h => (Or.elim h (fun h => (u30 h)) (fun h => (u17 h)))))

private theorem step3376 (s : Fin 60 → Fin 5)
    (c3367 : s 59 ≠ 4)
    (c3370 : s 14 = 1 ∨ s 14 = 2 ∨ s 57 = 2 ∨ s 57 = 1)
    (c156 : s 14 ≠ 0 ∨ s 14 ≠ 1)
    (c161 : s 14 ≠ 1 ∨ s 14 ≠ 3)
    (c162 : s 14 ≠ 1 ∨ s 14 ≠ 4)
    (c3352 : s 59 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3354 : s 59 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c1462 : s 17 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c2132 : s 32 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c2932 : s 50 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3167 : s 55 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3307 : s 58 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c1464 : s 17 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c3255 : s 57 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4)
    (c2934 : s 50 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c3254 : s 57 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c3309 : s 58 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c1465 : s 17 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4)
    (c2135 : s 32 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4)
    (c2640 : s 43 ≠ 4 ∨ s 59 = 3 ∨ s 59 = 4)
    (c2685 : s 44 ≠ 4 ∨ s 59 = 3 ∨ s 59 = 4)
    (c2100 : s 31 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c2221 : s 34 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c2671 : s 44 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c2096 : s 31 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c2141 : s 32 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c2186 : s 33 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c1260 : s 13 ≠ 4 ∨ s 17 = 3 ∨ s 17 = 4)
    (c1609 : s 21 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4)
    (c799 : s 3 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4)
    (c934 : s 6 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4)
    (c1114 : s 10 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4)
    (c1159 : s 11 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4)
    (c1249 : s 13 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4)
    (c1734 : s 23 ≠ 3 ∨ s 44 = 0 ∨ s 44 = 4)
    (c929 : s 5 ≠ 3 ∨ s 31 = 0 ∨ s 31 = 4)
    (c1113 : s 10 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1248 : s 13 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c933 : s 6 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1158 : s 11 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1608 : s 21 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c798 : s 3 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c3010 : s 52 ≠ 4 ∨ s 13 = 3 ∨ s 13 = 4)
    (c3371 : s 59 ≠ 2 ∨ s 3 = 2 ∨ s 21 = 2 ∨ s 11 = 2 ∨ s 6 = 2 ∨ s 5 = 3 ∨ s 11 = 3 ∨ s 6 = 3 ∨ s 3 = 3 ∨ s 21 = 3 ∨ s 34 = 0 ∨ s 50 = 1 ∨ s 17 = 1 ∨ s 59 = 1)
    (c2636 : s 43 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c3004 : s 52 ≠ 3 ∨ s 43 = 0 ∨ s 43 = 4)
    (c3372 : s 52 ≠ 1 ∨ s 43 = 0 ∨ s 13 = 2 ∨ s 50 = 3 ∨ s 50 = 1)
    (c3375 : s 52 = 0 ∨ s 52 = 1 ∨ s 43 = 0 ∨ s 52 = 4 ∨ s 11 = 2 ∨ s 10 = 2 ∨ s 23 = 3 ∨ s 11 = 3 ∨ s 31 = 0 ∨ s 58 = 1 ∨ s 17 = 1 ∨ s 14 ≠ 1)
    (c575 : s 52 ≠ 0 ∨ s 52 ≠ 2)
    (c3021 : s 52 ≠ 0 ∨ s 21 = 1 ∨ s 21 = 2 ∨ s 21 = 3)
    (c1691 : s 22 ≠ 0 ∨ s 52 = 1 ∨ s 52 = 2 ∨ s 52 = 3)
    (c1546 : s 19 ≠ 0 ∨ s 52 = 1 ∨ s 52 = 2 ∨ s 52 = 3)
    (c1636 : s 21 ≠ 0 ∨ s 52 = 1 ∨ s 52 = 2 ∨ s 52 = 3)
    (c1617 : s 21 ≠ 1 ∨ s 33 = 0 ∨ s 33 = 2)
    (c1622 : s 21 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c2173 : s 33 ≠ 2 ∨ s 22 = 0 ∨ s 22 = 1)
    (c2207 : s 34 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2)
    (c2213 : s 34 ≠ 2 ∨ s 55 = 0 ∨ s 55 = 1)
    (c248 : s 22 ≠ 1 ∨ s 22 ≠ 2)
    (c3273 : s 58 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c3146 : s 55 ≠ 0 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 10 = 3)
    (c2317 : s 36 ≠ 1 ∨ s 22 = 0 ∨ s 22 = 2)
    (c2281 : s 36 ≠ 0 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 58 = 3)
    (c1137 : s 10 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2)
    (c1523 : s 19 ≠ 2 ∨ s 36 = 0 ∨ s 36 = 1)
    : s 14 = 2 ∨ s 57 = 1 ∨ s 57 = 2 := by
  by_contra hc
  try simp only [not_or] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 59 ≠ 4 := c3367
  have u1 : s 14 = 1 := (Or.elim c3370 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (a1 h))))))))
  have u2 : s 14 ≠ 0 := (Or.elim c156 (fun h => h) (fun h => (False.elim (h u1))))
  have u3 : s 14 ≠ 3 := (Or.elim c161 (fun h => (False.elim (h u1))) (fun h => h))
  have u4 : s 14 ≠ 4 := (Or.elim c162 (fun h => (False.elim (h u1))) (fun h => h))
  have u5 : s 59 ≠ 1 := (Or.elim c3352 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a0 h))))))
  have u6 : s 59 ≠ 3 := (Or.elim c3354 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u4 h))))))
  have u7 : s 17 ≠ 1 := (Or.elim c1462 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a0 h))))))
  have u8 : s 32 ≠ 1 := (Or.elim c2132 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a0 h))))))
  have u9 : s 50 ≠ 1 := (Or.elim c2932 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a0 h))))))
  have u10 : s 55 ≠ 1 := (Or.elim c3167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a0 h))))))
  have u11 : s 58 ≠ 1 := (Or.elim c3307 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a0 h))))))
  have u12 : s 17 ≠ 3 := (Or.elim c1464 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u4 h))))))
  have u13 : s 57 ≠ 4 := (Or.elim c3255 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u4 h))))))
  have u14 : s 50 ≠ 3 := (Or.elim c2934 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u4 h))))))
  have u15 : s 57 ≠ 3 := (Or.elim c3254 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u4 h))))))
  have u16 : s 58 ≠ 3 := (Or.elim c3309 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u4 h))))))
  have u17 : s 17 ≠ 4 := (Or.elim c1465 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u4 h))))))
  have u18 : s 32 ≠ 4 := (Or.elim c2135 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u4 h))))))
  have u19 : s 43 ≠ 4 := (Or.elim c2640 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u0 h))))))
  have u20 : s 44 ≠ 4 := (Or.elim c2685 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u0 h))))))
  have u21 : s 31 ≠ 4 := (Or.elim c2100 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u13 h))))))
  have u22 : s 34 ≠ 0 := (Or.elim c2221 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u15 h))))))))
  have u23 : s 44 ≠ 0 := (Or.elim c2671 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u15 h))))))))
  have u24 : s 31 ≠ 0 := (Or.elim c2096 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u15 h))))))))
  have u25 : s 32 ≠ 0 := (Or.elim c2141 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u15 h))))))))
  have u26 : s 33 ≠ 0 := (Or.elim c2186 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u15 h))))))))
  have u27 : s 13 ≠ 4 := (Or.elim c1260 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u17 h))))))
  have u28 : s 21 ≠ 3 := (Or.elim c1609 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u18 h))))))
  have u29 : s 3 ≠ 3 := (Or.elim c799 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u18 h))))))
  have u30 : s 6 ≠ 3 := (Or.elim c934 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u18 h))))))
  have u31 : s 10 ≠ 3 := (Or.elim c1114 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u18 h))))))
  have u32 : s 11 ≠ 3 := (Or.elim c1159 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u18 h))))))
  have u33 : s 13 ≠ 3 := (Or.elim c1249 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u18 h))))))
  have u34 : s 23 ≠ 3 := (Or.elim c1734 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (False.elim (u20 h))))))
  have u35 : s 5 ≠ 3 := (Or.elim c929 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (False.elim (u21 h))))))
  have u36 : s 10 ≠ 2 := (Or.elim c1113 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u8 h))))))
  have u37 : s 13 ≠ 2 := (Or.elim c1248 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u8 h))))))
  have u38 : s 6 ≠ 2 := (Or.elim c933 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u8 h))))))
  have u39 : s 11 ≠ 2 := (Or.elim c1158 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u8 h))))))
  have u40 : s 21 ≠ 2 := (Or.elim c1608 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u8 h))))))
  have u41 : s 3 ≠ 2 := (Or.elim c798 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u8 h))))))
  have u42 : s 52 ≠ 4 := (Or.elim c3010 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u33 h))) (fun h => (False.elim (u27 h))))))
  have u43 : s 59 ≠ 2 := (Or.elim c3371 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u41 h))) (fun h => (Or.elim h (fun h => (False.elim (u40 h))) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (Or.elim h (fun h => (False.elim (u32 h))) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => (Or.elim h (fun h => (False.elim (u29 h))) (fun h => (Or.elim h (fun h => (False.elim (u28 h))) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u5 h))))))))))))))))))))))))))))
  have u44 : s 43 ≠ 0 := (Or.elim c2636 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u43 h))) (fun h => (False.elim (u6 h))))))))
  have u45 : s 52 ≠ 3 := (Or.elim c3004 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u44 h))) (fun h => (False.elim (u19 h))))))
  have u46 : s 52 ≠ 1 := (Or.elim c3372 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u44 h))) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (u9 h))))))))))
  have u47 : s 52 = 0 := (Or.elim c3375 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u46 h))) (fun h => (Or.elim h (fun h => (False.elim (u44 h))) (fun h => (Or.elim h (fun h => (False.elim (u42 h))) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (Or.elim h (fun h => (False.elim (u32 h))) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (h u1))))))))))))))))))))))))
  have u48 : s 52 ≠ 2 := (Or.elim c575 (fun h => (False.elim (h u47))) (fun h => h))
  have u49 : s 21 = 1 := (Or.elim c3021 (fun h => (False.elim (h u47))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u40 h))) (fun h => (False.elim (u28 h))))))))
  have u50 : s 22 ≠ 0 := (Or.elim c1691 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u46 h))) (fun h => (Or.elim h (fun h => (False.elim (u48 h))) (fun h => (False.elim (u45 h))))))))
  have u51 : s 19 ≠ 0 := (Or.elim c1546 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u46 h))) (fun h => (Or.elim h (fun h => (False.elim (u48 h))) (fun h => (False.elim (u45 h))))))))
  have u52 : s 21 ≠ 0 := (Or.elim c1636 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u46 h))) (fun h => (Or.elim h (fun h => (False.elim (u48 h))) (fun h => (False.elim (u45 h))))))))
  have u53 : s 33 = 2 := (Or.elim c1617 (fun h => (False.elim (h u49))) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => h))))
  have u54 : s 34 = 2 := (Or.elim c1622 (fun h => (False.elim (h u49))) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => h))))
  have u55 : s 22 = 1 := (Or.elim c2173 (fun h => (False.elim (h u53))) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => h))))
  have u56 : s 34 ≠ 1 := (Or.elim c2207 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u52 h))) (fun h => (False.elim (u40 h))))))
  have u57 : s 55 = 0 := (Or.elim c2213 (fun h => (False.elim (h u54))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u10 h))))))
  have u58 : s 22 ≠ 2 := (Or.elim c248 (fun h => (False.elim (h u55))) (fun h => h))
  have u59 : s 58 ≠ 2 := (Or.elim c3273 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u56 h))))))
  have u60 : s 10 = 1 := (Or.elim c3146 (fun h => (False.elim (h u57))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u31 h))))))))
  have u61 : s 36 ≠ 1 := (Or.elim c2317 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u50 h))) (fun h => (False.elim (u58 h))))))
  have u62 : s 36 ≠ 0 := (Or.elim c2281 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u59 h))) (fun h => (False.elim (u16 h))))))))
  have u63 : s 19 = 2 := (Or.elim c1137 (fun h => (False.elim (h u60))) (fun h => (Or.elim h (fun h => (False.elim (u51 h))) (fun h => h))))
  exact (Or.elim c1523 (fun h => (h u63)) (fun h => (Or.elim h (fun h => (u62 h)) (fun h => (u61 h)))))

private theorem step3377 (s : Fin 60 → Fin 5)
    (c157 : s 14 ≠ 0 ∨ s 14 ≠ 2)
    (c164 : s 14 ≠ 2 ∨ s 14 ≠ 4)
    (c1464 : s 17 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c163 : s 14 ≠ 2 ∨ s 14 ≠ 3)
    (c1465 : s 17 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4)
    (c680 : s 0 ≠ 4 ∨ s 17 = 3 ∨ s 17 = 4)
    (c160 : s 14 ≠ 1 ∨ s 14 ≠ 2)
    (c1463 : s 17 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c1303 : s 14 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1)
    (c676 : s 0 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c1126 : s 10 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c1176 : s 11 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c1256 : s 13 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c2976 : s 51 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c1456 : s 17 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3)
    (c1384 : s 16 ≠ 3 ∨ s 0 = 0 ∨ s 0 = 4)
    (c1418 : s 16 ≠ 2 ∨ s 10 = 0 ∨ s 10 = 1)
    (c2088 : s 31 ≠ 2 ∨ s 11 = 0 ∨ s 11 = 1)
    (c2963 : s 51 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1)
    (c1422 : s 16 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2)
    (c1268 : s 13 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c1056 : s 8 ≠ 0 ∨ s 16 = 1 ∨ s 16 = 2 ∨ s 16 = 3)
    (c1062 : s 8 ≠ 1 ∨ s 31 = 0 ∨ s 31 = 2)
    (c2957 : s 51 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c2598 : s 43 ≠ 2 ∨ s 8 = 0 ∨ s 8 = 1)
    : s 17 = 1 ∨ s 43 = 0 ∨ s 11 = 1 ∨ s 13 = 1 ∨ s 10 = 1 ∨ s 13 = 3 ∨ s 31 = 0 ∨ s 14 ≠ 2 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7⟩ := hc
  have u0 : s 14 ≠ 0 := (Or.elim c157 (fun h => h) (fun h => (False.elim (h a7))))
  have u1 : s 14 ≠ 4 := (Or.elim c164 (fun h => (False.elim (h a7))) (fun h => h))
  have u2 : s 17 ≠ 3 := (Or.elim c1464 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (u1 h))))))
  have u3 : s 14 ≠ 3 := (Or.elim c163 (fun h => (False.elim (h a7))) (fun h => h))
  have u4 : s 17 ≠ 4 := (Or.elim c1465 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u1 h))))))
  have u5 : s 0 ≠ 4 := (Or.elim c680 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u4 h))))))
  have u6 : s 14 ≠ 1 := (Or.elim c160 (fun h => h) (fun h => (False.elim (h a7))))
  have u7 : s 17 ≠ 2 := (Or.elim c1463 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (u6 h))))))
  have u8 : s 17 = 0 := (Or.elim c1303 (fun h => (False.elim (h a7))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a0 h))))))
  have u9 : s 0 ≠ 0 := (Or.elim c676 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u2 h))))))))
  have u10 : s 10 ≠ 0 := (Or.elim c1126 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u2 h))))))))
  have u11 : s 11 ≠ 0 := (Or.elim c1176 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u2 h))))))))
  have u12 : s 13 ≠ 0 := (Or.elim c1256 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u2 h))))))))
  have u13 : s 51 ≠ 0 := (Or.elim c2976 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u2 h))))))))
  have u14 : s 13 = 2 := (Or.elim c1456 (fun h => (False.elim (h u8))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a5 h))))))))
  have u15 : s 16 ≠ 3 := (Or.elim c1384 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u5 h))))))
  have u16 : s 16 ≠ 2 := (Or.elim c1418 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (a4 h))))))
  have u17 : s 31 ≠ 2 := (Or.elim c2088 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (a2 h))))))
  have u18 : s 51 ≠ 2 := (Or.elim c2963 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (a3 h))))))
  have u19 : s 16 ≠ 1 := (Or.elim c1422 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u18 h))))))
  have u20 : s 51 = 1 := (Or.elim c1268 (fun h => (False.elim (h u14))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => h))))
  have u21 : s 8 ≠ 0 := (Or.elim c1056 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (u15 h))))))))
  have u22 : s 8 ≠ 1 := (Or.elim c1062 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a6 h))) (fun h => (False.elim (u17 h))))))
  have u23 : s 43 = 2 := (Or.elim c2957 (fun h => (False.elim (h u20))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => h))))
  exact (Or.elim c2598 (fun h => (h u23)) (fun h => (Or.elim h (fun h => (u21 h)) (fun h => (u22 h)))))

private theorem step3379 (s : Fin 60 → Fin 5)
    (c1432 : s 17 ≠ 1 ∨ s 36 = 0 ∨ s 36 = 2)
    (c1523 : s 19 ≠ 2 ∨ s 36 = 0 ∨ s 36 = 1)
    (c1483 : s 18 ≠ 2 ∨ s 36 = 0 ∨ s 36 = 1)
    (c2288 : s 36 ≠ 2 ∨ s 7 = 0 ∨ s 7 = 1)
    (c3012 : s 52 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2)
    (c2337 : s 37 ≠ 1 ∨ s 18 = 0 ∨ s 18 = 2)
    (c986 : s 7 ≠ 0 ∨ s 37 = 1 ∨ s 37 = 2 ∨ s 37 = 3)
    (c1636 : s 21 ≠ 0 ∨ s 52 = 1 ∨ s 52 = 2 ∨ s 52 = 3)
    (c2348 : s 37 ≠ 2 ∨ s 21 = 0 ∨ s 21 = 1)
    : s 36 = 0 ∨ s 7 = 1 ∨ s 37 = 3 ∨ s 19 = 0 ∨ s 18 = 0 ∨ s 52 = 2 ∨ s 36 = 1 ∨ s 17 ≠ 1 ∨ s 52 = 3 ∨ s 21 = 1 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9⟩ := hc
  have u0 : s 36 = 2 := (Or.elim c1432 (fun h => (False.elim (h a7))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => h))))
  have u1 : s 19 ≠ 2 := (Or.elim c1523 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a6 h))))))
  have u2 : s 18 ≠ 2 := (Or.elim c1483 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a6 h))))))
  have u3 : s 7 = 0 := (Or.elim c2288 (fun h => (False.elim (h u0))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a1 h))))))
  have u4 : s 52 ≠ 1 := (Or.elim c3012 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (u1 h))))))
  have u5 : s 37 ≠ 1 := (Or.elim c2337 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (False.elim (u2 h))))))
  have u6 : s 37 = 2 := (Or.elim c986 (fun h => (False.elim (h u3))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a2 h))))))))
  have u7 : s 21 ≠ 0 := (Or.elim c1636 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => (False.elim (a8 h))))))))
  exact (Or.elim c2348 (fun h => (h u6)) (fun h => (Or.elim h (fun h => (u7 h)) (fun h => (a9 h)))))

private theorem step3380 (s : Fin 60 → Fin 5)
    (c3379 : s 36 = 0 ∨ s 7 = 1 ∨ s 37 = 3 ∨ s 19 = 0 ∨ s 18 = 0 ∨ s 52 = 2 ∨ s 36 = 1 ∨ s 17 ≠ 1 ∨ s 52 = 3 ∨ s 21 = 1)
    (c399 : s 36 ≠ 0 ∨ s 36 ≠ 2)
    (c2286 : s 36 ≠ 0 ∨ s 7 = 1 ∨ s 7 = 2 ∨ s 7 = 3)
    (c3281 : s 58 ≠ 0 ∨ s 36 = 1 ∨ s 36 = 2 ∨ s 36 = 3)
    (c998 : s 7 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c2417 : s 39 ≠ 1 ∨ s 58 = 0 ∨ s 58 = 2)
    : s 7 = 1 ∨ s 37 = 3 ∨ s 19 = 0 ∨ s 18 = 0 ∨ s 52 = 2 ∨ s 36 = 1 ∨ s 36 = 3 ∨ s 17 ≠ 1 ∨ s 52 = 3 ∨ s 21 = 1 ∨ s 7 = 3 ∨ s 39 = 0 ∨ s 58 = 2 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12⟩ := hc
  have u0 : s 36 = 0 := (Or.elim c3379 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => (Or.elim h (fun h => (False.elim (h a7))) (fun h => (Or.elim h (fun h => (False.elim (a8 h))) (fun h => (False.elim (a9 h))))))))))))))))))))
  have u1 : s 36 ≠ 2 := (Or.elim c399 (fun h => (False.elim (h u0))) (fun h => h))
  have u2 : s 7 = 2 := (Or.elim c2286 (fun h => (False.elim (h u0))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a10 h))))))))
  have u3 : s 58 ≠ 0 := (Or.elim c3281 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a6 h))))))))
  have u4 : s 39 = 1 := (Or.elim c998 (fun h => (False.elim (h u2))) (fun h => (Or.elim h (fun h => (False.elim (a11 h))) (fun h => h))))
  exact (Or.elim c2417 (fun h => (h u4)) (fun h => (Or.elim h (fun h => (u3 h)) (fun h => (a12 h)))))

private theorem step3381 (s : Fin 60 → Fin 5)
    (c2963 : s 51 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1)
    (c3008 : s 52 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1)
    (c1511 : s 18 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3)
    (c1421 : s 16 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3)
    (c1541 : s 19 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3)
    (c2339 : s 37 ≠ 3 ∨ s 18 = 0 ∨ s 18 = 4)
    (c3380 : s 7 = 1 ∨ s 37 = 3 ∨ s 19 = 0 ∨ s 18 = 0 ∨ s 52 = 2 ∨ s 36 = 1 ∨ s 36 = 3 ∨ s 17 ≠ 1 ∨ s 52 = 3 ∨ s 21 = 1 ∨ s 7 = 3 ∨ s 39 = 0 ∨ s 58 = 2)
    (c79 : s 7 ≠ 0 ∨ s 7 ≠ 1)
    (c83 : s 7 ≠ 1 ∨ s 7 ≠ 2)
    (c1017 : s 7 ≠ 1 ∨ s 31 = 0 ∨ s 31 = 2)
    (c2422 : s 39 ≠ 1 ∨ s 7 = 0 ∨ s 7 = 2)
    (c1402 : s 16 ≠ 1 ∨ s 7 = 0 ∨ s 7 = 2)
    (c2093 : s 31 ≠ 2 ∨ s 21 = 0 ∨ s 21 = 1)
    (c1683 : s 22 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c2298 : s 36 ≠ 2 ∨ s 16 = 0 ∨ s 16 = 1)
    (c1636 : s 21 ≠ 0 ∨ s 52 = 1 ∨ s 52 = 2 ∨ s 52 = 3)
    (c3027 : s 52 ≠ 1 ∨ s 22 = 0 ∨ s 22 = 2)
    (c1666 : s 22 ≠ 0 ∨ s 36 = 1 ∨ s 36 = 2 ∨ s 36 = 3)
    : s 13 = 0 ∨ s 36 = 1 ∨ s 51 = 1 ∨ s 36 = 3 ∨ s 17 ≠ 1 ∨ s 52 = 3 ∨ s 51 = 3 ∨ s 18 = 4 ∨ s 21 = 1 ∨ s 13 = 1 ∨ s 7 = 3 ∨ s 31 = 0 ∨ s 39 = 0 ∨ s 58 = 2 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13⟩ := hc
  have u0 : s 51 ≠ 2 := (Or.elim c2963 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a9 h))))))
  have u1 : s 52 ≠ 2 := (Or.elim c3008 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a9 h))))))
  have u2 : s 18 ≠ 0 := (Or.elim c1511 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (a6 h))))))))
  have u3 : s 16 ≠ 0 := (Or.elim c1421 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (a6 h))))))))
  have u4 : s 19 ≠ 0 := (Or.elim c1541 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (a6 h))))))))
  have u5 : s 37 ≠ 3 := (Or.elim c2339 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a7 h))))))
  have u6 : s 7 = 1 := (Or.elim c3380 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (h a4))) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => (Or.elim h (fun h => (False.elim (a8 h))) (fun h => (Or.elim h (fun h => (False.elim (a10 h))) (fun h => (Or.elim h (fun h => (False.elim (a12 h))) (fun h => (False.elim (a13 h))))))))))))))))))))))))))
  have u7 : s 7 ≠ 0 := (Or.elim c79 (fun h => h) (fun h => (False.elim (h u6))))
  have u8 : s 7 ≠ 2 := (Or.elim c83 (fun h => (False.elim (h u6))) (fun h => h))
  have u9 : s 31 = 2 := (Or.elim c1017 (fun h => (False.elim (h u6))) (fun h => (Or.elim h (fun h => (False.elim (a11 h))) (fun h => h))))
  have u10 : s 39 ≠ 1 := (Or.elim c2422 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u8 h))))))
  have u11 : s 16 ≠ 1 := (Or.elim c1402 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u8 h))))))
  have u12 : s 21 = 0 := (Or.elim c2093 (fun h => (False.elim (h u9))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a8 h))))))
  have u13 : s 22 ≠ 2 := (Or.elim c1683 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a12 h))) (fun h => (False.elim (u10 h))))))
  have u14 : s 36 ≠ 2 := (Or.elim c2298 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u11 h))))))
  have u15 : s 52 = 1 := (Or.elim c1636 (fun h => (False.elim (h u12))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a5 h))))))))
  have u16 : s 22 = 0 := (Or.elim c3027 (fun h => (False.elim (h u15))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u13 h))))))
  exact (Or.elim c1666 (fun h => (h u16)) (fun h => (Or.elim h (fun h => (a1 h)) (fun h => (Or.elim h (fun h => (u14 h)) (fun h => (a3 h)))))))

private theorem step3382 (s : Fin 60 → Fin 5)
    (c3367 : s 59 ≠ 4)
    (c164 : s 14 ≠ 2 ∨ s 14 ≠ 4)
    (c157 : s 14 ≠ 0 ∨ s 14 ≠ 2)
    (c3354 : s 59 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c2460 : s 39 ≠ 4 ∨ s 59 = 3 ∨ s 59 = 4)
    (c999 : s 7 ≠ 3 ∨ s 39 = 0 ∨ s 39 = 4)
    (c2640 : s 43 ≠ 4 ∨ s 59 = 3 ∨ s 59 = 4)
    (c163 : s 14 ≠ 2 ∨ s 14 ≠ 3)
    (c1465 : s 17 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4)
    (c2934 : s 50 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c160 : s 14 ≠ 1 ∨ s 14 ≠ 2)
    (c3308 : s 58 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c2933 : s 50 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c1463 : s 17 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c2959 : s 51 ≠ 3 ∨ s 43 = 0 ∨ s 43 = 4)
    (c3004 : s 52 ≠ 3 ∨ s 43 = 0 ∨ s 43 = 4)
    (c3377 : s 17 = 1 ∨ s 43 = 0 ∨ s 11 = 1 ∨ s 13 = 1 ∨ s 10 = 1 ∨ s 13 = 3 ∨ s 31 = 0 ∨ s 14 ≠ 2)
    (c189 : s 17 ≠ 0 ∨ s 17 ≠ 1)
    (c2304 : s 36 ≠ 3 ∨ s 17 = 0 ∨ s 17 = 4)
    (c2977 : s 51 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2)
    (c2302 : s 36 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2)
    (c3381 : s 13 = 0 ∨ s 36 = 1 ∨ s 51 = 1 ∨ s 36 = 3 ∨ s 17 ≠ 1 ∨ s 52 = 3 ∨ s 51 = 3 ∨ s 18 = 4 ∨ s 21 = 1 ∨ s 13 = 1 ∨ s 7 = 3 ∨ s 31 = 0 ∨ s 39 = 0 ∨ s 58 = 2)
    (c146 : s 13 ≠ 0 ∨ s 13 ≠ 2)
    (c1261 : s 13 ≠ 0 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 50 = 3)
    (c2961 : s 51 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3)
    (c2937 : s 50 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c2613 : s 43 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    : s 43 = 0 ∨ s 18 = 4 ∨ s 11 = 1 ∨ s 21 = 1 ∨ s 13 = 1 ∨ s 10 = 1 ∨ s 13 = 3 ∨ s 31 = 0 ∨ s 39 = 0 ∨ s 14 ≠ 2 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9⟩ := hc
  have u0 : s 59 ≠ 4 := c3367
  have u1 : s 14 ≠ 4 := (Or.elim c164 (fun h => (False.elim (h a9))) (fun h => h))
  have u2 : s 14 ≠ 0 := (Or.elim c157 (fun h => h) (fun h => (False.elim (h a9))))
  have u3 : s 59 ≠ 3 := (Or.elim c3354 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u1 h))))))
  have u4 : s 39 ≠ 4 := (Or.elim c2460 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u0 h))))))
  have u5 : s 7 ≠ 3 := (Or.elim c999 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a8 h))) (fun h => (False.elim (u4 h))))))
  have u6 : s 43 ≠ 4 := (Or.elim c2640 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u0 h))))))
  have u7 : s 14 ≠ 3 := (Or.elim c163 (fun h => (False.elim (h a9))) (fun h => h))
  have u8 : s 17 ≠ 4 := (Or.elim c1465 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u1 h))))))
  have u9 : s 50 ≠ 3 := (Or.elim c2934 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u1 h))))))
  have u10 : s 14 ≠ 1 := (Or.elim c160 (fun h => h) (fun h => (False.elim (h a9))))
  have u11 : s 58 ≠ 2 := (Or.elim c3308 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u10 h))))))
  have u12 : s 50 ≠ 2 := (Or.elim c2933 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u10 h))))))
  have u13 : s 17 ≠ 2 := (Or.elim c1463 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u10 h))))))
  have u14 : s 51 ≠ 3 := (Or.elim c2959 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u6 h))))))
  have u15 : s 52 ≠ 3 := (Or.elim c3004 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u6 h))))))
  have u16 : s 17 = 1 := (Or.elim c3377 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => (False.elim (a5 h))) (fun h => (Or.elim h (fun h => (False.elim (a6 h))) (fun h => (Or.elim h (fun h => (False.elim (a7 h))) (fun h => (False.elim (h a9))))))))))))))))
  have u17 : s 17 ≠ 0 := (Or.elim c189 (fun h => h) (fun h => (False.elim (h u16))))
  have u18 : s 36 ≠ 3 := (Or.elim c2304 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u8 h))))))
  have u19 : s 51 ≠ 1 := (Or.elim c2977 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u13 h))))))
  have u20 : s 36 ≠ 1 := (Or.elim c2302 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u13 h))))))
  have u21 : s 13 = 0 := (Or.elim c3381 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => (False.elim (h u16))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (a7 h))) (fun h => (Or.elim h (fun h => (False.elim (a8 h))) (fun h => (False.elim (u11 h))))))))))))))))))))))))))))
  have u22 : s 13 ≠ 2 := (Or.elim c146 (fun h => (False.elim (h u21))) (fun h => h))
  have u23 : s 50 = 1 := (Or.elim c1261 (fun h => (False.elim (h u21))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u9 h))))))))
  have u24 : s 51 ≠ 0 := (Or.elim c2961 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a4 h))) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (a6 h))))))))
  have u25 : s 43 = 2 := (Or.elim c2937 (fun h => (False.elim (h u23))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => h))))
  exact (Or.elim c2613 (fun h => (h u25)) (fun h => (Or.elim h (fun h => (u24 h)) (fun h => (u19 h)))))

private theorem step3383 (s : Fin 60 → Fin 5)
    (c3367 : s 59 ≠ 4)
    (c3376 : s 14 = 2 ∨ s 57 = 1 ∨ s 57 = 2)
    (c157 : s 14 ≠ 0 ∨ s 14 ≠ 2)
    (c160 : s 14 ≠ 1 ∨ s 14 ≠ 2)
    (c163 : s 14 ≠ 2 ∨ s 14 ≠ 3)
    (c164 : s 14 ≠ 2 ∨ s 14 ≠ 4)
    (c3353 : s 59 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c3354 : s 59 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c1463 : s 17 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c2133 : s 32 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c1464 : s 17 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c3254 : s 57 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c3309 : s 58 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c3310 : s 58 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4)
    (c2135 : s 32 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4)
    (c2010 : s 29 ≠ 4 ∨ s 59 = 3 ∨ s 59 = 4)
    (c1996 : s 29 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c2221 : s 34 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c2446 : s 39 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c2671 : s 44 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c2096 : s 31 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c2141 : s 32 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3)
    (c2375 : s 38 ≠ 4 ∨ s 58 = 3 ∨ s 58 = 4)
    (c934 : s 6 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4)
    (c1249 : s 13 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4)
    (c2414 : s 38 ≠ 3 ∨ s 29 = 0 ∨ s 29 = 4)
    (c1112 : s 10 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1247 : s 13 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1607 : s 21 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c932 : s 6 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1157 : s 11 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1500 : s 18 ≠ 4 ∨ s 38 = 3 ∨ s 38 = 4)
    (c3382 : s 43 = 0 ∨ s 18 = 4 ∨ s 11 = 1 ∨ s 21 = 1 ∨ s 13 = 1 ∨ s 10 = 1 ∨ s 13 = 3 ∨ s 31 = 0 ∨ s 39 = 0 ∨ s 14 ≠ 2)
    (c475 : s 43 ≠ 0 ∨ s 43 ≠ 1)
    (c476 : s 43 ≠ 0 ∨ s 43 ≠ 2)
    (c477 : s 43 ≠ 0 ∨ s 43 ≠ 3)
    (c2636 : s 43 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c1041 : s 8 ≠ 0 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 43 = 3)
    (c3341 : s 59 ≠ 0 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 43 = 3)
    (c2956 : s 51 ≠ 0 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 43 = 3)
    (c3317 : s 59 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c3347 : s 59 ≠ 1 ∨ s 44 = 0 ∨ s 44 = 2)
    (c2643 : s 44 ≠ 2 ∨ s 8 = 0 ∨ s 8 = 1)
    (c2232 : s 34 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c2203 : s 34 ≠ 2 ∨ s 11 = 0 ∨ s 11 = 1)
    (c94 : s 8 ≠ 1 ∨ s 8 ≠ 2)
    (c943 : s 6 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c1176 : s 11 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c1407 : s 16 ≠ 1 ∨ s 8 = 0 ∨ s 8 = 2)
    (c1396 : s 16 ≠ 0 ∨ s 6 = 1 ∨ s 6 = 2 ∨ s 6 = 3)
    (c1467 : s 17 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2)
    (c2973 : s 51 ≠ 2 ∨ s 16 = 0 ∨ s 16 = 1)
    : s 57 = 1 ∨ s 57 = 2 := by
  by_contra hc
  try simp only [not_or] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 59 ≠ 4 := c3367
  have u1 : s 14 = 2 := (Or.elim c3376 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))
  have u2 : s 14 ≠ 0 := (Or.elim c157 (fun h => h) (fun h => (False.elim (h u1))))
  have u3 : s 14 ≠ 1 := (Or.elim c160 (fun h => h) (fun h => (False.elim (h u1))))
  have u4 : s 14 ≠ 3 := (Or.elim c163 (fun h => (False.elim (h u1))) (fun h => h))
  have u5 : s 14 ≠ 4 := (Or.elim c164 (fun h => (False.elim (h u1))) (fun h => h))
  have u6 : s 59 ≠ 2 := (Or.elim c3353 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u3 h))))))
  have u7 : s 59 ≠ 3 := (Or.elim c3354 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u5 h))))))
  have u8 : s 17 ≠ 2 := (Or.elim c1463 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u3 h))))))
  have u9 : s 32 ≠ 2 := (Or.elim c2133 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u3 h))))))
  have u10 : s 17 ≠ 3 := (Or.elim c1464 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u5 h))))))
  have u11 : s 57 ≠ 3 := (Or.elim c3254 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u5 h))))))
  have u12 : s 58 ≠ 3 := (Or.elim c3309 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u5 h))))))
  have u13 : s 58 ≠ 4 := (Or.elim c3310 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u5 h))))))
  have u14 : s 32 ≠ 4 := (Or.elim c2135 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u5 h))))))
  have u15 : s 29 ≠ 4 := (Or.elim c2010 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u0 h))))))
  have u16 : s 29 ≠ 0 := (Or.elim c1996 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u11 h))))))))
  have u17 : s 34 ≠ 0 := (Or.elim c2221 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u11 h))))))))
  have u18 : s 39 ≠ 0 := (Or.elim c2446 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u11 h))))))))
  have u19 : s 44 ≠ 0 := (Or.elim c2671 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u11 h))))))))
  have u20 : s 31 ≠ 0 := (Or.elim c2096 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u11 h))))))))
  have u21 : s 32 ≠ 0 := (Or.elim c2141 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u11 h))))))))
  have u22 : s 38 ≠ 4 := (Or.elim c2375 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u13 h))))))
  have u23 : s 6 ≠ 3 := (Or.elim c934 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u14 h))))))
  have u24 : s 13 ≠ 3 := (Or.elim c1249 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u14 h))))))
  have u25 : s 38 ≠ 3 := (Or.elim c2414 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (u15 h))))))
  have u26 : s 10 ≠ 1 := (Or.elim c1112 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u9 h))))))
  have u27 : s 13 ≠ 1 := (Or.elim c1247 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u9 h))))))
  have u28 : s 21 ≠ 1 := (Or.elim c1607 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u9 h))))))
  have u29 : s 6 ≠ 1 := (Or.elim c932 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u9 h))))))
  have u30 : s 11 ≠ 1 := (Or.elim c1157 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u9 h))))))
  have u31 : s 18 ≠ 4 := (Or.elim c1500 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u22 h))))))
  have u32 : s 43 = 0 := (Or.elim c3382 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => (Or.elim h (fun h => (False.elim (u28 h))) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (False.elim (h u1))))))))))))))))))))
  have u33 : s 43 ≠ 1 := (Or.elim c475 (fun h => (False.elim (h u32))) (fun h => h))
  have u34 : s 43 ≠ 2 := (Or.elim c476 (fun h => (False.elim (h u32))) (fun h => h))
  have u35 : s 43 ≠ 3 := (Or.elim c477 (fun h => (False.elim (h u32))) (fun h => h))
  have u36 : s 59 = 1 := (Or.elim c2636 (fun h => (False.elim (h u32))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u7 h))))))))
  have u37 : s 8 ≠ 0 := (Or.elim c1041 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u33 h))) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (u35 h))))))))
  have u38 : s 59 ≠ 0 := (Or.elim c3341 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u33 h))) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (u35 h))))))))
  have u39 : s 51 ≠ 0 := (Or.elim c2956 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u33 h))) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (u35 h))))))))
  have u40 : s 34 = 2 := (Or.elim c3317 (fun h => (False.elim (h u36))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => h))))
  have u41 : s 44 = 2 := (Or.elim c3347 (fun h => (False.elim (h u36))) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => h))))
  have u42 : s 8 = 1 := (Or.elim c2643 (fun h => (False.elim (h u41))) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => h))))
  have u43 : s 34 ≠ 1 := (Or.elim c2232 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u6 h))))))
  have u44 : s 11 = 0 := (Or.elim c2203 (fun h => (False.elim (h u40))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u30 h))))))
  have u45 : s 8 ≠ 2 := (Or.elim c94 (fun h => (False.elim (h u42))) (fun h => h))
  have u46 : s 6 ≠ 2 := (Or.elim c943 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u43 h))))))
  have u47 : s 17 = 1 := (Or.elim c1176 (fun h => (False.elim (h u44))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u10 h))))))))
  have u48 : s 16 ≠ 1 := (Or.elim c1407 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => (False.elim (u45 h))))))
  have u49 : s 16 ≠ 0 := (Or.elim c1396 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u29 h))) (fun h => (Or.elim h (fun h => (False.elim (u46 h))) (fun h => (False.elim (u23 h))))))))
  have u50 : s 51 = 2 := (Or.elim c1467 (fun h => (False.elim (h u47))) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => h))))
  exact (Or.elim c2973 (fun h => (h u50)) (fun h => (Or.elim h (fun h => (u49 h)) (fun h => (u48 h)))))

private theorem step3384 (s : Fin 60 → Fin 5)
    (c3383 : s 57 = 1 ∨ s 57 = 2)
    (c629 : s 57 ≠ 0 ∨ s 57 ≠ 1)
    (c635 : s 57 ≠ 1 ∨ s 57 ≠ 4)
    (c2224 : s 34 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c634 : s 57 ≠ 1 ∨ s 57 ≠ 3)
    (c2225 : s 34 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c810 : s 3 ≠ 4 ∨ s 34 = 3 ∨ s 34 = 4)
    (c2142 : s 32 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2144 : s 32 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c1322 : s 14 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2133 : s 32 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c796 : s 3 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c1354 : s 15 ≠ 3 ∨ s 3 = 0 ∨ s 3 = 4)
    (c1246 : s 13 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c1156 : s 11 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c1111 : s 10 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c1325 : s 14 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c3309 : s 58 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c2934 : s 50 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c3308 : s 58 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c2933 : s 50 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c2189 : s 33 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c2187 : s 33 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2222 : s 34 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c475 : s 43 ≠ 0 ∨ s 43 ≠ 1)
    (c476 : s 43 ≠ 0 ∨ s 43 ≠ 2)
    (c477 : s 43 ≠ 0 ∨ s 43 ≠ 3)
    (c2606 : s 43 ≠ 0 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 50 = 3)
    (c2936 : s 50 ≠ 0 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 43 = 3)
    (c3001 : s 52 ≠ 0 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 43 = 3)
    (c2956 : s 51 ≠ 0 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 43 = 3)
    (c2917 : s 50 ≠ 1 ∨ s 11 = 0 ∨ s 11 = 2)
    (c1262 : s 13 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2)
    (c1147 : s 10 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2)
    (c1182 : s 11 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2)
    (c1168 : s 11 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c2963 : s 51 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1)
    (c3008 : s 52 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1)
    (c1373 : s 15 ≠ 2 ∨ s 10 = 0 ∨ s 10 = 1)
    (c2158 : s 33 ≠ 2 ∨ s 11 = 0 ∨ s 11 = 1)
    (c2226 : s 34 ≠ 0 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 58 = 3)
    (c1377 : s 15 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2)
    (c1692 : s 22 ≠ 1 ∨ s 52 = 0 ∨ s 52 = 2)
    (c2291 : s 36 ≠ 0 ∨ s 15 = 1 ∨ s 15 = 2 ∨ s 15 = 3)
    (c1656 : s 22 ≠ 0 ∨ s 33 = 1 ∨ s 33 = 2 ∨ s 33 = 3)
    (c3282 : s 58 ≠ 1 ∨ s 36 = 0 ∨ s 36 = 2)
    (c2318 : s 36 ≠ 2 ∨ s 22 = 0 ∨ s 22 = 1)
    : s 43 ≠ 0 ∨ s 14 = 0 ∨ s 57 = 2 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 57 = 1 := (Or.elim c3383 (fun h => h) (fun h => (False.elim (a2 h))))
  have u1 : s 57 ≠ 0 := (Or.elim c629 (fun h => h) (fun h => (False.elim (h u0))))
  have u2 : s 57 ≠ 4 := (Or.elim c635 (fun h => (False.elim (h u0))) (fun h => h))
  have u3 : s 34 ≠ 3 := (Or.elim c2224 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u4 : s 57 ≠ 3 := (Or.elim c634 (fun h => (False.elim (h u0))) (fun h => h))
  have u5 : s 34 ≠ 4 := (Or.elim c2225 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u6 : s 3 ≠ 4 := (Or.elim c810 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u7 : s 32 ≠ 1 := (Or.elim c2142 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a2 h))))))
  have u8 : s 32 ≠ 3 := (Or.elim c2144 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u9 : s 14 ≠ 1 := (Or.elim c1322 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a2 h))))))
  have u10 : s 32 ≠ 2 := (Or.elim c2133 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u9 h))))))
  have u11 : s 3 ≠ 0 := (Or.elim c796 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u8 h))))))))
  have u12 : s 15 ≠ 3 := (Or.elim c1354 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u6 h))))))
  have u13 : s 13 ≠ 0 := (Or.elim c1246 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u8 h))))))))
  have u14 : s 11 ≠ 0 := (Or.elim c1156 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u8 h))))))))
  have u15 : s 10 ≠ 0 := (Or.elim c1111 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u8 h))))))))
  have u16 : s 14 ≠ 4 := (Or.elim c1325 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u17 : s 58 ≠ 3 := (Or.elim c3309 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u16 h))))))
  have u18 : s 50 ≠ 3 := (Or.elim c2934 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u16 h))))))
  have u19 : s 58 ≠ 2 := (Or.elim c3308 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u9 h))))))
  have u20 : s 50 ≠ 2 := (Or.elim c2933 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u9 h))))))
  have u21 : s 33 ≠ 3 := (Or.elim c2189 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u22 : s 33 ≠ 1 := (Or.elim c2187 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a2 h))))))
  have u23 : s 34 ≠ 1 := (Or.elim c2222 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a2 h))))))
  have u24 : s 43 ≠ 1 := (Or.elim c475 (fun h => (False.elim (h a0))) (fun h => h))
  have u25 : s 43 ≠ 2 := (Or.elim c476 (fun h => (False.elim (h a0))) (fun h => h))
  have u26 : s 43 ≠ 3 := (Or.elim c477 (fun h => (False.elim (h a0))) (fun h => h))
  have u27 : s 50 = 1 := (Or.elim c2606 (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u18 h))))))))
  have u28 : s 50 ≠ 0 := (Or.elim c2936 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u26 h))))))))
  have u29 : s 52 ≠ 0 := (Or.elim c3001 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u26 h))))))))
  have u30 : s 51 ≠ 0 := (Or.elim c2956 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u26 h))))))))
  have u31 : s 11 = 2 := (Or.elim c2917 (fun h => (False.elim (h u27))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => h))))
  have u32 : s 13 ≠ 1 := (Or.elim c1262 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u28 h))) (fun h => (False.elim (u20 h))))))
  have u33 : s 10 ≠ 1 := (Or.elim c1147 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u28 h))) (fun h => (False.elim (u20 h))))))
  have u34 : s 11 ≠ 1 := (Or.elim c1182 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u28 h))) (fun h => (False.elim (u20 h))))))
  have u35 : s 34 = 0 := (Or.elim c1168 (fun h => (False.elim (h u31))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u23 h))))))
  have u36 : s 51 ≠ 2 := (Or.elim c2963 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u32 h))))))
  have u37 : s 52 ≠ 2 := (Or.elim c3008 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u32 h))))))
  have u38 : s 15 ≠ 2 := (Or.elim c1373 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u33 h))))))
  have u39 : s 33 ≠ 2 := (Or.elim c2158 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (u34 h))))))
  have u40 : s 58 = 1 := (Or.elim c2226 (fun h => (False.elim (h u35))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u17 h))))))))
  have u41 : s 15 ≠ 1 := (Or.elim c1377 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => (False.elim (u36 h))))))
  have u42 : s 22 ≠ 1 := (Or.elim c1692 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u29 h))) (fun h => (False.elim (u37 h))))))
  have u43 : s 36 ≠ 0 := (Or.elim c2291 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u41 h))) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u12 h))))))))
  have u44 : s 22 ≠ 0 := (Or.elim c1656 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (False.elim (u21 h))))))))
  have u45 : s 36 = 2 := (Or.elim c3282 (fun h => (False.elim (h u40))) (fun h => (Or.elim h (fun h => (False.elim (u43 h))) (fun h => h))))
  exact (Or.elim c2318 (fun h => (h u45)) (fun h => (Or.elim h (fun h => (u44 h)) (fun h => (u42 h)))))

private theorem step3385 (s : Fin 60 → Fin 5)
    (c3383 : s 57 = 1 ∨ s 57 = 2)
    (c629 : s 57 ≠ 0 ∨ s 57 ≠ 1)
    (c2142 : s 32 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c635 : s 57 ≠ 1 ∨ s 57 ≠ 4)
    (c2144 : s 32 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c1322 : s 14 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2133 : s 32 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c1111 : s 10 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c1533 : s 19 ≠ 2 ∨ s 10 = 0 ∨ s 10 = 1)
    (c1418 : s 16 ≠ 2 ∨ s 10 = 0 ∨ s 10 = 1)
    (c3384 : s 43 ≠ 0 ∨ s 14 = 0 ∨ s 57 = 2)
    (c634 : s 57 ≠ 1 ∨ s 57 ≠ 3)
    (c2145 : s 32 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c1250 : s 13 ≠ 4 ∨ s 32 = 3 ∨ s 32 = 4)
    (c1246 : s 13 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c2964 : s 51 ≠ 3 ∨ s 13 = 0 ∨ s 13 = 4)
    (c2224 : s 34 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c2225 : s 34 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c1625 : s 21 ≠ 4 ∨ s 34 = 3 ∨ s 34 = 4)
    (c1606 : s 21 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c3024 : s 52 ≠ 3 ∨ s 21 = 0 ∨ s 21 = 4)
    (c1156 : s 11 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c1325 : s 14 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c3354 : s 59 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c3353 : s 59 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c2189 : s 33 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c2099 : s 31 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c2187 : s 33 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2222 : s 34 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2097 : s 31 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2158 : s 33 ≠ 2 ∨ s 11 = 0 ∨ s 11 = 1)
    (c2203 : s 34 ≠ 2 ∨ s 11 = 0 ∨ s 11 = 1)
    (c2088 : s 31 ≠ 2 ∨ s 11 = 0 ∨ s 11 = 1)
    (c1701 : s 23 ≠ 0 ∨ s 33 = 1 ∨ s 33 = 2 ∨ s 33 = 3)
    (c3237 : s 57 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c3316 : s 59 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3)
    (c1061 : s 8 ≠ 0 ∨ s 31 = 1 ∨ s 31 = 2 ∨ s 31 = 3)
    (c2231 : s 34 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3)
    (c2637 : s 43 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    (c3342 : s 59 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c2958 : s 51 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c3003 : s 52 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c1728 : s 23 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    (c2598 : s 43 ≠ 2 ∨ s 8 = 0 ∨ s 8 = 1)
    (c3032 : s 52 ≠ 1 ∨ s 23 = 0 ∨ s 23 = 2)
    (c1057 : s 8 ≠ 1 ∨ s 16 = 0 ∨ s 16 = 2)
    (c1546 : s 19 ≠ 0 ∨ s 52 = 1 ∨ s 52 = 2 ∨ s 52 = 3)
    (c1421 : s 16 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3)
    (c2987 : s 51 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2)
    : s 11 = 1 ∨ s 10 = 1 ∨ s 14 = 0 ∨ s 57 = 2 := by
  by_contra hc
  try simp only [not_or] at hc
  obtain ⟨a0,a1,a2,a3⟩ := hc
  have u0 : s 57 = 1 := (Or.elim c3383 (fun h => h) (fun h => (False.elim (a3 h))))
  have u1 : s 57 ≠ 0 := (Or.elim c629 (fun h => h) (fun h => (False.elim (h u0))))
  have u2 : s 32 ≠ 1 := (Or.elim c2142 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a3 h))))))
  have u3 : s 57 ≠ 4 := (Or.elim c635 (fun h => (False.elim (h u0))) (fun h => h))
  have u4 : s 32 ≠ 3 := (Or.elim c2144 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u3 h))))))
  have u5 : s 14 ≠ 1 := (Or.elim c1322 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a3 h))))))
  have u6 : s 32 ≠ 2 := (Or.elim c2133 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u5 h))))))
  have u7 : s 10 ≠ 0 := (Or.elim c1111 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u4 h))))))))
  have u8 : s 19 ≠ 2 := (Or.elim c1533 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (a1 h))))))
  have u9 : s 16 ≠ 2 := (Or.elim c1418 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (a1 h))))))
  have u10 : s 43 ≠ 0 := (Or.elim c3384 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (a3 h))))))
  have u11 : s 57 ≠ 3 := (Or.elim c634 (fun h => (False.elim (h u0))) (fun h => h))
  have u12 : s 32 ≠ 4 := (Or.elim c2145 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u3 h))))))
  have u13 : s 13 ≠ 4 := (Or.elim c1250 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u12 h))))))
  have u14 : s 13 ≠ 0 := (Or.elim c1246 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u4 h))))))))
  have u15 : s 51 ≠ 3 := (Or.elim c2964 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (u13 h))))))
  have u16 : s 34 ≠ 3 := (Or.elim c2224 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u3 h))))))
  have u17 : s 34 ≠ 4 := (Or.elim c2225 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u3 h))))))
  have u18 : s 21 ≠ 4 := (Or.elim c1625 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (u17 h))))))
  have u19 : s 21 ≠ 0 := (Or.elim c1606 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u4 h))))))))
  have u20 : s 52 ≠ 3 := (Or.elim c3024 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u18 h))))))
  have u21 : s 11 ≠ 0 := (Or.elim c1156 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u4 h))))))))
  have u22 : s 14 ≠ 4 := (Or.elim c1325 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u3 h))))))
  have u23 : s 59 ≠ 3 := (Or.elim c3354 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u22 h))))))
  have u24 : s 59 ≠ 2 := (Or.elim c3353 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u5 h))))))
  have u25 : s 33 ≠ 3 := (Or.elim c2189 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u3 h))))))
  have u26 : s 31 ≠ 3 := (Or.elim c2099 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u3 h))))))
  have u27 : s 33 ≠ 1 := (Or.elim c2187 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a3 h))))))
  have u28 : s 34 ≠ 1 := (Or.elim c2222 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a3 h))))))
  have u29 : s 31 ≠ 1 := (Or.elim c2097 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a3 h))))))
  have u30 : s 33 ≠ 2 := (Or.elim c2158 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (a0 h))))))
  have u31 : s 34 ≠ 2 := (Or.elim c2203 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (a0 h))))))
  have u32 : s 31 ≠ 2 := (Or.elim c2088 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (a0 h))))))
  have u33 : s 23 ≠ 0 := (Or.elim c1701 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => (False.elim (u25 h))))))))
  have u34 : s 34 = 0 := (Or.elim c3237 (fun h => (False.elim (h u0))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u31 h))))))
  have u35 : s 59 ≠ 0 := (Or.elim c3316 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u28 h))) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u16 h))))))))
  have u36 : s 8 ≠ 0 := (Or.elim c1061 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u29 h))) (fun h => (Or.elim h (fun h => (False.elim (u32 h))) (fun h => (False.elim (u26 h))))))))
  have u37 : s 59 = 1 := (Or.elim c2231 (fun h => (False.elim (h u34))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (False.elim (u23 h))))))))
  have u38 : s 43 ≠ 1 := (Or.elim c2637 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u24 h))))))
  have u39 : s 43 = 2 := (Or.elim c3342 (fun h => (False.elim (h u37))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => h))))
  have u40 : s 51 ≠ 2 := (Or.elim c2958 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u38 h))))))
  have u41 : s 52 ≠ 2 := (Or.elim c3003 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u38 h))))))
  have u42 : s 23 ≠ 2 := (Or.elim c1728 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u38 h))))))
  have u43 : s 8 = 1 := (Or.elim c2598 (fun h => (False.elim (h u39))) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => h))))
  have u44 : s 52 ≠ 1 := (Or.elim c3032 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u33 h))) (fun h => (False.elim (u42 h))))))
  have u45 : s 16 = 0 := (Or.elim c1057 (fun h => (False.elim (h u43))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u9 h))))))
  have u46 : s 19 ≠ 0 := (Or.elim c1546 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u44 h))) (fun h => (Or.elim h (fun h => (False.elim (u41 h))) (fun h => (False.elim (u20 h))))))))
  have u47 : s 51 = 1 := (Or.elim c1421 (fun h => (False.elim (h u45))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u40 h))) (fun h => (False.elim (u15 h))))))))
  exact (Or.elim c2987 (fun h => (h u47)) (fun h => (Or.elim h (fun h => (u46 h)) (fun h => (u8 h)))))

private theorem step3386 (s : Fin 60 → Fin 5)
    (c3383 : s 57 = 1 ∨ s 57 = 2)
    (c629 : s 57 ≠ 0 ∨ s 57 ≠ 1)
    (c635 : s 57 ≠ 1 ∨ s 57 ≠ 4)
    (c2144 : s 32 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c634 : s 57 ≠ 1 ∨ s 57 ≠ 3)
    (c2145 : s 32 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c1115 : s 10 ≠ 4 ∨ s 32 = 3 ∨ s 32 = 4)
    (c2142 : s 32 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c1322 : s 14 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2133 : s 32 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c1111 : s 10 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c1534 : s 19 ≠ 3 ∨ s 10 = 0 ∨ s 10 = 4)
    (c1324 : s 14 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c1325 : s 14 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c2935 : s 50 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4)
    (c2934 : s 50 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c1940 : s 28 ≠ 4 ∨ s 50 = 3 ∨ s 50 = 4)
    (c1156 : s 11 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c3169 : s 55 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c1464 : s 17 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c3168 : s 55 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c2933 : s 50 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c1463 : s 17 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c1997 : s 29 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2052 : s 30 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c1533 : s 19 ≠ 2 ∨ s 10 = 0 ∨ s 10 = 1)
    (c3385 : s 11 = 1 ∨ s 10 = 1 ∨ s 14 = 0 ∨ s 57 = 2)
    (c127 : s 11 ≠ 1 ∨ s 11 ≠ 2)
    (c1182 : s 11 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2)
    (c1447 : s 17 ≠ 1 ∨ s 11 = 0 ∨ s 11 = 2)
    (c2917 : s 50 ≠ 1 ∨ s 11 = 0 ∨ s 11 = 2)
    (c3152 : s 55 ≠ 1 ∨ s 11 = 0 ∨ s 11 = 2)
    (c2941 : s 50 ≠ 0 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 19 = 3)
    (c676 : s 0 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c2976 : s 51 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c1936 : s 28 ≠ 0 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 50 = 3)
    (c1536 : s 19 ≠ 0 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 50 = 3)
    (c1986 : s 29 ≠ 0 ∨ s 55 = 1 ∨ s 55 = 2 ∨ s 55 = 3)
    (c1517 : s 19 ≠ 1 ∨ s 0 = 0 ∨ s 0 = 2)
    (c784 : s 2 ≠ 3 ∨ s 28 = 0 ∨ s 28 = 4)
    (c2987 : s 51 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2)
    (c788 : s 2 ≠ 2 ∨ s 29 = 0 ∨ s 29 = 1)
    (c703 : s 0 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1)
    (c1943 : s 28 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c2021 : s 30 ≠ 0 ∨ s 2 = 1 ∨ s 2 = 2 ∨ s 2 = 3)
    (c782 : s 2 ≠ 1 ∨ s 28 = 0 ∨ s 28 = 2)
    : s 10 = 1 ∨ s 14 = 0 ∨ s 57 = 2 := by
  by_contra hc
  try simp only [not_or] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 57 = 1 := (Or.elim c3383 (fun h => h) (fun h => (False.elim (a2 h))))
  have u1 : s 57 ≠ 0 := (Or.elim c629 (fun h => h) (fun h => (False.elim (h u0))))
  have u2 : s 57 ≠ 4 := (Or.elim c635 (fun h => (False.elim (h u0))) (fun h => h))
  have u3 : s 32 ≠ 3 := (Or.elim c2144 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u4 : s 57 ≠ 3 := (Or.elim c634 (fun h => (False.elim (h u0))) (fun h => h))
  have u5 : s 32 ≠ 4 := (Or.elim c2145 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u6 : s 10 ≠ 4 := (Or.elim c1115 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u7 : s 32 ≠ 1 := (Or.elim c2142 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a2 h))))))
  have u8 : s 14 ≠ 1 := (Or.elim c1322 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a2 h))))))
  have u9 : s 32 ≠ 2 := (Or.elim c2133 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u8 h))))))
  have u10 : s 10 ≠ 0 := (Or.elim c1111 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u3 h))))))))
  have u11 : s 19 ≠ 3 := (Or.elim c1534 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u6 h))))))
  have u12 : s 14 ≠ 3 := (Or.elim c1324 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u13 : s 14 ≠ 4 := (Or.elim c1325 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u14 : s 50 ≠ 4 := (Or.elim c2935 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u13 h))))))
  have u15 : s 50 ≠ 3 := (Or.elim c2934 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u13 h))))))
  have u16 : s 28 ≠ 4 := (Or.elim c1940 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u14 h))))))
  have u17 : s 11 ≠ 0 := (Or.elim c1156 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u3 h))))))))
  have u18 : s 55 ≠ 3 := (Or.elim c3169 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u13 h))))))
  have u19 : s 17 ≠ 3 := (Or.elim c1464 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u13 h))))))
  have u20 : s 55 ≠ 2 := (Or.elim c3168 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u8 h))))))
  have u21 : s 50 ≠ 2 := (Or.elim c2933 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u8 h))))))
  have u22 : s 17 ≠ 2 := (Or.elim c1463 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u8 h))))))
  have u23 : s 29 ≠ 1 := (Or.elim c1997 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a2 h))))))
  have u24 : s 30 ≠ 1 := (Or.elim c2052 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a2 h))))))
  have u25 : s 19 ≠ 2 := (Or.elim c1533 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (a0 h))))))
  have u26 : s 11 = 1 := (Or.elim c3385 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (a2 h))))))))
  have u27 : s 11 ≠ 2 := (Or.elim c127 (fun h => (False.elim (h u26))) (fun h => h))
  have u28 : s 50 = 0 := (Or.elim c1182 (fun h => (False.elim (h u26))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u21 h))))))
  have u29 : s 17 ≠ 1 := (Or.elim c1447 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u27 h))))))
  have u30 : s 50 ≠ 1 := (Or.elim c2917 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u27 h))))))
  have u31 : s 55 ≠ 1 := (Or.elim c3152 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u27 h))))))
  have u32 : s 19 = 1 := (Or.elim c2941 (fun h => (False.elim (h u28))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u11 h))))))))
  have u33 : s 0 ≠ 0 := (Or.elim c676 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u29 h))) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u19 h))))))))
  have u34 : s 51 ≠ 0 := (Or.elim c2976 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u29 h))) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u19 h))))))))
  have u35 : s 28 ≠ 0 := (Or.elim c1936 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u15 h))))))))
  have u36 : s 19 ≠ 0 := (Or.elim c1536 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u15 h))))))))
  have u37 : s 29 ≠ 0 := (Or.elim c1986 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u18 h))))))))
  have u38 : s 0 = 2 := (Or.elim c1517 (fun h => (False.elim (h u32))) (fun h => (Or.elim h (fun h => (False.elim (u33 h))) (fun h => h))))
  have u39 : s 2 ≠ 3 := (Or.elim c784 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u16 h))))))
  have u40 : s 51 ≠ 1 := (Or.elim c2987 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u25 h))))))
  have u41 : s 2 ≠ 2 := (Or.elim c788 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => (False.elim (u23 h))))))
  have u42 : s 30 = 0 := (Or.elim c703 (fun h => (False.elim (h u38))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u24 h))))))
  have u43 : s 28 ≠ 2 := (Or.elim c1943 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (u40 h))))))
  have u44 : s 2 = 1 := (Or.elim c2021 (fun h => (False.elim (h u42))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u41 h))) (fun h => (False.elim (u39 h))))))))
  exact (Or.elim c782 (fun h => (h u44)) (fun h => (Or.elim h (fun h => (u35 h)) (fun h => (u43 h)))))

private theorem step3387 (s : Fin 60 → Fin 5)
    (c3383 : s 57 = 1 ∨ s 57 = 2)
    (c629 : s 57 ≠ 0 ∨ s 57 ≠ 1)
    (c635 : s 57 ≠ 1 ∨ s 57 ≠ 4)
    (c2144 : s 32 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c634 : s 57 ≠ 1 ∨ s 57 ≠ 3)
    (c2145 : s 32 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c1115 : s 10 ≠ 4 ∨ s 32 = 3 ∨ s 32 = 4)
    (c2449 : s 39 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c1325 : s 14 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c2447 : s 39 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c1322 : s 14 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2222 : s 34 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2142 : s 32 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c1463 : s 17 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c2133 : s 32 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c2933 : s 50 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c3168 : s 55 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1)
    (c1464 : s 17 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c2934 : s 50 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c3169 : s 55 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c1606 : s 21 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c1111 : s 10 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c1534 : s 19 ≠ 3 ∨ s 10 = 0 ∨ s 10 = 4)
    (c1509 : s 18 ≠ 3 ∨ s 10 = 0 ∨ s 10 = 4)
    (c3386 : s 10 = 1 ∨ s 14 = 0 ∨ s 57 = 2)
    (c116 : s 10 ≠ 1 ∨ s 10 ≠ 2)
    (c1147 : s 10 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2)
    (c1152 : s 10 ≠ 1 ∨ s 55 = 0 ∨ s 55 = 2)
    (c1442 : s 17 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2)
    (c1507 : s 18 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2)
    (c1532 : s 19 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2)
    (c2912 : s 50 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2)
    (c3147 : s 55 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2)
    (c3141 : s 55 ≠ 0 ∨ s 39 = 1 ∨ s 39 = 2 ∨ s 39 = 3)
    (c2976 : s 51 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c2428 : s 39 ≠ 2 ∨ s 18 = 0 ∨ s 18 = 1)
    (c2941 : s 50 ≠ 0 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 19 = 3)
    (c1761 : s 24 ≠ 0 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 50 = 3)
    (c2211 : s 34 ≠ 0 ∨ s 55 = 1 ∨ s 55 = 2 ∨ s 55 = 3)
    (c201 : s 18 ≠ 0 ∨ s 18 ≠ 2)
    (c1543 : s 19 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c1623 : s 21 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1)
    (c2336 : s 37 ≠ 0 ∨ s 18 = 1 ∨ s 18 = 2 ∨ s 18 = 3)
    (c2992 : s 51 ≠ 1 ∨ s 24 = 0 ∨ s 24 = 2)
    (c2347 : s 37 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2)
    (c1753 : s 24 ≠ 2 ∨ s 37 = 0 ∨ s 37 = 1)
    : s 14 = 0 ∨ s 57 = 2 := by
  by_contra hc
  try simp only [not_or] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 57 = 1 := (Or.elim c3383 (fun h => h) (fun h => (False.elim (a1 h))))
  have u1 : s 57 ≠ 0 := (Or.elim c629 (fun h => h) (fun h => (False.elim (h u0))))
  have u2 : s 57 ≠ 4 := (Or.elim c635 (fun h => (False.elim (h u0))) (fun h => h))
  have u3 : s 32 ≠ 3 := (Or.elim c2144 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u4 : s 57 ≠ 3 := (Or.elim c634 (fun h => (False.elim (h u0))) (fun h => h))
  have u5 : s 32 ≠ 4 := (Or.elim c2145 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u6 : s 10 ≠ 4 := (Or.elim c1115 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u7 : s 39 ≠ 3 := (Or.elim c2449 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u8 : s 14 ≠ 4 := (Or.elim c1325 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u9 : s 39 ≠ 1 := (Or.elim c2447 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u10 : s 14 ≠ 1 := (Or.elim c1322 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u11 : s 34 ≠ 1 := (Or.elim c2222 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u12 : s 32 ≠ 1 := (Or.elim c2142 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u13 : s 17 ≠ 2 := (Or.elim c1463 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u10 h))))))
  have u14 : s 32 ≠ 2 := (Or.elim c2133 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u10 h))))))
  have u15 : s 50 ≠ 2 := (Or.elim c2933 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u10 h))))))
  have u16 : s 55 ≠ 2 := (Or.elim c3168 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u10 h))))))
  have u17 : s 17 ≠ 3 := (Or.elim c1464 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u8 h))))))
  have u18 : s 50 ≠ 3 := (Or.elim c2934 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u8 h))))))
  have u19 : s 55 ≠ 3 := (Or.elim c3169 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u8 h))))))
  have u20 : s 21 ≠ 0 := (Or.elim c1606 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (u3 h))))))))
  have u21 : s 10 ≠ 0 := (Or.elim c1111 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (u3 h))))))))
  have u22 : s 19 ≠ 3 := (Or.elim c1534 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u6 h))))))
  have u23 : s 18 ≠ 3 := (Or.elim c1509 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u6 h))))))
  have u24 : s 10 = 1 := (Or.elim c3386 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))
  have u25 : s 10 ≠ 2 := (Or.elim c116 (fun h => (False.elim (h u24))) (fun h => h))
  have u26 : s 50 = 0 := (Or.elim c1147 (fun h => (False.elim (h u24))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u15 h))))))
  have u27 : s 55 = 0 := (Or.elim c1152 (fun h => (False.elim (h u24))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u16 h))))))
  have u28 : s 17 ≠ 1 := (Or.elim c1442 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u25 h))))))
  have u29 : s 18 ≠ 1 := (Or.elim c1507 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u25 h))))))
  have u30 : s 19 ≠ 1 := (Or.elim c1532 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u25 h))))))
  have u31 : s 50 ≠ 1 := (Or.elim c2912 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u25 h))))))
  have u32 : s 55 ≠ 1 := (Or.elim c3147 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u25 h))))))
  have u33 : s 39 = 2 := (Or.elim c3141 (fun h => (False.elim (h u27))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u7 h))))))))
  have u34 : s 51 ≠ 0 := (Or.elim c2976 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u28 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u17 h))))))))
  have u35 : s 18 = 0 := (Or.elim c2428 (fun h => (False.elim (h u33))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u29 h))))))
  have u36 : s 19 = 2 := (Or.elim c2941 (fun h => (False.elim (h u26))) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u22 h))))))))
  have u37 : s 24 ≠ 0 := (Or.elim c1761 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u18 h))))))))
  have u38 : s 34 ≠ 0 := (Or.elim c2211 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u32 h))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (u19 h))))))))
  have u39 : s 18 ≠ 2 := (Or.elim c201 (fun h => (False.elim (h u35))) (fun h => h))
  have u40 : s 51 = 1 := (Or.elim c1543 (fun h => (False.elim (h u36))) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => h))))
  have u41 : s 21 ≠ 2 := (Or.elim c1623 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u11 h))))))
  have u42 : s 37 ≠ 0 := (Or.elim c2336 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u29 h))) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (False.elim (u23 h))))))))
  have u43 : s 24 = 2 := (Or.elim c2992 (fun h => (False.elim (h u40))) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => h))))
  have u44 : s 37 ≠ 1 := (Or.elim c2347 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u41 h))))))
  exact (Or.elim c1753 (fun h => (h u43)) (fun h => (Or.elim h (fun h => (u42 h)) (fun h => (u44 h)))))

private theorem step3388 (s : Fin 60 → Fin 5)
    (c3383 : s 57 = 1 ∨ s 57 = 2)
    (c629 : s 57 ≠ 0 ∨ s 57 ≠ 1)
    (c635 : s 57 ≠ 1 ∨ s 57 ≠ 4)
    (c1324 : s 14 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c634 : s 57 ≠ 1 ∨ s 57 ≠ 3)
    (c1325 : s 14 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c1465 : s 17 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4)
    (c1322 : s 14 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c3387 : s 14 = 0 ∨ s 57 = 2)
    (c157 : s 14 ≠ 0 ∨ s 14 ≠ 2)
    (c1461 : s 17 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2979 : s 51 ≠ 3 ∨ s 17 = 0 ∨ s 17 = 4)
    (c2142 : s 32 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2131 : s 32 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c1608 : s 21 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1113 : s 10 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1999 : s 29 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c2000 : s 29 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c3315 : s 58 ≠ 4 ∨ s 29 = 3 ∨ s 29 = 4)
    (c3306 : s 58 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2329 : s 37 ≠ 3 ∨ s 58 = 0 ∨ s 58 = 4)
    (c2931 : s 50 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c3166 : s 55 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2449 : s 39 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c2224 : s 34 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c2447 : s 39 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2222 : s 34 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c112 : s 10 ≠ 0 ∨ s 10 ≠ 1)
    (c1147 : s 10 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2)
    (c1442 : s 17 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2)
    (c1507 : s 18 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2)
    (c1532 : s 19 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2)
    (c2912 : s 50 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2)
    (c3147 : s 55 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2)
    (c2978 : s 51 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1)
    (c2943 : s 50 ≠ 2 ∨ s 19 = 0 ∨ s 19 = 1)
    (c1763 : s 24 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1)
    (c2438 : s 39 ≠ 2 ∨ s 55 = 0 ∨ s 55 = 1)
    (c2213 : s 34 ≠ 2 ∨ s 55 = 0 ∨ s 55 = 1)
    (c1541 : s 19 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3)
    (c1501 : s 18 ≠ 0 ∨ s 39 = 1 ∨ s 39 = 2 ∨ s 39 = 3)
    (c1621 : s 21 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3)
    (c2992 : s 51 ≠ 1 ∨ s 24 = 0 ∨ s 24 = 2)
    (c2338 : s 37 ≠ 2 ∨ s 18 = 0 ∨ s 18 = 1)
    (c2347 : s 37 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2)
    (c1751 : s 24 ≠ 0 ∨ s 37 = 1 ∨ s 37 = 2 ∨ s 37 = 3)
    : s 10 ≠ 1 ∨ s 57 = 2 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 57 = 1 := (Or.elim c3383 (fun h => h) (fun h => (False.elim (a1 h))))
  have u1 : s 57 ≠ 0 := (Or.elim c629 (fun h => h) (fun h => (False.elim (h u0))))
  have u2 : s 57 ≠ 4 := (Or.elim c635 (fun h => (False.elim (h u0))) (fun h => h))
  have u3 : s 14 ≠ 3 := (Or.elim c1324 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u4 : s 57 ≠ 3 := (Or.elim c634 (fun h => (False.elim (h u0))) (fun h => h))
  have u5 : s 14 ≠ 4 := (Or.elim c1325 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u6 : s 17 ≠ 4 := (Or.elim c1465 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u7 : s 14 ≠ 1 := (Or.elim c1322 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u8 : s 14 = 0 := (Or.elim c3387 (fun h => h) (fun h => (False.elim (a1 h))))
  have u9 : s 14 ≠ 2 := (Or.elim c157 (fun h => (False.elim (h u8))) (fun h => h))
  have u10 : s 17 ≠ 0 := (Or.elim c1461 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u3 h))))))))
  have u11 : s 51 ≠ 3 := (Or.elim c2979 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u6 h))))))
  have u12 : s 32 ≠ 1 := (Or.elim c2142 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u13 : s 32 ≠ 0 := (Or.elim c2131 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u3 h))))))))
  have u14 : s 21 ≠ 2 := (Or.elim c1608 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u12 h))))))
  have u15 : s 10 ≠ 2 := (Or.elim c1113 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u12 h))))))
  have u16 : s 29 ≠ 3 := (Or.elim c1999 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u17 : s 29 ≠ 4 := (Or.elim c2000 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u18 : s 58 ≠ 4 := (Or.elim c3315 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (u17 h))))))
  have u19 : s 58 ≠ 0 := (Or.elim c3306 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u3 h))))))))
  have u20 : s 37 ≠ 3 := (Or.elim c2329 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u18 h))))))
  have u21 : s 50 ≠ 0 := (Or.elim c2931 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u3 h))))))))
  have u22 : s 55 ≠ 0 := (Or.elim c3166 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u3 h))))))))
  have u23 : s 39 ≠ 3 := (Or.elim c2449 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u24 : s 34 ≠ 3 := (Or.elim c2224 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u25 : s 39 ≠ 1 := (Or.elim c2447 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u26 : s 34 ≠ 1 := (Or.elim c2222 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u27 : s 10 ≠ 0 := (Or.elim c112 (fun h => h) (fun h => (False.elim (h a0))))
  have u28 : s 50 = 2 := (Or.elim c1147 (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => h))))
  have u29 : s 17 ≠ 1 := (Or.elim c1442 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (False.elim (u15 h))))))
  have u30 : s 18 ≠ 1 := (Or.elim c1507 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (False.elim (u15 h))))))
  have u31 : s 19 ≠ 1 := (Or.elim c1532 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (False.elim (u15 h))))))
  have u32 : s 50 ≠ 1 := (Or.elim c2912 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (False.elim (u15 h))))))
  have u33 : s 55 ≠ 1 := (Or.elim c3147 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (False.elim (u15 h))))))
  have u34 : s 51 ≠ 2 := (Or.elim c2978 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u29 h))))))
  have u35 : s 19 = 0 := (Or.elim c2943 (fun h => (False.elim (h u28))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u31 h))))))
  have u36 : s 24 ≠ 2 := (Or.elim c1763 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u32 h))))))
  have u37 : s 39 ≠ 2 := (Or.elim c2438 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u33 h))))))
  have u38 : s 34 ≠ 2 := (Or.elim c2213 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u33 h))))))
  have u39 : s 51 = 1 := (Or.elim c1541 (fun h => (False.elim (h u35))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (u11 h))))))))
  have u40 : s 18 ≠ 0 := (Or.elim c1501 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => (False.elim (u23 h))))))))
  have u41 : s 21 ≠ 0 := (Or.elim c1621 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u24 h))))))))
  have u42 : s 24 = 0 := (Or.elim c2992 (fun h => (False.elim (h u39))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u36 h))))))
  have u43 : s 37 ≠ 2 := (Or.elim c2338 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u40 h))) (fun h => (False.elim (u30 h))))))
  have u44 : s 37 ≠ 1 := (Or.elim c2347 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u41 h))) (fun h => (False.elim (u14 h))))))
  exact (Or.elim c1751 (fun h => (h u42)) (fun h => (Or.elim h (fun h => (u44 h)) (fun h => (Or.elim h (fun h => (u43 h)) (fun h => (u20 h)))))))

private theorem step3389 (s : Fin 60 → Fin 5)
    (c3383 : s 57 = 1 ∨ s 57 = 2)
    (c629 : s 57 ≠ 0 ∨ s 57 ≠ 1)
    (c635 : s 57 ≠ 1 ∨ s 57 ≠ 4)
    (c2449 : s 39 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c634 : s 57 ≠ 1 ∨ s 57 ≠ 3)
    (c2450 : s 39 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c1860 : s 26 ≠ 4 ∨ s 39 = 3 ∨ s 39 = 4)
    (c1999 : s 29 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c2000 : s 29 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c3225 : s 56 ≠ 4 ∨ s 29 = 3 ∨ s 29 = 4)
    (c1324 : s 14 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c1322 : s 14 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c3387 : s 14 = 0 ∨ s 57 = 2)
    (c157 : s 14 ≠ 0 ∨ s 14 ≠ 2)
    (c3196 : s 56 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c1874 : s 26 ≠ 3 ∨ s 56 = 0 ∨ s 56 = 4)
    (c2325 : s 36 ≠ 4 ∨ s 26 = 3 ∨ s 26 = 4)
    (c3315 : s 58 ≠ 4 ∨ s 29 = 3 ∨ s 29 = 4)
    (c3306 : s 58 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2284 : s 36 ≠ 3 ∨ s 58 = 0 ∨ s 58 = 4)
    (c1390 : s 16 ≠ 4 ∨ s 36 = 3 ∨ s 36 = 4)
    (c3180 : s 55 ≠ 4 ∨ s 29 = 3 ∨ s 29 = 4)
    (c3166 : s 55 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c1154 : s 10 ≠ 3 ∨ s 55 = 0 ∨ s 55 = 4)
    (c2142 : s 32 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2131 : s 32 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c1113 : s 10 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c3388 : s 10 ≠ 1 ∨ s 57 = 2)
    (c1416 : s 16 ≠ 0 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 10 = 3)
    (c1014 : s 7 ≠ 3 ∨ s 16 = 0 ∨ s 16 = 4)
    (c1506 : s 18 ≠ 0 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 10 = 3)
    (c1531 : s 19 ≠ 0 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 10 = 3)
    (c2145 : s 32 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c1609 : s 21 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4)
    (c1608 : s 21 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1248 : s 13 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1289 : s 13 ≠ 3 ∨ s 55 = 0 ∨ s 55 = 4)
    (c2447 : s 39 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c563 : s 51 ≠ 0 ∨ s 51 ≠ 1)
    (c567 : s 51 ≠ 1 ∨ s 51 ≠ 2)
    (c2982 : s 51 ≠ 1 ∨ s 18 = 0 ∨ s 18 = 2)
    (c1512 : s 18 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2)
    (c1422 : s 16 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2)
    (c1267 : s 13 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2)
    (c1542 : s 19 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2)
    (c1503 : s 18 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1)
    (c2338 : s 37 ≠ 2 ∨ s 18 = 0 ∨ s 18 = 1)
    (c1013 : s 7 ≠ 2 ∨ s 16 = 0 ∨ s 16 = 1)
    (c3006 : s 52 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3)
    (c3013 : s 52 ≠ 2 ∨ s 19 = 0 ∨ s 19 = 1)
    (c2421 : s 39 ≠ 0 ∨ s 7 = 1 ∨ s 7 = 2 ∨ s 7 = 3)
    (c987 : s 7 ≠ 1 ∨ s 37 = 0 ∨ s 37 = 2)
    (c1637 : s 21 ≠ 1 ∨ s 52 = 0 ∨ s 52 = 2)
    (c2346 : s 37 ≠ 0 ∨ s 21 = 1 ∨ s 21 = 2 ∨ s 21 = 3)
    : s 51 ≠ 1 ∨ s 57 = 2 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 57 = 1 := (Or.elim c3383 (fun h => h) (fun h => (False.elim (a1 h))))
  have u1 : s 57 ≠ 0 := (Or.elim c629 (fun h => h) (fun h => (False.elim (h u0))))
  have u2 : s 57 ≠ 4 := (Or.elim c635 (fun h => (False.elim (h u0))) (fun h => h))
  have u3 : s 39 ≠ 3 := (Or.elim c2449 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u4 : s 57 ≠ 3 := (Or.elim c634 (fun h => (False.elim (h u0))) (fun h => h))
  have u5 : s 39 ≠ 4 := (Or.elim c2450 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u6 : s 26 ≠ 4 := (Or.elim c1860 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u5 h))))))
  have u7 : s 29 ≠ 3 := (Or.elim c1999 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u8 : s 29 ≠ 4 := (Or.elim c2000 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u9 : s 56 ≠ 4 := (Or.elim c3225 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u8 h))))))
  have u10 : s 14 ≠ 3 := (Or.elim c1324 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))
  have u11 : s 14 ≠ 1 := (Or.elim c1322 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u12 : s 14 = 0 := (Or.elim c3387 (fun h => h) (fun h => (False.elim (a1 h))))
  have u13 : s 14 ≠ 2 := (Or.elim c157 (fun h => (False.elim (h u12))) (fun h => h))
  have u14 : s 56 ≠ 0 := (Or.elim c3196 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u10 h))))))))
  have u15 : s 26 ≠ 3 := (Or.elim c1874 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (u9 h))))))
  have u16 : s 36 ≠ 4 := (Or.elim c2325 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u6 h))))))
  have u17 : s 58 ≠ 4 := (Or.elim c3315 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u8 h))))))
  have u18 : s 58 ≠ 0 := (Or.elim c3306 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u10 h))))))))
  have u19 : s 36 ≠ 3 := (Or.elim c2284 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (False.elim (u17 h))))))
  have u20 : s 16 ≠ 4 := (Or.elim c1390 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u16 h))))))
  have u21 : s 55 ≠ 4 := (Or.elim c3180 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u8 h))))))
  have u22 : s 55 ≠ 0 := (Or.elim c3166 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u10 h))))))))
  have u23 : s 10 ≠ 3 := (Or.elim c1154 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u21 h))))))
  have u24 : s 32 ≠ 1 := (Or.elim c2142 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u25 : s 32 ≠ 0 := (Or.elim c2131 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u10 h))))))))
  have u26 : s 10 ≠ 2 := (Or.elim c1113 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u24 h))))))
  have u27 : s 10 ≠ 1 := (Or.elim c3388 (fun h => h) (fun h => (False.elim (a1 h))))
  have u28 : s 16 ≠ 0 := (Or.elim c1416 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (False.elim (u23 h))))))))
  have u29 : s 7 ≠ 3 := (Or.elim c1014 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u28 h))) (fun h => (False.elim (u20 h))))))
  have u30 : s 18 ≠ 0 := (Or.elim c1506 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (False.elim (u23 h))))))))
  have u31 : s 19 ≠ 0 := (Or.elim c1531 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (False.elim (u23 h))))))))
  have u32 : s 32 ≠ 4 := (Or.elim c2145 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u2 h))))))
  have u33 : s 21 ≠ 3 := (Or.elim c1609 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u32 h))))))
  have u34 : s 21 ≠ 2 := (Or.elim c1608 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u24 h))))))
  have u35 : s 13 ≠ 2 := (Or.elim c1248 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u24 h))))))
  have u36 : s 13 ≠ 3 := (Or.elim c1289 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u21 h))))))
  have u37 : s 39 ≠ 1 := (Or.elim c2447 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u38 : s 51 ≠ 0 := (Or.elim c563 (fun h => h) (fun h => (False.elim (h a0))))
  have u39 : s 51 ≠ 2 := (Or.elim c567 (fun h => (False.elim (h a0))) (fun h => h))
  have u40 : s 18 = 2 := (Or.elim c2982 (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => h))))
  have u41 : s 18 ≠ 1 := (Or.elim c1512 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u39 h))))))
  have u42 : s 16 ≠ 1 := (Or.elim c1422 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u39 h))))))
  have u43 : s 13 ≠ 1 := (Or.elim c1267 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u39 h))))))
  have u44 : s 19 ≠ 1 := (Or.elim c1542 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u39 h))))))
  have u45 : s 39 = 0 := (Or.elim c1503 (fun h => (False.elim (h u40))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u37 h))))))
  have u46 : s 37 ≠ 2 := (Or.elim c2338 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => (False.elim (u41 h))))))
  have u47 : s 7 ≠ 2 := (Or.elim c1013 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u28 h))) (fun h => (False.elim (u42 h))))))
  have u48 : s 52 ≠ 0 := (Or.elim c3006 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u43 h))) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u36 h))))))))
  have u49 : s 52 ≠ 2 := (Or.elim c3013 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u44 h))))))
  have u50 : s 7 = 1 := (Or.elim c2421 (fun h => (False.elim (h u45))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u47 h))) (fun h => (False.elim (u29 h))))))))
  have u51 : s 37 = 0 := (Or.elim c987 (fun h => (False.elim (h u50))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u46 h))))))
  have u52 : s 21 ≠ 1 := (Or.elim c1637 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u48 h))) (fun h => (False.elim (u49 h))))))
  exact (Or.elim c2346 (fun h => (h u51)) (fun h => (Or.elim h (fun h => (u52 h)) (fun h => (Or.elim h (fun h => (u34 h)) (fun h => (u33 h)))))))

private theorem step3390 (s : Fin 60 → Fin 5)
    (c3389 : s 51 ≠ 1 ∨ s 57 = 2)
    (c3383 : s 57 = 1 ∨ s 57 = 2)
    (c629 : s 57 ≠ 0 ∨ s 57 ≠ 1)
    (c635 : s 57 ≠ 1 ∨ s 57 ≠ 4)
    (c2144 : s 32 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c634 : s 57 ≠ 1 ∨ s 57 ≠ 3)
    (c2145 : s 32 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c1115 : s 10 ≠ 4 ∨ s 32 = 3 ∨ s 32 = 4)
    (c1999 : s 29 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c2000 : s 29 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c3180 : s 55 ≠ 4 ∨ s 29 = 3 ∨ s 29 = 4)
    (c1324 : s 14 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c1322 : s 14 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c3387 : s 14 = 0 ∨ s 57 = 2)
    (c157 : s 14 ≠ 0 ∨ s 14 ≠ 2)
    (c3166 : s 55 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c1154 : s 10 ≠ 3 ∨ s 55 = 0 ∨ s 55 = 4)
    (c1535 : s 19 ≠ 4 ∨ s 10 = 3 ∨ s 10 = 4)
    (c2142 : s 32 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2131 : s 32 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c1113 : s 10 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c3388 : s 10 ≠ 1 ∨ s 57 = 2)
    (c1531 : s 19 ≠ 0 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 10 = 3)
    (c2944 : s 50 ≠ 3 ∨ s 19 = 0 ∨ s 19 = 4)
    (c1325 : s 14 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c1465 : s 17 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4)
    (c1461 : s 17 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2979 : s 51 ≠ 3 ∨ s 17 = 0 ∨ s 17 = 4)
    (c1248 : s 13 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c2943 : s 50 ≠ 2 ∨ s 19 = 0 ∨ s 19 = 1)
    (c2988 : s 51 ≠ 2 ∨ s 19 = 0 ∨ s 19 = 1)
    (c1306 : s 14 ≠ 0 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 50 = 3)
    (c1266 : s 13 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3)
    (c2927 : s 50 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2)
    : s 19 = 1 ∨ s 57 = 2 := by
  by_contra hc
  try simp only [not_or] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 51 ≠ 1 := (Or.elim c3389 (fun h => h) (fun h => (False.elim (a1 h))))
  have u1 : s 57 = 1 := (Or.elim c3383 (fun h => h) (fun h => (False.elim (a1 h))))
  have u2 : s 57 ≠ 0 := (Or.elim c629 (fun h => h) (fun h => (False.elim (h u1))))
  have u3 : s 57 ≠ 4 := (Or.elim c635 (fun h => (False.elim (h u1))) (fun h => h))
  have u4 : s 32 ≠ 3 := (Or.elim c2144 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u3 h))))))
  have u5 : s 57 ≠ 3 := (Or.elim c634 (fun h => (False.elim (h u1))) (fun h => h))
  have u6 : s 32 ≠ 4 := (Or.elim c2145 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u3 h))))))
  have u7 : s 10 ≠ 4 := (Or.elim c1115 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u6 h))))))
  have u8 : s 29 ≠ 3 := (Or.elim c1999 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u3 h))))))
  have u9 : s 29 ≠ 4 := (Or.elim c2000 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u3 h))))))
  have u10 : s 55 ≠ 4 := (Or.elim c3180 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u9 h))))))
  have u11 : s 14 ≠ 3 := (Or.elim c1324 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u3 h))))))
  have u12 : s 14 ≠ 1 := (Or.elim c1322 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a1 h))))))
  have u13 : s 14 = 0 := (Or.elim c3387 (fun h => h) (fun h => (False.elim (a1 h))))
  have u14 : s 14 ≠ 2 := (Or.elim c157 (fun h => (False.elim (h u13))) (fun h => h))
  have u15 : s 55 ≠ 0 := (Or.elim c3166 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (u11 h))))))))
  have u16 : s 10 ≠ 3 := (Or.elim c1154 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u10 h))))))
  have u17 : s 19 ≠ 4 := (Or.elim c1535 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (u7 h))))))
  have u18 : s 32 ≠ 1 := (Or.elim c2142 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a1 h))))))
  have u19 : s 32 ≠ 0 := (Or.elim c2131 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (u11 h))))))))
  have u20 : s 10 ≠ 2 := (Or.elim c1113 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u18 h))))))
  have u21 : s 10 ≠ 1 := (Or.elim c3388 (fun h => h) (fun h => (False.elim (a1 h))))
  have u22 : s 19 ≠ 0 := (Or.elim c1531 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u16 h))))))))
  have u23 : s 50 ≠ 3 := (Or.elim c2944 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u17 h))))))
  have u24 : s 14 ≠ 4 := (Or.elim c1325 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u3 h))))))
  have u25 : s 17 ≠ 4 := (Or.elim c1465 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u24 h))))))
  have u26 : s 17 ≠ 0 := (Or.elim c1461 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (u11 h))))))))
  have u27 : s 51 ≠ 3 := (Or.elim c2979 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (False.elim (u25 h))))))
  have u28 : s 13 ≠ 2 := (Or.elim c1248 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u18 h))))))
  have u29 : s 50 ≠ 2 := (Or.elim c2943 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (a0 h))))))
  have u30 : s 51 ≠ 2 := (Or.elim c2988 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (a0 h))))))
  have u31 : s 50 = 1 := (Or.elim c1306 (fun h => (False.elim (h u13))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u29 h))) (fun h => (False.elim (u23 h))))))))
  have u32 : s 13 ≠ 0 := (Or.elim c1266 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => (False.elim (u27 h))))))))
  exact (Or.elim c2927 (fun h => (h u31)) (fun h => (Or.elim h (fun h => (u32 h)) (fun h => (u28 h)))))

private theorem step3391 (s : Fin 60 → Fin 5)
    (c3367 : s 59 ≠ 4)
    (c3383 : s 57 = 1 ∨ s 57 = 2)
    (c629 : s 57 ≠ 0 ∨ s 57 ≠ 1)
    (c635 : s 57 ≠ 1 ∨ s 57 ≠ 4)
    (c1324 : s 14 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c1322 : s 14 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c3387 : s 14 = 0 ∨ s 57 = 2)
    (c157 : s 14 ≠ 0 ∨ s 14 ≠ 2)
    (c2931 : s 50 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2142 : s 32 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2131 : s 32 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c1113 : s 10 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1999 : s 29 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c634 : s 57 ≠ 1 ∨ s 57 ≠ 3)
    (c2000 : s 29 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c3180 : s 55 ≠ 4 ∨ s 29 = 3 ∨ s 29 = 4)
    (c3166 : s 55 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c1154 : s 10 ≠ 3 ∨ s 55 = 0 ∨ s 55 = 4)
    (c3388 : s 10 ≠ 1 ∨ s 57 = 2)
    (c1531 : s 19 ≠ 0 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 10 = 3)
    (c3390 : s 19 = 1 ∨ s 57 = 2)
    (c215 : s 19 ≠ 1 ∨ s 19 ≠ 2)
    (c2942 : s 50 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2)
    (c2608 : s 43 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1)
    (c922 : s 5 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2)
    (c3389 : s 51 ≠ 1 ∨ s 57 = 2)
    (c3351 : s 59 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2504 : s 40 ≠ 3 ∨ s 59 = 0 ∨ s 59 = 4)
    (c1325 : s 14 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c1465 : s 17 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4)
    (c1461 : s 17 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2979 : s 51 ≠ 3 ∨ s 17 = 0 ∨ s 17 = 4)
    (c933 : s 6 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1248 : s 13 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1289 : s 13 ≠ 3 ∨ s 55 = 0 ∨ s 55 = 4)
    (c2224 : s 34 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c2222 : s 34 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c1542 : s 19 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2)
    (c2611 : s 43 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3)
    (c2961 : s 51 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3)
    (c3342 : s 59 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c1257 : s 13 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2)
    (c2233 : s 34 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c2503 : s 40 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1)
    (c1438 : s 17 ≠ 2 ∨ s 5 = 0 ∨ s 5 = 1)
    (c941 : s 6 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3)
    (c891 : s 5 ≠ 0 ∨ s 40 = 1 ∨ s 40 = 2 ∨ s 40 = 3)
    (c2467 : s 40 ≠ 1 ∨ s 6 = 0 ∨ s 6 = 2)
    : s 51 = 2 ∨ s 57 = 2 := by
  by_contra hc
  try simp only [not_or] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 59 ≠ 4 := c3367
  have u1 : s 57 = 1 := (Or.elim c3383 (fun h => h) (fun h => (False.elim (a1 h))))
  have u2 : s 57 ≠ 0 := (Or.elim c629 (fun h => h) (fun h => (False.elim (h u1))))
  have u3 : s 57 ≠ 4 := (Or.elim c635 (fun h => (False.elim (h u1))) (fun h => h))
  have u4 : s 14 ≠ 3 := (Or.elim c1324 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u3 h))))))
  have u5 : s 14 ≠ 1 := (Or.elim c1322 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a1 h))))))
  have u6 : s 14 = 0 := (Or.elim c3387 (fun h => h) (fun h => (False.elim (a1 h))))
  have u7 : s 14 ≠ 2 := (Or.elim c157 (fun h => (False.elim (h u6))) (fun h => h))
  have u8 : s 50 ≠ 0 := (Or.elim c2931 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u4 h))))))))
  have u9 : s 32 ≠ 1 := (Or.elim c2142 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a1 h))))))
  have u10 : s 32 ≠ 0 := (Or.elim c2131 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u4 h))))))))
  have u11 : s 10 ≠ 2 := (Or.elim c1113 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u9 h))))))
  have u12 : s 29 ≠ 3 := (Or.elim c1999 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u3 h))))))
  have u13 : s 57 ≠ 3 := (Or.elim c634 (fun h => (False.elim (h u1))) (fun h => h))
  have u14 : s 29 ≠ 4 := (Or.elim c2000 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u3 h))))))
  have u15 : s 55 ≠ 4 := (Or.elim c3180 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u14 h))))))
  have u16 : s 55 ≠ 0 := (Or.elim c3166 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u4 h))))))))
  have u17 : s 10 ≠ 3 := (Or.elim c1154 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (u15 h))))))
  have u18 : s 10 ≠ 1 := (Or.elim c3388 (fun h => h) (fun h => (False.elim (a1 h))))
  have u19 : s 19 ≠ 0 := (Or.elim c1531 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u17 h))))))))
  have u20 : s 19 = 1 := (Or.elim c3390 (fun h => h) (fun h => (False.elim (a1 h))))
  have u21 : s 19 ≠ 2 := (Or.elim c215 (fun h => (False.elim (h u20))) (fun h => h))
  have u22 : s 50 ≠ 1 := (Or.elim c2942 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u21 h))))))
  have u23 : s 43 ≠ 2 := (Or.elim c2608 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u22 h))))))
  have u24 : s 5 ≠ 1 := (Or.elim c922 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u21 h))))))
  have u25 : s 51 ≠ 1 := (Or.elim c3389 (fun h => h) (fun h => (False.elim (a1 h))))
  have u26 : s 59 ≠ 0 := (Or.elim c3351 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u4 h))))))))
  have u27 : s 40 ≠ 3 := (Or.elim c2504 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (False.elim (u0 h))))))
  have u28 : s 14 ≠ 4 := (Or.elim c1325 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u3 h))))))
  have u29 : s 17 ≠ 4 := (Or.elim c1465 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u28 h))))))
  have u30 : s 17 ≠ 0 := (Or.elim c1461 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u4 h))))))))
  have u31 : s 51 ≠ 3 := (Or.elim c2979 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => (False.elim (u29 h))))))
  have u32 : s 6 ≠ 2 := (Or.elim c933 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u9 h))))))
  have u33 : s 13 ≠ 2 := (Or.elim c1248 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u9 h))))))
  have u34 : s 13 ≠ 3 := (Or.elim c1289 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (u15 h))))))
  have u35 : s 34 ≠ 3 := (Or.elim c2224 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u3 h))))))
  have u36 : s 34 ≠ 1 := (Or.elim c2222 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (a1 h))))))
  have u37 : s 51 = 0 := (Or.elim c1542 (fun h => (False.elim (h u20))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a0 h))))))
  have u38 : s 43 ≠ 0 := (Or.elim c2611 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u31 h))))))))
  have u39 : s 13 = 1 := (Or.elim c2961 (fun h => (False.elim (h u37))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u33 h))) (fun h => (False.elim (u34 h))))))))
  have u40 : s 59 ≠ 1 := (Or.elim c3342 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u38 h))) (fun h => (False.elim (u23 h))))))
  have u41 : s 17 = 2 := (Or.elim c1257 (fun h => (False.elim (h u39))) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => h))))
  have u42 : s 34 ≠ 2 := (Or.elim c2233 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (False.elim (u40 h))))))
  have u43 : s 40 ≠ 2 := (Or.elim c2503 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (False.elim (u40 h))))))
  have u44 : s 5 = 0 := (Or.elim c1438 (fun h => (False.elim (h u41))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u24 h))))))
  have u45 : s 6 ≠ 0 := (Or.elim c941 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (Or.elim h (fun h => (False.elim (u42 h))) (fun h => (False.elim (u35 h))))))))
  have u46 : s 40 = 1 := (Or.elim c891 (fun h => (False.elim (h u44))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u43 h))) (fun h => (False.elim (u27 h))))))))
  exact (Or.elim c2467 (fun h => (h u46)) (fun h => (Or.elim h (fun h => (u45 h)) (fun h => (u32 h)))))

private theorem step3392 (s : Fin 60 → Fin 5)
    (c3383 : s 57 = 1 ∨ s 57 = 2)
    (c629 : s 57 ≠ 0 ∨ s 57 ≠ 1)
    (c634 : s 57 ≠ 1 ∨ s 57 ≠ 3)
    (c635 : s 57 ≠ 1 ∨ s 57 ≠ 4)
    (c2142 : s 32 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2222 : s 34 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c1322 : s 14 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2)
    (c2000 : s 29 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c1324 : s 14 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c2145 : s 32 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    (c1999 : s 29 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c2224 : s 34 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    (c3180 : s 55 ≠ 4 ∨ s 29 = 3 ∨ s 29 = 4)
    (c3387 : s 14 = 0 ∨ s 57 = 2)
    (c157 : s 14 ≠ 0 ∨ s 14 ≠ 2)
    (c3196 : s 56 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c3166 : s 55 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2131 : s 32 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c1461 : s 17 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c1154 : s 10 ≠ 3 ∨ s 55 = 0 ∨ s 55 = 4)
    (c1289 : s 13 ≠ 3 ∨ s 55 = 0 ∨ s 55 = 4)
    (c1113 : s 10 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1248 : s 13 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c1158 : s 11 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c798 : s 3 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1)
    (c799 : s 3 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4)
    (c3388 : s 10 ≠ 1 ∨ s 57 = 2)
    (c1371 : s 15 ≠ 0 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 10 = 3)
    (c1531 : s 19 ≠ 0 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 10 = 3)
    (c3389 : s 51 ≠ 1 ∨ s 57 = 2)
    (c3390 : s 19 = 1 ∨ s 57 = 2)
    (c215 : s 19 ≠ 1 ∨ s 19 ≠ 2)
    (c3057 : s 53 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2)
    (c3391 : s 51 = 2 ∨ s 57 = 2)
    (c564 : s 51 ≠ 0 ∨ s 51 ≠ 2)
    (c2978 : s 51 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1)
    (c1468 : s 17 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c1378 : s 15 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c1447 : s 17 ≠ 1 ∨ s 11 = 0 ∨ s 11 = 2)
    (c1257 : s 13 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2)
    (c817 : s 3 ≠ 1 ∨ s 15 = 0 ∨ s 15 = 2)
    (c1166 : s 11 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3)
    (c3051 : s 53 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3)
    (c1801 : s 25 ≠ 0 ∨ s 3 = 1 ∨ s 3 = 2 ∨ s 3 = 3)
    (c2218 : s 34 ≠ 2 ∨ s 56 = 0 ∨ s 56 = 1)
    (c1823 : s 25 ≠ 2 ∨ s 53 = 0 ∨ s 53 = 1)
    (c3202 : s 56 ≠ 1 ∨ s 25 = 0 ∨ s 25 = 2)
    : s 57 = 2 := by
  by_contra hc
  have u0 : s 57 = 1 := (Or.elim c3383 (fun h => h) (fun h => (False.elim (hc h))))
  have u1 : s 57 ≠ 0 := (Or.elim c629 (fun h => h) (fun h => (False.elim (h u0))))
  have u2 : s 57 ≠ 3 := (Or.elim c634 (fun h => (False.elim (h u0))) (fun h => h))
  have u3 : s 57 ≠ 4 := (Or.elim c635 (fun h => (False.elim (h u0))) (fun h => h))
  have u4 : s 32 ≠ 1 := (Or.elim c2142 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (hc h))))))
  have u5 : s 34 ≠ 1 := (Or.elim c2222 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (hc h))))))
  have u6 : s 14 ≠ 1 := (Or.elim c1322 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (hc h))))))
  have u7 : s 29 ≠ 4 := (Or.elim c2000 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u3 h))))))
  have u8 : s 14 ≠ 3 := (Or.elim c1324 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u3 h))))))
  have u9 : s 32 ≠ 4 := (Or.elim c2145 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u3 h))))))
  have u10 : s 29 ≠ 3 := (Or.elim c1999 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u3 h))))))
  have u11 : s 34 ≠ 3 := (Or.elim c2224 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u3 h))))))
  have u12 : s 55 ≠ 4 := (Or.elim c3180 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u7 h))))))
  have u13 : s 14 = 0 := (Or.elim c3387 (fun h => h) (fun h => (False.elim (hc h))))
  have u14 : s 14 ≠ 2 := (Or.elim c157 (fun h => (False.elim (h u13))) (fun h => h))
  have u15 : s 56 ≠ 0 := (Or.elim c3196 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (u8 h))))))))
  have u16 : s 55 ≠ 0 := (Or.elim c3166 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (u8 h))))))))
  have u17 : s 32 ≠ 0 := (Or.elim c2131 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (u8 h))))))))
  have u18 : s 17 ≠ 0 := (Or.elim c1461 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (u8 h))))))))
  have u19 : s 10 ≠ 3 := (Or.elim c1154 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (u12 h))))))
  have u20 : s 13 ≠ 3 := (Or.elim c1289 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (u12 h))))))
  have u21 : s 10 ≠ 2 := (Or.elim c1113 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u4 h))))))
  have u22 : s 13 ≠ 2 := (Or.elim c1248 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u4 h))))))
  have u23 : s 11 ≠ 2 := (Or.elim c1158 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u4 h))))))
  have u24 : s 3 ≠ 2 := (Or.elim c798 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u4 h))))))
  have u25 : s 3 ≠ 3 := (Or.elim c799 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u9 h))))))
  have u26 : s 10 ≠ 1 := (Or.elim c3388 (fun h => h) (fun h => (False.elim (hc h))))
  have u27 : s 15 ≠ 0 := (Or.elim c1371 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u19 h))))))))
  have u28 : s 19 ≠ 0 := (Or.elim c1531 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u19 h))))))))
  have u29 : s 51 ≠ 1 := (Or.elim c3389 (fun h => h) (fun h => (False.elim (hc h))))
  have u30 : s 19 = 1 := (Or.elim c3390 (fun h => h) (fun h => (False.elim (hc h))))
  have u31 : s 19 ≠ 2 := (Or.elim c215 (fun h => (False.elim (h u30))) (fun h => h))
  have u32 : s 53 ≠ 1 := (Or.elim c3057 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u28 h))) (fun h => (False.elim (u31 h))))))
  have u33 : s 51 = 2 := (Or.elim c3391 (fun h => h) (fun h => (False.elim (hc h))))
  have u34 : s 51 ≠ 0 := (Or.elim c564 (fun h => h) (fun h => (False.elim (h u33))))
  have u35 : s 17 = 1 := (Or.elim c2978 (fun h => (False.elim (h u33))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => h))))
  have u36 : s 17 ≠ 2 := (Or.elim c1468 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (u29 h))))))
  have u37 : s 15 ≠ 2 := (Or.elim c1378 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (u29 h))))))
  have u38 : s 11 = 0 := (Or.elim c1447 (fun h => (False.elim (h u35))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u23 h))))))
  have u39 : s 13 ≠ 1 := (Or.elim c1257 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (False.elim (u36 h))))))
  have u40 : s 3 ≠ 1 := (Or.elim c817 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (False.elim (u37 h))))))
  have u41 : s 34 = 2 := (Or.elim c1166 (fun h => (False.elim (h u38))) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u11 h))))))))
  have u42 : s 53 ≠ 0 := (Or.elim c3051 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u20 h))))))))
  have u43 : s 25 ≠ 0 := (Or.elim c1801 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u40 h))) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (False.elim (u25 h))))))))
  have u44 : s 56 = 1 := (Or.elim c2218 (fun h => (False.elim (h u41))) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => h))))
  have u45 : s 25 ≠ 2 := (Or.elim c1823 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u42 h))) (fun h => (False.elim (u32 h))))))
  exact (Or.elim c3202 (fun h => (h u44)) (fun h => (Or.elim h (fun h => (u43 h)) (fun h => (u45 h)))))

private theorem step3393 (s : Fin 60 → Fin 5)
    (c3392 : s 57 = 2)
    (c630 : s 57 ≠ 0 ∨ s 57 ≠ 2)
    : s 57 ≠ 0 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 57 = 2 := c3392
  exact (Or.elim c630 (fun h => (h hc)) (fun h => (h u0)))

private theorem step3394 (s : Fin 60 → Fin 5)
    (c3392 : s 57 = 2)
    (c633 : s 57 ≠ 1 ∨ s 57 ≠ 2)
    : s 57 ≠ 1 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 57 = 2 := c3392
  exact (Or.elim c633 (fun h => (h hc)) (fun h => (h u0)))

private theorem step3395 (s : Fin 60 → Fin 5)
    (c3392 : s 57 = 2)
    (c636 : s 57 ≠ 2 ∨ s 57 ≠ 3)
    : s 57 ≠ 3 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 57 = 2 := c3392
  exact (Or.elim c636 (fun h => (h u0)) (fun h => (h hc)))

private theorem step3396 (s : Fin 60 → Fin 5)
    (c3392 : s 57 = 2)
    (c637 : s 57 ≠ 2 ∨ s 57 ≠ 4)
    : s 57 ≠ 4 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 57 = 2 := c3392
  exact (Or.elim c637 (fun h => (h u0)) (fun h => (h hc)))

private theorem step3398 (s : Fin 60 → Fin 5)
    (c3393 : s 57 ≠ 0)
    (c3394 : s 57 ≠ 1)
    (c2098 : s 31 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    : s 31 ≠ 2 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 57 ≠ 0 := c3393
  have u1 : s 57 ≠ 1 := c3394
  exact (Or.elim c2098 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3400 (s : Fin 60 → Fin 5)
    (c3393 : s 57 ≠ 0)
    (c3394 : s 57 ≠ 1)
    (c1323 : s 14 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    : s 14 ≠ 2 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 57 ≠ 0 := c3393
  have u1 : s 57 ≠ 1 := c3394
  exact (Or.elim c1323 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3401 (s : Fin 60 → Fin 5)
    (c3393 : s 57 ≠ 0)
    (c3394 : s 57 ≠ 1)
    (c1998 : s 29 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    : s 29 ≠ 2 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 57 ≠ 0 := c3393
  have u1 : s 57 ≠ 1 := c3394
  exact (Or.elim c1998 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3402 (s : Fin 60 → Fin 5)
    (c3393 : s 57 ≠ 0)
    (c3394 : s 57 ≠ 1)
    (c2143 : s 32 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    : s 32 ≠ 2 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 57 ≠ 0 := c3393
  have u1 : s 57 ≠ 1 := c3394
  exact (Or.elim c2143 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3403 (s : Fin 60 → Fin 5)
    (c3393 : s 57 ≠ 0)
    (c3394 : s 57 ≠ 1)
    (c2223 : s 34 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    : s 34 ≠ 2 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 57 ≠ 0 := c3393
  have u1 : s 57 ≠ 1 := c3394
  exact (Or.elim c2223 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3404 (s : Fin 60 → Fin 5)
    (c3393 : s 57 ≠ 0)
    (c3394 : s 57 ≠ 1)
    (c2673 : s 44 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    : s 44 ≠ 2 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 57 ≠ 0 := c3393
  have u1 : s 57 ≠ 1 := c3394
  exact (Or.elim c2673 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3405 (s : Fin 60 → Fin 5)
    (c3393 : s 57 ≠ 0)
    (c3394 : s 57 ≠ 1)
    (c2448 : s 39 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1)
    : s 39 ≠ 2 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 57 ≠ 0 := c3393
  have u1 : s 57 ≠ 1 := c3394
  exact (Or.elim c2448 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3407 (s : Fin 60 → Fin 5)
    (c3395 : s 57 ≠ 3)
    (c3396 : s 57 ≠ 4)
    (c2225 : s 34 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    : s 34 ≠ 4 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 57 ≠ 3 := c3395
  have u1 : s 57 ≠ 4 := c3396
  exact (Or.elim c2225 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3409 (s : Fin 60 → Fin 5)
    (c3395 : s 57 ≠ 3)
    (c3396 : s 57 ≠ 4)
    (c1325 : s 14 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    : s 14 ≠ 4 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 57 ≠ 3 := c3395
  have u1 : s 57 ≠ 4 := c3396
  exact (Or.elim c1325 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3411 (s : Fin 60 → Fin 5)
    (c3396 : s 57 ≠ 4)
    (c3393 : s 57 ≠ 0)
    (c1324 : s 14 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    : s 14 ≠ 3 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 57 ≠ 4 := c3396
  have u1 : s 57 ≠ 0 := c3393
  exact (Or.elim c1324 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u0 h)))))

private theorem step3413 (s : Fin 60 → Fin 5)
    (c3396 : s 57 ≠ 4)
    (c3395 : s 57 ≠ 3)
    (c2145 : s 32 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4)
    : s 32 ≠ 4 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 57 ≠ 4 := c3396
  have u1 : s 57 ≠ 3 := c3395
  exact (Or.elim c2145 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u0 h)))))

private theorem step3419 (s : Fin 60 → Fin 5)
    (c3396 : s 57 ≠ 4)
    (c3393 : s 57 ≠ 0)
    (c2144 : s 32 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    : s 32 ≠ 3 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 57 ≠ 4 := c3396
  have u1 : s 57 ≠ 0 := c3393
  exact (Or.elim c2144 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u0 h)))))

private theorem step3421 (s : Fin 60 → Fin 5)
    (c3396 : s 57 ≠ 4)
    (c3393 : s 57 ≠ 0)
    (c2224 : s 34 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    : s 34 ≠ 3 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 57 ≠ 4 := c3396
  have u1 : s 57 ≠ 0 := c3393
  exact (Or.elim c2224 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u0 h)))))

private theorem step3423 (s : Fin 60 → Fin 5)
    (c3396 : s 57 ≠ 4)
    (c3393 : s 57 ≠ 0)
    (c2674 : s 44 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4)
    : s 44 ≠ 3 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 57 ≠ 4 := c3396
  have u1 : s 57 ≠ 0 := c3393
  exact (Or.elim c2674 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u0 h)))))

private theorem step3431 (s : Fin 60 → Fin 5)
    (c3407 : s 34 ≠ 4)
    (c3421 : s 34 ≠ 3)
    (c1625 : s 21 ≠ 4 ∨ s 34 = 3 ∨ s 34 = 4)
    : s 21 ≠ 4 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 34 ≠ 4 := c3407
  have u1 : s 34 ≠ 3 := c3421
  exact (Or.elim c1625 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u0 h)))))

private theorem step3432 (s : Fin 60 → Fin 5)
    (c3409 : s 14 ≠ 4)
    (c3411 : s 14 ≠ 3)
    (c1465 : s 17 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4)
    : s 17 ≠ 4 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 14 ≠ 4 := c3409
  have u1 : s 14 ≠ 3 := c3411
  exact (Or.elim c1465 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u0 h)))))

private theorem step3433 (s : Fin 60 → Fin 5)
    (c3409 : s 14 ≠ 4)
    (c3411 : s 14 ≠ 3)
    (c2810 : s 47 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4)
    : s 47 ≠ 4 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 14 ≠ 4 := c3409
  have u1 : s 14 ≠ 3 := c3411
  exact (Or.elim c2810 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u0 h)))))

private theorem step3438 (s : Fin 60 → Fin 5)
    (c3413 : s 32 ≠ 4)
    (c3419 : s 32 ≠ 3)
    (c1115 : s 10 ≠ 4 ∨ s 32 = 3 ∨ s 32 = 4)
    : s 10 ≠ 4 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 32 ≠ 4 := c3413
  have u1 : s 32 ≠ 3 := c3419
  exact (Or.elim c1115 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u0 h)))))

private theorem step3440 (s : Fin 60 → Fin 5)
    (c3413 : s 32 ≠ 4)
    (c3419 : s 32 ≠ 3)
    (c1250 : s 13 ≠ 4 ∨ s 32 = 3 ∨ s 32 = 4)
    : s 13 ≠ 4 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 32 ≠ 4 := c3413
  have u1 : s 32 ≠ 3 := c3419
  exact (Or.elim c1250 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u0 h)))))

private theorem step3456 (s : Fin 60 → Fin 5)
    (c3402 : s 32 ≠ 2)
    (c3413 : s 32 ≠ 4)
    (c3405 : s 39 ≠ 2)
    (c217 : s 19 ≠ 1 ∨ s 19 ≠ 4)
    (c216 : s 19 ≠ 1 ∨ s 19 ≠ 3)
    (c2990 : s 51 ≠ 4 ∨ s 19 = 3 ∨ s 19 = 4)
    (c564 : s 51 ≠ 0 ∨ s 51 ≠ 2)
    (c1514 : s 18 ≠ 3 ∨ s 51 = 0 ∨ s 51 = 4)
    (c1469 : s 17 ≠ 3 ∨ s 51 = 0 ∨ s 51 = 4)
    (c1269 : s 13 ≠ 3 ∨ s 51 = 0 ∨ s 51 = 4)
    (c3015 : s 52 ≠ 4 ∨ s 19 = 3 ∨ s 19 = 4)
    (c211 : s 19 ≠ 0 ∨ s 19 ≠ 1)
    (c215 : s 19 ≠ 1 ∨ s 19 ≠ 2)
    (c3012 : s 52 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2)
    (c3122 : s 54 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2)
    (c2942 : s 50 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2)
    (c2126 : s 32 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3)
    (c2963 : s 51 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1)
    (c2926 : s 50 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3)
    (c3006 : s 52 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3)
    (c3116 : s 54 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3)
    (c1607 : s 21 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1609 : s 21 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4)
    (c1256 : s 13 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c1148 : s 10 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1)
    (c1694 : s 22 ≠ 3 ∨ s 52 = 0 ∨ s 52 = 4)
    (c1693 : s 22 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1)
    (c1638 : s 21 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1)
    (c2543 : s 41 ≠ 2 ∨ s 54 = 0 ∨ s 54 = 1)
    (c2521 : s 41 ≠ 0 ∨ s 21 = 1 ∨ s 21 = 2 ∨ s 21 = 3)
    (c1442 : s 17 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2)
    (c1687 : s 22 ≠ 1 ∨ s 41 = 0 ∨ s 41 = 2)
    (c1131 : s 10 ≠ 0 ∨ s 18 = 1 ∨ s 18 = 2 ∨ s 18 = 3)
    (c2431 : s 39 ≠ 0 ∨ s 22 = 1 ∨ s 22 = 2 ∨ s 22 = 3)
    (c1502 : s 18 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2)
    : s 13 = 1 ∨ s 13 = 2 ∨ s 18 = 2 ∨ s 17 = 2 ∨ s 51 ≠ 2 ∨ s 19 ≠ 1 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5⟩ := hc
  have u0 : s 32 ≠ 2 := c3402
  have u1 : s 32 ≠ 4 := c3413
  have u2 : s 39 ≠ 2 := c3405
  have u3 : s 19 ≠ 4 := (Or.elim c217 (fun h => (False.elim (h a5))) (fun h => h))
  have u4 : s 19 ≠ 3 := (Or.elim c216 (fun h => (False.elim (h a5))) (fun h => h))
  have u5 : s 51 ≠ 4 := (Or.elim c2990 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u3 h))))))
  have u6 : s 51 ≠ 0 := (Or.elim c564 (fun h => h) (fun h => (False.elim (h a4))))
  have u7 : s 18 ≠ 3 := (Or.elim c1514 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u5 h))))))
  have u8 : s 17 ≠ 3 := (Or.elim c1469 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u5 h))))))
  have u9 : s 13 ≠ 3 := (Or.elim c1269 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u5 h))))))
  have u10 : s 52 ≠ 4 := (Or.elim c3015 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u4 h))) (fun h => (False.elim (u3 h))))))
  have u11 : s 19 ≠ 0 := (Or.elim c211 (fun h => h) (fun h => (False.elim (h a5))))
  have u12 : s 19 ≠ 2 := (Or.elim c215 (fun h => (False.elim (h a5))) (fun h => h))
  have u13 : s 52 ≠ 1 := (Or.elim c3012 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u12 h))))))
  have u14 : s 54 ≠ 1 := (Or.elim c3122 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u12 h))))))
  have u15 : s 50 ≠ 1 := (Or.elim c2942 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u12 h))))))
  have u16 : s 32 ≠ 0 := (Or.elim c2126 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u9 h))))))))
  have u17 : s 13 = 0 := (Or.elim c2963 (fun h => (False.elim (h a4))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a0 h))))))
  have u18 : s 50 ≠ 0 := (Or.elim c2926 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u9 h))))))))
  have u19 : s 52 ≠ 0 := (Or.elim c3006 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u9 h))))))))
  have u20 : s 54 ≠ 0 := (Or.elim c3116 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u9 h))))))))
  have u21 : s 21 ≠ 1 := (Or.elim c1607 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (u0 h))))))
  have u22 : s 21 ≠ 3 := (Or.elim c1609 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (u1 h))))))
  have u23 : s 17 = 1 := (Or.elim c1256 (fun h => (False.elim (h u17))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (u8 h))))))))
  have u24 : s 10 ≠ 2 := (Or.elim c1148 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (False.elim (u15 h))))))
  have u25 : s 22 ≠ 3 := (Or.elim c1694 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u10 h))))))
  have u26 : s 22 ≠ 2 := (Or.elim c1693 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u13 h))))))
  have u27 : s 21 ≠ 2 := (Or.elim c1638 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u13 h))))))
  have u28 : s 41 ≠ 2 := (Or.elim c2543 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u14 h))))))
  have u29 : s 41 ≠ 0 := (Or.elim c2521 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (False.elim (u22 h))))))))
  have u30 : s 10 = 0 := (Or.elim c1442 (fun h => (False.elim (h u23))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u24 h))))))
  have u31 : s 22 ≠ 1 := (Or.elim c1687 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u29 h))) (fun h => (False.elim (u28 h))))))
  have u32 : s 18 = 1 := (Or.elim c1131 (fun h => (False.elim (h u30))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (False.elim (u7 h))))))))
  have u33 : s 39 ≠ 0 := (Or.elim c2431 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (False.elim (u25 h))))))))
  exact (Or.elim c1502 (fun h => (h u32)) (fun h => (Or.elim h (fun h => (u33 h)) (fun h => (u2 h)))))

private theorem step3457 (s : Fin 60 → Fin 5)
    (c3402 : s 32 ≠ 2)
    (c3419 : s 32 ≠ 3)
    (c3400 : s 14 ≠ 2)
    (c3409 : s 14 ≠ 4)
    (c3421 : s 34 ≠ 3)
    (c3403 : s 34 ≠ 2)
    (c217 : s 19 ≠ 1 ∨ s 19 ≠ 4)
    (c216 : s 19 ≠ 1 ∨ s 19 ≠ 3)
    (c2990 : s 51 ≠ 4 ∨ s 19 = 3 ∨ s 19 = 4)
    (c211 : s 19 ≠ 0 ∨ s 19 ≠ 1)
    (c215 : s 19 ≠ 1 ∨ s 19 ≠ 2)
    (c2942 : s 50 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2)
    (c2312 : s 36 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2)
    (c1137 : s 10 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2)
    (c2944 : s 50 ≠ 3 ∨ s 19 = 0 ∨ s 19 = 4)
    (c1139 : s 10 ≠ 3 ∨ s 19 = 0 ∨ s 19 = 4)
    (c564 : s 51 ≠ 0 ∨ s 51 ≠ 2)
    (c1468 : s 17 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c1469 : s 17 ≠ 3 ∨ s 51 = 0 ∨ s 51 = 4)
    (c1513 : s 18 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c1768 : s 24 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c1268 : s 13 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c3456 : s 13 = 1 ∨ s 13 = 2 ∨ s 18 = 2 ∨ s 17 = 2 ∨ s 51 ≠ 2 ∨ s 19 ≠ 1)
    (c145 : s 13 ≠ 0 ∨ s 13 ≠ 1)
    (c1247 : s 13 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c2127 : s 32 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2)
    (c1457 : s 17 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2)
    (c3162 : s 55 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2)
    (c2111 : s 32 ≠ 0 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 10 = 3)
    (c1606 : s 21 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c1111 : s 10 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c1291 : s 14 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c2301 : s 36 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c1153 : s 10 ≠ 2 ∨ s 55 = 0 ∨ s 55 = 1)
    (c2913 : s 50 ≠ 2 ∨ s 10 = 0 ∨ s 10 = 1)
    (c3307 : s 58 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3309 : s 58 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4)
    (c3283 : s 58 ≠ 2 ∨ s 36 = 0 ∨ s 36 = 1)
    (c3136 : s 55 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3)
    (c1761 : s 24 ≠ 0 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 50 = 3)
    (c2326 : s 37 ≠ 0 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 58 = 3)
    (c2207 : s 34 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2)
    (c2362 : s 37 ≠ 1 ∨ s 24 = 0 ∨ s 24 = 2)
    (c1628 : s 21 ≠ 2 ∨ s 37 = 0 ∨ s 37 = 1)
    : s 51 ≠ 2 ∨ s 19 ≠ 1 ∨ s 51 = 1 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 32 ≠ 2 := c3402
  have u1 : s 32 ≠ 3 := c3419
  have u2 : s 14 ≠ 2 := c3400
  have u3 : s 14 ≠ 4 := c3409
  have u4 : s 34 ≠ 3 := c3421
  have u5 : s 34 ≠ 2 := c3403
  have u6 : s 19 ≠ 4 := (Or.elim c217 (fun h => (False.elim (h a1))) (fun h => h))
  have u7 : s 19 ≠ 3 := (Or.elim c216 (fun h => (False.elim (h a1))) (fun h => h))
  have u8 : s 51 ≠ 4 := (Or.elim c2990 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u6 h))))))
  have u9 : s 19 ≠ 0 := (Or.elim c211 (fun h => h) (fun h => (False.elim (h a1))))
  have u10 : s 19 ≠ 2 := (Or.elim c215 (fun h => (False.elim (h a1))) (fun h => h))
  have u11 : s 50 ≠ 1 := (Or.elim c2942 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u10 h))))))
  have u12 : s 36 ≠ 1 := (Or.elim c2312 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u10 h))))))
  have u13 : s 10 ≠ 1 := (Or.elim c1137 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u10 h))))))
  have u14 : s 50 ≠ 3 := (Or.elim c2944 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u6 h))))))
  have u15 : s 10 ≠ 3 := (Or.elim c1139 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u6 h))))))
  have u16 : s 51 ≠ 0 := (Or.elim c564 (fun h => h) (fun h => (False.elim (h a0))))
  have u17 : s 17 ≠ 2 := (Or.elim c1468 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (a2 h))))))
  have u18 : s 17 ≠ 3 := (Or.elim c1469 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (u8 h))))))
  have u19 : s 18 ≠ 2 := (Or.elim c1513 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (a2 h))))))
  have u20 : s 24 ≠ 2 := (Or.elim c1768 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (a2 h))))))
  have u21 : s 13 ≠ 2 := (Or.elim c1268 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (a2 h))))))
  have u22 : s 13 = 1 := (Or.elim c3456 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (False.elim (h a1))))))))))))
  have u23 : s 13 ≠ 0 := (Or.elim c145 (fun h => h) (fun h => (False.elim (h u22))))
  have u24 : s 32 = 0 := (Or.elim c1247 (fun h => (False.elim (h u22))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u0 h))))))
  have u25 : s 32 ≠ 1 := (Or.elim c2127 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (False.elim (u21 h))))))
  have u26 : s 17 ≠ 1 := (Or.elim c1457 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (False.elim (u21 h))))))
  have u27 : s 55 ≠ 1 := (Or.elim c3162 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (False.elim (u21 h))))))
  have u28 : s 10 = 2 := (Or.elim c2111 (fun h => (False.elim (h u24))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u15 h))))))))
  have u29 : s 21 ≠ 0 := (Or.elim c1606 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (u1 h))))))))
  have u30 : s 10 ≠ 0 := (Or.elim c1111 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (u1 h))))))))
  have u31 : s 14 ≠ 0 := (Or.elim c1291 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (Or.elim h (fun h => (False.elim (u0 h))) (fun h => (False.elim (u1 h))))))))
  have u32 : s 36 ≠ 0 := (Or.elim c2301 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u18 h))))))))
  have u33 : s 55 = 0 := (Or.elim c1153 (fun h => (False.elim (h u28))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u27 h))))))
  have u34 : s 50 ≠ 2 := (Or.elim c2913 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => (False.elim (u13 h))))))
  have u35 : s 58 ≠ 1 := (Or.elim c3307 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u2 h))))))
  have u36 : s 58 ≠ 3 := (Or.elim c3309 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (False.elim (u3 h))))))
  have u37 : s 58 ≠ 2 := (Or.elim c3283 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u32 h))) (fun h => (False.elim (u12 h))))))
  have u38 : s 34 = 1 := (Or.elim c3136 (fun h => (False.elim (h u33))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u4 h))))))))
  have u39 : s 24 ≠ 0 := (Or.elim c1761 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (u14 h))))))))
  have u40 : s 37 ≠ 0 := (Or.elim c2326 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => (False.elim (u36 h))))))))
  have u41 : s 21 = 2 := (Or.elim c2207 (fun h => (False.elim (h u38))) (fun h => (Or.elim h (fun h => (False.elim (u29 h))) (fun h => h))))
  have u42 : s 37 ≠ 1 := (Or.elim c2362 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (False.elim (u20 h))))))
  exact (Or.elim c1628 (fun h => (h u41)) (fun h => (Or.elim h (fun h => (u40 h)) (fun h => (u42 h)))))

private theorem step3458 (s : Fin 60 → Fin 5)
    (c3432 : s 17 ≠ 4)
    (c3402 : s 32 ≠ 2)
    (c1259 : s 13 ≠ 3 ∨ s 17 = 0 ∨ s 17 = 4)
    (c2961 : s 51 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3)
    (c1457 : s 17 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2)
    (c1247 : s 13 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1128 : s 10 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1)
    (c2111 : s 32 ≠ 0 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 10 = 3)
    : s 13 = 2 ∨ s 13 = 0 ∨ s 51 ≠ 0 ∨ s 17 = 0 ∨ s 10 = 1 ∨ s 10 = 3 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2,a3,a4,a5⟩ := hc
  have u0 : s 17 ≠ 4 := c3432
  have u1 : s 32 ≠ 2 := c3402
  have u2 : s 13 ≠ 3 := (Or.elim c1259 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (u0 h))))))
  have u3 : s 13 = 1 := (Or.elim c2961 (fun h => (False.elim (h a2))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u2 h))))))))
  have u4 : s 17 ≠ 1 := (Or.elim c1457 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (a0 h))))))
  have u5 : s 32 = 0 := (Or.elim c1247 (fun h => (False.elim (h u3))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u1 h))))))
  have u6 : s 10 ≠ 2 := (Or.elim c1128 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a3 h))) (fun h => (False.elim (u4 h))))))
  exact (Or.elim c2111 (fun h => (h u5)) (fun h => (Or.elim h (fun h => (a4 h)) (fun h => (Or.elim h (fun h => (u6 h)) (fun h => (a5 h)))))))

private theorem step3459 (s : Fin 60 → Fin 5)
    (c3411 : s 14 ≠ 3)
    (c3400 : s 14 ≠ 2)
    (c211 : s 19 ≠ 0 ∨ s 19 ≠ 1)
    (c215 : s 19 ≠ 1 ∨ s 19 ≠ 2)
    (c217 : s 19 ≠ 1 ∨ s 19 ≠ 4)
    (c2989 : s 51 ≠ 3 ∨ s 19 = 0 ∨ s 19 = 4)
    (c1139 : s 10 ≠ 3 ∨ s 19 = 0 ∨ s 19 = 4)
    (c1137 : s 10 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2)
    (c2942 : s 50 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2)
    (c3457 : s 51 ≠ 2 ∨ s 19 ≠ 1 ∨ s 51 = 1)
    (c1466 : s 17 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3)
    (c1542 : s 19 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2)
    (c1266 : s 13 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3)
    (c3458 : s 13 = 2 ∨ s 13 = 0 ∨ s 51 ≠ 0 ∨ s 17 = 0 ∨ s 10 = 1 ∨ s 10 = 3)
    (c149 : s 13 ≠ 1 ∨ s 13 ≠ 2)
    (c1263 : s 13 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1)
    (c1458 : s 17 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1)
    (c2931 : s 50 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c1302 : s 14 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2)
    : s 19 ≠ 1 ∨ s 51 = 1 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 14 ≠ 3 := c3411
  have u1 : s 14 ≠ 2 := c3400
  have u2 : s 19 ≠ 0 := (Or.elim c211 (fun h => h) (fun h => (False.elim (h a0))))
  have u3 : s 19 ≠ 2 := (Or.elim c215 (fun h => (False.elim (h a0))) (fun h => h))
  have u4 : s 19 ≠ 4 := (Or.elim c217 (fun h => (False.elim (h a0))) (fun h => h))
  have u5 : s 51 ≠ 3 := (Or.elim c2989 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u4 h))))))
  have u6 : s 10 ≠ 3 := (Or.elim c1139 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u4 h))))))
  have u7 : s 10 ≠ 1 := (Or.elim c1137 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u3 h))))))
  have u8 : s 50 ≠ 1 := (Or.elim c2942 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u3 h))))))
  have u9 : s 51 ≠ 2 := (Or.elim c3457 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (False.elim (a1 h))))))
  have u10 : s 17 ≠ 0 := (Or.elim c1466 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u5 h))))))))
  have u11 : s 51 = 0 := (Or.elim c1542 (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u9 h))))))
  have u12 : s 13 ≠ 0 := (Or.elim c1266 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u5 h))))))))
  have u13 : s 13 = 2 := (Or.elim c3458 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (Or.elim h (fun h => (False.elim (h u11))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u6 h))))))))))))
  have u14 : s 13 ≠ 1 := (Or.elim c149 (fun h => h) (fun h => (False.elim (h u13))))
  have u15 : s 50 = 0 := (Or.elim c1263 (fun h => (False.elim (h u13))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u8 h))))))
  have u16 : s 17 ≠ 2 := (Or.elim c1458 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u14 h))))))
  have u17 : s 14 = 1 := (Or.elim c2931 (fun h => (False.elim (h u15))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u0 h))))))))
  exact (Or.elim c1302 (fun h => (h u17)) (fun h => (Or.elim h (fun h => (u10 h)) (fun h => (u16 h)))))

private theorem step3460 (s : Fin 60 → Fin 5)
    (c3440 : s 13 ≠ 4)
    (c3432 : s 17 ≠ 4)
    (c3411 : s 14 ≠ 3)
    (c3400 : s 14 ≠ 2)
    (c3398 : s 31 ≠ 2)
    (c3423 : s 44 ≠ 3)
    (c3404 : s 44 ≠ 2)
    (c3459 : s 19 ≠ 1 ∨ s 51 = 1)
    (c146 : s 13 ≠ 0 ∨ s 13 ≠ 2)
    (c149 : s 13 ≠ 1 ∨ s 13 ≠ 2)
    (c1268 : s 13 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c2964 : s 51 ≠ 3 ∨ s 13 = 0 ∨ s 13 = 4)
    (c1459 : s 17 ≠ 3 ∨ s 13 = 0 ∨ s 13 = 4)
    (c2929 : s 50 ≠ 3 ∨ s 13 = 0 ∨ s 13 = 4)
    (c1458 : s 17 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1)
    (c2928 : s 50 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1)
    (c3163 : s 55 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1)
    (c1466 : s 17 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3)
    (c2611 : s 43 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3)
    (c1541 : s 19 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3)
    (c912 : s 5 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2)
    (c2976 : s 51 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c1302 : s 14 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2)
    (c914 : s 5 ≠ 3 ∨ s 17 = 0 ∨ s 17 = 4)
    (c923 : s 5 ≠ 2 ∨ s 19 = 0 ∨ s 19 = 1)
    (c1462 : s 17 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3166 : s 55 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2061 : s 31 ≠ 0 ∨ s 5 = 1 ∨ s 5 = 2 ∨ s 5 = 3)
    (c1306 : s 14 ≠ 0 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 50 = 3)
    (c2662 : s 44 ≠ 1 ∨ s 55 = 0 ∨ s 55 = 2)
    (c1062 : s 8 ≠ 1 ∨ s 31 = 0 ∨ s 31 = 2)
    (c2937 : s 50 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2)
    (c1046 : s 8 ≠ 0 ∨ s 44 = 1 ∨ s 44 = 2 ∨ s 44 = 3)
    (c2598 : s 43 ≠ 2 ∨ s 8 = 0 ∨ s 8 = 1)
    : s 13 ≠ 2 ∨ s 51 = 2 ∨ s 51 = 1 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 13 ≠ 4 := c3440
  have u1 : s 17 ≠ 4 := c3432
  have u2 : s 14 ≠ 3 := c3411
  have u3 : s 14 ≠ 2 := c3400
  have u4 : s 31 ≠ 2 := c3398
  have u5 : s 44 ≠ 3 := c3423
  have u6 : s 44 ≠ 2 := c3404
  have u7 : s 19 ≠ 1 := (Or.elim c3459 (fun h => h) (fun h => (False.elim (a2 h))))
  have u8 : s 13 ≠ 0 := (Or.elim c146 (fun h => h) (fun h => (False.elim (h a0))))
  have u9 : s 13 ≠ 1 := (Or.elim c149 (fun h => h) (fun h => (False.elim (h a0))))
  have u10 : s 51 = 0 := (Or.elim c1268 (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (a2 h))))))
  have u11 : s 51 ≠ 3 := (Or.elim c2964 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u0 h))))))
  have u12 : s 17 ≠ 3 := (Or.elim c1459 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u0 h))))))
  have u13 : s 50 ≠ 3 := (Or.elim c2929 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u0 h))))))
  have u14 : s 17 ≠ 2 := (Or.elim c1458 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u9 h))))))
  have u15 : s 50 ≠ 2 := (Or.elim c2928 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u9 h))))))
  have u16 : s 55 ≠ 2 := (Or.elim c3163 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u9 h))))))
  have u17 : s 17 ≠ 0 := (Or.elim c1466 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u11 h))))))))
  have u18 : s 43 ≠ 0 := (Or.elim c2611 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u11 h))))))))
  have u19 : s 19 ≠ 0 := (Or.elim c1541 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u11 h))))))))
  have u20 : s 5 ≠ 1 := (Or.elim c912 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u14 h))))))
  have u21 : s 17 = 1 := (Or.elim c2976 (fun h => (False.elim (h u10))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u14 h))) (fun h => (False.elim (u12 h))))))))
  have u22 : s 14 ≠ 1 := (Or.elim c1302 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u14 h))))))
  have u23 : s 5 ≠ 3 := (Or.elim c914 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u1 h))))))
  have u24 : s 5 ≠ 2 := (Or.elim c923 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u7 h))))))
  have u25 : s 14 = 0 := (Or.elim c1462 (fun h => (False.elim (h u21))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u3 h))))))
  have u26 : s 55 ≠ 0 := (Or.elim c3166 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (False.elim (u2 h))))))))
  have u27 : s 31 ≠ 0 := (Or.elim c2061 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (False.elim (u23 h))))))))
  have u28 : s 50 = 1 := (Or.elim c1306 (fun h => (False.elim (h u25))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u13 h))))))))
  have u29 : s 44 ≠ 1 := (Or.elim c2662 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (False.elim (u16 h))))))
  have u30 : s 8 ≠ 1 := (Or.elim c1062 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (False.elim (u4 h))))))
  have u31 : s 43 = 2 := (Or.elim c2937 (fun h => (False.elim (h u28))) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => h))))
  have u32 : s 8 ≠ 0 := (Or.elim c1046 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u29 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u5 h))))))))
  exact (Or.elim c2598 (fun h => (h u31)) (fun h => (Or.elim h (fun h => (u32 h)) (fun h => (u30 h)))))

private theorem step3461 (s : Fin 60 → Fin 5)
    (c3432 : s 17 ≠ 4)
    (c3402 : s 32 ≠ 2)
    (c3419 : s 32 ≠ 3)
    (c3404 : s 44 ≠ 2)
    (c3460 : s 13 ≠ 2 ∨ s 51 = 2 ∨ s 51 = 1)
    (c3459 : s 19 ≠ 1 ∨ s 51 = 1)
    (c565 : s 51 ≠ 0 ∨ s 51 ≠ 3)
    (c566 : s 51 ≠ 0 ∨ s 51 ≠ 4)
    (c2615 : s 43 ≠ 4 ∨ s 51 = 3 ∨ s 51 = 4)
    (c1466 : s 17 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3)
    (c2611 : s 43 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3)
    (c1266 : s 13 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3)
    (c1421 : s 16 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3)
    (c1541 : s 19 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3)
    (c1129 : s 10 ≠ 3 ∨ s 17 = 0 ∨ s 17 = 4)
    (c3109 : s 54 ≠ 3 ∨ s 43 = 0 ∨ s 43 = 4)
    (c3004 : s 52 ≠ 3 ∨ s 43 = 0 ∨ s 43 = 4)
    (c3117 : s 54 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2)
    (c3007 : s 52 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2)
    (c3458 : s 13 = 2 ∨ s 13 = 0 ∨ s 51 ≠ 0 ∨ s 17 = 0 ∨ s 10 = 1 ∨ s 10 = 3)
    (c2127 : s 32 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2)
    (c1122 : s 10 ≠ 1 ∨ s 16 = 0 ∨ s 16 = 2)
    (c3013 : s 52 ≠ 2 ∨ s 19 = 0 ∨ s 19 = 1)
    (c3123 : s 54 ≠ 2 ∨ s 19 = 0 ∨ s 19 = 1)
    (c2491 : s 40 ≠ 0 ∨ s 54 = 1 ∨ s 54 = 2 ∨ s 54 = 3)
    (c2656 : s 44 ≠ 0 ∨ s 54 = 1 ∨ s 54 = 2 ∨ s 54 = 3)
    (c1736 : s 23 ≠ 0 ∨ s 52 = 1 ∨ s 52 = 2 ∨ s 52 = 3)
    (c931 : s 6 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c1732 : s 23 ≠ 1 ∨ s 44 = 0 ∨ s 44 = 2)
    (c2498 : s 40 ≠ 2 ∨ s 23 = 0 ∨ s 23 = 1)
    (c1398 : s 16 ≠ 2 ∨ s 6 = 0 ∨ s 6 = 1)
    (c952 : s 6 ≠ 1 ∨ s 40 = 0 ∨ s 40 = 2)
    : s 51 ≠ 0 ∨ s 51 = 2 ∨ s 51 = 1 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 17 ≠ 4 := c3432
  have u1 : s 32 ≠ 2 := c3402
  have u2 : s 32 ≠ 3 := c3419
  have u3 : s 44 ≠ 2 := c3404
  have u4 : s 13 ≠ 2 := (Or.elim c3460 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (a2 h))))))
  have u5 : s 19 ≠ 1 := (Or.elim c3459 (fun h => h) (fun h => (False.elim (a2 h))))
  have u6 : s 51 ≠ 3 := (Or.elim c565 (fun h => (False.elim (h a0))) (fun h => h))
  have u7 : s 51 ≠ 4 := (Or.elim c566 (fun h => (False.elim (h a0))) (fun h => h))
  have u8 : s 43 ≠ 4 := (Or.elim c2615 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u7 h))))))
  have u9 : s 17 ≠ 0 := (Or.elim c1466 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u6 h))))))))
  have u10 : s 43 ≠ 0 := (Or.elim c2611 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u6 h))))))))
  have u11 : s 13 ≠ 0 := (Or.elim c1266 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u6 h))))))))
  have u12 : s 16 ≠ 0 := (Or.elim c1421 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u6 h))))))))
  have u13 : s 19 ≠ 0 := (Or.elim c1541 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (u6 h))))))))
  have u14 : s 10 ≠ 3 := (Or.elim c1129 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u0 h))))))
  have u15 : s 54 ≠ 3 := (Or.elim c3109 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u8 h))))))
  have u16 : s 52 ≠ 3 := (Or.elim c3004 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (False.elim (u8 h))))))
  have u17 : s 54 ≠ 1 := (Or.elim c3117 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u4 h))))))
  have u18 : s 52 ≠ 1 := (Or.elim c3007 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u4 h))))))
  have u19 : s 10 = 1 := (Or.elim c3458 (fun h => (False.elim (u4 h))) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u14 h))))))))))))
  have u20 : s 32 ≠ 1 := (Or.elim c2127 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (False.elim (u4 h))))))
  have u21 : s 16 = 2 := (Or.elim c1122 (fun h => (False.elim (h u19))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => h))))
  have u22 : s 52 ≠ 2 := (Or.elim c3013 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u5 h))))))
  have u23 : s 54 ≠ 2 := (Or.elim c3123 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u5 h))))))
  have u24 : s 40 ≠ 0 := (Or.elim c2491 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (False.elim (u15 h))))))))
  have u25 : s 44 ≠ 0 := (Or.elim c2656 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (False.elim (u15 h))))))))
  have u26 : s 23 ≠ 0 := (Or.elim c1736 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u16 h))))))))
  have u27 : s 6 ≠ 0 := (Or.elim c931 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))))
  have u28 : s 23 ≠ 1 := (Or.elim c1732 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u3 h))))))
  have u29 : s 40 ≠ 2 := (Or.elim c2498 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (False.elim (u28 h))))))
  have u30 : s 6 = 1 := (Or.elim c1398 (fun h => (False.elim (h u21))) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => h))))
  exact (Or.elim c952 (fun h => (h u30)) (fun h => (Or.elim h (fun h => (u24 h)) (fun h => (u29 h)))))

private theorem step3462 (s : Fin 60 → Fin 5)
    (c3440 : s 13 ≠ 4)
    (c3432 : s 17 ≠ 4)
    (c3461 : s 51 ≠ 0 ∨ s 51 = 2 ∨ s 51 = 1)
    (c2964 : s 51 ≠ 3 ∨ s 13 = 0 ∨ s 13 = 4)
    (c1459 : s 17 ≠ 3 ∨ s 13 = 0 ∨ s 13 = 4)
    (c562 : s 51 = 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3 ∨ s 51 = 4)
    (c2980 : s 51 ≠ 4 ∨ s 17 = 3 ∨ s 17 = 4)
    : s 13 = 0 ∨ s 51 = 2 ∨ s 51 = 1 := by
  by_contra hc
  try simp only [not_or] at hc
  obtain ⟨a0,a1,a2⟩ := hc
  have u0 : s 13 ≠ 4 := c3440
  have u1 : s 17 ≠ 4 := c3432
  have u2 : s 51 ≠ 0 := (Or.elim c3461 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (False.elim (a2 h))))))
  have u3 : s 51 ≠ 3 := (Or.elim c2964 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u0 h))))))
  have u4 : s 17 ≠ 3 := (Or.elim c1459 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (u0 h))))))
  have u5 : s 51 = 4 := (Or.elim c562 (fun h => (False.elim (u2 h))) (fun h => (Or.elim h (fun h => (False.elim (a2 h))) (fun h => (Or.elim h (fun h => (False.elim (a1 h))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => h))))))))
  exact (Or.elim c2980 (fun h => (h u5)) (fun h => (Or.elim h (fun h => (u4 h)) (fun h => (u1 h)))))

private theorem step3463 (s : Fin 60 → Fin 5)
    (c3440 : s 13 ≠ 4)
    (c3461 : s 51 ≠ 0 ∨ s 51 = 2 ∨ s 51 = 1)
    (c1468 : s 17 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c1467 : s 17 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2)
    (c3462 : s 13 = 0 ∨ s 51 = 2 ∨ s 51 = 1)
    (c147 : s 13 ≠ 0 ∨ s 13 ≠ 3)
    (c1256 : s 13 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c2965 : s 51 ≠ 4 ∨ s 13 = 3 ∨ s 13 = 4)
    (c1469 : s 17 ≠ 3 ∨ s 51 = 0 ∨ s 51 = 4)
    : s 51 = 2 ∨ s 51 = 1 := by
  by_contra hc
  try simp only [not_or] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 13 ≠ 4 := c3440
  have u1 : s 51 ≠ 0 := (Or.elim c3461 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))
  have u2 : s 17 ≠ 2 := (Or.elim c1468 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a1 h))))))
  have u3 : s 17 ≠ 1 := (Or.elim c1467 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (a0 h))))))
  have u4 : s 13 = 0 := (Or.elim c3462 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (a0 h))) (fun h => (False.elim (a1 h))))))
  have u5 : s 13 ≠ 3 := (Or.elim c147 (fun h => (False.elim (h u4))) (fun h => h))
  have u6 : s 17 = 3 := (Or.elim c1256 (fun h => (False.elim (h u4))) (fun h => (Or.elim h (fun h => (False.elim (u3 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => h))))))
  have u7 : s 51 ≠ 4 := (Or.elim c2965 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u0 h))))))
  exact (Or.elim c1469 (fun h => (h u6)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u7 h)))))

private theorem step3464 (s : Fin 60 → Fin 5)
    (c3402 : s 32 ≠ 2)
    (c3411 : s 14 ≠ 3)
    (c3400 : s 14 ≠ 2)
    (c3403 : s 34 ≠ 2)
    (c3463 : s 51 = 2 ∨ s 51 = 1)
    (c570 : s 51 ≠ 2 ∨ s 51 ≠ 3)
    (c571 : s 51 ≠ 2 ∨ s 51 ≠ 4)
    (c1545 : s 19 ≠ 4 ∨ s 51 = 3 ∨ s 51 = 4)
    (c564 : s 51 ≠ 0 ∨ s 51 ≠ 2)
    (c1544 : s 19 ≠ 3 ∨ s 51 = 0 ∨ s 51 = 4)
    (c3015 : s 52 ≠ 4 ∨ s 19 = 3 ∨ s 19 = 4)
    (c3459 : s 19 ≠ 1 ∨ s 51 = 1)
    (c1543 : s 19 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c3011 : s 52 ≠ 0 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 19 = 3)
    (c1639 : s 21 ≠ 3 ∨ s 52 = 0 ∨ s 52 = 4)
    (c2311 : s 36 ≠ 0 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 19 = 3)
    (c2941 : s 50 ≠ 0 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 19 = 3)
    (c1136 : s 10 ≠ 0 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 19 = 3)
    (c1469 : s 17 ≠ 3 ∨ s 51 = 0 ∨ s 51 = 4)
    (c1769 : s 24 ≠ 3 ∨ s 51 = 0 ∨ s 51 = 4)
    (c1269 : s 13 ≠ 3 ∨ s 51 = 0 ∨ s 51 = 4)
    (c1268 : s 13 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c1768 : s 24 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c1468 : s 17 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c145 : s 13 ≠ 0 ∨ s 13 ≠ 1)
    (c1256 : s 13 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c2126 : s 32 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3)
    (c1456 : s 17 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3)
    (c3161 : s 55 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3)
    (c1442 : s 17 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2)
    (c1112 : s 10 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1607 : s 21 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c1292 : s 14 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    (c2302 : s 36 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2)
    (c1153 : s 10 ≠ 2 ∨ s 55 = 0 ∨ s 55 = 1)
    (c2913 : s 50 ≠ 2 ∨ s 10 = 0 ∨ s 10 = 1)
    (c3306 : s 58 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c3283 : s 58 ≠ 2 ∨ s 36 = 0 ∨ s 36 = 1)
    (c3137 : s 55 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c1762 : s 24 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2)
    (c2327 : s 37 ≠ 1 ∨ s 58 = 0 ∨ s 58 = 2)
    (c2206 : s 34 ≠ 0 ∨ s 21 = 1 ∨ s 21 = 2 ∨ s 21 = 3)
    (c2361 : s 37 ≠ 0 ∨ s 24 = 1 ∨ s 24 = 2 ∨ s 24 = 3)
    (c1628 : s 21 ≠ 2 ∨ s 37 = 0 ∨ s 37 = 1)
    : s 13 ≠ 0 ∨ s 51 = 1 := by
  by_contra hc
  try simp only [not_or,not_not] at hc
  obtain ⟨a0,a1⟩ := hc
  have u0 : s 32 ≠ 2 := c3402
  have u1 : s 14 ≠ 3 := c3411
  have u2 : s 14 ≠ 2 := c3400
  have u3 : s 34 ≠ 2 := c3403
  have u4 : s 51 = 2 := (Or.elim c3463 (fun h => h) (fun h => (False.elim (a1 h))))
  have u5 : s 51 ≠ 3 := (Or.elim c570 (fun h => (False.elim (h u4))) (fun h => h))
  have u6 : s 51 ≠ 4 := (Or.elim c571 (fun h => (False.elim (h u4))) (fun h => h))
  have u7 : s 19 ≠ 4 := (Or.elim c1545 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (False.elim (u6 h))))))
  have u8 : s 51 ≠ 0 := (Or.elim c564 (fun h => h) (fun h => (False.elim (h u4))))
  have u9 : s 19 ≠ 3 := (Or.elim c1544 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u6 h))))))
  have u10 : s 52 ≠ 4 := (Or.elim c3015 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u7 h))))))
  have u11 : s 19 ≠ 1 := (Or.elim c3459 (fun h => h) (fun h => (False.elim (a1 h))))
  have u12 : s 19 ≠ 2 := (Or.elim c1543 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (a1 h))))))
  have u13 : s 52 ≠ 0 := (Or.elim c3011 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u9 h))))))))
  have u14 : s 21 ≠ 3 := (Or.elim c1639 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u10 h))))))
  have u15 : s 36 ≠ 0 := (Or.elim c2311 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u9 h))))))))
  have u16 : s 50 ≠ 0 := (Or.elim c2941 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u9 h))))))))
  have u17 : s 10 ≠ 0 := (Or.elim c1136 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u11 h))) (fun h => (Or.elim h (fun h => (False.elim (u12 h))) (fun h => (False.elim (u9 h))))))))
  have u18 : s 17 ≠ 3 := (Or.elim c1469 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u6 h))))))
  have u19 : s 24 ≠ 3 := (Or.elim c1769 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u6 h))))))
  have u20 : s 13 ≠ 3 := (Or.elim c1269 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u6 h))))))
  have u21 : s 13 ≠ 2 := (Or.elim c1268 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (a1 h))))))
  have u22 : s 24 ≠ 2 := (Or.elim c1768 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (a1 h))))))
  have u23 : s 17 ≠ 2 := (Or.elim c1468 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (a1 h))))))
  have u24 : s 13 ≠ 1 := (Or.elim c145 (fun h => (False.elim (h a0))) (fun h => h))
  have u25 : s 17 = 1 := (Or.elim c1256 (fun h => (False.elim (h a0))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (False.elim (u18 h))))))))
  have u26 : s 32 ≠ 0 := (Or.elim c2126 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u20 h))))))))
  have u27 : s 17 ≠ 0 := (Or.elim c1456 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u20 h))))))))
  have u28 : s 55 ≠ 0 := (Or.elim c3161 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u24 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u20 h))))))))
  have u29 : s 10 = 2 := (Or.elim c1442 (fun h => (False.elim (h u25))) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => h))))
  have u30 : s 10 ≠ 1 := (Or.elim c1112 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (False.elim (u0 h))))))
  have u31 : s 21 ≠ 1 := (Or.elim c1607 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (False.elim (u0 h))))))
  have u32 : s 14 ≠ 1 := (Or.elim c1292 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => (False.elim (u0 h))))))
  have u33 : s 36 ≠ 1 := (Or.elim c2302 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (False.elim (u23 h))))))
  have u34 : s 55 = 1 := (Or.elim c1153 (fun h => (False.elim (h u29))) (fun h => (Or.elim h (fun h => (False.elim (u28 h))) (fun h => h))))
  have u35 : s 50 ≠ 2 := (Or.elim c2913 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u30 h))))))
  have u36 : s 58 ≠ 0 := (Or.elim c3306 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u32 h))) (fun h => (Or.elim h (fun h => (False.elim (u2 h))) (fun h => (False.elim (u1 h))))))))
  have u37 : s 58 ≠ 2 := (Or.elim c3283 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u33 h))))))
  have u38 : s 34 = 0 := (Or.elim c3137 (fun h => (False.elim (h u34))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u3 h))))))
  have u39 : s 24 ≠ 1 := (Or.elim c1762 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (u35 h))))))
  have u40 : s 37 ≠ 1 := (Or.elim c2327 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u37 h))))))
  have u41 : s 21 = 2 := (Or.elim c2206 (fun h => (False.elim (h u38))) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u14 h))))))))
  have u42 : s 37 ≠ 0 := (Or.elim c2361 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u39 h))) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u19 h))))))))
  exact (Or.elim c1628 (fun h => (h u41)) (fun h => (Or.elim h (fun h => (u42 h)) (fun h => (u40 h)))))

private theorem step3465 (s : Fin 60 → Fin 5)
    (c3438 : s 10 ≠ 4)
    (c3402 : s 32 ≠ 2)
    (c3419 : s 32 ≠ 3)
    (c3431 : s 21 ≠ 4)
    (c3400 : s 14 ≠ 2)
    (c3421 : s 34 ≠ 3)
    (c3403 : s 34 ≠ 2)
    (c3459 : s 19 ≠ 1 ∨ s 51 = 1)
    (c3463 : s 51 = 2 ∨ s 51 = 1)
    (c564 : s 51 ≠ 0 ∨ s 51 ≠ 2)
    (c571 : s 51 ≠ 2 ∨ s 51 ≠ 4)
    (c2988 : s 51 ≠ 2 ∨ s 19 = 0 ∨ s 19 = 1)
    (c1513 : s 18 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c1543 : s 19 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c1268 : s 13 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1)
    (c1544 : s 19 ≠ 3 ∨ s 51 = 0 ∨ s 51 = 4)
    (c1136 : s 10 ≠ 0 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 19 = 3)
    (c2941 : s 50 ≠ 0 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 19 = 3)
    (c3011 : s 52 ≠ 0 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 19 = 3)
    (c2914 : s 50 ≠ 3 ∨ s 10 = 0 ∨ s 10 = 4)
    (c3464 : s 13 ≠ 0 ∨ s 51 = 1)
    (c2927 : s 50 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2)
    (c3007 : s 52 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2)
    (c2127 : s 32 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2)
    (c1536 : s 19 ≠ 0 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 50 = 3)
    (c1183 : s 11 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1)
    (c1638 : s 21 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1)
    (c1606 : s 21 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c1156 : s 11 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c1291 : s 14 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c2913 : s 50 ≠ 2 ∨ s 10 = 0 ∨ s 10 = 1)
    (c2202 : s 34 ≠ 1 ∨ s 11 = 0 ∨ s 11 = 2)
    (c2347 : s 37 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2)
    (c2349 : s 37 ≠ 3 ∨ s 21 = 0 ∨ s 21 = 4)
    (c3307 : s 58 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c1132 : s 10 ≠ 1 ∨ s 18 = 0 ∨ s 18 = 2)
    (c3271 : s 58 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3)
    (c1491 : s 18 ≠ 0 ∨ s 37 = 1 ∨ s 37 = 2 ∨ s 37 = 3)
    (c2328 : s 37 ≠ 2 ∨ s 58 = 0 ∨ s 58 = 1)
    : s 51 = 1 := by
  by_contra hc
  have u0 : s 10 ≠ 4 := c3438
  have u1 : s 32 ≠ 2 := c3402
  have u2 : s 32 ≠ 3 := c3419
  have u3 : s 21 ≠ 4 := c3431
  have u4 : s 14 ≠ 2 := c3400
  have u5 : s 34 ≠ 3 := c3421
  have u6 : s 34 ≠ 2 := c3403
  have u7 : s 19 ≠ 1 := (Or.elim c3459 (fun h => h) (fun h => (False.elim (hc h))))
  have u8 : s 51 = 2 := (Or.elim c3463 (fun h => h) (fun h => (False.elim (hc h))))
  have u9 : s 51 ≠ 0 := (Or.elim c564 (fun h => h) (fun h => (False.elim (h u8))))
  have u10 : s 51 ≠ 4 := (Or.elim c571 (fun h => (False.elim (h u8))) (fun h => h))
  have u11 : s 19 = 0 := (Or.elim c2988 (fun h => (False.elim (h u8))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u7 h))))))
  have u12 : s 18 ≠ 2 := (Or.elim c1513 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (hc h))))))
  have u13 : s 19 ≠ 2 := (Or.elim c1543 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (hc h))))))
  have u14 : s 13 ≠ 2 := (Or.elim c1268 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (hc h))))))
  have u15 : s 19 ≠ 3 := (Or.elim c1544 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u9 h))) (fun h => (False.elim (u10 h))))))
  have u16 : s 10 ≠ 0 := (Or.elim c1136 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u15 h))))))))
  have u17 : s 50 ≠ 0 := (Or.elim c2941 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u15 h))))))))
  have u18 : s 52 ≠ 0 := (Or.elim c3011 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (Or.elim h (fun h => (False.elim (u13 h))) (fun h => (False.elim (u15 h))))))))
  have u19 : s 50 ≠ 3 := (Or.elim c2914 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => (False.elim (u0 h))))))
  have u20 : s 13 ≠ 0 := (Or.elim c3464 (fun h => h) (fun h => (False.elim (hc h))))
  have u21 : s 50 ≠ 1 := (Or.elim c2927 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u14 h))))))
  have u22 : s 52 ≠ 1 := (Or.elim c3007 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u14 h))))))
  have u23 : s 32 ≠ 1 := (Or.elim c2127 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u14 h))))))
  have u24 : s 50 = 2 := (Or.elim c1536 (fun h => (False.elim (h u11))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u19 h))))))))
  have u25 : s 11 ≠ 2 := (Or.elim c1183 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u17 h))) (fun h => (False.elim (u21 h))))))
  have u26 : s 21 ≠ 2 := (Or.elim c1638 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u18 h))) (fun h => (False.elim (u22 h))))))
  have u27 : s 21 ≠ 0 := (Or.elim c1606 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))))
  have u28 : s 11 ≠ 0 := (Or.elim c1156 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))))
  have u29 : s 14 ≠ 0 := (Or.elim c1291 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u23 h))) (fun h => (Or.elim h (fun h => (False.elim (u1 h))) (fun h => (False.elim (u2 h))))))))
  have u30 : s 10 = 1 := (Or.elim c2913 (fun h => (False.elim (h u24))) (fun h => (Or.elim h (fun h => (False.elim (u16 h))) (fun h => h))))
  have u31 : s 34 ≠ 1 := (Or.elim c2202 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u28 h))) (fun h => (False.elim (u25 h))))))
  have u32 : s 37 ≠ 1 := (Or.elim c2347 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (False.elim (u26 h))))))
  have u33 : s 37 ≠ 3 := (Or.elim c2349 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u27 h))) (fun h => (False.elim (u3 h))))))
  have u34 : s 58 ≠ 1 := (Or.elim c3307 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u29 h))) (fun h => (False.elim (u4 h))))))
  have u35 : s 18 = 0 := (Or.elim c1132 (fun h => (False.elim (h u30))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u12 h))))))
  have u36 : s 58 ≠ 0 := (Or.elim c3271 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (Or.elim h (fun h => (False.elim (u6 h))) (fun h => (False.elim (u5 h))))))))
  have u37 : s 37 = 2 := (Or.elim c1491 (fun h => (False.elim (h u35))) (fun h => (Or.elim h (fun h => (False.elim (u32 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u33 h))))))))
  exact (Or.elim c2328 (fun h => (h u37)) (fun h => (Or.elim h (fun h => (u36 h)) (fun h => (u34 h)))))

private theorem step3466 (s : Fin 60 → Fin 5)
    (c3465 : s 51 = 1)
    (c563 : s 51 ≠ 0 ∨ s 51 ≠ 1)
    : s 51 ≠ 0 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 51 = 1 := c3465
  exact (Or.elim c563 (fun h => (h hc)) (fun h => (h u0)))

private theorem step3467 (s : Fin 60 → Fin 5)
    (c3465 : s 51 = 1)
    (c567 : s 51 ≠ 1 ∨ s 51 ≠ 2)
    : s 51 ≠ 2 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 51 = 1 := c3465
  exact (Or.elim c567 (fun h => (h u0)) (fun h => (h hc)))

private theorem step3468 (s : Fin 60 → Fin 5)
    (c3465 : s 51 = 1)
    (c568 : s 51 ≠ 1 ∨ s 51 ≠ 3)
    : s 51 ≠ 3 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 51 = 1 := c3465
  exact (Or.elim c568 (fun h => (h u0)) (fun h => (h hc)))

private theorem step3469 (s : Fin 60 → Fin 5)
    (c3465 : s 51 = 1)
    (c569 : s 51 ≠ 1 ∨ s 51 ≠ 4)
    : s 51 ≠ 4 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 51 = 1 := c3465
  exact (Or.elim c569 (fun h => (h u0)) (fun h => (h hc)))

private theorem step3470 (s : Fin 60 → Fin 5)
    (c3466 : s 51 ≠ 0)
    (c3467 : s 51 ≠ 2)
    (c1467 : s 17 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2)
    : s 17 ≠ 1 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 51 ≠ 0 := c3466
  have u1 : s 51 ≠ 2 := c3467
  exact (Or.elim c1467 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3473 (s : Fin 60 → Fin 5)
    (c3466 : s 51 ≠ 0)
    (c3467 : s 51 ≠ 2)
    (c1422 : s 16 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2)
    : s 16 ≠ 1 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 51 ≠ 0 := c3466
  have u1 : s 51 ≠ 2 := c3467
  exact (Or.elim c1422 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3474 (s : Fin 60 → Fin 5)
    (c3466 : s 51 ≠ 0)
    (c3467 : s 51 ≠ 2)
    (c2612 : s 43 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2)
    : s 43 ≠ 1 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 51 ≠ 0 := c3466
  have u1 : s 51 ≠ 2 := c3467
  exact (Or.elim c2612 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3475 (s : Fin 60 → Fin 5)
    (c3466 : s 51 ≠ 0)
    (c3467 : s 51 ≠ 2)
    (c1267 : s 13 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2)
    : s 13 ≠ 1 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 51 ≠ 0 := c3466
  have u1 : s 51 ≠ 2 := c3467
  exact (Or.elim c1267 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3476 (s : Fin 60 → Fin 5)
    (c3466 : s 51 ≠ 0)
    (c3467 : s 51 ≠ 2)
    (c1942 : s 28 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2)
    : s 28 ≠ 1 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 51 ≠ 0 := c3466
  have u1 : s 51 ≠ 2 := c3467
  exact (Or.elim c1942 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3478 (s : Fin 60 → Fin 5)
    (c3467 : s 51 ≠ 2)
    (c3466 : s 51 ≠ 0)
    (c1542 : s 19 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2)
    : s 19 ≠ 1 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 51 ≠ 2 := c3467
  have u1 : s 51 ≠ 0 := c3466
  exact (Or.elim c1542 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u0 h)))))

private theorem step3480 (s : Fin 60 → Fin 5)
    (c3469 : s 51 ≠ 4)
    (c3468 : s 51 ≠ 3)
    (c1425 : s 16 ≠ 4 ∨ s 51 = 3 ∨ s 51 = 4)
    : s 16 ≠ 4 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 51 ≠ 4 := c3469
  have u1 : s 51 ≠ 3 := c3468
  exact (Or.elim c1425 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u0 h)))))

private theorem step3485 (s : Fin 60 → Fin 5)
    (c3469 : s 51 ≠ 4)
    (c3466 : s 51 ≠ 0)
    (c1544 : s 19 ≠ 3 ∨ s 51 = 0 ∨ s 51 = 4)
    : s 19 ≠ 3 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 51 ≠ 4 := c3469
  have u1 : s 51 ≠ 0 := c3466
  exact (Or.elim c1544 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u0 h)))))

private theorem step3488 (s : Fin 60 → Fin 5)
    (c3469 : s 51 ≠ 4)
    (c3466 : s 51 ≠ 0)
    (c1269 : s 13 ≠ 3 ∨ s 51 = 0 ∨ s 51 = 4)
    : s 13 ≠ 3 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 51 ≠ 4 := c3469
  have u1 : s 51 ≠ 0 := c3466
  exact (Or.elim c1269 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u0 h)))))

private theorem step3490 (s : Fin 60 → Fin 5)
    (c3469 : s 51 ≠ 4)
    (c3466 : s 51 ≠ 0)
    (c1469 : s 17 ≠ 3 ∨ s 51 = 0 ∨ s 51 = 4)
    : s 17 ≠ 3 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 51 ≠ 4 := c3469
  have u1 : s 51 ≠ 0 := c3466
  exact (Or.elim c1469 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u0 h)))))

private theorem step3498 (s : Fin 60 → Fin 5)
    (c3440 : s 13 ≠ 4)
    (c3465 : s 51 = 1)
    (c3475 : s 13 ≠ 1)
    (c3433 : s 47 ≠ 4)
    (c3490 : s 17 ≠ 3)
    (c3470 : s 17 ≠ 1)
    (c3411 : s 14 ≠ 3)
    (c3400 : s 14 ≠ 2)
    (c3402 : s 32 ≠ 2)
    (c3419 : s 32 ≠ 3)
    (c3478 : s 19 ≠ 1)
    (c3485 : s 19 ≠ 3)
    (c3476 : s 28 ≠ 1)
    (c3403 : s 34 ≠ 2)
    (c3401 : s 29 ≠ 2)
    (c2804 : s 47 ≠ 3 ∨ s 13 = 0 ∨ s 13 = 4)
    (c2929 : s 50 ≠ 3 ∨ s 13 = 0 ∨ s 13 = 4)
    (c3164 : s 55 ≠ 3 ∨ s 13 = 0 ∨ s 13 = 4)
    (c2962 : s 51 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2)
    (c2928 : s 50 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1)
    (c2803 : s 47 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1)
    (c3163 : s 55 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1)
    (c1458 : s 17 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1)
    (c1900 : s 27 ≠ 4 ∨ s 47 = 3 ∨ s 47 = 4)
    (c1258 : s 13 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1)
    (c1301 : s 14 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c1126 : s 10 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    (c1461 : s 17 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    (c2132 : s 32 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c2807 : s 47 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c2932 : s 50 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c3167 : s 55 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2)
    (c1307 : s 14 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2)
    (c796 : s 3 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3)
    (c1896 : s 27 ≠ 0 ∨ s 47 = 1 ∨ s 47 = 2 ∨ s 47 = 3)
    (c1936 : s 28 ≠ 0 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 50 = 3)
    (c2211 : s 34 ≠ 0 ∨ s 55 = 1 ∨ s 55 = 2 ∨ s 55 = 3)
    (c1986 : s 29 ≠ 0 ∨ s 55 = 1 ∨ s 55 = 2 ∨ s 55 = 3)
    (c2941 : s 50 ≠ 0 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 19 = 3)
    (c779 : s 2 ≠ 3 ∨ s 27 = 0 ∨ s 27 = 4)
    (c783 : s 2 ≠ 2 ∨ s 28 = 0 ∨ s 28 = 1)
    (c807 : s 3 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2)
    (c787 : s 2 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2)
    (c1533 : s 19 ≠ 2 ∨ s 10 = 0 ∨ s 10 = 1)
    (c1353 : s 15 ≠ 2 ∨ s 3 = 0 ∨ s 3 = 1)
    (c1346 : s 15 ≠ 0 ∨ s 2 = 1 ∨ s 2 = 2 ∨ s 2 = 3)
    (c1117 : s 10 ≠ 1 ∨ s 15 = 0 ∨ s 15 = 2)
    : s 13 = 0 := by
  by_contra hc
  have u0 : s 13 ≠ 4 := c3440
  have u1 : s 51 = 1 := c3465
  have u2 : s 13 ≠ 1 := c3475
  have u3 : s 47 ≠ 4 := c3433
  have u4 : s 17 ≠ 3 := c3490
  have u5 : s 17 ≠ 1 := c3470
  have u6 : s 14 ≠ 3 := c3411
  have u7 : s 14 ≠ 2 := c3400
  have u8 : s 32 ≠ 2 := c3402
  have u9 : s 32 ≠ 3 := c3419
  have u10 : s 19 ≠ 1 := c3478
  have u11 : s 19 ≠ 3 := c3485
  have u12 : s 28 ≠ 1 := c3476
  have u13 : s 34 ≠ 2 := c3403
  have u14 : s 29 ≠ 2 := c3401
  have u15 : s 47 ≠ 3 := (Or.elim c2804 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (hc h))) (fun h => (False.elim (u0 h))))))
  have u16 : s 50 ≠ 3 := (Or.elim c2929 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (hc h))) (fun h => (False.elim (u0 h))))))
  have u17 : s 55 ≠ 3 := (Or.elim c3164 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (hc h))) (fun h => (False.elim (u0 h))))))
  have u18 : s 13 = 2 := (Or.elim c2962 (fun h => (False.elim (h u1))) (fun h => (Or.elim h (fun h => (False.elim (hc h))) (fun h => h))))
  have u19 : s 50 ≠ 2 := (Or.elim c2928 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (hc h))) (fun h => (False.elim (u2 h))))))
  have u20 : s 47 ≠ 2 := (Or.elim c2803 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (hc h))) (fun h => (False.elim (u2 h))))))
  have u21 : s 55 ≠ 2 := (Or.elim c3163 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (hc h))) (fun h => (False.elim (u2 h))))))
  have u22 : s 17 ≠ 2 := (Or.elim c1458 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (hc h))) (fun h => (False.elim (u2 h))))))
  have u23 : s 27 ≠ 4 := (Or.elim c1900 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u15 h))) (fun h => (False.elim (u3 h))))))
  have u24 : s 17 = 0 := (Or.elim c1258 (fun h => (False.elim (h u18))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u5 h))))))
  have u25 : s 14 ≠ 0 := (Or.elim c1301 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u4 h))))))))
  have u26 : s 10 ≠ 0 := (Or.elim c1126 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u5 h))) (fun h => (Or.elim h (fun h => (False.elim (u22 h))) (fun h => (False.elim (u4 h))))))))
  have u27 : s 14 = 1 := (Or.elim c1461 (fun h => (False.elim (h u24))) (fun h => (Or.elim h (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u7 h))) (fun h => (False.elim (u6 h))))))))
  have u28 : s 32 ≠ 1 := (Or.elim c2132 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u7 h))))))
  have u29 : s 47 ≠ 1 := (Or.elim c2807 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u7 h))))))
  have u30 : s 50 ≠ 1 := (Or.elim c2932 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u7 h))))))
  have u31 : s 55 ≠ 1 := (Or.elim c3167 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u25 h))) (fun h => (False.elim (u7 h))))))
  have u32 : s 50 = 0 := (Or.elim c1307 (fun h => (False.elim (h u27))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u19 h))))))
  have u33 : s 3 ≠ 0 := (Or.elim c796 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u28 h))) (fun h => (Or.elim h (fun h => (False.elim (u8 h))) (fun h => (False.elim (u9 h))))))))
  have u34 : s 27 ≠ 0 := (Or.elim c1896 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u29 h))) (fun h => (Or.elim h (fun h => (False.elim (u20 h))) (fun h => (False.elim (u15 h))))))))
  have u35 : s 28 ≠ 0 := (Or.elim c1936 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u30 h))) (fun h => (Or.elim h (fun h => (False.elim (u19 h))) (fun h => (False.elim (u16 h))))))))
  have u36 : s 34 ≠ 0 := (Or.elim c2211 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u17 h))))))))
  have u37 : s 29 ≠ 0 := (Or.elim c1986 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u31 h))) (fun h => (Or.elim h (fun h => (False.elim (u21 h))) (fun h => (False.elim (u17 h))))))))
  have u38 : s 19 = 2 := (Or.elim c2941 (fun h => (False.elim (h u32))) (fun h => (Or.elim h (fun h => (False.elim (u10 h))) (fun h => (Or.elim h (fun h => h) (fun h => (False.elim (u11 h))))))))
  have u39 : s 2 ≠ 3 := (Or.elim c779 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u34 h))) (fun h => (False.elim (u23 h))))))
  have u40 : s 2 ≠ 2 := (Or.elim c783 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u35 h))) (fun h => (False.elim (u12 h))))))
  have u41 : s 3 ≠ 1 := (Or.elim c807 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u36 h))) (fun h => (False.elim (u13 h))))))
  have u42 : s 2 ≠ 1 := (Or.elim c787 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u37 h))) (fun h => (False.elim (u14 h))))))
  have u43 : s 10 = 1 := (Or.elim c1533 (fun h => (False.elim (h u38))) (fun h => (Or.elim h (fun h => (False.elim (u26 h))) (fun h => h))))
  have u44 : s 15 ≠ 2 := (Or.elim c1353 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u33 h))) (fun h => (False.elim (u41 h))))))
  have u45 : s 15 ≠ 0 := (Or.elim c1346 (fun h => h) (fun h => (Or.elim h (fun h => (False.elim (u42 h))) (fun h => (Or.elim h (fun h => (False.elim (u40 h))) (fun h => (False.elim (u39 h))))))))
  exact (Or.elim c1117 (fun h => (h u43)) (fun h => (Or.elim h (fun h => (u45 h)) (fun h => (u44 h)))))

private theorem step3499 (s : Fin 60 → Fin 5)
    (c3498 : s 13 = 0)
    (c146 : s 13 ≠ 0 ∨ s 13 ≠ 2)
    : s 13 ≠ 2 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 13 = 0 := c3498
  exact (Or.elim c146 (fun h => (h u0)) (fun h => (h hc)))

private theorem step3500 (s : Fin 60 → Fin 5)
    (c3498 : s 13 = 0)
    (c3490 : s 17 ≠ 3)
    (c3470 : s 17 ≠ 1)
    (c1256 : s 13 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3)
    : s 17 = 2 := by
  by_contra hc
  have u0 : s 13 = 0 := c3498
  have u1 : s 17 ≠ 3 := c3490
  have u2 : s 17 ≠ 1 := c3470
  exact (Or.elim c1256 (fun h => (h u0)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (hc h)) (fun h => (u1 h)))))))

private theorem step3502 (s : Fin 60 → Fin 5)
    (c3499 : s 13 ≠ 2)
    (c3488 : s 13 ≠ 3)
    (c3475 : s 13 ≠ 1)
    (c2126 : s 32 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3)
    : s 32 ≠ 0 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 13 ≠ 2 := c3499
  have u1 : s 13 ≠ 3 := c3488
  have u2 : s 13 ≠ 1 := c3475
  exact (Or.elim c2126 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))))

private theorem step3503 (s : Fin 60 → Fin 5)
    (c3499 : s 13 ≠ 2)
    (c3475 : s 13 ≠ 1)
    (c3488 : s 13 ≠ 3)
    (c1456 : s 17 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3)
    : s 17 ≠ 0 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 13 ≠ 2 := c3499
  have u1 : s 13 ≠ 1 := c3475
  have u2 : s 13 ≠ 3 := c3488
  exact (Or.elim c1456 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u2 h)))))))

private theorem step3511 (s : Fin 60 → Fin 5)
    (c3502 : s 32 ≠ 0)
    (c3402 : s 32 ≠ 2)
    (c1112 : s 10 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    : s 10 ≠ 1 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 32 ≠ 0 := c3502
  have u1 : s 32 ≠ 2 := c3402
  exact (Or.elim c1112 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3516 (s : Fin 60 → Fin 5)
    (c3502 : s 32 ≠ 0)
    (c3402 : s 32 ≠ 2)
    (c1157 : s 11 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    : s 11 ≠ 1 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 32 ≠ 0 := c3502
  have u1 : s 32 ≠ 2 := c3402
  exact (Or.elim c1157 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3517 (s : Fin 60 → Fin 5)
    (c3502 : s 32 ≠ 0)
    (c3402 : s 32 ≠ 2)
    (c1292 : s 14 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2)
    : s 14 ≠ 1 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 32 ≠ 0 := c3502
  have u1 : s 32 ≠ 2 := c3402
  exact (Or.elim c1292 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3521 (s : Fin 60 → Fin 5)
    (c3502 : s 32 ≠ 0)
    (c3413 : s 32 ≠ 4)
    (c1114 : s 10 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4)
    : s 10 ≠ 3 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 32 ≠ 0 := c3502
  have u1 : s 32 ≠ 4 := c3413
  exact (Or.elim c1114 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3522 (s : Fin 60 → Fin 5)
    (c3502 : s 32 ≠ 0)
    (c3413 : s 32 ≠ 4)
    (c1159 : s 11 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4)
    : s 11 ≠ 3 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 32 ≠ 0 := c3502
  have u1 : s 32 ≠ 4 := c3413
  exact (Or.elim c1159 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3527 (s : Fin 60 → Fin 5)
    (c3503 : s 17 ≠ 0)
    (c3470 : s 17 ≠ 1)
    (c1128 : s 10 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1)
    : s 10 ≠ 2 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 17 ≠ 0 := c3503
  have u1 : s 17 ≠ 1 := c3470
  exact (Or.elim c1128 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3528 (s : Fin 60 → Fin 5)
    (c3503 : s 17 ≠ 0)
    (c3470 : s 17 ≠ 1)
    (c1178 : s 11 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1)
    : s 11 ≠ 2 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 17 ≠ 0 := c3503
  have u1 : s 17 ≠ 1 := c3470
  exact (Or.elim c1178 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3546 (s : Fin 60 → Fin 5)
    (c3516 : s 11 ≠ 1)
    (c3500 : s 17 = 2)
    (c1448 : s 17 ≠ 2 ∨ s 11 = 0 ∨ s 11 = 1)
    : s 11 = 0 := by
  by_contra hc
  have u0 : s 11 ≠ 1 := c3516
  have u1 : s 17 = 2 := c3500
  exact (Or.elim c1448 (fun h => (h u1)) (fun h => (Or.elim h (fun h => (hc h)) (fun h => (u0 h)))))

private theorem step3549 (s : Fin 60 → Fin 5)
    (c3517 : s 14 ≠ 1)
    (c3400 : s 14 ≠ 2)
    (c3411 : s 14 ≠ 3)
    (c3351 : s 59 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3)
    : s 59 ≠ 0 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 14 ≠ 1 := c3517
  have u1 : s 14 ≠ 2 := c3400
  have u2 : s 14 ≠ 3 := c3411
  exact (Or.elim c3351 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (u2 h)))))))

private theorem step3554 (s : Fin 60 → Fin 5)
    (c3527 : s 10 ≠ 2)
    (c3511 : s 10 ≠ 1)
    (c3521 : s 10 ≠ 3)
    (c1416 : s 16 ≠ 0 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 10 = 3)
    : s 16 ≠ 0 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 10 ≠ 2 := c3527
  have u1 : s 10 ≠ 1 := c3511
  have u2 : s 10 ≠ 3 := c3521
  exact (Or.elim c1416 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u2 h)))))))

private theorem step3560 (s : Fin 60 → Fin 5)
    (c3528 : s 11 ≠ 2)
    (c3516 : s 11 ≠ 1)
    (c3522 : s 11 ≠ 3)
    (c2086 : s 31 ≠ 0 ∨ s 11 = 1 ∨ s 11 = 2 ∨ s 11 = 3)
    : s 31 ≠ 0 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 11 ≠ 2 := c3528
  have u1 : s 11 ≠ 1 := c3516
  have u2 : s 11 ≠ 3 := c3522
  exact (Or.elim c2086 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u2 h)))))))

private theorem step3574 (s : Fin 60 → Fin 5)
    (c3546 : s 11 = 0)
    (c3421 : s 34 ≠ 3)
    (c3403 : s 34 ≠ 2)
    (c1166 : s 11 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3)
    : s 34 = 1 := by
  by_contra hc
  have u0 : s 11 = 0 := c3546
  have u1 : s 34 ≠ 3 := c3421
  have u2 : s 34 ≠ 2 := c3403
  exact (Or.elim c1166 (fun h => (h u0)) (fun h => (Or.elim h (fun h => (hc h)) (fun h => (Or.elim h (fun h => (u2 h)) (fun h => (u1 h)))))))

private theorem step3579 (s : Fin 60 → Fin 5)
    (c3549 : s 59 ≠ 0)
    (c3574 : s 34 = 1)
    (c2232 : s 34 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2)
    : s 59 = 2 := by
  by_contra hc
  have u0 : s 59 ≠ 0 := c3549
  have u1 : s 34 = 1 := c3574
  exact (Or.elim c2232 (fun h => (h u1)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (hc h)))))

private theorem step3581 (s : Fin 60 → Fin 5)
    (c3554 : s 16 ≠ 0)
    (c3480 : s 16 ≠ 4)
    (c1059 : s 8 ≠ 3 ∨ s 16 = 0 ∨ s 16 = 4)
    : s 8 ≠ 3 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 16 ≠ 0 := c3554
  have u1 : s 16 ≠ 4 := c3480
  exact (Or.elim c1059 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3583 (s : Fin 60 → Fin 5)
    (c3554 : s 16 ≠ 0)
    (c3473 : s 16 ≠ 1)
    (c1058 : s 8 ≠ 2 ∨ s 16 = 0 ∨ s 16 = 1)
    : s 8 ≠ 2 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 16 ≠ 0 := c3554
  have u1 : s 16 ≠ 1 := c3473
  exact (Or.elim c1058 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3617 (s : Fin 60 → Fin 5)
    (c3560 : s 31 ≠ 0)
    (c3398 : s 31 ≠ 2)
    (c1062 : s 8 ≠ 1 ∨ s 31 = 0 ∨ s 31 = 2)
    : s 8 ≠ 1 := by
  by_contra hc
  try simp only [not_not] at hc
  have u0 : s 31 ≠ 0 := c3560
  have u1 : s 31 ≠ 2 := c3398
  exact (Or.elim c1062 (fun h => (h hc)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u1 h)))))

private theorem step3634 (s : Fin 60 → Fin 5)
    (c3579 : s 59 = 2)
    (c3474 : s 43 ≠ 1)
    (c3343 : s 59 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1)
    : s 43 = 0 := by
  by_contra hc
  have u0 : s 59 = 2 := c3579
  have u1 : s 43 ≠ 1 := c3474
  exact (Or.elim c3343 (fun h => (h u0)) (fun h => (Or.elim h (fun h => (hc h)) (fun h => (u1 h)))))

private theorem step3643 (s : Fin 60 → Fin 5)
    (c3583 : s 8 ≠ 2)
    (c3617 : s 8 ≠ 1)
    (c3634 : s 43 = 0)
    (c3581 : s 8 ≠ 3)
    (c2596 : s 43 ≠ 0 ∨ s 8 = 1 ∨ s 8 = 2 ∨ s 8 = 3)
    : False := by
  have u0 : s 8 ≠ 2 := c3583
  have u1 : s 8 ≠ 1 := c3617
  have u2 : s 43 = 0 := c3634
  have u3 : s 8 ≠ 3 := c3581
  exact (Or.elim c2596 (fun h => (h u2)) (fun h => (Or.elim h (fun h => (u1 h)) (fun h => (Or.elim h (fun h => (u0 h)) (fun h => (u3 h)))))))

/-- The finite certificate, with all hypotheses derived from the actual source edges. -/
theorem no_private (s : Fin 60 → Fin 5)
    (hs : ∀ i j, A2.Adj (point i) (point j) → Allowed (s i) (s j))
    (hbad : ∃ i, s i = 1 ∨ s i = 2) : False := by
  have c79 : s 7 ≠ 0 ∨ s 7 ≠ 1 := by
    omega
  have c83 : s 7 ≠ 1 ∨ s 7 ≠ 2 := by
    omega
  have c94 : s 8 ≠ 1 ∨ s 8 ≠ 2 := by
    omega
  have c112 : s 10 ≠ 0 ∨ s 10 ≠ 1 := by
    omega
  have c116 : s 10 ≠ 1 ∨ s 10 ≠ 2 := by
    omega
  have c127 : s 11 ≠ 1 ∨ s 11 ≠ 2 := by
    omega
  have c145 : s 13 ≠ 0 ∨ s 13 ≠ 1 := by
    omega
  have c146 : s 13 ≠ 0 ∨ s 13 ≠ 2 := by
    omega
  have c147 : s 13 ≠ 0 ∨ s 13 ≠ 3 := by
    omega
  have c149 : s 13 ≠ 1 ∨ s 13 ≠ 2 := by
    omega
  have c156 : s 14 ≠ 0 ∨ s 14 ≠ 1 := by
    omega
  have c157 : s 14 ≠ 0 ∨ s 14 ≠ 2 := by
    omega
  have c158 : s 14 ≠ 0 ∨ s 14 ≠ 3 := by
    omega
  have c160 : s 14 ≠ 1 ∨ s 14 ≠ 2 := by
    omega
  have c161 : s 14 ≠ 1 ∨ s 14 ≠ 3 := by
    omega
  have c162 : s 14 ≠ 1 ∨ s 14 ≠ 4 := by
    omega
  have c163 : s 14 ≠ 2 ∨ s 14 ≠ 3 := by
    omega
  have c164 : s 14 ≠ 2 ∨ s 14 ≠ 4 := by
    omega
  have c165 : s 14 ≠ 3 ∨ s 14 ≠ 4 := by
    omega
  have c189 : s 17 ≠ 0 ∨ s 17 ≠ 1 := by
    omega
  have c190 : s 17 ≠ 0 ∨ s 17 ≠ 2 := by
    omega
  have c201 : s 18 ≠ 0 ∨ s 18 ≠ 2 := by
    omega
  have c211 : s 19 ≠ 0 ∨ s 19 ≠ 1 := by
    omega
  have c215 : s 19 ≠ 1 ∨ s 19 ≠ 2 := by
    omega
  have c216 : s 19 ≠ 1 ∨ s 19 ≠ 3 := by
    omega
  have c217 : s 19 ≠ 1 ∨ s 19 ≠ 4 := by
    omega
  have c248 : s 22 ≠ 1 ∨ s 22 ≠ 2 := by
    omega
  have c399 : s 36 ≠ 0 ∨ s 36 ≠ 2 := by
    omega
  have c475 : s 43 ≠ 0 ∨ s 43 ≠ 1 := by
    omega
  have c476 : s 43 ≠ 0 ∨ s 43 ≠ 2 := by
    omega
  have c477 : s 43 ≠ 0 ∨ s 43 ≠ 3 := by
    omega
  have c562 : s 51 = 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3 ∨ s 51 = 4 := by
    exact five_cases (s 51)
  have c563 : s 51 ≠ 0 ∨ s 51 ≠ 1 := by
    omega
  have c564 : s 51 ≠ 0 ∨ s 51 ≠ 2 := by
    omega
  have c565 : s 51 ≠ 0 ∨ s 51 ≠ 3 := by
    omega
  have c566 : s 51 ≠ 0 ∨ s 51 ≠ 4 := by
    omega
  have c567 : s 51 ≠ 1 ∨ s 51 ≠ 2 := by
    omega
  have c568 : s 51 ≠ 1 ∨ s 51 ≠ 3 := by
    omega
  have c569 : s 51 ≠ 1 ∨ s 51 ≠ 4 := by
    omega
  have c570 : s 51 ≠ 2 ∨ s 51 ≠ 3 := by
    omega
  have c571 : s 51 ≠ 2 ∨ s 51 ≠ 4 := by
    omega
  have c574 : s 52 ≠ 0 ∨ s 52 ≠ 1 := by
    omega
  have c575 : s 52 ≠ 0 ∨ s 52 ≠ 2 := by
    omega
  have c578 : s 52 ≠ 1 ∨ s 52 ≠ 2 := by
    omega
  have c628 : s 57 = 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3 ∨ s 57 = 4 := by
    exact five_cases (s 57)
  have c629 : s 57 ≠ 0 ∨ s 57 ≠ 1 := by
    omega
  have c630 : s 57 ≠ 0 ∨ s 57 ≠ 2 := by
    omega
  have c631 : s 57 ≠ 0 ∨ s 57 ≠ 3 := by
    omega
  have c632 : s 57 ≠ 0 ∨ s 57 ≠ 4 := by
    omega
  have c633 : s 57 ≠ 1 ∨ s 57 ≠ 2 := by
    omega
  have c634 : s 57 ≠ 1 ∨ s 57 ≠ 3 := by
    omega
  have c635 : s 57 ≠ 1 ∨ s 57 ≠ 4 := by
    omega
  have c636 : s 57 ≠ 2 ∨ s 57 ≠ 3 := by
    omega
  have c637 : s 57 ≠ 2 ∨ s 57 ≠ 4 := by
    omega
  have c638 : s 57 ≠ 3 ∨ s 57 ≠ 4 := by
    omega
  have c643 : s 58 ≠ 0 ∨ s 58 ≠ 4 := by
    omega
  have c649 : s 58 ≠ 3 ∨ s 58 ≠ 4 := by
    omega
  have c652 : s 59 ≠ 0 ∨ s 59 ≠ 2 := by
    omega
  have c654 : s 59 ≠ 0 ∨ s 59 ≠ 4 := by
    omega
  have c656 : s 59 ≠ 1 ∨ s 59 ≠ 3 := by
    omega
  have c657 : s 59 ≠ 1 ∨ s 59 ≠ 4 := by
    omega
  have c658 : s 59 ≠ 2 ∨ s 59 ≠ 3 := by
    omega
  have c659 : s 59 ≠ 2 ∨ s 59 ≠ 4 := by
    omega
  have c660 : s 59 ≠ 3 ∨ s 59 ≠ 4 := by
    omega
  have c676 : s 0 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3 := by
    by_cases he : s 0 = 0
    · exact Or.inr ((row0 (s 17)).mp (he ▸ hs 0 17 (by decide +kernel)))
    · exact Or.inl he
  have c677 : s 0 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2 := by
    by_cases he : s 0 = 1
    · exact Or.inr ((row1 (s 17)).mp (he ▸ hs 0 17 (by decide +kernel)))
    · exact Or.inl he
  have c678 : s 0 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1 := by
    by_cases he : s 0 = 2
    · exact Or.inr ((row2 (s 17)).mp (he ▸ hs 0 17 (by decide +kernel)))
    · exact Or.inl he
  have c680 : s 0 ≠ 4 ∨ s 17 = 3 ∨ s 17 = 4 := by
    by_cases he : s 0 = 4
    · exact Or.inr ((row4 (s 17)).mp (he ▸ hs 0 17 (by decide +kernel)))
    · exact Or.inl he
  have c702 : s 0 ≠ 1 ∨ s 30 = 0 ∨ s 30 = 2 := by
    by_cases he : s 0 = 1
    · exact Or.inr ((row1 (s 30)).mp (he ▸ hs 0 30 (by decide +kernel)))
    · exact Or.inl he
  have c703 : s 0 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1 := by
    by_cases he : s 0 = 2
    · exact Or.inr ((row2 (s 30)).mp (he ▸ hs 0 30 (by decide +kernel)))
    · exact Or.inl he
  have c722 : s 1 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2 := by
    by_cases he : s 1 = 1
    · exact Or.inr ((row1 (s 21)).mp (he ▸ hs 1 21 (by decide +kernel)))
    · exact Or.inl he
  have c723 : s 1 ≠ 2 ∨ s 21 = 0 ∨ s 21 = 1 := by
    by_cases he : s 1 = 2
    · exact Or.inr ((row2 (s 21)).mp (he ▸ hs 1 21 (by decide +kernel)))
    · exact Or.inl he
  have c747 : s 1 ≠ 1 ∨ s 30 = 0 ∨ s 30 = 2 := by
    by_cases he : s 1 = 1
    · exact Or.inr ((row1 (s 30)).mp (he ▸ hs 1 30 (by decide +kernel)))
    · exact Or.inl he
  have c748 : s 1 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1 := by
    by_cases he : s 1 = 2
    · exact Or.inr ((row2 (s 30)).mp (he ▸ hs 1 30 (by decide +kernel)))
    · exact Or.inl he
  have c762 : s 2 ≠ 1 ∨ s 20 = 0 ∨ s 20 = 2 := by
    by_cases he : s 2 = 1
    · exact Or.inr ((row1 (s 20)).mp (he ▸ hs 2 20 (by decide +kernel)))
    · exact Or.inl he
  have c763 : s 2 ≠ 2 ∨ s 20 = 0 ∨ s 20 = 1 := by
    by_cases he : s 2 = 2
    · exact Or.inr ((row2 (s 20)).mp (he ▸ hs 2 20 (by decide +kernel)))
    · exact Or.inl he
  have c779 : s 2 ≠ 3 ∨ s 27 = 0 ∨ s 27 = 4 := by
    by_cases he : s 2 = 3
    · exact Or.inr ((row3 (s 27)).mp (he ▸ hs 2 27 (by decide +kernel)))
    · exact Or.inl he
  have c782 : s 2 ≠ 1 ∨ s 28 = 0 ∨ s 28 = 2 := by
    by_cases he : s 2 = 1
    · exact Or.inr ((row1 (s 28)).mp (he ▸ hs 2 28 (by decide +kernel)))
    · exact Or.inl he
  have c783 : s 2 ≠ 2 ∨ s 28 = 0 ∨ s 28 = 1 := by
    by_cases he : s 2 = 2
    · exact Or.inr ((row2 (s 28)).mp (he ▸ hs 2 28 (by decide +kernel)))
    · exact Or.inl he
  have c784 : s 2 ≠ 3 ∨ s 28 = 0 ∨ s 28 = 4 := by
    by_cases he : s 2 = 3
    · exact Or.inr ((row3 (s 28)).mp (he ▸ hs 2 28 (by decide +kernel)))
    · exact Or.inl he
  have c786 : s 2 ≠ 0 ∨ s 29 = 1 ∨ s 29 = 2 ∨ s 29 = 3 := by
    by_cases he : s 2 = 0
    · exact Or.inr ((row0 (s 29)).mp (he ▸ hs 2 29 (by decide +kernel)))
    · exact Or.inl he
  have c787 : s 2 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2 := by
    by_cases he : s 2 = 1
    · exact Or.inr ((row1 (s 29)).mp (he ▸ hs 2 29 (by decide +kernel)))
    · exact Or.inl he
  have c788 : s 2 ≠ 2 ∨ s 29 = 0 ∨ s 29 = 1 := by
    by_cases he : s 2 = 2
    · exact Or.inr ((row2 (s 29)).mp (he ▸ hs 2 29 (by decide +kernel)))
    · exact Or.inl he
  have c792 : s 2 ≠ 1 ∨ s 30 = 0 ∨ s 30 = 2 := by
    by_cases he : s 2 = 1
    · exact Or.inr ((row1 (s 30)).mp (he ▸ hs 2 30 (by decide +kernel)))
    · exact Or.inl he
  have c793 : s 2 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1 := by
    by_cases he : s 2 = 2
    · exact Or.inr ((row2 (s 30)).mp (he ▸ hs 2 30 (by decide +kernel)))
    · exact Or.inl he
  have c796 : s 3 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3 := by
    by_cases he : s 3 = 0
    · exact Or.inr ((row0 (s 32)).mp (he ▸ hs 3 32 (by decide +kernel)))
    · exact Or.inl he
  have c797 : s 3 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2 := by
    by_cases he : s 3 = 1
    · exact Or.inr ((row1 (s 32)).mp (he ▸ hs 3 32 (by decide +kernel)))
    · exact Or.inl he
  have c798 : s 3 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1 := by
    by_cases he : s 3 = 2
    · exact Or.inr ((row2 (s 32)).mp (he ▸ hs 3 32 (by decide +kernel)))
    · exact Or.inl he
  have c799 : s 3 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4 := by
    by_cases he : s 3 = 3
    · exact Or.inr ((row3 (s 32)).mp (he ▸ hs 3 32 (by decide +kernel)))
    · exact Or.inl he
  have c806 : s 3 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3 := by
    by_cases he : s 3 = 0
    · exact Or.inr ((row0 (s 34)).mp (he ▸ hs 3 34 (by decide +kernel)))
    · exact Or.inl he
  have c807 : s 3 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2 := by
    by_cases he : s 3 = 1
    · exact Or.inr ((row1 (s 34)).mp (he ▸ hs 3 34 (by decide +kernel)))
    · exact Or.inl he
  have c808 : s 3 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1 := by
    by_cases he : s 3 = 2
    · exact Or.inr ((row2 (s 34)).mp (he ▸ hs 3 34 (by decide +kernel)))
    · exact Or.inl he
  have c809 : s 3 ≠ 3 ∨ s 34 = 0 ∨ s 34 = 4 := by
    by_cases he : s 3 = 3
    · exact Or.inr ((row3 (s 34)).mp (he ▸ hs 3 34 (by decide +kernel)))
    · exact Or.inl he
  have c810 : s 3 ≠ 4 ∨ s 34 = 3 ∨ s 34 = 4 := by
    by_cases he : s 3 = 4
    · exact Or.inr ((row4 (s 34)).mp (he ▸ hs 3 34 (by decide +kernel)))
    · exact Or.inl he
  have c817 : s 3 ≠ 1 ∨ s 15 = 0 ∨ s 15 = 2 := by
    by_cases he : s 3 = 1
    · exact Or.inr ((row1 (s 15)).mp (he ▸ hs 3 15 (by decide +kernel)))
    · exact Or.inl he
  have c833 : s 3 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1 := by
    by_cases he : s 3 = 2
    · exact Or.inr ((row2 (s 30)).mp (he ▸ hs 3 30 (by decide +kernel)))
    · exact Or.inl he
  have c856 : s 4 ≠ 0 ∨ s 47 = 1 ∨ s 47 = 2 ∨ s 47 = 3 := by
    by_cases he : s 4 = 0
    · exact Or.inr ((row0 (s 47)).mp (he ▸ hs 4 47 (by decide +kernel)))
    · exact Or.inl he
  have c857 : s 4 ≠ 1 ∨ s 47 = 0 ∨ s 47 = 2 := by
    by_cases he : s 4 = 1
    · exact Or.inr ((row1 (s 47)).mp (he ▸ hs 4 47 (by decide +kernel)))
    · exact Or.inl he
  have c858 : s 4 ≠ 2 ∨ s 47 = 0 ∨ s 47 = 1 := by
    by_cases he : s 4 = 2
    · exact Or.inr ((row2 (s 47)).mp (he ▸ hs 4 47 (by decide +kernel)))
    · exact Or.inl he
  have c882 : s 4 ≠ 1 ∨ s 30 = 0 ∨ s 30 = 2 := by
    by_cases he : s 4 = 1
    · exact Or.inr ((row1 (s 30)).mp (he ▸ hs 4 30 (by decide +kernel)))
    · exact Or.inl he
  have c883 : s 4 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1 := by
    by_cases he : s 4 = 2
    · exact Or.inr ((row2 (s 30)).mp (he ▸ hs 4 30 (by decide +kernel)))
    · exact Or.inl he
  have c891 : s 5 ≠ 0 ∨ s 40 = 1 ∨ s 40 = 2 ∨ s 40 = 3 := by
    by_cases he : s 5 = 0
    · exact Or.inr ((row0 (s 40)).mp (he ▸ hs 5 40 (by decide +kernel)))
    · exact Or.inl he
  have c892 : s 5 ≠ 1 ∨ s 40 = 0 ∨ s 40 = 2 := by
    by_cases he : s 5 = 1
    · exact Or.inr ((row1 (s 40)).mp (he ▸ hs 5 40 (by decide +kernel)))
    · exact Or.inl he
  have c893 : s 5 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1 := by
    by_cases he : s 5 = 2
    · exact Or.inr ((row2 (s 40)).mp (he ▸ hs 5 40 (by decide +kernel)))
    · exact Or.inl he
  have c912 : s 5 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2 := by
    by_cases he : s 5 = 1
    · exact Or.inr ((row1 (s 17)).mp (he ▸ hs 5 17 (by decide +kernel)))
    · exact Or.inl he
  have c913 : s 5 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1 := by
    by_cases he : s 5 = 2
    · exact Or.inr ((row2 (s 17)).mp (he ▸ hs 5 17 (by decide +kernel)))
    · exact Or.inl he
  have c914 : s 5 ≠ 3 ∨ s 17 = 0 ∨ s 17 = 4 := by
    by_cases he : s 5 = 3
    · exact Or.inr ((row3 (s 17)).mp (he ▸ hs 5 17 (by decide +kernel)))
    · exact Or.inl he
  have c922 : s 5 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2 := by
    by_cases he : s 5 = 1
    · exact Or.inr ((row1 (s 19)).mp (he ▸ hs 5 19 (by decide +kernel)))
    · exact Or.inl he
  have c923 : s 5 ≠ 2 ∨ s 19 = 0 ∨ s 19 = 1 := by
    by_cases he : s 5 = 2
    · exact Or.inr ((row2 (s 19)).mp (he ▸ hs 5 19 (by decide +kernel)))
    · exact Or.inl he
  have c927 : s 5 ≠ 1 ∨ s 31 = 0 ∨ s 31 = 2 := by
    by_cases he : s 5 = 1
    · exact Or.inr ((row1 (s 31)).mp (he ▸ hs 5 31 (by decide +kernel)))
    · exact Or.inl he
  have c928 : s 5 ≠ 2 ∨ s 31 = 0 ∨ s 31 = 1 := by
    by_cases he : s 5 = 2
    · exact Or.inr ((row2 (s 31)).mp (he ▸ hs 5 31 (by decide +kernel)))
    · exact Or.inl he
  have c929 : s 5 ≠ 3 ∨ s 31 = 0 ∨ s 31 = 4 := by
    by_cases he : s 5 = 3
    · exact Or.inr ((row3 (s 31)).mp (he ▸ hs 5 31 (by decide +kernel)))
    · exact Or.inl he
  have c931 : s 6 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3 := by
    by_cases he : s 6 = 0
    · exact Or.inr ((row0 (s 32)).mp (he ▸ hs 6 32 (by decide +kernel)))
    · exact Or.inl he
  have c932 : s 6 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2 := by
    by_cases he : s 6 = 1
    · exact Or.inr ((row1 (s 32)).mp (he ▸ hs 6 32 (by decide +kernel)))
    · exact Or.inl he
  have c933 : s 6 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1 := by
    by_cases he : s 6 = 2
    · exact Or.inr ((row2 (s 32)).mp (he ▸ hs 6 32 (by decide +kernel)))
    · exact Or.inl he
  have c934 : s 6 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4 := by
    by_cases he : s 6 = 3
    · exact Or.inr ((row3 (s 32)).mp (he ▸ hs 6 32 (by decide +kernel)))
    · exact Or.inl he
  have c941 : s 6 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3 := by
    by_cases he : s 6 = 0
    · exact Or.inr ((row0 (s 34)).mp (he ▸ hs 6 34 (by decide +kernel)))
    · exact Or.inl he
  have c942 : s 6 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2 := by
    by_cases he : s 6 = 1
    · exact Or.inr ((row1 (s 34)).mp (he ▸ hs 6 34 (by decide +kernel)))
    · exact Or.inl he
  have c943 : s 6 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1 := by
    by_cases he : s 6 = 2
    · exact Or.inr ((row2 (s 34)).mp (he ▸ hs 6 34 (by decide +kernel)))
    · exact Or.inl he
  have c952 : s 6 ≠ 1 ∨ s 40 = 0 ∨ s 40 = 2 := by
    by_cases he : s 6 = 1
    · exact Or.inr ((row1 (s 40)).mp (he ▸ hs 6 40 (by decide +kernel)))
    · exact Or.inl he
  have c966 : s 6 ≠ 0 ∨ s 30 = 1 ∨ s 30 = 2 ∨ s 30 = 3 := by
    by_cases he : s 6 = 0
    · exact Or.inr ((row0 (s 30)).mp (he ▸ hs 6 30 (by decide +kernel)))
    · exact Or.inl he
  have c968 : s 6 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1 := by
    by_cases he : s 6 = 2
    · exact Or.inr ((row2 (s 30)).mp (he ▸ hs 6 30 (by decide +kernel)))
    · exact Or.inl he
  have c986 : s 7 ≠ 0 ∨ s 37 = 1 ∨ s 37 = 2 ∨ s 37 = 3 := by
    by_cases he : s 7 = 0
    · exact Or.inr ((row0 (s 37)).mp (he ▸ hs 7 37 (by decide +kernel)))
    · exact Or.inl he
  have c987 : s 7 ≠ 1 ∨ s 37 = 0 ∨ s 37 = 2 := by
    by_cases he : s 7 = 1
    · exact Or.inr ((row1 (s 37)).mp (he ▸ hs 7 37 (by decide +kernel)))
    · exact Or.inl he
  have c997 : s 7 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2 := by
    by_cases he : s 7 = 1
    · exact Or.inr ((row1 (s 39)).mp (he ▸ hs 7 39 (by decide +kernel)))
    · exact Or.inl he
  have c998 : s 7 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1 := by
    by_cases he : s 7 = 2
    · exact Or.inr ((row2 (s 39)).mp (he ▸ hs 7 39 (by decide +kernel)))
    · exact Or.inl he
  have c999 : s 7 ≠ 3 ∨ s 39 = 0 ∨ s 39 = 4 := by
    by_cases he : s 7 = 3
    · exact Or.inr ((row3 (s 39)).mp (he ▸ hs 7 39 (by decide +kernel)))
    · exact Or.inl he
  have c1007 : s 7 ≠ 1 ∨ s 46 = 0 ∨ s 46 = 2 := by
    by_cases he : s 7 = 1
    · exact Or.inr ((row1 (s 46)).mp (he ▸ hs 7 46 (by decide +kernel)))
    · exact Or.inl he
  have c1008 : s 7 ≠ 2 ∨ s 46 = 0 ∨ s 46 = 1 := by
    by_cases he : s 7 = 2
    · exact Or.inr ((row2 (s 46)).mp (he ▸ hs 7 46 (by decide +kernel)))
    · exact Or.inl he
  have c1013 : s 7 ≠ 2 ∨ s 16 = 0 ∨ s 16 = 1 := by
    by_cases he : s 7 = 2
    · exact Or.inr ((row2 (s 16)).mp (he ▸ hs 7 16 (by decide +kernel)))
    · exact Or.inl he
  have c1014 : s 7 ≠ 3 ∨ s 16 = 0 ∨ s 16 = 4 := by
    by_cases he : s 7 = 3
    · exact Or.inr ((row3 (s 16)).mp (he ▸ hs 7 16 (by decide +kernel)))
    · exact Or.inl he
  have c1017 : s 7 ≠ 1 ∨ s 31 = 0 ∨ s 31 = 2 := by
    by_cases he : s 7 = 1
    · exact Or.inr ((row1 (s 31)).mp (he ▸ hs 7 31 (by decide +kernel)))
    · exact Or.inl he
  have c1018 : s 7 ≠ 2 ∨ s 31 = 0 ∨ s 31 = 1 := by
    by_cases he : s 7 = 2
    · exact Or.inr ((row2 (s 31)).mp (he ▸ hs 7 31 (by decide +kernel)))
    · exact Or.inl he
  have c1028 : s 8 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1 := by
    by_cases he : s 8 = 2
    · exact Or.inr ((row2 (s 40)).mp (he ▸ hs 8 40 (by decide +kernel)))
    · exact Or.inl he
  have c1041 : s 8 ≠ 0 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 43 = 3 := by
    by_cases he : s 8 = 0
    · exact Or.inr ((row0 (s 43)).mp (he ▸ hs 8 43 (by decide +kernel)))
    · exact Or.inl he
  have c1042 : s 8 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2 := by
    by_cases he : s 8 = 1
    · exact Or.inr ((row1 (s 43)).mp (he ▸ hs 8 43 (by decide +kernel)))
    · exact Or.inl he
  have c1046 : s 8 ≠ 0 ∨ s 44 = 1 ∨ s 44 = 2 ∨ s 44 = 3 := by
    by_cases he : s 8 = 0
    · exact Or.inr ((row0 (s 44)).mp (he ▸ hs 8 44 (by decide +kernel)))
    · exact Or.inl he
  have c1052 : s 8 ≠ 1 ∨ s 46 = 0 ∨ s 46 = 2 := by
    by_cases he : s 8 = 1
    · exact Or.inr ((row1 (s 46)).mp (he ▸ hs 8 46 (by decide +kernel)))
    · exact Or.inl he
  have c1053 : s 8 ≠ 2 ∨ s 46 = 0 ∨ s 46 = 1 := by
    by_cases he : s 8 = 2
    · exact Or.inr ((row2 (s 46)).mp (he ▸ hs 8 46 (by decide +kernel)))
    · exact Or.inl he
  have c1056 : s 8 ≠ 0 ∨ s 16 = 1 ∨ s 16 = 2 ∨ s 16 = 3 := by
    by_cases he : s 8 = 0
    · exact Or.inr ((row0 (s 16)).mp (he ▸ hs 8 16 (by decide +kernel)))
    · exact Or.inl he
  have c1057 : s 8 ≠ 1 ∨ s 16 = 0 ∨ s 16 = 2 := by
    by_cases he : s 8 = 1
    · exact Or.inr ((row1 (s 16)).mp (he ▸ hs 8 16 (by decide +kernel)))
    · exact Or.inl he
  have c1058 : s 8 ≠ 2 ∨ s 16 = 0 ∨ s 16 = 1 := by
    by_cases he : s 8 = 2
    · exact Or.inr ((row2 (s 16)).mp (he ▸ hs 8 16 (by decide +kernel)))
    · exact Or.inl he
  have c1059 : s 8 ≠ 3 ∨ s 16 = 0 ∨ s 16 = 4 := by
    by_cases he : s 8 = 3
    · exact Or.inr ((row3 (s 16)).mp (he ▸ hs 8 16 (by decide +kernel)))
    · exact Or.inl he
  have c1061 : s 8 ≠ 0 ∨ s 31 = 1 ∨ s 31 = 2 ∨ s 31 = 3 := by
    by_cases he : s 8 = 0
    · exact Or.inr ((row0 (s 31)).mp (he ▸ hs 8 31 (by decide +kernel)))
    · exact Or.inl he
  have c1062 : s 8 ≠ 1 ∨ s 31 = 0 ∨ s 31 = 2 := by
    by_cases he : s 8 = 1
    · exact Or.inr ((row1 (s 31)).mp (he ▸ hs 8 31 (by decide +kernel)))
    · exact Or.inl he
  have c1063 : s 8 ≠ 2 ∨ s 31 = 0 ∨ s 31 = 1 := by
    by_cases he : s 8 = 2
    · exact Or.inr ((row2 (s 31)).mp (he ▸ hs 8 31 (by decide +kernel)))
    · exact Or.inl he
  have c1071 : s 9 ≠ 0 ∨ s 40 = 1 ∨ s 40 = 2 ∨ s 40 = 3 := by
    by_cases he : s 9 = 0
    · exact Or.inr ((row0 (s 40)).mp (he ▸ hs 9 40 (by decide +kernel)))
    · exact Or.inl he
  have c1072 : s 9 ≠ 1 ∨ s 40 = 0 ∨ s 40 = 2 := by
    by_cases he : s 9 = 1
    · exact Or.inr ((row1 (s 40)).mp (he ▸ hs 9 40 (by decide +kernel)))
    · exact Or.inl he
  have c1073 : s 9 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1 := by
    by_cases he : s 9 = 2
    · exact Or.inr ((row2 (s 40)).mp (he ▸ hs 9 40 (by decide +kernel)))
    · exact Or.inl he
  have c1087 : s 9 ≠ 1 ∨ s 47 = 0 ∨ s 47 = 2 := by
    by_cases he : s 9 = 1
    · exact Or.inr ((row1 (s 47)).mp (he ▸ hs 9 47 (by decide +kernel)))
    · exact Or.inl he
  have c1088 : s 9 ≠ 2 ∨ s 47 = 0 ∨ s 47 = 1 := by
    by_cases he : s 9 = 2
    · exact Or.inr ((row2 (s 47)).mp (he ▸ hs 9 47 (by decide +kernel)))
    · exact Or.inl he
  have c1107 : s 9 ≠ 1 ∨ s 31 = 0 ∨ s 31 = 2 := by
    by_cases he : s 9 = 1
    · exact Or.inr ((row1 (s 31)).mp (he ▸ hs 9 31 (by decide +kernel)))
    · exact Or.inl he
  have c1108 : s 9 ≠ 2 ∨ s 31 = 0 ∨ s 31 = 1 := by
    by_cases he : s 9 = 2
    · exact Or.inr ((row2 (s 31)).mp (he ▸ hs 9 31 (by decide +kernel)))
    · exact Or.inl he
  have c1111 : s 10 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3 := by
    by_cases he : s 10 = 0
    · exact Or.inr ((row0 (s 32)).mp (he ▸ hs 10 32 (by decide +kernel)))
    · exact Or.inl he
  have c1112 : s 10 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2 := by
    by_cases he : s 10 = 1
    · exact Or.inr ((row1 (s 32)).mp (he ▸ hs 10 32 (by decide +kernel)))
    · exact Or.inl he
  have c1113 : s 10 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1 := by
    by_cases he : s 10 = 2
    · exact Or.inr ((row2 (s 32)).mp (he ▸ hs 10 32 (by decide +kernel)))
    · exact Or.inl he
  have c1114 : s 10 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4 := by
    by_cases he : s 10 = 3
    · exact Or.inr ((row3 (s 32)).mp (he ▸ hs 10 32 (by decide +kernel)))
    · exact Or.inl he
  have c1115 : s 10 ≠ 4 ∨ s 32 = 3 ∨ s 32 = 4 := by
    by_cases he : s 10 = 4
    · exact Or.inr ((row4 (s 32)).mp (he ▸ hs 10 32 (by decide +kernel)))
    · exact Or.inl he
  have c1117 : s 10 ≠ 1 ∨ s 15 = 0 ∨ s 15 = 2 := by
    by_cases he : s 10 = 1
    · exact Or.inr ((row1 (s 15)).mp (he ▸ hs 10 15 (by decide +kernel)))
    · exact Or.inl he
  have c1122 : s 10 ≠ 1 ∨ s 16 = 0 ∨ s 16 = 2 := by
    by_cases he : s 10 = 1
    · exact Or.inr ((row1 (s 16)).mp (he ▸ hs 10 16 (by decide +kernel)))
    · exact Or.inl he
  have c1126 : s 10 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3 := by
    by_cases he : s 10 = 0
    · exact Or.inr ((row0 (s 17)).mp (he ▸ hs 10 17 (by decide +kernel)))
    · exact Or.inl he
  have c1128 : s 10 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1 := by
    by_cases he : s 10 = 2
    · exact Or.inr ((row2 (s 17)).mp (he ▸ hs 10 17 (by decide +kernel)))
    · exact Or.inl he
  have c1129 : s 10 ≠ 3 ∨ s 17 = 0 ∨ s 17 = 4 := by
    by_cases he : s 10 = 3
    · exact Or.inr ((row3 (s 17)).mp (he ▸ hs 10 17 (by decide +kernel)))
    · exact Or.inl he
  have c1131 : s 10 ≠ 0 ∨ s 18 = 1 ∨ s 18 = 2 ∨ s 18 = 3 := by
    by_cases he : s 10 = 0
    · exact Or.inr ((row0 (s 18)).mp (he ▸ hs 10 18 (by decide +kernel)))
    · exact Or.inl he
  have c1132 : s 10 ≠ 1 ∨ s 18 = 0 ∨ s 18 = 2 := by
    by_cases he : s 10 = 1
    · exact Or.inr ((row1 (s 18)).mp (he ▸ hs 10 18 (by decide +kernel)))
    · exact Or.inl he
  have c1136 : s 10 ≠ 0 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 19 = 3 := by
    by_cases he : s 10 = 0
    · exact Or.inr ((row0 (s 19)).mp (he ▸ hs 10 19 (by decide +kernel)))
    · exact Or.inl he
  have c1137 : s 10 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2 := by
    by_cases he : s 10 = 1
    · exact Or.inr ((row1 (s 19)).mp (he ▸ hs 10 19 (by decide +kernel)))
    · exact Or.inl he
  have c1139 : s 10 ≠ 3 ∨ s 19 = 0 ∨ s 19 = 4 := by
    by_cases he : s 10 = 3
    · exact Or.inr ((row3 (s 19)).mp (he ▸ hs 10 19 (by decide +kernel)))
    · exact Or.inl he
  have c1147 : s 10 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2 := by
    by_cases he : s 10 = 1
    · exact Or.inr ((row1 (s 50)).mp (he ▸ hs 10 50 (by decide +kernel)))
    · exact Or.inl he
  have c1148 : s 10 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1 := by
    by_cases he : s 10 = 2
    · exact Or.inr ((row2 (s 50)).mp (he ▸ hs 10 50 (by decide +kernel)))
    · exact Or.inl he
  have c1152 : s 10 ≠ 1 ∨ s 55 = 0 ∨ s 55 = 2 := by
    by_cases he : s 10 = 1
    · exact Or.inr ((row1 (s 55)).mp (he ▸ hs 10 55 (by decide +kernel)))
    · exact Or.inl he
  have c1153 : s 10 ≠ 2 ∨ s 55 = 0 ∨ s 55 = 1 := by
    by_cases he : s 10 = 2
    · exact Or.inr ((row2 (s 55)).mp (he ▸ hs 10 55 (by decide +kernel)))
    · exact Or.inl he
  have c1154 : s 10 ≠ 3 ∨ s 55 = 0 ∨ s 55 = 4 := by
    by_cases he : s 10 = 3
    · exact Or.inr ((row3 (s 55)).mp (he ▸ hs 10 55 (by decide +kernel)))
    · exact Or.inl he
  have c1156 : s 11 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3 := by
    by_cases he : s 11 = 0
    · exact Or.inr ((row0 (s 32)).mp (he ▸ hs 11 32 (by decide +kernel)))
    · exact Or.inl he
  have c1157 : s 11 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2 := by
    by_cases he : s 11 = 1
    · exact Or.inr ((row1 (s 32)).mp (he ▸ hs 11 32 (by decide +kernel)))
    · exact Or.inl he
  have c1158 : s 11 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1 := by
    by_cases he : s 11 = 2
    · exact Or.inr ((row2 (s 32)).mp (he ▸ hs 11 32 (by decide +kernel)))
    · exact Or.inl he
  have c1159 : s 11 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4 := by
    by_cases he : s 11 = 3
    · exact Or.inr ((row3 (s 32)).mp (he ▸ hs 11 32 (by decide +kernel)))
    · exact Or.inl he
  have c1166 : s 11 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3 := by
    by_cases he : s 11 = 0
    · exact Or.inr ((row0 (s 34)).mp (he ▸ hs 11 34 (by decide +kernel)))
    · exact Or.inl he
  have c1167 : s 11 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2 := by
    by_cases he : s 11 = 1
    · exact Or.inr ((row1 (s 34)).mp (he ▸ hs 11 34 (by decide +kernel)))
    · exact Or.inl he
  have c1168 : s 11 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1 := by
    by_cases he : s 11 = 2
    · exact Or.inr ((row2 (s 34)).mp (he ▸ hs 11 34 (by decide +kernel)))
    · exact Or.inl he
  have c1169 : s 11 ≠ 3 ∨ s 34 = 0 ∨ s 34 = 4 := by
    by_cases he : s 11 = 3
    · exact Or.inr ((row3 (s 34)).mp (he ▸ hs 11 34 (by decide +kernel)))
    · exact Or.inl he
  have c1176 : s 11 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3 := by
    by_cases he : s 11 = 0
    · exact Or.inr ((row0 (s 17)).mp (he ▸ hs 11 17 (by decide +kernel)))
    · exact Or.inl he
  have c1178 : s 11 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1 := by
    by_cases he : s 11 = 2
    · exact Or.inr ((row2 (s 17)).mp (he ▸ hs 11 17 (by decide +kernel)))
    · exact Or.inl he
  have c1182 : s 11 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2 := by
    by_cases he : s 11 = 1
    · exact Or.inr ((row1 (s 50)).mp (he ▸ hs 11 50 (by decide +kernel)))
    · exact Or.inl he
  have c1183 : s 11 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1 := by
    by_cases he : s 11 = 2
    · exact Or.inr ((row2 (s 50)).mp (he ▸ hs 11 50 (by decide +kernel)))
    · exact Or.inl he
  have c1193 : s 11 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1 := by
    by_cases he : s 11 = 2
    · exact Or.inr ((row2 (s 30)).mp (he ▸ hs 11 30 (by decide +kernel)))
    · exact Or.inl he
  have c1197 : s 11 ≠ 1 ∨ s 31 = 0 ∨ s 31 = 2 := by
    by_cases he : s 11 = 1
    · exact Or.inr ((row1 (s 31)).mp (he ▸ hs 11 31 (by decide +kernel)))
    · exact Or.inl he
  have c1202 : s 12 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2 := by
    by_cases he : s 12 = 1
    · exact Or.inr ((row1 (s 32)).mp (he ▸ hs 12 32 (by decide +kernel)))
    · exact Or.inl he
  have c1203 : s 12 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1 := by
    by_cases he : s 12 = 2
    · exact Or.inr ((row2 (s 32)).mp (he ▸ hs 12 32 (by decide +kernel)))
    · exact Or.inl he
  have c1242 : s 12 ≠ 1 ∨ s 55 = 0 ∨ s 55 = 2 := by
    by_cases he : s 12 = 1
    · exact Or.inr ((row1 (s 55)).mp (he ▸ hs 12 55 (by decide +kernel)))
    · exact Or.inl he
  have c1243 : s 12 ≠ 2 ∨ s 55 = 0 ∨ s 55 = 1 := by
    by_cases he : s 12 = 2
    · exact Or.inr ((row2 (s 55)).mp (he ▸ hs 12 55 (by decide +kernel)))
    · exact Or.inl he
  have c1246 : s 13 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3 := by
    by_cases he : s 13 = 0
    · exact Or.inr ((row0 (s 32)).mp (he ▸ hs 13 32 (by decide +kernel)))
    · exact Or.inl he
  have c1247 : s 13 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2 := by
    by_cases he : s 13 = 1
    · exact Or.inr ((row1 (s 32)).mp (he ▸ hs 13 32 (by decide +kernel)))
    · exact Or.inl he
  have c1248 : s 13 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1 := by
    by_cases he : s 13 = 2
    · exact Or.inr ((row2 (s 32)).mp (he ▸ hs 13 32 (by decide +kernel)))
    · exact Or.inl he
  have c1249 : s 13 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4 := by
    by_cases he : s 13 = 3
    · exact Or.inr ((row3 (s 32)).mp (he ▸ hs 13 32 (by decide +kernel)))
    · exact Or.inl he
  have c1250 : s 13 ≠ 4 ∨ s 32 = 3 ∨ s 32 = 4 := by
    by_cases he : s 13 = 4
    · exact Or.inr ((row4 (s 32)).mp (he ▸ hs 13 32 (by decide +kernel)))
    · exact Or.inl he
  have c1256 : s 13 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3 := by
    by_cases he : s 13 = 0
    · exact Or.inr ((row0 (s 17)).mp (he ▸ hs 13 17 (by decide +kernel)))
    · exact Or.inl he
  have c1257 : s 13 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2 := by
    by_cases he : s 13 = 1
    · exact Or.inr ((row1 (s 17)).mp (he ▸ hs 13 17 (by decide +kernel)))
    · exact Or.inl he
  have c1258 : s 13 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1 := by
    by_cases he : s 13 = 2
    · exact Or.inr ((row2 (s 17)).mp (he ▸ hs 13 17 (by decide +kernel)))
    · exact Or.inl he
  have c1259 : s 13 ≠ 3 ∨ s 17 = 0 ∨ s 17 = 4 := by
    by_cases he : s 13 = 3
    · exact Or.inr ((row3 (s 17)).mp (he ▸ hs 13 17 (by decide +kernel)))
    · exact Or.inl he
  have c1260 : s 13 ≠ 4 ∨ s 17 = 3 ∨ s 17 = 4 := by
    by_cases he : s 13 = 4
    · exact Or.inr ((row4 (s 17)).mp (he ▸ hs 13 17 (by decide +kernel)))
    · exact Or.inl he
  have c1261 : s 13 ≠ 0 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 50 = 3 := by
    by_cases he : s 13 = 0
    · exact Or.inr ((row0 (s 50)).mp (he ▸ hs 13 50 (by decide +kernel)))
    · exact Or.inl he
  have c1262 : s 13 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2 := by
    by_cases he : s 13 = 1
    · exact Or.inr ((row1 (s 50)).mp (he ▸ hs 13 50 (by decide +kernel)))
    · exact Or.inl he
  have c1263 : s 13 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1 := by
    by_cases he : s 13 = 2
    · exact Or.inr ((row2 (s 50)).mp (he ▸ hs 13 50 (by decide +kernel)))
    · exact Or.inl he
  have c1266 : s 13 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3 := by
    by_cases he : s 13 = 0
    · exact Or.inr ((row0 (s 51)).mp (he ▸ hs 13 51 (by decide +kernel)))
    · exact Or.inl he
  have c1267 : s 13 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2 := by
    by_cases he : s 13 = 1
    · exact Or.inr ((row1 (s 51)).mp (he ▸ hs 13 51 (by decide +kernel)))
    · exact Or.inl he
  have c1268 : s 13 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1 := by
    by_cases he : s 13 = 2
    · exact Or.inr ((row2 (s 51)).mp (he ▸ hs 13 51 (by decide +kernel)))
    · exact Or.inl he
  have c1269 : s 13 ≠ 3 ∨ s 51 = 0 ∨ s 51 = 4 := by
    by_cases he : s 13 = 3
    · exact Or.inr ((row3 (s 51)).mp (he ▸ hs 13 51 (by decide +kernel)))
    · exact Or.inl he
  have c1287 : s 13 ≠ 1 ∨ s 55 = 0 ∨ s 55 = 2 := by
    by_cases he : s 13 = 1
    · exact Or.inr ((row1 (s 55)).mp (he ▸ hs 13 55 (by decide +kernel)))
    · exact Or.inl he
  have c1288 : s 13 ≠ 2 ∨ s 55 = 0 ∨ s 55 = 1 := by
    by_cases he : s 13 = 2
    · exact Or.inr ((row2 (s 55)).mp (he ▸ hs 13 55 (by decide +kernel)))
    · exact Or.inl he
  have c1289 : s 13 ≠ 3 ∨ s 55 = 0 ∨ s 55 = 4 := by
    by_cases he : s 13 = 3
    · exact Or.inr ((row3 (s 55)).mp (he ▸ hs 13 55 (by decide +kernel)))
    · exact Or.inl he
  have c1291 : s 14 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3 := by
    by_cases he : s 14 = 0
    · exact Or.inr ((row0 (s 32)).mp (he ▸ hs 14 32 (by decide +kernel)))
    · exact Or.inl he
  have c1292 : s 14 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2 := by
    by_cases he : s 14 = 1
    · exact Or.inr ((row1 (s 32)).mp (he ▸ hs 14 32 (by decide +kernel)))
    · exact Or.inl he
  have c1294 : s 14 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4 := by
    by_cases he : s 14 = 3
    · exact Or.inr ((row3 (s 32)).mp (he ▸ hs 14 32 (by decide +kernel)))
    · exact Or.inl he
  have c1301 : s 14 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3 := by
    by_cases he : s 14 = 0
    · exact Or.inr ((row0 (s 17)).mp (he ▸ hs 14 17 (by decide +kernel)))
    · exact Or.inl he
  have c1302 : s 14 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2 := by
    by_cases he : s 14 = 1
    · exact Or.inr ((row1 (s 17)).mp (he ▸ hs 14 17 (by decide +kernel)))
    · exact Or.inl he
  have c1303 : s 14 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1 := by
    by_cases he : s 14 = 2
    · exact Or.inr ((row2 (s 17)).mp (he ▸ hs 14 17 (by decide +kernel)))
    · exact Or.inl he
  have c1306 : s 14 ≠ 0 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 50 = 3 := by
    by_cases he : s 14 = 0
    · exact Or.inr ((row0 (s 50)).mp (he ▸ hs 14 50 (by decide +kernel)))
    · exact Or.inl he
  have c1307 : s 14 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2 := by
    by_cases he : s 14 = 1
    · exact Or.inr ((row1 (s 50)).mp (he ▸ hs 14 50 (by decide +kernel)))
    · exact Or.inl he
  have c1322 : s 14 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2 := by
    by_cases he : s 14 = 1
    · exact Or.inr ((row1 (s 57)).mp (he ▸ hs 14 57 (by decide +kernel)))
    · exact Or.inl he
  have c1323 : s 14 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1 := by
    by_cases he : s 14 = 2
    · exact Or.inr ((row2 (s 57)).mp (he ▸ hs 14 57 (by decide +kernel)))
    · exact Or.inl he
  have c1324 : s 14 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4 := by
    by_cases he : s 14 = 3
    · exact Or.inr ((row3 (s 57)).mp (he ▸ hs 14 57 (by decide +kernel)))
    · exact Or.inl he
  have c1325 : s 14 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4 := by
    by_cases he : s 14 = 4
    · exact Or.inr ((row4 (s 57)).mp (he ▸ hs 14 57 (by decide +kernel)))
    · exact Or.inl he
  have c1329 : s 14 ≠ 3 ∨ s 58 = 0 ∨ s 58 = 4 := by
    by_cases he : s 14 = 3
    · exact Or.inr ((row3 (s 58)).mp (he ▸ hs 14 58 (by decide +kernel)))
    · exact Or.inl he
  have c1331 : s 14 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3 := by
    by_cases he : s 14 = 0
    · exact Or.inr ((row0 (s 59)).mp (he ▸ hs 14 59 (by decide +kernel)))
    · exact Or.inl he
  have c1332 : s 14 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2 := by
    by_cases he : s 14 = 1
    · exact Or.inr ((row1 (s 59)).mp (he ▸ hs 14 59 (by decide +kernel)))
    · exact Or.inl he
  have c1333 : s 14 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1 := by
    by_cases he : s 14 = 2
    · exact Or.inr ((row2 (s 59)).mp (he ▸ hs 14 59 (by decide +kernel)))
    · exact Or.inl he
  have c1335 : s 14 ≠ 4 ∨ s 59 = 3 ∨ s 59 = 4 := by
    by_cases he : s 14 = 4
    · exact Or.inr ((row4 (s 59)).mp (he ▸ hs 14 59 (by decide +kernel)))
    · exact Or.inl he
  have c1346 : s 15 ≠ 0 ∨ s 2 = 1 ∨ s 2 = 2 ∨ s 2 = 3 := by
    by_cases he : s 15 = 0
    · exact Or.inr ((row0 (s 2)).mp (he ▸ hs 15 2 (by decide +kernel)))
    · exact Or.inl he
  have c1347 : s 15 ≠ 1 ∨ s 2 = 0 ∨ s 2 = 2 := by
    by_cases he : s 15 = 1
    · exact Or.inr ((row1 (s 2)).mp (he ▸ hs 15 2 (by decide +kernel)))
    · exact Or.inl he
  have c1348 : s 15 ≠ 2 ∨ s 2 = 0 ∨ s 2 = 1 := by
    by_cases he : s 15 = 2
    · exact Or.inr ((row2 (s 2)).mp (he ▸ hs 15 2 (by decide +kernel)))
    · exact Or.inl he
  have c1351 : s 15 ≠ 0 ∨ s 3 = 1 ∨ s 3 = 2 ∨ s 3 = 3 := by
    by_cases he : s 15 = 0
    · exact Or.inr ((row0 (s 3)).mp (he ▸ hs 15 3 (by decide +kernel)))
    · exact Or.inl he
  have c1352 : s 15 ≠ 1 ∨ s 3 = 0 ∨ s 3 = 2 := by
    by_cases he : s 15 = 1
    · exact Or.inr ((row1 (s 3)).mp (he ▸ hs 15 3 (by decide +kernel)))
    · exact Or.inl he
  have c1353 : s 15 ≠ 2 ∨ s 3 = 0 ∨ s 3 = 1 := by
    by_cases he : s 15 = 2
    · exact Or.inr ((row2 (s 3)).mp (he ▸ hs 15 3 (by decide +kernel)))
    · exact Or.inl he
  have c1354 : s 15 ≠ 3 ∨ s 3 = 0 ∨ s 3 = 4 := by
    by_cases he : s 15 = 3
    · exact Or.inr ((row3 (s 3)).mp (he ▸ hs 15 3 (by decide +kernel)))
    · exact Or.inl he
  have c1358 : s 15 ≠ 2 ∨ s 4 = 0 ∨ s 4 = 1 := by
    by_cases he : s 15 = 2
    · exact Or.inr ((row2 (s 4)).mp (he ▸ hs 15 4 (by decide +kernel)))
    · exact Or.inl he
  have c1367 : s 15 ≠ 1 ∨ s 36 = 0 ∨ s 36 = 2 := by
    by_cases he : s 15 = 1
    · exact Or.inr ((row1 (s 36)).mp (he ▸ hs 15 36 (by decide +kernel)))
    · exact Or.inl he
  have c1368 : s 15 ≠ 2 ∨ s 36 = 0 ∨ s 36 = 1 := by
    by_cases he : s 15 = 2
    · exact Or.inr ((row2 (s 36)).mp (he ▸ hs 15 36 (by decide +kernel)))
    · exact Or.inl he
  have c1371 : s 15 ≠ 0 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 10 = 3 := by
    by_cases he : s 15 = 0
    · exact Or.inr ((row0 (s 10)).mp (he ▸ hs 15 10 (by decide +kernel)))
    · exact Or.inl he
  have c1373 : s 15 ≠ 2 ∨ s 10 = 0 ∨ s 10 = 1 := by
    by_cases he : s 15 = 2
    · exact Or.inr ((row2 (s 10)).mp (he ▸ hs 15 10 (by decide +kernel)))
    · exact Or.inl he
  have c1377 : s 15 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2 := by
    by_cases he : s 15 = 1
    · exact Or.inr ((row1 (s 51)).mp (he ▸ hs 15 51 (by decide +kernel)))
    · exact Or.inl he
  have c1378 : s 15 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1 := by
    by_cases he : s 15 = 2
    · exact Or.inr ((row2 (s 51)).mp (he ▸ hs 15 51 (by decide +kernel)))
    · exact Or.inl he
  have c1383 : s 16 ≠ 2 ∨ s 0 = 0 ∨ s 0 = 1 := by
    by_cases he : s 16 = 2
    · exact Or.inr ((row2 (s 0)).mp (he ▸ hs 16 0 (by decide +kernel)))
    · exact Or.inl he
  have c1384 : s 16 ≠ 3 ∨ s 0 = 0 ∨ s 0 = 4 := by
    by_cases he : s 16 = 3
    · exact Or.inr ((row3 (s 0)).mp (he ▸ hs 16 0 (by decide +kernel)))
    · exact Or.inl he
  have c1387 : s 16 ≠ 1 ∨ s 36 = 0 ∨ s 36 = 2 := by
    by_cases he : s 16 = 1
    · exact Or.inr ((row1 (s 36)).mp (he ▸ hs 16 36 (by decide +kernel)))
    · exact Or.inl he
  have c1388 : s 16 ≠ 2 ∨ s 36 = 0 ∨ s 36 = 1 := by
    by_cases he : s 16 = 2
    · exact Or.inr ((row2 (s 36)).mp (he ▸ hs 16 36 (by decide +kernel)))
    · exact Or.inl he
  have c1390 : s 16 ≠ 4 ∨ s 36 = 3 ∨ s 36 = 4 := by
    by_cases he : s 16 = 4
    · exact Or.inr ((row4 (s 36)).mp (he ▸ hs 16 36 (by decide +kernel)))
    · exact Or.inl he
  have c1396 : s 16 ≠ 0 ∨ s 6 = 1 ∨ s 6 = 2 ∨ s 6 = 3 := by
    by_cases he : s 16 = 0
    · exact Or.inr ((row0 (s 6)).mp (he ▸ hs 16 6 (by decide +kernel)))
    · exact Or.inl he
  have c1397 : s 16 ≠ 1 ∨ s 6 = 0 ∨ s 6 = 2 := by
    by_cases he : s 16 = 1
    · exact Or.inr ((row1 (s 6)).mp (he ▸ hs 16 6 (by decide +kernel)))
    · exact Or.inl he
  have c1398 : s 16 ≠ 2 ∨ s 6 = 0 ∨ s 6 = 1 := by
    by_cases he : s 16 = 2
    · exact Or.inr ((row2 (s 6)).mp (he ▸ hs 16 6 (by decide +kernel)))
    · exact Or.inl he
  have c1402 : s 16 ≠ 1 ∨ s 7 = 0 ∨ s 7 = 2 := by
    by_cases he : s 16 = 1
    · exact Or.inr ((row1 (s 7)).mp (he ▸ hs 16 7 (by decide +kernel)))
    · exact Or.inl he
  have c1407 : s 16 ≠ 1 ∨ s 8 = 0 ∨ s 8 = 2 := by
    by_cases he : s 16 = 1
    · exact Or.inr ((row1 (s 8)).mp (he ▸ hs 16 8 (by decide +kernel)))
    · exact Or.inl he
  have c1416 : s 16 ≠ 0 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 10 = 3 := by
    by_cases he : s 16 = 0
    · exact Or.inr ((row0 (s 10)).mp (he ▸ hs 16 10 (by decide +kernel)))
    · exact Or.inl he
  have c1417 : s 16 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2 := by
    by_cases he : s 16 = 1
    · exact Or.inr ((row1 (s 10)).mp (he ▸ hs 16 10 (by decide +kernel)))
    · exact Or.inl he
  have c1418 : s 16 ≠ 2 ∨ s 10 = 0 ∨ s 10 = 1 := by
    by_cases he : s 16 = 2
    · exact Or.inr ((row2 (s 10)).mp (he ▸ hs 16 10 (by decide +kernel)))
    · exact Or.inl he
  have c1421 : s 16 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3 := by
    by_cases he : s 16 = 0
    · exact Or.inr ((row0 (s 51)).mp (he ▸ hs 16 51 (by decide +kernel)))
    · exact Or.inl he
  have c1422 : s 16 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2 := by
    by_cases he : s 16 = 1
    · exact Or.inr ((row1 (s 51)).mp (he ▸ hs 16 51 (by decide +kernel)))
    · exact Or.inl he
  have c1423 : s 16 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1 := by
    by_cases he : s 16 = 2
    · exact Or.inr ((row2 (s 51)).mp (he ▸ hs 16 51 (by decide +kernel)))
    · exact Or.inl he
  have c1425 : s 16 ≠ 4 ∨ s 51 = 3 ∨ s 51 = 4 := by
    by_cases he : s 16 = 4
    · exact Or.inr ((row4 (s 51)).mp (he ▸ hs 16 51 (by decide +kernel)))
    · exact Or.inl he
  have c1432 : s 17 ≠ 1 ∨ s 36 = 0 ∨ s 36 = 2 := by
    by_cases he : s 17 = 1
    · exact Or.inr ((row1 (s 36)).mp (he ▸ hs 17 36 (by decide +kernel)))
    · exact Or.inl he
  have c1438 : s 17 ≠ 2 ∨ s 5 = 0 ∨ s 5 = 1 := by
    by_cases he : s 17 = 2
    · exact Or.inr ((row2 (s 5)).mp (he ▸ hs 17 5 (by decide +kernel)))
    · exact Or.inl he
  have c1442 : s 17 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2 := by
    by_cases he : s 17 = 1
    · exact Or.inr ((row1 (s 10)).mp (he ▸ hs 17 10 (by decide +kernel)))
    · exact Or.inl he
  have c1446 : s 17 ≠ 0 ∨ s 11 = 1 ∨ s 11 = 2 ∨ s 11 = 3 := by
    by_cases he : s 17 = 0
    · exact Or.inr ((row0 (s 11)).mp (he ▸ hs 17 11 (by decide +kernel)))
    · exact Or.inl he
  have c1447 : s 17 ≠ 1 ∨ s 11 = 0 ∨ s 11 = 2 := by
    by_cases he : s 17 = 1
    · exact Or.inr ((row1 (s 11)).mp (he ▸ hs 17 11 (by decide +kernel)))
    · exact Or.inl he
  have c1448 : s 17 ≠ 2 ∨ s 11 = 0 ∨ s 11 = 1 := by
    by_cases he : s 17 = 2
    · exact Or.inr ((row2 (s 11)).mp (he ▸ hs 17 11 (by decide +kernel)))
    · exact Or.inl he
  have c1456 : s 17 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3 := by
    by_cases he : s 17 = 0
    · exact Or.inr ((row0 (s 13)).mp (he ▸ hs 17 13 (by decide +kernel)))
    · exact Or.inl he
  have c1457 : s 17 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2 := by
    by_cases he : s 17 = 1
    · exact Or.inr ((row1 (s 13)).mp (he ▸ hs 17 13 (by decide +kernel)))
    · exact Or.inl he
  have c1458 : s 17 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1 := by
    by_cases he : s 17 = 2
    · exact Or.inr ((row2 (s 13)).mp (he ▸ hs 17 13 (by decide +kernel)))
    · exact Or.inl he
  have c1459 : s 17 ≠ 3 ∨ s 13 = 0 ∨ s 13 = 4 := by
    by_cases he : s 17 = 3
    · exact Or.inr ((row3 (s 13)).mp (he ▸ hs 17 13 (by decide +kernel)))
    · exact Or.inl he
  have c1461 : s 17 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3 := by
    by_cases he : s 17 = 0
    · exact Or.inr ((row0 (s 14)).mp (he ▸ hs 17 14 (by decide +kernel)))
    · exact Or.inl he
  have c1462 : s 17 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2 := by
    by_cases he : s 17 = 1
    · exact Or.inr ((row1 (s 14)).mp (he ▸ hs 17 14 (by decide +kernel)))
    · exact Or.inl he
  have c1463 : s 17 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1 := by
    by_cases he : s 17 = 2
    · exact Or.inr ((row2 (s 14)).mp (he ▸ hs 17 14 (by decide +kernel)))
    · exact Or.inl he
  have c1464 : s 17 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4 := by
    by_cases he : s 17 = 3
    · exact Or.inr ((row3 (s 14)).mp (he ▸ hs 17 14 (by decide +kernel)))
    · exact Or.inl he
  have c1465 : s 17 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4 := by
    by_cases he : s 17 = 4
    · exact Or.inr ((row4 (s 14)).mp (he ▸ hs 17 14 (by decide +kernel)))
    · exact Or.inl he
  have c1466 : s 17 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3 := by
    by_cases he : s 17 = 0
    · exact Or.inr ((row0 (s 51)).mp (he ▸ hs 17 51 (by decide +kernel)))
    · exact Or.inl he
  have c1467 : s 17 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2 := by
    by_cases he : s 17 = 1
    · exact Or.inr ((row1 (s 51)).mp (he ▸ hs 17 51 (by decide +kernel)))
    · exact Or.inl he
  have c1468 : s 17 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1 := by
    by_cases he : s 17 = 2
    · exact Or.inr ((row2 (s 51)).mp (he ▸ hs 17 51 (by decide +kernel)))
    · exact Or.inl he
  have c1469 : s 17 ≠ 3 ∨ s 51 = 0 ∨ s 51 = 4 := by
    by_cases he : s 17 = 3
    · exact Or.inr ((row3 (s 51)).mp (he ▸ hs 17 51 (by decide +kernel)))
    · exact Or.inl he
  have c1483 : s 18 ≠ 2 ∨ s 36 = 0 ∨ s 36 = 1 := by
    by_cases he : s 18 = 2
    · exact Or.inr ((row2 (s 36)).mp (he ▸ hs 18 36 (by decide +kernel)))
    · exact Or.inl he
  have c1487 : s 18 ≠ 1 ∨ s 5 = 0 ∨ s 5 = 2 := by
    by_cases he : s 18 = 1
    · exact Or.inr ((row1 (s 5)).mp (he ▸ hs 18 5 (by decide +kernel)))
    · exact Or.inl he
  have c1488 : s 18 ≠ 2 ∨ s 5 = 0 ∨ s 5 = 1 := by
    by_cases he : s 18 = 2
    · exact Or.inr ((row2 (s 5)).mp (he ▸ hs 18 5 (by decide +kernel)))
    · exact Or.inl he
  have c1491 : s 18 ≠ 0 ∨ s 37 = 1 ∨ s 37 = 2 ∨ s 37 = 3 := by
    by_cases he : s 18 = 0
    · exact Or.inr ((row0 (s 37)).mp (he ▸ hs 18 37 (by decide +kernel)))
    · exact Or.inl he
  have c1500 : s 18 ≠ 4 ∨ s 38 = 3 ∨ s 38 = 4 := by
    by_cases he : s 18 = 4
    · exact Or.inr ((row4 (s 38)).mp (he ▸ hs 18 38 (by decide +kernel)))
    · exact Or.inl he
  have c1501 : s 18 ≠ 0 ∨ s 39 = 1 ∨ s 39 = 2 ∨ s 39 = 3 := by
    by_cases he : s 18 = 0
    · exact Or.inr ((row0 (s 39)).mp (he ▸ hs 18 39 (by decide +kernel)))
    · exact Or.inl he
  have c1502 : s 18 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2 := by
    by_cases he : s 18 = 1
    · exact Or.inr ((row1 (s 39)).mp (he ▸ hs 18 39 (by decide +kernel)))
    · exact Or.inl he
  have c1503 : s 18 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1 := by
    by_cases he : s 18 = 2
    · exact Or.inr ((row2 (s 39)).mp (he ▸ hs 18 39 (by decide +kernel)))
    · exact Or.inl he
  have c1506 : s 18 ≠ 0 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 10 = 3 := by
    by_cases he : s 18 = 0
    · exact Or.inr ((row0 (s 10)).mp (he ▸ hs 18 10 (by decide +kernel)))
    · exact Or.inl he
  have c1507 : s 18 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2 := by
    by_cases he : s 18 = 1
    · exact Or.inr ((row1 (s 10)).mp (he ▸ hs 18 10 (by decide +kernel)))
    · exact Or.inl he
  have c1509 : s 18 ≠ 3 ∨ s 10 = 0 ∨ s 10 = 4 := by
    by_cases he : s 18 = 3
    · exact Or.inr ((row3 (s 10)).mp (he ▸ hs 18 10 (by decide +kernel)))
    · exact Or.inl he
  have c1511 : s 18 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3 := by
    by_cases he : s 18 = 0
    · exact Or.inr ((row0 (s 51)).mp (he ▸ hs 18 51 (by decide +kernel)))
    · exact Or.inl he
  have c1512 : s 18 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2 := by
    by_cases he : s 18 = 1
    · exact Or.inr ((row1 (s 51)).mp (he ▸ hs 18 51 (by decide +kernel)))
    · exact Or.inl he
  have c1513 : s 18 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1 := by
    by_cases he : s 18 = 2
    · exact Or.inr ((row2 (s 51)).mp (he ▸ hs 18 51 (by decide +kernel)))
    · exact Or.inl he
  have c1514 : s 18 ≠ 3 ∨ s 51 = 0 ∨ s 51 = 4 := by
    by_cases he : s 18 = 3
    · exact Or.inr ((row3 (s 51)).mp (he ▸ hs 18 51 (by decide +kernel)))
    · exact Or.inl he
  have c1517 : s 19 ≠ 1 ∨ s 0 = 0 ∨ s 0 = 2 := by
    by_cases he : s 19 = 1
    · exact Or.inr ((row1 (s 0)).mp (he ▸ hs 19 0 (by decide +kernel)))
    · exact Or.inl he
  have c1518 : s 19 ≠ 2 ∨ s 0 = 0 ∨ s 0 = 1 := by
    by_cases he : s 19 = 2
    · exact Or.inr ((row2 (s 0)).mp (he ▸ hs 19 0 (by decide +kernel)))
    · exact Or.inl he
  have c1522 : s 19 ≠ 1 ∨ s 36 = 0 ∨ s 36 = 2 := by
    by_cases he : s 19 = 1
    · exact Or.inr ((row1 (s 36)).mp (he ▸ hs 19 36 (by decide +kernel)))
    · exact Or.inl he
  have c1523 : s 19 ≠ 2 ∨ s 36 = 0 ∨ s 36 = 1 := by
    by_cases he : s 19 = 2
    · exact Or.inr ((row2 (s 36)).mp (he ▸ hs 19 36 (by decide +kernel)))
    · exact Or.inl he
  have c1526 : s 19 ≠ 0 ∨ s 5 = 1 ∨ s 5 = 2 ∨ s 5 = 3 := by
    by_cases he : s 19 = 0
    · exact Or.inr ((row0 (s 5)).mp (he ▸ hs 19 5 (by decide +kernel)))
    · exact Or.inl he
  have c1531 : s 19 ≠ 0 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 10 = 3 := by
    by_cases he : s 19 = 0
    · exact Or.inr ((row0 (s 10)).mp (he ▸ hs 19 10 (by decide +kernel)))
    · exact Or.inl he
  have c1532 : s 19 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2 := by
    by_cases he : s 19 = 1
    · exact Or.inr ((row1 (s 10)).mp (he ▸ hs 19 10 (by decide +kernel)))
    · exact Or.inl he
  have c1533 : s 19 ≠ 2 ∨ s 10 = 0 ∨ s 10 = 1 := by
    by_cases he : s 19 = 2
    · exact Or.inr ((row2 (s 10)).mp (he ▸ hs 19 10 (by decide +kernel)))
    · exact Or.inl he
  have c1534 : s 19 ≠ 3 ∨ s 10 = 0 ∨ s 10 = 4 := by
    by_cases he : s 19 = 3
    · exact Or.inr ((row3 (s 10)).mp (he ▸ hs 19 10 (by decide +kernel)))
    · exact Or.inl he
  have c1535 : s 19 ≠ 4 ∨ s 10 = 3 ∨ s 10 = 4 := by
    by_cases he : s 19 = 4
    · exact Or.inr ((row4 (s 10)).mp (he ▸ hs 19 10 (by decide +kernel)))
    · exact Or.inl he
  have c1536 : s 19 ≠ 0 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 50 = 3 := by
    by_cases he : s 19 = 0
    · exact Or.inr ((row0 (s 50)).mp (he ▸ hs 19 50 (by decide +kernel)))
    · exact Or.inl he
  have c1537 : s 19 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2 := by
    by_cases he : s 19 = 1
    · exact Or.inr ((row1 (s 50)).mp (he ▸ hs 19 50 (by decide +kernel)))
    · exact Or.inl he
  have c1538 : s 19 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1 := by
    by_cases he : s 19 = 2
    · exact Or.inr ((row2 (s 50)).mp (he ▸ hs 19 50 (by decide +kernel)))
    · exact Or.inl he
  have c1541 : s 19 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3 := by
    by_cases he : s 19 = 0
    · exact Or.inr ((row0 (s 51)).mp (he ▸ hs 19 51 (by decide +kernel)))
    · exact Or.inl he
  have c1542 : s 19 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2 := by
    by_cases he : s 19 = 1
    · exact Or.inr ((row1 (s 51)).mp (he ▸ hs 19 51 (by decide +kernel)))
    · exact Or.inl he
  have c1543 : s 19 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1 := by
    by_cases he : s 19 = 2
    · exact Or.inr ((row2 (s 51)).mp (he ▸ hs 19 51 (by decide +kernel)))
    · exact Or.inl he
  have c1544 : s 19 ≠ 3 ∨ s 51 = 0 ∨ s 51 = 4 := by
    by_cases he : s 19 = 3
    · exact Or.inr ((row3 (s 51)).mp (he ▸ hs 19 51 (by decide +kernel)))
    · exact Or.inl he
  have c1545 : s 19 ≠ 4 ∨ s 51 = 3 ∨ s 51 = 4 := by
    by_cases he : s 19 = 4
    · exact Or.inr ((row4 (s 51)).mp (he ▸ hs 19 51 (by decide +kernel)))
    · exact Or.inl he
  have c1546 : s 19 ≠ 0 ∨ s 52 = 1 ∨ s 52 = 2 ∨ s 52 = 3 := by
    by_cases he : s 19 = 0
    · exact Or.inr ((row0 (s 52)).mp (he ▸ hs 19 52 (by decide +kernel)))
    · exact Or.inl he
  have c1548 : s 19 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1 := by
    by_cases he : s 19 = 2
    · exact Or.inr ((row2 (s 52)).mp (he ▸ hs 19 52 (by decide +kernel)))
    · exact Or.inl he
  have c1549 : s 19 ≠ 3 ∨ s 52 = 0 ∨ s 52 = 4 := by
    by_cases he : s 19 = 3
    · exact Or.inr ((row3 (s 52)).mp (he ▸ hs 19 52 (by decide +kernel)))
    · exact Or.inl he
  have c1576 : s 20 ≠ 0 ∨ s 3 = 1 ∨ s 3 = 2 ∨ s 3 = 3 := by
    by_cases he : s 20 = 0
    · exact Or.inr ((row0 (s 3)).mp (he ▸ hs 20 3 (by decide +kernel)))
    · exact Or.inl he
  have c1577 : s 20 ≠ 1 ∨ s 3 = 0 ∨ s 3 = 2 := by
    by_cases he : s 20 = 1
    · exact Or.inr ((row1 (s 3)).mp (he ▸ hs 20 3 (by decide +kernel)))
    · exact Or.inl he
  have c1578 : s 20 ≠ 2 ∨ s 3 = 0 ∨ s 3 = 1 := by
    by_cases he : s 20 = 2
    · exact Or.inr ((row2 (s 3)).mp (he ▸ hs 20 3 (by decide +kernel)))
    · exact Or.inl he
  have c1587 : s 20 ≠ 1 ∨ s 33 = 0 ∨ s 33 = 2 := by
    by_cases he : s 20 = 1
    · exact Or.inr ((row1 (s 33)).mp (he ▸ hs 20 33 (by decide +kernel)))
    · exact Or.inl he
  have c1588 : s 20 ≠ 2 ∨ s 33 = 0 ∨ s 33 = 1 := by
    by_cases he : s 20 = 2
    · exact Or.inr ((row2 (s 33)).mp (he ▸ hs 20 33 (by decide +kernel)))
    · exact Or.inl he
  have c1596 : s 20 ≠ 0 ∨ s 41 = 1 ∨ s 41 = 2 ∨ s 41 = 3 := by
    by_cases he : s 20 = 0
    · exact Or.inr ((row0 (s 41)).mp (he ▸ hs 20 41 (by decide +kernel)))
    · exact Or.inl he
  have c1597 : s 20 ≠ 1 ∨ s 41 = 0 ∨ s 41 = 2 := by
    by_cases he : s 20 = 1
    · exact Or.inr ((row1 (s 41)).mp (he ▸ hs 20 41 (by decide +kernel)))
    · exact Or.inl he
  have c1598 : s 20 ≠ 2 ∨ s 41 = 0 ∨ s 41 = 1 := by
    by_cases he : s 20 = 2
    · exact Or.inr ((row2 (s 41)).mp (he ▸ hs 20 41 (by decide +kernel)))
    · exact Or.inl he
  have c1603 : s 20 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1 := by
    by_cases he : s 20 = 2
    · exact Or.inr ((row2 (s 52)).mp (he ▸ hs 20 52 (by decide +kernel)))
    · exact Or.inl he
  have c1606 : s 21 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3 := by
    by_cases he : s 21 = 0
    · exact Or.inr ((row0 (s 32)).mp (he ▸ hs 21 32 (by decide +kernel)))
    · exact Or.inl he
  have c1607 : s 21 ≠ 1 ∨ s 32 = 0 ∨ s 32 = 2 := by
    by_cases he : s 21 = 1
    · exact Or.inr ((row1 (s 32)).mp (he ▸ hs 21 32 (by decide +kernel)))
    · exact Or.inl he
  have c1608 : s 21 ≠ 2 ∨ s 32 = 0 ∨ s 32 = 1 := by
    by_cases he : s 21 = 2
    · exact Or.inr ((row2 (s 32)).mp (he ▸ hs 21 32 (by decide +kernel)))
    · exact Or.inl he
  have c1609 : s 21 ≠ 3 ∨ s 32 = 0 ∨ s 32 = 4 := by
    by_cases he : s 21 = 3
    · exact Or.inr ((row3 (s 32)).mp (he ▸ hs 21 32 (by decide +kernel)))
    · exact Or.inl he
  have c1617 : s 21 ≠ 1 ∨ s 33 = 0 ∨ s 33 = 2 := by
    by_cases he : s 21 = 1
    · exact Or.inr ((row1 (s 33)).mp (he ▸ hs 21 33 (by decide +kernel)))
    · exact Or.inl he
  have c1621 : s 21 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3 := by
    by_cases he : s 21 = 0
    · exact Or.inr ((row0 (s 34)).mp (he ▸ hs 21 34 (by decide +kernel)))
    · exact Or.inl he
  have c1622 : s 21 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2 := by
    by_cases he : s 21 = 1
    · exact Or.inr ((row1 (s 34)).mp (he ▸ hs 21 34 (by decide +kernel)))
    · exact Or.inl he
  have c1623 : s 21 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1 := by
    by_cases he : s 21 = 2
    · exact Or.inr ((row2 (s 34)).mp (he ▸ hs 21 34 (by decide +kernel)))
    · exact Or.inl he
  have c1624 : s 21 ≠ 3 ∨ s 34 = 0 ∨ s 34 = 4 := by
    by_cases he : s 21 = 3
    · exact Or.inr ((row3 (s 34)).mp (he ▸ hs 21 34 (by decide +kernel)))
    · exact Or.inl he
  have c1625 : s 21 ≠ 4 ∨ s 34 = 3 ∨ s 34 = 4 := by
    by_cases he : s 21 = 4
    · exact Or.inr ((row4 (s 34)).mp (he ▸ hs 21 34 (by decide +kernel)))
    · exact Or.inl he
  have c1628 : s 21 ≠ 2 ∨ s 37 = 0 ∨ s 37 = 1 := by
    by_cases he : s 21 = 2
    · exact Or.inr ((row2 (s 37)).mp (he ▸ hs 21 37 (by decide +kernel)))
    · exact Or.inl he
  have c1631 : s 21 ≠ 0 ∨ s 41 = 1 ∨ s 41 = 2 ∨ s 41 = 3 := by
    by_cases he : s 21 = 0
    · exact Or.inr ((row0 (s 41)).mp (he ▸ hs 21 41 (by decide +kernel)))
    · exact Or.inl he
  have c1636 : s 21 ≠ 0 ∨ s 52 = 1 ∨ s 52 = 2 ∨ s 52 = 3 := by
    by_cases he : s 21 = 0
    · exact Or.inr ((row0 (s 52)).mp (he ▸ hs 21 52 (by decide +kernel)))
    · exact Or.inl he
  have c1637 : s 21 ≠ 1 ∨ s 52 = 0 ∨ s 52 = 2 := by
    by_cases he : s 21 = 1
    · exact Or.inr ((row1 (s 52)).mp (he ▸ hs 21 52 (by decide +kernel)))
    · exact Or.inl he
  have c1638 : s 21 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1 := by
    by_cases he : s 21 = 2
    · exact Or.inr ((row2 (s 52)).mp (he ▸ hs 21 52 (by decide +kernel)))
    · exact Or.inl he
  have c1639 : s 21 ≠ 3 ∨ s 52 = 0 ∨ s 52 = 4 := by
    by_cases he : s 21 = 3
    · exact Or.inr ((row3 (s 52)).mp (he ▸ hs 21 52 (by decide +kernel)))
    · exact Or.inl he
  have c1641 : s 21 ≠ 0 ∨ s 30 = 1 ∨ s 30 = 2 ∨ s 30 = 3 := by
    by_cases he : s 21 = 0
    · exact Or.inr ((row0 (s 30)).mp (he ▸ hs 21 30 (by decide +kernel)))
    · exact Or.inl he
  have c1643 : s 21 ≠ 2 ∨ s 30 = 0 ∨ s 30 = 1 := by
    by_cases he : s 21 = 2
    · exact Or.inr ((row2 (s 30)).mp (he ▸ hs 21 30 (by decide +kernel)))
    · exact Or.inl he
  have c1656 : s 22 ≠ 0 ∨ s 33 = 1 ∨ s 33 = 2 ∨ s 33 = 3 := by
    by_cases he : s 22 = 0
    · exact Or.inr ((row0 (s 33)).mp (he ▸ hs 22 33 (by decide +kernel)))
    · exact Or.inl he
  have c1657 : s 22 ≠ 1 ∨ s 33 = 0 ∨ s 33 = 2 := by
    by_cases he : s 22 = 1
    · exact Or.inr ((row1 (s 33)).mp (he ▸ hs 22 33 (by decide +kernel)))
    · exact Or.inl he
  have c1658 : s 22 ≠ 2 ∨ s 33 = 0 ∨ s 33 = 1 := by
    by_cases he : s 22 = 2
    · exact Or.inr ((row2 (s 33)).mp (he ▸ hs 22 33 (by decide +kernel)))
    · exact Or.inl he
  have c1666 : s 22 ≠ 0 ∨ s 36 = 1 ∨ s 36 = 2 ∨ s 36 = 3 := by
    by_cases he : s 22 = 0
    · exact Or.inr ((row0 (s 36)).mp (he ▸ hs 22 36 (by decide +kernel)))
    · exact Or.inl he
  have c1682 : s 22 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2 := by
    by_cases he : s 22 = 1
    · exact Or.inr ((row1 (s 39)).mp (he ▸ hs 22 39 (by decide +kernel)))
    · exact Or.inl he
  have c1683 : s 22 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1 := by
    by_cases he : s 22 = 2
    · exact Or.inr ((row2 (s 39)).mp (he ▸ hs 22 39 (by decide +kernel)))
    · exact Or.inl he
  have c1687 : s 22 ≠ 1 ∨ s 41 = 0 ∨ s 41 = 2 := by
    by_cases he : s 22 = 1
    · exact Or.inr ((row1 (s 41)).mp (he ▸ hs 22 41 (by decide +kernel)))
    · exact Or.inl he
  have c1691 : s 22 ≠ 0 ∨ s 52 = 1 ∨ s 52 = 2 ∨ s 52 = 3 := by
    by_cases he : s 22 = 0
    · exact Or.inr ((row0 (s 52)).mp (he ▸ hs 22 52 (by decide +kernel)))
    · exact Or.inl he
  have c1692 : s 22 ≠ 1 ∨ s 52 = 0 ∨ s 52 = 2 := by
    by_cases he : s 22 = 1
    · exact Or.inr ((row1 (s 52)).mp (he ▸ hs 22 52 (by decide +kernel)))
    · exact Or.inl he
  have c1693 : s 22 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1 := by
    by_cases he : s 22 = 2
    · exact Or.inr ((row2 (s 52)).mp (he ▸ hs 22 52 (by decide +kernel)))
    · exact Or.inl he
  have c1694 : s 22 ≠ 3 ∨ s 52 = 0 ∨ s 52 = 4 := by
    by_cases he : s 22 = 3
    · exact Or.inr ((row3 (s 52)).mp (he ▸ hs 22 52 (by decide +kernel)))
    · exact Or.inl he
  have c1701 : s 23 ≠ 0 ∨ s 33 = 1 ∨ s 33 = 2 ∨ s 33 = 3 := by
    by_cases he : s 23 = 0
    · exact Or.inr ((row0 (s 33)).mp (he ▸ hs 23 33 (by decide +kernel)))
    · exact Or.inl he
  have c1702 : s 23 ≠ 1 ∨ s 33 = 0 ∨ s 33 = 2 := by
    by_cases he : s 23 = 1
    · exact Or.inr ((row1 (s 33)).mp (he ▸ hs 23 33 (by decide +kernel)))
    · exact Or.inl he
  have c1703 : s 23 ≠ 2 ∨ s 33 = 0 ∨ s 33 = 1 := by
    by_cases he : s 23 = 2
    · exact Or.inr ((row2 (s 33)).mp (he ▸ hs 23 33 (by decide +kernel)))
    · exact Or.inl he
  have c1713 : s 23 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1 := by
    by_cases he : s 23 = 2
    · exact Or.inr ((row2 (s 40)).mp (he ▸ hs 23 40 (by decide +kernel)))
    · exact Or.inl he
  have c1727 : s 23 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2 := by
    by_cases he : s 23 = 1
    · exact Or.inr ((row1 (s 43)).mp (he ▸ hs 23 43 (by decide +kernel)))
    · exact Or.inl he
  have c1728 : s 23 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1 := by
    by_cases he : s 23 = 2
    · exact Or.inr ((row2 (s 43)).mp (he ▸ hs 23 43 (by decide +kernel)))
    · exact Or.inl he
  have c1732 : s 23 ≠ 1 ∨ s 44 = 0 ∨ s 44 = 2 := by
    by_cases he : s 23 = 1
    · exact Or.inr ((row1 (s 44)).mp (he ▸ hs 23 44 (by decide +kernel)))
    · exact Or.inl he
  have c1734 : s 23 ≠ 3 ∨ s 44 = 0 ∨ s 44 = 4 := by
    by_cases he : s 23 = 3
    · exact Or.inr ((row3 (s 44)).mp (he ▸ hs 23 44 (by decide +kernel)))
    · exact Or.inl he
  have c1736 : s 23 ≠ 0 ∨ s 52 = 1 ∨ s 52 = 2 ∨ s 52 = 3 := by
    by_cases he : s 23 = 0
    · exact Or.inr ((row0 (s 52)).mp (he ▸ hs 23 52 (by decide +kernel)))
    · exact Or.inl he
  have c1737 : s 23 ≠ 1 ∨ s 52 = 0 ∨ s 52 = 2 := by
    by_cases he : s 23 = 1
    · exact Or.inr ((row1 (s 52)).mp (he ▸ hs 23 52 (by decide +kernel)))
    · exact Or.inl he
  have c1738 : s 23 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1 := by
    by_cases he : s 23 = 2
    · exact Or.inr ((row2 (s 52)).mp (he ▸ hs 23 52 (by decide +kernel)))
    · exact Or.inl he
  have c1747 : s 24 ≠ 1 ∨ s 33 = 0 ∨ s 33 = 2 := by
    by_cases he : s 24 = 1
    · exact Or.inr ((row1 (s 33)).mp (he ▸ hs 24 33 (by decide +kernel)))
    · exact Or.inl he
  have c1748 : s 24 ≠ 2 ∨ s 33 = 0 ∨ s 33 = 1 := by
    by_cases he : s 24 = 2
    · exact Or.inr ((row2 (s 33)).mp (he ▸ hs 24 33 (by decide +kernel)))
    · exact Or.inl he
  have c1751 : s 24 ≠ 0 ∨ s 37 = 1 ∨ s 37 = 2 ∨ s 37 = 3 := by
    by_cases he : s 24 = 0
    · exact Or.inr ((row0 (s 37)).mp (he ▸ hs 24 37 (by decide +kernel)))
    · exact Or.inl he
  have c1753 : s 24 ≠ 2 ∨ s 37 = 0 ∨ s 37 = 1 := by
    by_cases he : s 24 = 2
    · exact Or.inr ((row2 (s 37)).mp (he ▸ hs 24 37 (by decide +kernel)))
    · exact Or.inl he
  have c1756 : s 24 ≠ 0 ∨ s 41 = 1 ∨ s 41 = 2 ∨ s 41 = 3 := by
    by_cases he : s 24 = 0
    · exact Or.inr ((row0 (s 41)).mp (he ▸ hs 24 41 (by decide +kernel)))
    · exact Or.inl he
  have c1757 : s 24 ≠ 1 ∨ s 41 = 0 ∨ s 41 = 2 := by
    by_cases he : s 24 = 1
    · exact Or.inr ((row1 (s 41)).mp (he ▸ hs 24 41 (by decide +kernel)))
    · exact Or.inl he
  have c1758 : s 24 ≠ 2 ∨ s 41 = 0 ∨ s 41 = 1 := by
    by_cases he : s 24 = 2
    · exact Or.inr ((row2 (s 41)).mp (he ▸ hs 24 41 (by decide +kernel)))
    · exact Or.inl he
  have c1761 : s 24 ≠ 0 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 50 = 3 := by
    by_cases he : s 24 = 0
    · exact Or.inr ((row0 (s 50)).mp (he ▸ hs 24 50 (by decide +kernel)))
    · exact Or.inl he
  have c1762 : s 24 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2 := by
    by_cases he : s 24 = 1
    · exact Or.inr ((row1 (s 50)).mp (he ▸ hs 24 50 (by decide +kernel)))
    · exact Or.inl he
  have c1763 : s 24 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1 := by
    by_cases he : s 24 = 2
    · exact Or.inr ((row2 (s 50)).mp (he ▸ hs 24 50 (by decide +kernel)))
    · exact Or.inl he
  have c1766 : s 24 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3 := by
    by_cases he : s 24 = 0
    · exact Or.inr ((row0 (s 51)).mp (he ▸ hs 24 51 (by decide +kernel)))
    · exact Or.inl he
  have c1768 : s 24 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1 := by
    by_cases he : s 24 = 2
    · exact Or.inr ((row2 (s 51)).mp (he ▸ hs 24 51 (by decide +kernel)))
    · exact Or.inl he
  have c1769 : s 24 ≠ 3 ∨ s 51 = 0 ∨ s 51 = 4 := by
    by_cases he : s 24 = 3
    · exact Or.inr ((row3 (s 51)).mp (he ▸ hs 24 51 (by decide +kernel)))
    · exact Or.inl he
  have c1773 : s 24 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1 := by
    by_cases he : s 24 = 2
    · exact Or.inr ((row2 (s 52)).mp (he ▸ hs 24 52 (by decide +kernel)))
    · exact Or.inl he
  have c1801 : s 25 ≠ 0 ∨ s 3 = 1 ∨ s 3 = 2 ∨ s 3 = 3 := by
    by_cases he : s 25 = 0
    · exact Or.inr ((row0 (s 3)).mp (he ▸ hs 25 3 (by decide +kernel)))
    · exact Or.inl he
  have c1802 : s 25 ≠ 1 ∨ s 3 = 0 ∨ s 3 = 2 := by
    by_cases he : s 25 = 1
    · exact Or.inr ((row1 (s 3)).mp (he ▸ hs 25 3 (by decide +kernel)))
    · exact Or.inl he
  have c1803 : s 25 ≠ 2 ∨ s 3 = 0 ∨ s 3 = 1 := by
    by_cases he : s 25 = 2
    · exact Or.inr ((row2 (s 3)).mp (he ▸ hs 25 3 (by decide +kernel)))
    · exact Or.inl he
  have c1808 : s 25 ≠ 2 ∨ s 4 = 0 ∨ s 4 = 1 := by
    by_cases he : s 25 = 2
    · exact Or.inr ((row2 (s 4)).mp (he ▸ hs 25 4 (by decide +kernel)))
    · exact Or.inl he
  have c1812 : s 25 ≠ 1 ∨ s 38 = 0 ∨ s 38 = 2 := by
    by_cases he : s 25 = 1
    · exact Or.inr ((row1 (s 38)).mp (he ▸ hs 25 38 (by decide +kernel)))
    · exact Or.inl he
  have c1813 : s 25 ≠ 2 ∨ s 38 = 0 ∨ s 38 = 1 := by
    by_cases he : s 25 = 2
    · exact Or.inr ((row2 (s 38)).mp (he ▸ hs 25 38 (by decide +kernel)))
    · exact Or.inl he
  have c1823 : s 25 ≠ 2 ∨ s 53 = 0 ∨ s 53 = 1 := by
    by_cases he : s 25 = 2
    · exact Or.inr ((row2 (s 53)).mp (he ▸ hs 25 53 (by decide +kernel)))
    · exact Or.inl he
  have c1827 : s 25 ≠ 1 ∨ s 56 = 0 ∨ s 56 = 2 := by
    by_cases he : s 25 = 1
    · exact Or.inr ((row1 (s 56)).mp (he ▸ hs 25 56 (by decide +kernel)))
    · exact Or.inl he
  have c1828 : s 25 ≠ 2 ∨ s 56 = 0 ∨ s 56 = 1 := by
    by_cases he : s 25 = 2
    · exact Or.inr ((row2 (s 56)).mp (he ▸ hs 25 56 (by decide +kernel)))
    · exact Or.inl he
  have c1833 : s 26 ≠ 2 ∨ s 2 = 0 ∨ s 2 = 1 := by
    by_cases he : s 26 = 2
    · exact Or.inr ((row2 (s 2)).mp (he ▸ hs 26 2 (by decide +kernel)))
    · exact Or.inl he
  have c1856 : s 26 ≠ 0 ∨ s 39 = 1 ∨ s 39 = 2 ∨ s 39 = 3 := by
    by_cases he : s 26 = 0
    · exact Or.inr ((row0 (s 39)).mp (he ▸ hs 26 39 (by decide +kernel)))
    · exact Or.inl he
  have c1857 : s 26 ≠ 1 ∨ s 39 = 0 ∨ s 39 = 2 := by
    by_cases he : s 26 = 1
    · exact Or.inr ((row1 (s 39)).mp (he ▸ hs 26 39 (by decide +kernel)))
    · exact Or.inl he
  have c1858 : s 26 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1 := by
    by_cases he : s 26 = 2
    · exact Or.inr ((row2 (s 39)).mp (he ▸ hs 26 39 (by decide +kernel)))
    · exact Or.inl he
  have c1860 : s 26 ≠ 4 ∨ s 39 = 3 ∨ s 39 = 4 := by
    by_cases he : s 26 = 4
    · exact Or.inr ((row4 (s 39)).mp (he ▸ hs 26 39 (by decide +kernel)))
    · exact Or.inl he
  have c1862 : s 26 ≠ 1 ∨ s 48 = 0 ∨ s 48 = 2 := by
    by_cases he : s 26 = 1
    · exact Or.inr ((row1 (s 48)).mp (he ▸ hs 26 48 (by decide +kernel)))
    · exact Or.inl he
  have c1874 : s 26 ≠ 3 ∨ s 56 = 0 ∨ s 56 = 4 := by
    by_cases he : s 26 = 3
    · exact Or.inr ((row3 (s 56)).mp (he ▸ hs 26 56 (by decide +kernel)))
    · exact Or.inl he
  have c1882 : s 27 ≠ 1 ∨ s 38 = 0 ∨ s 38 = 2 := by
    by_cases he : s 27 = 1
    · exact Or.inr ((row1 (s 38)).mp (he ▸ hs 27 38 (by decide +kernel)))
    · exact Or.inl he
  have c1883 : s 27 ≠ 2 ∨ s 38 = 0 ∨ s 38 = 1 := by
    by_cases he : s 27 = 2
    · exact Or.inr ((row2 (s 38)).mp (he ▸ hs 27 38 (by decide +kernel)))
    · exact Or.inl he
  have c1887 : s 27 ≠ 1 ∨ s 45 = 0 ∨ s 45 = 2 := by
    by_cases he : s 27 = 1
    · exact Or.inr ((row1 (s 45)).mp (he ▸ hs 27 45 (by decide +kernel)))
    · exact Or.inl he
  have c1888 : s 27 ≠ 2 ∨ s 45 = 0 ∨ s 45 = 1 := by
    by_cases he : s 27 = 2
    · exact Or.inr ((row2 (s 45)).mp (he ▸ hs 27 45 (by decide +kernel)))
    · exact Or.inl he
  have c1896 : s 27 ≠ 0 ∨ s 47 = 1 ∨ s 47 = 2 ∨ s 47 = 3 := by
    by_cases he : s 27 = 0
    · exact Or.inr ((row0 (s 47)).mp (he ▸ hs 27 47 (by decide +kernel)))
    · exact Or.inl he
  have c1897 : s 27 ≠ 1 ∨ s 47 = 0 ∨ s 47 = 2 := by
    by_cases he : s 27 = 1
    · exact Or.inr ((row1 (s 47)).mp (he ▸ hs 27 47 (by decide +kernel)))
    · exact Or.inl he
  have c1898 : s 27 ≠ 2 ∨ s 47 = 0 ∨ s 47 = 1 := by
    by_cases he : s 27 = 2
    · exact Or.inr ((row2 (s 47)).mp (he ▸ hs 27 47 (by decide +kernel)))
    · exact Or.inl he
  have c1900 : s 27 ≠ 4 ∨ s 47 = 3 ∨ s 47 = 4 := by
    by_cases he : s 27 = 4
    · exact Or.inr ((row4 (s 47)).mp (he ▸ hs 27 47 (by decide +kernel)))
    · exact Or.inl he
  have c1917 : s 27 ≠ 1 ∨ s 56 = 0 ∨ s 56 = 2 := by
    by_cases he : s 27 = 1
    · exact Or.inr ((row1 (s 56)).mp (he ▸ hs 27 56 (by decide +kernel)))
    · exact Or.inl he
  have c1918 : s 27 ≠ 2 ∨ s 56 = 0 ∨ s 56 = 1 := by
    by_cases he : s 27 = 2
    · exact Or.inr ((row2 (s 56)).mp (he ▸ hs 27 56 (by decide +kernel)))
    · exact Or.inl he
  have c1927 : s 28 ≠ 1 ∨ s 38 = 0 ∨ s 38 = 2 := by
    by_cases he : s 28 = 1
    · exact Or.inr ((row1 (s 38)).mp (he ▸ hs 28 38 (by decide +kernel)))
    · exact Or.inl he
  have c1928 : s 28 ≠ 2 ∨ s 38 = 0 ∨ s 38 = 1 := by
    by_cases he : s 28 = 2
    · exact Or.inr ((row2 (s 38)).mp (he ▸ hs 28 38 (by decide +kernel)))
    · exact Or.inl he
  have c1936 : s 28 ≠ 0 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 50 = 3 := by
    by_cases he : s 28 = 0
    · exact Or.inr ((row0 (s 50)).mp (he ▸ hs 28 50 (by decide +kernel)))
    · exact Or.inl he
  have c1937 : s 28 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2 := by
    by_cases he : s 28 = 1
    · exact Or.inr ((row1 (s 50)).mp (he ▸ hs 28 50 (by decide +kernel)))
    · exact Or.inl he
  have c1938 : s 28 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1 := by
    by_cases he : s 28 = 2
    · exact Or.inr ((row2 (s 50)).mp (he ▸ hs 28 50 (by decide +kernel)))
    · exact Or.inl he
  have c1940 : s 28 ≠ 4 ∨ s 50 = 3 ∨ s 50 = 4 := by
    by_cases he : s 28 = 4
    · exact Or.inr ((row4 (s 50)).mp (he ▸ hs 28 50 (by decide +kernel)))
    · exact Or.inl he
  have c1942 : s 28 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2 := by
    by_cases he : s 28 = 1
    · exact Or.inr ((row1 (s 51)).mp (he ▸ hs 28 51 (by decide +kernel)))
    · exact Or.inl he
  have c1943 : s 28 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1 := by
    by_cases he : s 28 = 2
    · exact Or.inr ((row2 (s 51)).mp (he ▸ hs 28 51 (by decide +kernel)))
    · exact Or.inl he
  have c1947 : s 28 ≠ 1 ∨ s 52 = 0 ∨ s 52 = 2 := by
    by_cases he : s 28 = 1
    · exact Or.inr ((row1 (s 52)).mp (he ▸ hs 28 52 (by decide +kernel)))
    · exact Or.inl he
  have c1948 : s 28 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1 := by
    by_cases he : s 28 = 2
    · exact Or.inr ((row2 (s 52)).mp (he ▸ hs 28 52 (by decide +kernel)))
    · exact Or.inl he
  have c1962 : s 28 ≠ 1 ∨ s 56 = 0 ∨ s 56 = 2 := by
    by_cases he : s 28 = 1
    · exact Or.inr ((row1 (s 56)).mp (he ▸ hs 28 56 (by decide +kernel)))
    · exact Or.inl he
  have c1963 : s 28 ≠ 2 ∨ s 56 = 0 ∨ s 56 = 1 := by
    by_cases he : s 28 = 2
    · exact Or.inr ((row2 (s 56)).mp (he ▸ hs 28 56 (by decide +kernel)))
    · exact Or.inl he
  have c1974 : s 29 ≠ 3 ∨ s 38 = 0 ∨ s 38 = 4 := by
    by_cases he : s 29 = 3
    · exact Or.inr ((row3 (s 38)).mp (he ▸ hs 29 38 (by decide +kernel)))
    · exact Or.inl he
  have c1986 : s 29 ≠ 0 ∨ s 55 = 1 ∨ s 55 = 2 ∨ s 55 = 3 := by
    by_cases he : s 29 = 0
    · exact Or.inr ((row0 (s 55)).mp (he ▸ hs 29 55 (by decide +kernel)))
    · exact Or.inl he
  have c1996 : s 29 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3 := by
    by_cases he : s 29 = 0
    · exact Or.inr ((row0 (s 57)).mp (he ▸ hs 29 57 (by decide +kernel)))
    · exact Or.inl he
  have c1997 : s 29 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2 := by
    by_cases he : s 29 = 1
    · exact Or.inr ((row1 (s 57)).mp (he ▸ hs 29 57 (by decide +kernel)))
    · exact Or.inl he
  have c1998 : s 29 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1 := by
    by_cases he : s 29 = 2
    · exact Or.inr ((row2 (s 57)).mp (he ▸ hs 29 57 (by decide +kernel)))
    · exact Or.inl he
  have c1999 : s 29 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4 := by
    by_cases he : s 29 = 3
    · exact Or.inr ((row3 (s 57)).mp (he ▸ hs 29 57 (by decide +kernel)))
    · exact Or.inl he
  have c2000 : s 29 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4 := by
    by_cases he : s 29 = 4
    · exact Or.inr ((row4 (s 57)).mp (he ▸ hs 29 57 (by decide +kernel)))
    · exact Or.inl he
  have c2004 : s 29 ≠ 3 ∨ s 58 = 0 ∨ s 58 = 4 := by
    by_cases he : s 29 = 3
    · exact Or.inr ((row3 (s 58)).mp (he ▸ hs 29 58 (by decide +kernel)))
    · exact Or.inl he
  have c2006 : s 29 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3 := by
    by_cases he : s 29 = 0
    · exact Or.inr ((row0 (s 59)).mp (he ▸ hs 29 59 (by decide +kernel)))
    · exact Or.inl he
  have c2007 : s 29 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2 := by
    by_cases he : s 29 = 1
    · exact Or.inr ((row1 (s 59)).mp (he ▸ hs 29 59 (by decide +kernel)))
    · exact Or.inl he
  have c2008 : s 29 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1 := by
    by_cases he : s 29 = 2
    · exact Or.inr ((row2 (s 59)).mp (he ▸ hs 29 59 (by decide +kernel)))
    · exact Or.inl he
  have c2009 : s 29 ≠ 3 ∨ s 59 = 0 ∨ s 59 = 4 := by
    by_cases he : s 29 = 3
    · exact Or.inr ((row3 (s 59)).mp (he ▸ hs 29 59 (by decide +kernel)))
    · exact Or.inl he
  have c2010 : s 29 ≠ 4 ∨ s 59 = 3 ∨ s 59 = 4 := by
    by_cases he : s 29 = 4
    · exact Or.inr ((row4 (s 59)).mp (he ▸ hs 29 59 (by decide +kernel)))
    · exact Or.inl he
  have c2021 : s 30 ≠ 0 ∨ s 2 = 1 ∨ s 2 = 2 ∨ s 2 = 3 := by
    by_cases he : s 30 = 0
    · exact Or.inr ((row0 (s 2)).mp (he ▸ hs 30 2 (by decide +kernel)))
    · exact Or.inl he
  have c2051 : s 30 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3 := by
    by_cases he : s 30 = 0
    · exact Or.inr ((row0 (s 57)).mp (he ▸ hs 30 57 (by decide +kernel)))
    · exact Or.inl he
  have c2052 : s 30 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2 := by
    by_cases he : s 30 = 1
    · exact Or.inr ((row1 (s 57)).mp (he ▸ hs 30 57 (by decide +kernel)))
    · exact Or.inl he
  have c2053 : s 30 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1 := by
    by_cases he : s 30 = 2
    · exact Or.inr ((row2 (s 57)).mp (he ▸ hs 30 57 (by decide +kernel)))
    · exact Or.inl he
  have c2054 : s 30 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4 := by
    by_cases he : s 30 = 3
    · exact Or.inr ((row3 (s 57)).mp (he ▸ hs 30 57 (by decide +kernel)))
    · exact Or.inl he
  have c2061 : s 31 ≠ 0 ∨ s 5 = 1 ∨ s 5 = 2 ∨ s 5 = 3 := by
    by_cases he : s 31 = 0
    · exact Or.inr ((row0 (s 5)).mp (he ▸ hs 31 5 (by decide +kernel)))
    · exact Or.inl he
  have c2078 : s 31 ≠ 2 ∨ s 8 = 0 ∨ s 8 = 1 := by
    by_cases he : s 31 = 2
    · exact Or.inr ((row2 (s 8)).mp (he ▸ hs 31 8 (by decide +kernel)))
    · exact Or.inl he
  have c2086 : s 31 ≠ 0 ∨ s 11 = 1 ∨ s 11 = 2 ∨ s 11 = 3 := by
    by_cases he : s 31 = 0
    · exact Or.inr ((row0 (s 11)).mp (he ▸ hs 31 11 (by decide +kernel)))
    · exact Or.inl he
  have c2088 : s 31 ≠ 2 ∨ s 11 = 0 ∨ s 11 = 1 := by
    by_cases he : s 31 = 2
    · exact Or.inr ((row2 (s 11)).mp (he ▸ hs 31 11 (by decide +kernel)))
    · exact Or.inl he
  have c2093 : s 31 ≠ 2 ∨ s 21 = 0 ∨ s 21 = 1 := by
    by_cases he : s 31 = 2
    · exact Or.inr ((row2 (s 21)).mp (he ▸ hs 31 21 (by decide +kernel)))
    · exact Or.inl he
  have c2096 : s 31 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3 := by
    by_cases he : s 31 = 0
    · exact Or.inr ((row0 (s 57)).mp (he ▸ hs 31 57 (by decide +kernel)))
    · exact Or.inl he
  have c2097 : s 31 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2 := by
    by_cases he : s 31 = 1
    · exact Or.inr ((row1 (s 57)).mp (he ▸ hs 31 57 (by decide +kernel)))
    · exact Or.inl he
  have c2098 : s 31 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1 := by
    by_cases he : s 31 = 2
    · exact Or.inr ((row2 (s 57)).mp (he ▸ hs 31 57 (by decide +kernel)))
    · exact Or.inl he
  have c2099 : s 31 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4 := by
    by_cases he : s 31 = 3
    · exact Or.inr ((row3 (s 57)).mp (he ▸ hs 31 57 (by decide +kernel)))
    · exact Or.inl he
  have c2100 : s 31 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4 := by
    by_cases he : s 31 = 4
    · exact Or.inr ((row4 (s 57)).mp (he ▸ hs 31 57 (by decide +kernel)))
    · exact Or.inl he
  have c2111 : s 32 ≠ 0 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 10 = 3 := by
    by_cases he : s 32 = 0
    · exact Or.inr ((row0 (s 10)).mp (he ▸ hs 32 10 (by decide +kernel)))
    · exact Or.inl he
  have c2126 : s 32 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3 := by
    by_cases he : s 32 = 0
    · exact Or.inr ((row0 (s 13)).mp (he ▸ hs 32 13 (by decide +kernel)))
    · exact Or.inl he
  have c2127 : s 32 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2 := by
    by_cases he : s 32 = 1
    · exact Or.inr ((row1 (s 13)).mp (he ▸ hs 32 13 (by decide +kernel)))
    · exact Or.inl he
  have c2131 : s 32 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3 := by
    by_cases he : s 32 = 0
    · exact Or.inr ((row0 (s 14)).mp (he ▸ hs 32 14 (by decide +kernel)))
    · exact Or.inl he
  have c2132 : s 32 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2 := by
    by_cases he : s 32 = 1
    · exact Or.inr ((row1 (s 14)).mp (he ▸ hs 32 14 (by decide +kernel)))
    · exact Or.inl he
  have c2133 : s 32 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1 := by
    by_cases he : s 32 = 2
    · exact Or.inr ((row2 (s 14)).mp (he ▸ hs 32 14 (by decide +kernel)))
    · exact Or.inl he
  have c2134 : s 32 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4 := by
    by_cases he : s 32 = 3
    · exact Or.inr ((row3 (s 14)).mp (he ▸ hs 32 14 (by decide +kernel)))
    · exact Or.inl he
  have c2135 : s 32 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4 := by
    by_cases he : s 32 = 4
    · exact Or.inr ((row4 (s 14)).mp (he ▸ hs 32 14 (by decide +kernel)))
    · exact Or.inl he
  have c2141 : s 32 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3 := by
    by_cases he : s 32 = 0
    · exact Or.inr ((row0 (s 57)).mp (he ▸ hs 32 57 (by decide +kernel)))
    · exact Or.inl he
  have c2142 : s 32 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2 := by
    by_cases he : s 32 = 1
    · exact Or.inr ((row1 (s 57)).mp (he ▸ hs 32 57 (by decide +kernel)))
    · exact Or.inl he
  have c2143 : s 32 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1 := by
    by_cases he : s 32 = 2
    · exact Or.inr ((row2 (s 57)).mp (he ▸ hs 32 57 (by decide +kernel)))
    · exact Or.inl he
  have c2144 : s 32 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4 := by
    by_cases he : s 32 = 3
    · exact Or.inr ((row3 (s 57)).mp (he ▸ hs 32 57 (by decide +kernel)))
    · exact Or.inl he
  have c2145 : s 32 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4 := by
    by_cases he : s 32 = 4
    · exact Or.inr ((row4 (s 57)).mp (he ▸ hs 32 57 (by decide +kernel)))
    · exact Or.inl he
  have c2158 : s 33 ≠ 2 ∨ s 11 = 0 ∨ s 11 = 1 := by
    by_cases he : s 33 = 2
    · exact Or.inr ((row2 (s 11)).mp (he ▸ hs 33 11 (by decide +kernel)))
    · exact Or.inl he
  have c2173 : s 33 ≠ 2 ∨ s 22 = 0 ∨ s 22 = 1 := by
    by_cases he : s 33 = 2
    · exact Or.inr ((row2 (s 22)).mp (he ▸ hs 33 22 (by decide +kernel)))
    · exact Or.inl he
  have c2186 : s 33 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3 := by
    by_cases he : s 33 = 0
    · exact Or.inr ((row0 (s 57)).mp (he ▸ hs 33 57 (by decide +kernel)))
    · exact Or.inl he
  have c2187 : s 33 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2 := by
    by_cases he : s 33 = 1
    · exact Or.inr ((row1 (s 57)).mp (he ▸ hs 33 57 (by decide +kernel)))
    · exact Or.inl he
  have c2188 : s 33 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1 := by
    by_cases he : s 33 = 2
    · exact Or.inr ((row2 (s 57)).mp (he ▸ hs 33 57 (by decide +kernel)))
    · exact Or.inl he
  have c2189 : s 33 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4 := by
    by_cases he : s 33 = 3
    · exact Or.inr ((row3 (s 57)).mp (he ▸ hs 33 57 (by decide +kernel)))
    · exact Or.inl he
  have c2191 : s 34 ≠ 0 ∨ s 3 = 1 ∨ s 3 = 2 ∨ s 3 = 3 := by
    by_cases he : s 34 = 0
    · exact Or.inr ((row0 (s 3)).mp (he ▸ hs 34 3 (by decide +kernel)))
    · exact Or.inl he
  have c2202 : s 34 ≠ 1 ∨ s 11 = 0 ∨ s 11 = 2 := by
    by_cases he : s 34 = 1
    · exact Or.inr ((row1 (s 11)).mp (he ▸ hs 34 11 (by decide +kernel)))
    · exact Or.inl he
  have c2203 : s 34 ≠ 2 ∨ s 11 = 0 ∨ s 11 = 1 := by
    by_cases he : s 34 = 2
    · exact Or.inr ((row2 (s 11)).mp (he ▸ hs 34 11 (by decide +kernel)))
    · exact Or.inl he
  have c2206 : s 34 ≠ 0 ∨ s 21 = 1 ∨ s 21 = 2 ∨ s 21 = 3 := by
    by_cases he : s 34 = 0
    · exact Or.inr ((row0 (s 21)).mp (he ▸ hs 34 21 (by decide +kernel)))
    · exact Or.inl he
  have c2207 : s 34 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2 := by
    by_cases he : s 34 = 1
    · exact Or.inr ((row1 (s 21)).mp (he ▸ hs 34 21 (by decide +kernel)))
    · exact Or.inl he
  have c2211 : s 34 ≠ 0 ∨ s 55 = 1 ∨ s 55 = 2 ∨ s 55 = 3 := by
    by_cases he : s 34 = 0
    · exact Or.inr ((row0 (s 55)).mp (he ▸ hs 34 55 (by decide +kernel)))
    · exact Or.inl he
  have c2213 : s 34 ≠ 2 ∨ s 55 = 0 ∨ s 55 = 1 := by
    by_cases he : s 34 = 2
    · exact Or.inr ((row2 (s 55)).mp (he ▸ hs 34 55 (by decide +kernel)))
    · exact Or.inl he
  have c2218 : s 34 ≠ 2 ∨ s 56 = 0 ∨ s 56 = 1 := by
    by_cases he : s 34 = 2
    · exact Or.inr ((row2 (s 56)).mp (he ▸ hs 34 56 (by decide +kernel)))
    · exact Or.inl he
  have c2221 : s 34 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3 := by
    by_cases he : s 34 = 0
    · exact Or.inr ((row0 (s 57)).mp (he ▸ hs 34 57 (by decide +kernel)))
    · exact Or.inl he
  have c2222 : s 34 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2 := by
    by_cases he : s 34 = 1
    · exact Or.inr ((row1 (s 57)).mp (he ▸ hs 34 57 (by decide +kernel)))
    · exact Or.inl he
  have c2223 : s 34 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1 := by
    by_cases he : s 34 = 2
    · exact Or.inr ((row2 (s 57)).mp (he ▸ hs 34 57 (by decide +kernel)))
    · exact Or.inl he
  have c2224 : s 34 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4 := by
    by_cases he : s 34 = 3
    · exact Or.inr ((row3 (s 57)).mp (he ▸ hs 34 57 (by decide +kernel)))
    · exact Or.inl he
  have c2225 : s 34 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4 := by
    by_cases he : s 34 = 4
    · exact Or.inr ((row4 (s 57)).mp (he ▸ hs 34 57 (by decide +kernel)))
    · exact Or.inl he
  have c2226 : s 34 ≠ 0 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 58 = 3 := by
    by_cases he : s 34 = 0
    · exact Or.inr ((row0 (s 58)).mp (he ▸ hs 34 58 (by decide +kernel)))
    · exact Or.inl he
  have c2229 : s 34 ≠ 3 ∨ s 58 = 0 ∨ s 58 = 4 := by
    by_cases he : s 34 = 3
    · exact Or.inr ((row3 (s 58)).mp (he ▸ hs 34 58 (by decide +kernel)))
    · exact Or.inl he
  have c2231 : s 34 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3 := by
    by_cases he : s 34 = 0
    · exact Or.inr ((row0 (s 59)).mp (he ▸ hs 34 59 (by decide +kernel)))
    · exact Or.inl he
  have c2232 : s 34 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2 := by
    by_cases he : s 34 = 1
    · exact Or.inr ((row1 (s 59)).mp (he ▸ hs 34 59 (by decide +kernel)))
    · exact Or.inl he
  have c2233 : s 34 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1 := by
    by_cases he : s 34 = 2
    · exact Or.inr ((row2 (s 59)).mp (he ▸ hs 34 59 (by decide +kernel)))
    · exact Or.inl he
  have c2234 : s 34 ≠ 3 ∨ s 59 = 0 ∨ s 59 = 4 := by
    by_cases he : s 34 = 3
    · exact Or.inr ((row3 (s 59)).mp (he ▸ hs 34 59 (by decide +kernel)))
    · exact Or.inl he
  have c2235 : s 34 ≠ 4 ∨ s 59 = 3 ∨ s 59 = 4 := by
    by_cases he : s 34 = 4
    · exact Or.inr ((row4 (s 59)).mp (he ▸ hs 34 59 (by decide +kernel)))
    · exact Or.inl he
  have c2237 : s 35 ≠ 1 ∨ s 58 = 0 ∨ s 58 = 2 := by
    by_cases he : s 35 = 1
    · exact Or.inr ((row1 (s 58)).mp (he ▸ hs 35 58 (by decide +kernel)))
    · exact Or.inl he
  have c2238 : s 35 ≠ 2 ∨ s 58 = 0 ∨ s 58 = 1 := by
    by_cases he : s 35 = 2
    · exact Or.inr ((row2 (s 58)).mp (he ▸ hs 35 58 (by decide +kernel)))
    · exact Or.inl he
  have c2247 : s 35 ≠ 1 ∨ s 6 = 0 ∨ s 6 = 2 := by
    by_cases he : s 35 = 1
    · exact Or.inr ((row1 (s 6)).mp (he ▸ hs 35 6 (by decide +kernel)))
    · exact Or.inl he
  have c2248 : s 35 ≠ 2 ∨ s 6 = 0 ∨ s 6 = 1 := by
    by_cases he : s 35 = 2
    · exact Or.inr ((row2 (s 6)).mp (he ▸ hs 35 6 (by decide +kernel)))
    · exact Or.inl he
  have c2281 : s 36 ≠ 0 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 58 = 3 := by
    by_cases he : s 36 = 0
    · exact Or.inr ((row0 (s 58)).mp (he ▸ hs 36 58 (by decide +kernel)))
    · exact Or.inl he
  have c2282 : s 36 ≠ 1 ∨ s 58 = 0 ∨ s 58 = 2 := by
    by_cases he : s 36 = 1
    · exact Or.inr ((row1 (s 58)).mp (he ▸ hs 36 58 (by decide +kernel)))
    · exact Or.inl he
  have c2283 : s 36 ≠ 2 ∨ s 58 = 0 ∨ s 58 = 1 := by
    by_cases he : s 36 = 2
    · exact Or.inr ((row2 (s 58)).mp (he ▸ hs 36 58 (by decide +kernel)))
    · exact Or.inl he
  have c2284 : s 36 ≠ 3 ∨ s 58 = 0 ∨ s 58 = 4 := by
    by_cases he : s 36 = 3
    · exact Or.inr ((row3 (s 58)).mp (he ▸ hs 36 58 (by decide +kernel)))
    · exact Or.inl he
  have c2286 : s 36 ≠ 0 ∨ s 7 = 1 ∨ s 7 = 2 ∨ s 7 = 3 := by
    by_cases he : s 36 = 0
    · exact Or.inr ((row0 (s 7)).mp (he ▸ hs 36 7 (by decide +kernel)))
    · exact Or.inl he
  have c2288 : s 36 ≠ 2 ∨ s 7 = 0 ∨ s 7 = 1 := by
    by_cases he : s 36 = 2
    · exact Or.inr ((row2 (s 7)).mp (he ▸ hs 36 7 (by decide +kernel)))
    · exact Or.inl he
  have c2291 : s 36 ≠ 0 ∨ s 15 = 1 ∨ s 15 = 2 ∨ s 15 = 3 := by
    by_cases he : s 36 = 0
    · exact Or.inr ((row0 (s 15)).mp (he ▸ hs 36 15 (by decide +kernel)))
    · exact Or.inl he
  have c2293 : s 36 ≠ 2 ∨ s 15 = 0 ∨ s 15 = 1 := by
    by_cases he : s 36 = 2
    · exact Or.inr ((row2 (s 15)).mp (he ▸ hs 36 15 (by decide +kernel)))
    · exact Or.inl he
  have c2298 : s 36 ≠ 2 ∨ s 16 = 0 ∨ s 16 = 1 := by
    by_cases he : s 36 = 2
    · exact Or.inr ((row2 (s 16)).mp (he ▸ hs 36 16 (by decide +kernel)))
    · exact Or.inl he
  have c2301 : s 36 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3 := by
    by_cases he : s 36 = 0
    · exact Or.inr ((row0 (s 17)).mp (he ▸ hs 36 17 (by decide +kernel)))
    · exact Or.inl he
  have c2302 : s 36 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2 := by
    by_cases he : s 36 = 1
    · exact Or.inr ((row1 (s 17)).mp (he ▸ hs 36 17 (by decide +kernel)))
    · exact Or.inl he
  have c2303 : s 36 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1 := by
    by_cases he : s 36 = 2
    · exact Or.inr ((row2 (s 17)).mp (he ▸ hs 36 17 (by decide +kernel)))
    · exact Or.inl he
  have c2304 : s 36 ≠ 3 ∨ s 17 = 0 ∨ s 17 = 4 := by
    by_cases he : s 36 = 3
    · exact Or.inr ((row3 (s 17)).mp (he ▸ hs 36 17 (by decide +kernel)))
    · exact Or.inl he
  have c2311 : s 36 ≠ 0 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 19 = 3 := by
    by_cases he : s 36 = 0
    · exact Or.inr ((row0 (s 19)).mp (he ▸ hs 36 19 (by decide +kernel)))
    · exact Or.inl he
  have c2312 : s 36 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2 := by
    by_cases he : s 36 = 1
    · exact Or.inr ((row1 (s 19)).mp (he ▸ hs 36 19 (by decide +kernel)))
    · exact Or.inl he
  have c2317 : s 36 ≠ 1 ∨ s 22 = 0 ∨ s 22 = 2 := by
    by_cases he : s 36 = 1
    · exact Or.inr ((row1 (s 22)).mp (he ▸ hs 36 22 (by decide +kernel)))
    · exact Or.inl he
  have c2318 : s 36 ≠ 2 ∨ s 22 = 0 ∨ s 22 = 1 := by
    by_cases he : s 36 = 2
    · exact Or.inr ((row2 (s 22)).mp (he ▸ hs 36 22 (by decide +kernel)))
    · exact Or.inl he
  have c2325 : s 36 ≠ 4 ∨ s 26 = 3 ∨ s 26 = 4 := by
    by_cases he : s 36 = 4
    · exact Or.inr ((row4 (s 26)).mp (he ▸ hs 36 26 (by decide +kernel)))
    · exact Or.inl he
  have c2326 : s 37 ≠ 0 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 58 = 3 := by
    by_cases he : s 37 = 0
    · exact Or.inr ((row0 (s 58)).mp (he ▸ hs 37 58 (by decide +kernel)))
    · exact Or.inl he
  have c2327 : s 37 ≠ 1 ∨ s 58 = 0 ∨ s 58 = 2 := by
    by_cases he : s 37 = 1
    · exact Or.inr ((row1 (s 58)).mp (he ▸ hs 37 58 (by decide +kernel)))
    · exact Or.inl he
  have c2328 : s 37 ≠ 2 ∨ s 58 = 0 ∨ s 58 = 1 := by
    by_cases he : s 37 = 2
    · exact Or.inr ((row2 (s 58)).mp (he ▸ hs 37 58 (by decide +kernel)))
    · exact Or.inl he
  have c2329 : s 37 ≠ 3 ∨ s 58 = 0 ∨ s 58 = 4 := by
    by_cases he : s 37 = 3
    · exact Or.inr ((row3 (s 58)).mp (he ▸ hs 37 58 (by decide +kernel)))
    · exact Or.inl he
  have c2336 : s 37 ≠ 0 ∨ s 18 = 1 ∨ s 18 = 2 ∨ s 18 = 3 := by
    by_cases he : s 37 = 0
    · exact Or.inr ((row0 (s 18)).mp (he ▸ hs 37 18 (by decide +kernel)))
    · exact Or.inl he
  have c2337 : s 37 ≠ 1 ∨ s 18 = 0 ∨ s 18 = 2 := by
    by_cases he : s 37 = 1
    · exact Or.inr ((row1 (s 18)).mp (he ▸ hs 37 18 (by decide +kernel)))
    · exact Or.inl he
  have c2338 : s 37 ≠ 2 ∨ s 18 = 0 ∨ s 18 = 1 := by
    by_cases he : s 37 = 2
    · exact Or.inr ((row2 (s 18)).mp (he ▸ hs 37 18 (by decide +kernel)))
    · exact Or.inl he
  have c2339 : s 37 ≠ 3 ∨ s 18 = 0 ∨ s 18 = 4 := by
    by_cases he : s 37 = 3
    · exact Or.inr ((row3 (s 18)).mp (he ▸ hs 37 18 (by decide +kernel)))
    · exact Or.inl he
  have c2346 : s 37 ≠ 0 ∨ s 21 = 1 ∨ s 21 = 2 ∨ s 21 = 3 := by
    by_cases he : s 37 = 0
    · exact Or.inr ((row0 (s 21)).mp (he ▸ hs 37 21 (by decide +kernel)))
    · exact Or.inl he
  have c2347 : s 37 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2 := by
    by_cases he : s 37 = 1
    · exact Or.inr ((row1 (s 21)).mp (he ▸ hs 37 21 (by decide +kernel)))
    · exact Or.inl he
  have c2348 : s 37 ≠ 2 ∨ s 21 = 0 ∨ s 21 = 1 := by
    by_cases he : s 37 = 2
    · exact Or.inr ((row2 (s 21)).mp (he ▸ hs 37 21 (by decide +kernel)))
    · exact Or.inl he
  have c2349 : s 37 ≠ 3 ∨ s 21 = 0 ∨ s 21 = 4 := by
    by_cases he : s 37 = 3
    · exact Or.inr ((row3 (s 21)).mp (he ▸ hs 37 21 (by decide +kernel)))
    · exact Or.inl he
  have c2356 : s 37 ≠ 0 ∨ s 23 = 1 ∨ s 23 = 2 ∨ s 23 = 3 := by
    by_cases he : s 37 = 0
    · exact Or.inr ((row0 (s 23)).mp (he ▸ hs 37 23 (by decide +kernel)))
    · exact Or.inl he
  have c2361 : s 37 ≠ 0 ∨ s 24 = 1 ∨ s 24 = 2 ∨ s 24 = 3 := by
    by_cases he : s 37 = 0
    · exact Or.inr ((row0 (s 24)).mp (he ▸ hs 37 24 (by decide +kernel)))
    · exact Or.inl he
  have c2362 : s 37 ≠ 1 ∨ s 24 = 0 ∨ s 24 = 2 := by
    by_cases he : s 37 = 1
    · exact Or.inr ((row1 (s 24)).mp (he ▸ hs 37 24 (by decide +kernel)))
    · exact Or.inl he
  have c2371 : s 38 ≠ 0 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 58 = 3 := by
    by_cases he : s 38 = 0
    · exact Or.inr ((row0 (s 58)).mp (he ▸ hs 38 58 (by decide +kernel)))
    · exact Or.inl he
  have c2375 : s 38 ≠ 4 ∨ s 58 = 3 ∨ s 58 = 4 := by
    by_cases he : s 38 = 4
    · exact Or.inr ((row4 (s 58)).mp (he ▸ hs 38 58 (by decide +kernel)))
    · exact Or.inl he
  have c2382 : s 38 ≠ 1 ∨ s 18 = 0 ∨ s 18 = 2 := by
    by_cases he : s 38 = 1
    · exact Or.inr ((row1 (s 18)).mp (he ▸ hs 38 18 (by decide +kernel)))
    · exact Or.inl he
  have c2383 : s 38 ≠ 2 ∨ s 18 = 0 ∨ s 18 = 1 := by
    by_cases he : s 38 = 2
    · exact Or.inr ((row2 (s 18)).mp (he ▸ hs 38 18 (by decide +kernel)))
    · exact Or.inl he
  have c2411 : s 38 ≠ 0 ∨ s 29 = 1 ∨ s 29 = 2 ∨ s 29 = 3 := by
    by_cases he : s 38 = 0
    · exact Or.inr ((row0 (s 29)).mp (he ▸ hs 38 29 (by decide +kernel)))
    · exact Or.inl he
  have c2412 : s 38 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2 := by
    by_cases he : s 38 = 1
    · exact Or.inr ((row1 (s 29)).mp (he ▸ hs 38 29 (by decide +kernel)))
    · exact Or.inl he
  have c2413 : s 38 ≠ 2 ∨ s 29 = 0 ∨ s 29 = 1 := by
    by_cases he : s 38 = 2
    · exact Or.inr ((row2 (s 29)).mp (he ▸ hs 38 29 (by decide +kernel)))
    · exact Or.inl he
  have c2414 : s 38 ≠ 3 ∨ s 29 = 0 ∨ s 29 = 4 := by
    by_cases he : s 38 = 3
    · exact Or.inr ((row3 (s 29)).mp (he ▸ hs 38 29 (by decide +kernel)))
    · exact Or.inl he
  have c2417 : s 39 ≠ 1 ∨ s 58 = 0 ∨ s 58 = 2 := by
    by_cases he : s 39 = 1
    · exact Or.inr ((row1 (s 58)).mp (he ▸ hs 39 58 (by decide +kernel)))
    · exact Or.inl he
  have c2421 : s 39 ≠ 0 ∨ s 7 = 1 ∨ s 7 = 2 ∨ s 7 = 3 := by
    by_cases he : s 39 = 0
    · exact Or.inr ((row0 (s 7)).mp (he ▸ hs 39 7 (by decide +kernel)))
    · exact Or.inl he
  have c2422 : s 39 ≠ 1 ∨ s 7 = 0 ∨ s 7 = 2 := by
    by_cases he : s 39 = 1
    · exact Or.inr ((row1 (s 7)).mp (he ▸ hs 39 7 (by decide +kernel)))
    · exact Or.inl he
  have c2428 : s 39 ≠ 2 ∨ s 18 = 0 ∨ s 18 = 1 := by
    by_cases he : s 39 = 2
    · exact Or.inr ((row2 (s 18)).mp (he ▸ hs 39 18 (by decide +kernel)))
    · exact Or.inl he
  have c2431 : s 39 ≠ 0 ∨ s 22 = 1 ∨ s 22 = 2 ∨ s 22 = 3 := by
    by_cases he : s 39 = 0
    · exact Or.inr ((row0 (s 22)).mp (he ▸ hs 39 22 (by decide +kernel)))
    · exact Or.inl he
  have c2438 : s 39 ≠ 2 ∨ s 55 = 0 ∨ s 55 = 1 := by
    by_cases he : s 39 = 2
    · exact Or.inr ((row2 (s 55)).mp (he ▸ hs 39 55 (by decide +kernel)))
    · exact Or.inl he
  have c2446 : s 39 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3 := by
    by_cases he : s 39 = 0
    · exact Or.inr ((row0 (s 57)).mp (he ▸ hs 39 57 (by decide +kernel)))
    · exact Or.inl he
  have c2447 : s 39 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2 := by
    by_cases he : s 39 = 1
    · exact Or.inr ((row1 (s 57)).mp (he ▸ hs 39 57 (by decide +kernel)))
    · exact Or.inl he
  have c2448 : s 39 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1 := by
    by_cases he : s 39 = 2
    · exact Or.inr ((row2 (s 57)).mp (he ▸ hs 39 57 (by decide +kernel)))
    · exact Or.inl he
  have c2449 : s 39 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4 := by
    by_cases he : s 39 = 3
    · exact Or.inr ((row3 (s 57)).mp (he ▸ hs 39 57 (by decide +kernel)))
    · exact Or.inl he
  have c2450 : s 39 ≠ 4 ∨ s 57 = 3 ∨ s 57 = 4 := by
    by_cases he : s 39 = 4
    · exact Or.inr ((row4 (s 57)).mp (he ▸ hs 39 57 (by decide +kernel)))
    · exact Or.inl he
  have c2456 : s 39 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3 := by
    by_cases he : s 39 = 0
    · exact Or.inr ((row0 (s 59)).mp (he ▸ hs 39 59 (by decide +kernel)))
    · exact Or.inl he
  have c2457 : s 39 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2 := by
    by_cases he : s 39 = 1
    · exact Or.inr ((row1 (s 59)).mp (he ▸ hs 39 59 (by decide +kernel)))
    · exact Or.inl he
  have c2458 : s 39 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1 := by
    by_cases he : s 39 = 2
    · exact Or.inr ((row2 (s 59)).mp (he ▸ hs 39 59 (by decide +kernel)))
    · exact Or.inl he
  have c2459 : s 39 ≠ 3 ∨ s 59 = 0 ∨ s 59 = 4 := by
    by_cases he : s 39 = 3
    · exact Or.inr ((row3 (s 59)).mp (he ▸ hs 39 59 (by decide +kernel)))
    · exact Or.inl he
  have c2460 : s 39 ≠ 4 ∨ s 59 = 3 ∨ s 59 = 4 := by
    by_cases he : s 39 = 4
    · exact Or.inr ((row4 (s 59)).mp (he ▸ hs 39 59 (by decide +kernel)))
    · exact Or.inl he
  have c2466 : s 40 ≠ 0 ∨ s 6 = 1 ∨ s 6 = 2 ∨ s 6 = 3 := by
    by_cases he : s 40 = 0
    · exact Or.inr ((row0 (s 6)).mp (he ▸ hs 40 6 (by decide +kernel)))
    · exact Or.inl he
  have c2467 : s 40 ≠ 1 ∨ s 6 = 0 ∨ s 6 = 2 := by
    by_cases he : s 40 = 1
    · exact Or.inr ((row1 (s 6)).mp (he ▸ hs 40 6 (by decide +kernel)))
    · exact Or.inl he
  have c2468 : s 40 ≠ 2 ∨ s 6 = 0 ∨ s 6 = 1 := by
    by_cases he : s 40 = 2
    · exact Or.inr ((row2 (s 6)).mp (he ▸ hs 40 6 (by decide +kernel)))
    · exact Or.inl he
  have c2491 : s 40 ≠ 0 ∨ s 54 = 1 ∨ s 54 = 2 ∨ s 54 = 3 := by
    by_cases he : s 40 = 0
    · exact Or.inr ((row0 (s 54)).mp (he ▸ hs 40 54 (by decide +kernel)))
    · exact Or.inl he
  have c2498 : s 40 ≠ 2 ∨ s 23 = 0 ∨ s 23 = 1 := by
    by_cases he : s 40 = 2
    · exact Or.inr ((row2 (s 23)).mp (he ▸ hs 40 23 (by decide +kernel)))
    · exact Or.inl he
  have c2501 : s 40 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3 := by
    by_cases he : s 40 = 0
    · exact Or.inr ((row0 (s 59)).mp (he ▸ hs 40 59 (by decide +kernel)))
    · exact Or.inl he
  have c2502 : s 40 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2 := by
    by_cases he : s 40 = 1
    · exact Or.inr ((row1 (s 59)).mp (he ▸ hs 40 59 (by decide +kernel)))
    · exact Or.inl he
  have c2503 : s 40 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1 := by
    by_cases he : s 40 = 2
    · exact Or.inr ((row2 (s 59)).mp (he ▸ hs 40 59 (by decide +kernel)))
    · exact Or.inl he
  have c2504 : s 40 ≠ 3 ∨ s 59 = 0 ∨ s 59 = 4 := by
    by_cases he : s 40 = 3
    · exact Or.inr ((row3 (s 59)).mp (he ▸ hs 40 59 (by decide +kernel)))
    · exact Or.inl he
  have c2517 : s 41 ≠ 1 ∨ s 20 = 0 ∨ s 20 = 2 := by
    by_cases he : s 41 = 1
    · exact Or.inr ((row1 (s 20)).mp (he ▸ hs 41 20 (by decide +kernel)))
    · exact Or.inl he
  have c2521 : s 41 ≠ 0 ∨ s 21 = 1 ∨ s 21 = 2 ∨ s 21 = 3 := by
    by_cases he : s 41 = 0
    · exact Or.inr ((row0 (s 21)).mp (he ▸ hs 41 21 (by decide +kernel)))
    · exact Or.inl he
  have c2522 : s 41 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2 := by
    by_cases he : s 41 = 1
    · exact Or.inr ((row1 (s 21)).mp (he ▸ hs 41 21 (by decide +kernel)))
    · exact Or.inl he
  have c2523 : s 41 ≠ 2 ∨ s 21 = 0 ∨ s 21 = 1 := by
    by_cases he : s 41 = 2
    · exact Or.inr ((row2 (s 21)).mp (he ▸ hs 41 21 (by decide +kernel)))
    · exact Or.inl he
  have c2543 : s 41 ≠ 2 ∨ s 54 = 0 ∨ s 54 = 1 := by
    by_cases he : s 41 = 2
    · exact Or.inr ((row2 (s 54)).mp (he ▸ hs 41 54 (by decide +kernel)))
    · exact Or.inl he
  have c2546 : s 41 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3 := by
    by_cases he : s 41 = 0
    · exact Or.inr ((row0 (s 59)).mp (he ▸ hs 41 59 (by decide +kernel)))
    · exact Or.inl he
  have c2547 : s 41 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2 := by
    by_cases he : s 41 = 1
    · exact Or.inr ((row1 (s 59)).mp (he ▸ hs 41 59 (by decide +kernel)))
    · exact Or.inl he
  have c2548 : s 41 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1 := by
    by_cases he : s 41 = 2
    · exact Or.inr ((row2 (s 59)).mp (he ▸ hs 41 59 (by decide +kernel)))
    · exact Or.inl he
  have c2549 : s 41 ≠ 3 ∨ s 59 = 0 ∨ s 59 = 4 := by
    by_cases he : s 41 = 3
    · exact Or.inr ((row3 (s 59)).mp (he ▸ hs 41 59 (by decide +kernel)))
    · exact Or.inl he
  have c2557 : s 42 ≠ 1 ∨ s 45 = 0 ∨ s 45 = 2 := by
    by_cases he : s 42 = 1
    · exact Or.inr ((row1 (s 45)).mp (he ▸ hs 42 45 (by decide +kernel)))
    · exact Or.inl he
  have c2558 : s 42 ≠ 2 ∨ s 45 = 0 ∨ s 45 = 1 := by
    by_cases he : s 42 = 2
    · exact Or.inr ((row2 (s 45)).mp (he ▸ hs 42 45 (by decide +kernel)))
    · exact Or.inl he
  have c2567 : s 42 ≠ 1 ∨ s 47 = 0 ∨ s 47 = 2 := by
    by_cases he : s 42 = 1
    · exact Or.inr ((row1 (s 47)).mp (he ▸ hs 42 47 (by decide +kernel)))
    · exact Or.inl he
  have c2568 : s 42 ≠ 2 ∨ s 47 = 0 ∨ s 47 = 1 := by
    by_cases he : s 42 = 2
    · exact Or.inr ((row2 (s 47)).mp (he ▸ hs 42 47 (by decide +kernel)))
    · exact Or.inl he
  have c2591 : s 42 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3 := by
    by_cases he : s 42 = 0
    · exact Or.inr ((row0 (s 59)).mp (he ▸ hs 42 59 (by decide +kernel)))
    · exact Or.inl he
  have c2592 : s 42 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2 := by
    by_cases he : s 42 = 1
    · exact Or.inr ((row1 (s 59)).mp (he ▸ hs 42 59 (by decide +kernel)))
    · exact Or.inl he
  have c2593 : s 42 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1 := by
    by_cases he : s 42 = 2
    · exact Or.inr ((row2 (s 59)).mp (he ▸ hs 42 59 (by decide +kernel)))
    · exact Or.inl he
  have c2594 : s 42 ≠ 3 ∨ s 59 = 0 ∨ s 59 = 4 := by
    by_cases he : s 42 = 3
    · exact Or.inr ((row3 (s 59)).mp (he ▸ hs 42 59 (by decide +kernel)))
    · exact Or.inl he
  have c2596 : s 43 ≠ 0 ∨ s 8 = 1 ∨ s 8 = 2 ∨ s 8 = 3 := by
    by_cases he : s 43 = 0
    · exact Or.inr ((row0 (s 8)).mp (he ▸ hs 43 8 (by decide +kernel)))
    · exact Or.inl he
  have c2598 : s 43 ≠ 2 ∨ s 8 = 0 ∨ s 8 = 1 := by
    by_cases he : s 43 = 2
    · exact Or.inr ((row2 (s 8)).mp (he ▸ hs 43 8 (by decide +kernel)))
    · exact Or.inl he
  have c2606 : s 43 ≠ 0 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 50 = 3 := by
    by_cases he : s 43 = 0
    · exact Or.inr ((row0 (s 50)).mp (he ▸ hs 43 50 (by decide +kernel)))
    · exact Or.inl he
  have c2607 : s 43 ≠ 1 ∨ s 50 = 0 ∨ s 50 = 2 := by
    by_cases he : s 43 = 1
    · exact Or.inr ((row1 (s 50)).mp (he ▸ hs 43 50 (by decide +kernel)))
    · exact Or.inl he
  have c2608 : s 43 ≠ 2 ∨ s 50 = 0 ∨ s 50 = 1 := by
    by_cases he : s 43 = 2
    · exact Or.inr ((row2 (s 50)).mp (he ▸ hs 43 50 (by decide +kernel)))
    · exact Or.inl he
  have c2611 : s 43 ≠ 0 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 51 = 3 := by
    by_cases he : s 43 = 0
    · exact Or.inr ((row0 (s 51)).mp (he ▸ hs 43 51 (by decide +kernel)))
    · exact Or.inl he
  have c2612 : s 43 ≠ 1 ∨ s 51 = 0 ∨ s 51 = 2 := by
    by_cases he : s 43 = 1
    · exact Or.inr ((row1 (s 51)).mp (he ▸ hs 43 51 (by decide +kernel)))
    · exact Or.inl he
  have c2613 : s 43 ≠ 2 ∨ s 51 = 0 ∨ s 51 = 1 := by
    by_cases he : s 43 = 2
    · exact Or.inr ((row2 (s 51)).mp (he ▸ hs 43 51 (by decide +kernel)))
    · exact Or.inl he
  have c2615 : s 43 ≠ 4 ∨ s 51 = 3 ∨ s 51 = 4 := by
    by_cases he : s 43 = 4
    · exact Or.inr ((row4 (s 51)).mp (he ▸ hs 43 51 (by decide +kernel)))
    · exact Or.inl he
  have c2617 : s 43 ≠ 1 ∨ s 52 = 0 ∨ s 52 = 2 := by
    by_cases he : s 43 = 1
    · exact Or.inr ((row1 (s 52)).mp (he ▸ hs 43 52 (by decide +kernel)))
    · exact Or.inl he
  have c2618 : s 43 ≠ 2 ∨ s 52 = 0 ∨ s 52 = 1 := by
    by_cases he : s 43 = 2
    · exact Or.inr ((row2 (s 52)).mp (he ▸ hs 43 52 (by decide +kernel)))
    · exact Or.inl he
  have c2636 : s 43 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3 := by
    by_cases he : s 43 = 0
    · exact Or.inr ((row0 (s 59)).mp (he ▸ hs 43 59 (by decide +kernel)))
    · exact Or.inl he
  have c2637 : s 43 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2 := by
    by_cases he : s 43 = 1
    · exact Or.inr ((row1 (s 59)).mp (he ▸ hs 43 59 (by decide +kernel)))
    · exact Or.inl he
  have c2638 : s 43 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1 := by
    by_cases he : s 43 = 2
    · exact Or.inr ((row2 (s 59)).mp (he ▸ hs 43 59 (by decide +kernel)))
    · exact Or.inl he
  have c2639 : s 43 ≠ 3 ∨ s 59 = 0 ∨ s 59 = 4 := by
    by_cases he : s 43 = 3
    · exact Or.inr ((row3 (s 59)).mp (he ▸ hs 43 59 (by decide +kernel)))
    · exact Or.inl he
  have c2640 : s 43 ≠ 4 ∨ s 59 = 3 ∨ s 59 = 4 := by
    by_cases he : s 43 = 4
    · exact Or.inr ((row4 (s 59)).mp (he ▸ hs 43 59 (by decide +kernel)))
    · exact Or.inl he
  have c2643 : s 44 ≠ 2 ∨ s 8 = 0 ∨ s 8 = 1 := by
    by_cases he : s 44 = 2
    · exact Or.inr ((row2 (s 8)).mp (he ▸ hs 44 8 (by decide +kernel)))
    · exact Or.inl he
  have c2656 : s 44 ≠ 0 ∨ s 54 = 1 ∨ s 54 = 2 ∨ s 54 = 3 := by
    by_cases he : s 44 = 0
    · exact Or.inr ((row0 (s 54)).mp (he ▸ hs 44 54 (by decide +kernel)))
    · exact Or.inl he
  have c2662 : s 44 ≠ 1 ∨ s 55 = 0 ∨ s 55 = 2 := by
    by_cases he : s 44 = 1
    · exact Or.inr ((row1 (s 55)).mp (he ▸ hs 44 55 (by decide +kernel)))
    · exact Or.inl he
  have c2671 : s 44 ≠ 0 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 57 = 3 := by
    by_cases he : s 44 = 0
    · exact Or.inr ((row0 (s 57)).mp (he ▸ hs 44 57 (by decide +kernel)))
    · exact Or.inl he
  have c2672 : s 44 ≠ 1 ∨ s 57 = 0 ∨ s 57 = 2 := by
    by_cases he : s 44 = 1
    · exact Or.inr ((row1 (s 57)).mp (he ▸ hs 44 57 (by decide +kernel)))
    · exact Or.inl he
  have c2673 : s 44 ≠ 2 ∨ s 57 = 0 ∨ s 57 = 1 := by
    by_cases he : s 44 = 2
    · exact Or.inr ((row2 (s 57)).mp (he ▸ hs 44 57 (by decide +kernel)))
    · exact Or.inl he
  have c2674 : s 44 ≠ 3 ∨ s 57 = 0 ∨ s 57 = 4 := by
    by_cases he : s 44 = 3
    · exact Or.inr ((row3 (s 57)).mp (he ▸ hs 44 57 (by decide +kernel)))
    · exact Or.inl he
  have c2681 : s 44 ≠ 0 ∨ s 59 = 1 ∨ s 59 = 2 ∨ s 59 = 3 := by
    by_cases he : s 44 = 0
    · exact Or.inr ((row0 (s 59)).mp (he ▸ hs 44 59 (by decide +kernel)))
    · exact Or.inl he
  have c2682 : s 44 ≠ 1 ∨ s 59 = 0 ∨ s 59 = 2 := by
    by_cases he : s 44 = 1
    · exact Or.inr ((row1 (s 59)).mp (he ▸ hs 44 59 (by decide +kernel)))
    · exact Or.inl he
  have c2683 : s 44 ≠ 2 ∨ s 59 = 0 ∨ s 59 = 1 := by
    by_cases he : s 44 = 2
    · exact Or.inr ((row2 (s 59)).mp (he ▸ hs 44 59 (by decide +kernel)))
    · exact Or.inl he
  have c2685 : s 44 ≠ 4 ∨ s 59 = 3 ∨ s 59 = 4 := by
    by_cases he : s 44 = 4
    · exact Or.inr ((row4 (s 59)).mp (he ▸ hs 44 59 (by decide +kernel)))
    · exact Or.inl he
  have c2701 : s 45 ≠ 0 ∨ s 3 = 1 ∨ s 3 = 2 ∨ s 3 = 3 := by
    by_cases he : s 45 = 0
    · exact Or.inr ((row0 (s 3)).mp (he ▸ hs 45 3 (by decide +kernel)))
    · exact Or.inl he
  have c2702 : s 45 ≠ 1 ∨ s 3 = 0 ∨ s 3 = 2 := by
    by_cases he : s 45 = 1
    · exact Or.inr ((row1 (s 3)).mp (he ▸ hs 45 3 (by decide +kernel)))
    · exact Or.inl he
  have c2703 : s 45 ≠ 2 ∨ s 3 = 0 ∨ s 3 = 1 := by
    by_cases he : s 45 = 2
    · exact Or.inr ((row2 (s 3)).mp (he ▸ hs 45 3 (by decide +kernel)))
    · exact Or.inl he
  have c2708 : s 45 ≠ 2 ∨ s 4 = 0 ∨ s 4 = 1 := by
    by_cases he : s 45 = 2
    · exact Or.inr ((row2 (s 4)).mp (he ▸ hs 45 4 (by decide +kernel)))
    · exact Or.inl he
  have c2717 : s 45 ≠ 1 ∨ s 42 = 0 ∨ s 42 = 2 := by
    by_cases he : s 45 = 1
    · exact Or.inr ((row1 (s 42)).mp (he ▸ hs 45 42 (by decide +kernel)))
    · exact Or.inl he
  have c2718 : s 45 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1 := by
    by_cases he : s 45 = 2
    · exact Or.inr ((row2 (s 42)).mp (he ▸ hs 45 42 (by decide +kernel)))
    · exact Or.inl he
  have c2733 : s 46 ≠ 2 ∨ s 4 = 0 ∨ s 4 = 1 := by
    by_cases he : s 46 = 2
    · exact Or.inr ((row2 (s 4)).mp (he ▸ hs 46 4 (by decide +kernel)))
    · exact Or.inl he
  have c2742 : s 46 ≠ 1 ∨ s 6 = 0 ∨ s 6 = 2 := by
    by_cases he : s 46 = 1
    · exact Or.inr ((row1 (s 6)).mp (he ▸ hs 46 6 (by decide +kernel)))
    · exact Or.inl he
  have c2743 : s 46 ≠ 2 ∨ s 6 = 0 ∨ s 6 = 1 := by
    by_cases he : s 46 = 2
    · exact Or.inr ((row2 (s 6)).mp (he ▸ hs 46 6 (by decide +kernel)))
    · exact Or.inl he
  have c2761 : s 46 ≠ 0 ∨ s 42 = 1 ∨ s 42 = 2 ∨ s 42 = 3 := by
    by_cases he : s 46 = 0
    · exact Or.inr ((row0 (s 42)).mp (he ▸ hs 46 42 (by decide +kernel)))
    · exact Or.inl he
  have c2762 : s 46 ≠ 1 ∨ s 42 = 0 ∨ s 42 = 2 := by
    by_cases he : s 46 = 1
    · exact Or.inr ((row1 (s 42)).mp (he ▸ hs 46 42 (by decide +kernel)))
    · exact Or.inl he
  have c2763 : s 46 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1 := by
    by_cases he : s 46 = 2
    · exact Or.inr ((row2 (s 42)).mp (he ▸ hs 46 42 (by decide +kernel)))
    · exact Or.inl he
  have c2792 : s 47 ≠ 1 ∨ s 11 = 0 ∨ s 11 = 2 := by
    by_cases he : s 47 = 1
    · exact Or.inr ((row1 (s 11)).mp (he ▸ hs 47 11 (by decide +kernel)))
    · exact Or.inl he
  have c2793 : s 47 ≠ 2 ∨ s 11 = 0 ∨ s 11 = 1 := by
    by_cases he : s 47 = 2
    · exact Or.inr ((row2 (s 11)).mp (he ▸ hs 47 11 (by decide +kernel)))
    · exact Or.inl he
  have c2803 : s 47 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1 := by
    by_cases he : s 47 = 2
    · exact Or.inr ((row2 (s 13)).mp (he ▸ hs 47 13 (by decide +kernel)))
    · exact Or.inl he
  have c2804 : s 47 ≠ 3 ∨ s 13 = 0 ∨ s 13 = 4 := by
    by_cases he : s 47 = 3
    · exact Or.inr ((row3 (s 13)).mp (he ▸ hs 47 13 (by decide +kernel)))
    · exact Or.inl he
  have c2806 : s 47 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3 := by
    by_cases he : s 47 = 0
    · exact Or.inr ((row0 (s 14)).mp (he ▸ hs 47 14 (by decide +kernel)))
    · exact Or.inl he
  have c2807 : s 47 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2 := by
    by_cases he : s 47 = 1
    · exact Or.inr ((row1 (s 14)).mp (he ▸ hs 47 14 (by decide +kernel)))
    · exact Or.inl he
  have c2808 : s 47 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1 := by
    by_cases he : s 47 = 2
    · exact Or.inr ((row2 (s 14)).mp (he ▸ hs 47 14 (by decide +kernel)))
    · exact Or.inl he
  have c2809 : s 47 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4 := by
    by_cases he : s 47 = 3
    · exact Or.inr ((row3 (s 14)).mp (he ▸ hs 47 14 (by decide +kernel)))
    · exact Or.inl he
  have c2810 : s 47 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4 := by
    by_cases he : s 47 = 4
    · exact Or.inr ((row4 (s 14)).mp (he ▸ hs 47 14 (by decide +kernel)))
    · exact Or.inl he
  have c2813 : s 47 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1 := by
    by_cases he : s 47 = 2
    · exact Or.inr ((row2 (s 42)).mp (he ▸ hs 47 42 (by decide +kernel)))
    · exact Or.inl he
  have c2827 : s 48 ≠ 1 ∨ s 9 = 0 ∨ s 9 = 2 := by
    by_cases he : s 48 = 1
    · exact Or.inr ((row1 (s 9)).mp (he ▸ hs 48 9 (by decide +kernel)))
    · exact Or.inl he
  have c2828 : s 48 ≠ 2 ∨ s 9 = 0 ∨ s 9 = 1 := by
    by_cases he : s 48 = 2
    · exact Or.inr ((row2 (s 9)).mp (he ▸ hs 48 9 (by decide +kernel)))
    · exact Or.inl he
  have c2833 : s 48 ≠ 2 ∨ s 42 = 0 ∨ s 42 = 1 := by
    by_cases he : s 48 = 2
    · exact Or.inr ((row2 (s 42)).mp (he ▸ hs 48 42 (by decide +kernel)))
    · exact Or.inl he
  have c2861 : s 48 ≠ 0 ∨ s 29 = 1 ∨ s 29 = 2 ∨ s 29 = 3 := by
    by_cases he : s 48 = 0
    · exact Or.inr ((row0 (s 29)).mp (he ▸ hs 48 29 (by decide +kernel)))
    · exact Or.inl he
  have c2862 : s 48 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2 := by
    by_cases he : s 48 = 1
    · exact Or.inr ((row1 (s 29)).mp (he ▸ hs 48 29 (by decide +kernel)))
    · exact Or.inl he
  have c2863 : s 48 ≠ 2 ∨ s 29 = 0 ∨ s 29 = 1 := by
    by_cases he : s 48 = 2
    · exact Or.inr ((row2 (s 29)).mp (he ▸ hs 48 29 (by decide +kernel)))
    · exact Or.inl he
  have c2873 : s 49 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1 := by
    by_cases he : s 49 = 2
    · exact Or.inr ((row2 (s 40)).mp (he ▸ hs 49 40 (by decide +kernel)))
    · exact Or.inl he
  have c2877 : s 49 ≠ 1 ∨ s 9 = 0 ∨ s 9 = 2 := by
    by_cases he : s 49 = 1
    · exact Or.inr ((row1 (s 9)).mp (he ▸ hs 49 9 (by decide +kernel)))
    · exact Or.inl he
  have c2878 : s 49 ≠ 2 ∨ s 9 = 0 ∨ s 9 = 1 := by
    by_cases he : s 49 = 2
    · exact Or.inr ((row2 (s 9)).mp (he ▸ hs 49 9 (by decide +kernel)))
    · exact Or.inl he
  have c2897 : s 49 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2 := by
    by_cases he : s 49 = 1
    · exact Or.inr ((row1 (s 43)).mp (he ▸ hs 49 43 (by decide +kernel)))
    · exact Or.inl he
  have c2902 : s 49 ≠ 1 ∨ s 44 = 0 ∨ s 44 = 2 := by
    by_cases he : s 49 = 1
    · exact Or.inr ((row1 (s 44)).mp (he ▸ hs 49 44 (by decide +kernel)))
    · exact Or.inl he
  have c2903 : s 49 ≠ 2 ∨ s 44 = 0 ∨ s 44 = 1 := by
    by_cases he : s 49 = 2
    · exact Or.inr ((row2 (s 44)).mp (he ▸ hs 49 44 (by decide +kernel)))
    · exact Or.inl he
  have c2912 : s 50 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2 := by
    by_cases he : s 50 = 1
    · exact Or.inr ((row1 (s 10)).mp (he ▸ hs 50 10 (by decide +kernel)))
    · exact Or.inl he
  have c2913 : s 50 ≠ 2 ∨ s 10 = 0 ∨ s 10 = 1 := by
    by_cases he : s 50 = 2
    · exact Or.inr ((row2 (s 10)).mp (he ▸ hs 50 10 (by decide +kernel)))
    · exact Or.inl he
  have c2914 : s 50 ≠ 3 ∨ s 10 = 0 ∨ s 10 = 4 := by
    by_cases he : s 50 = 3
    · exact Or.inr ((row3 (s 10)).mp (he ▸ hs 50 10 (by decide +kernel)))
    · exact Or.inl he
  have c2916 : s 50 ≠ 0 ∨ s 11 = 1 ∨ s 11 = 2 ∨ s 11 = 3 := by
    by_cases he : s 50 = 0
    · exact Or.inr ((row0 (s 11)).mp (he ▸ hs 50 11 (by decide +kernel)))
    · exact Or.inl he
  have c2917 : s 50 ≠ 1 ∨ s 11 = 0 ∨ s 11 = 2 := by
    by_cases he : s 50 = 1
    · exact Or.inr ((row1 (s 11)).mp (he ▸ hs 50 11 (by decide +kernel)))
    · exact Or.inl he
  have c2918 : s 50 ≠ 2 ∨ s 11 = 0 ∨ s 11 = 1 := by
    by_cases he : s 50 = 2
    · exact Or.inr ((row2 (s 11)).mp (he ▸ hs 50 11 (by decide +kernel)))
    · exact Or.inl he
  have c2926 : s 50 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3 := by
    by_cases he : s 50 = 0
    · exact Or.inr ((row0 (s 13)).mp (he ▸ hs 50 13 (by decide +kernel)))
    · exact Or.inl he
  have c2927 : s 50 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2 := by
    by_cases he : s 50 = 1
    · exact Or.inr ((row1 (s 13)).mp (he ▸ hs 50 13 (by decide +kernel)))
    · exact Or.inl he
  have c2928 : s 50 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1 := by
    by_cases he : s 50 = 2
    · exact Or.inr ((row2 (s 13)).mp (he ▸ hs 50 13 (by decide +kernel)))
    · exact Or.inl he
  have c2929 : s 50 ≠ 3 ∨ s 13 = 0 ∨ s 13 = 4 := by
    by_cases he : s 50 = 3
    · exact Or.inr ((row3 (s 13)).mp (he ▸ hs 50 13 (by decide +kernel)))
    · exact Or.inl he
  have c2931 : s 50 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3 := by
    by_cases he : s 50 = 0
    · exact Or.inr ((row0 (s 14)).mp (he ▸ hs 50 14 (by decide +kernel)))
    · exact Or.inl he
  have c2932 : s 50 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2 := by
    by_cases he : s 50 = 1
    · exact Or.inr ((row1 (s 14)).mp (he ▸ hs 50 14 (by decide +kernel)))
    · exact Or.inl he
  have c2933 : s 50 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1 := by
    by_cases he : s 50 = 2
    · exact Or.inr ((row2 (s 14)).mp (he ▸ hs 50 14 (by decide +kernel)))
    · exact Or.inl he
  have c2934 : s 50 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4 := by
    by_cases he : s 50 = 3
    · exact Or.inr ((row3 (s 14)).mp (he ▸ hs 50 14 (by decide +kernel)))
    · exact Or.inl he
  have c2935 : s 50 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4 := by
    by_cases he : s 50 = 4
    · exact Or.inr ((row4 (s 14)).mp (he ▸ hs 50 14 (by decide +kernel)))
    · exact Or.inl he
  have c2936 : s 50 ≠ 0 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 43 = 3 := by
    by_cases he : s 50 = 0
    · exact Or.inr ((row0 (s 43)).mp (he ▸ hs 50 43 (by decide +kernel)))
    · exact Or.inl he
  have c2937 : s 50 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2 := by
    by_cases he : s 50 = 1
    · exact Or.inr ((row1 (s 43)).mp (he ▸ hs 50 43 (by decide +kernel)))
    · exact Or.inl he
  have c2938 : s 50 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1 := by
    by_cases he : s 50 = 2
    · exact Or.inr ((row2 (s 43)).mp (he ▸ hs 50 43 (by decide +kernel)))
    · exact Or.inl he
  have c2941 : s 50 ≠ 0 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 19 = 3 := by
    by_cases he : s 50 = 0
    · exact Or.inr ((row0 (s 19)).mp (he ▸ hs 50 19 (by decide +kernel)))
    · exact Or.inl he
  have c2942 : s 50 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2 := by
    by_cases he : s 50 = 1
    · exact Or.inr ((row1 (s 19)).mp (he ▸ hs 50 19 (by decide +kernel)))
    · exact Or.inl he
  have c2943 : s 50 ≠ 2 ∨ s 19 = 0 ∨ s 19 = 1 := by
    by_cases he : s 50 = 2
    · exact Or.inr ((row2 (s 19)).mp (he ▸ hs 50 19 (by decide +kernel)))
    · exact Or.inl he
  have c2944 : s 50 ≠ 3 ∨ s 19 = 0 ∨ s 19 = 4 := by
    by_cases he : s 50 = 3
    · exact Or.inr ((row3 (s 19)).mp (he ▸ hs 50 19 (by decide +kernel)))
    · exact Or.inl he
  have c2956 : s 51 ≠ 0 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 43 = 3 := by
    by_cases he : s 51 = 0
    · exact Or.inr ((row0 (s 43)).mp (he ▸ hs 51 43 (by decide +kernel)))
    · exact Or.inl he
  have c2957 : s 51 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2 := by
    by_cases he : s 51 = 1
    · exact Or.inr ((row1 (s 43)).mp (he ▸ hs 51 43 (by decide +kernel)))
    · exact Or.inl he
  have c2958 : s 51 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1 := by
    by_cases he : s 51 = 2
    · exact Or.inr ((row2 (s 43)).mp (he ▸ hs 51 43 (by decide +kernel)))
    · exact Or.inl he
  have c2959 : s 51 ≠ 3 ∨ s 43 = 0 ∨ s 43 = 4 := by
    by_cases he : s 51 = 3
    · exact Or.inr ((row3 (s 43)).mp (he ▸ hs 51 43 (by decide +kernel)))
    · exact Or.inl he
  have c2961 : s 51 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3 := by
    by_cases he : s 51 = 0
    · exact Or.inr ((row0 (s 13)).mp (he ▸ hs 51 13 (by decide +kernel)))
    · exact Or.inl he
  have c2962 : s 51 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2 := by
    by_cases he : s 51 = 1
    · exact Or.inr ((row1 (s 13)).mp (he ▸ hs 51 13 (by decide +kernel)))
    · exact Or.inl he
  have c2963 : s 51 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1 := by
    by_cases he : s 51 = 2
    · exact Or.inr ((row2 (s 13)).mp (he ▸ hs 51 13 (by decide +kernel)))
    · exact Or.inl he
  have c2964 : s 51 ≠ 3 ∨ s 13 = 0 ∨ s 13 = 4 := by
    by_cases he : s 51 = 3
    · exact Or.inr ((row3 (s 13)).mp (he ▸ hs 51 13 (by decide +kernel)))
    · exact Or.inl he
  have c2965 : s 51 ≠ 4 ∨ s 13 = 3 ∨ s 13 = 4 := by
    by_cases he : s 51 = 4
    · exact Or.inr ((row4 (s 13)).mp (he ▸ hs 51 13 (by decide +kernel)))
    · exact Or.inl he
  have c2973 : s 51 ≠ 2 ∨ s 16 = 0 ∨ s 16 = 1 := by
    by_cases he : s 51 = 2
    · exact Or.inr ((row2 (s 16)).mp (he ▸ hs 51 16 (by decide +kernel)))
    · exact Or.inl he
  have c2976 : s 51 ≠ 0 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 17 = 3 := by
    by_cases he : s 51 = 0
    · exact Or.inr ((row0 (s 17)).mp (he ▸ hs 51 17 (by decide +kernel)))
    · exact Or.inl he
  have c2977 : s 51 ≠ 1 ∨ s 17 = 0 ∨ s 17 = 2 := by
    by_cases he : s 51 = 1
    · exact Or.inr ((row1 (s 17)).mp (he ▸ hs 51 17 (by decide +kernel)))
    · exact Or.inl he
  have c2978 : s 51 ≠ 2 ∨ s 17 = 0 ∨ s 17 = 1 := by
    by_cases he : s 51 = 2
    · exact Or.inr ((row2 (s 17)).mp (he ▸ hs 51 17 (by decide +kernel)))
    · exact Or.inl he
  have c2979 : s 51 ≠ 3 ∨ s 17 = 0 ∨ s 17 = 4 := by
    by_cases he : s 51 = 3
    · exact Or.inr ((row3 (s 17)).mp (he ▸ hs 51 17 (by decide +kernel)))
    · exact Or.inl he
  have c2980 : s 51 ≠ 4 ∨ s 17 = 3 ∨ s 17 = 4 := by
    by_cases he : s 51 = 4
    · exact Or.inr ((row4 (s 17)).mp (he ▸ hs 51 17 (by decide +kernel)))
    · exact Or.inl he
  have c2982 : s 51 ≠ 1 ∨ s 18 = 0 ∨ s 18 = 2 := by
    by_cases he : s 51 = 1
    · exact Or.inr ((row1 (s 18)).mp (he ▸ hs 51 18 (by decide +kernel)))
    · exact Or.inl he
  have c2986 : s 51 ≠ 0 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 19 = 3 := by
    by_cases he : s 51 = 0
    · exact Or.inr ((row0 (s 19)).mp (he ▸ hs 51 19 (by decide +kernel)))
    · exact Or.inl he
  have c2987 : s 51 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2 := by
    by_cases he : s 51 = 1
    · exact Or.inr ((row1 (s 19)).mp (he ▸ hs 51 19 (by decide +kernel)))
    · exact Or.inl he
  have c2988 : s 51 ≠ 2 ∨ s 19 = 0 ∨ s 19 = 1 := by
    by_cases he : s 51 = 2
    · exact Or.inr ((row2 (s 19)).mp (he ▸ hs 51 19 (by decide +kernel)))
    · exact Or.inl he
  have c2989 : s 51 ≠ 3 ∨ s 19 = 0 ∨ s 19 = 4 := by
    by_cases he : s 51 = 3
    · exact Or.inr ((row3 (s 19)).mp (he ▸ hs 51 19 (by decide +kernel)))
    · exact Or.inl he
  have c2990 : s 51 ≠ 4 ∨ s 19 = 3 ∨ s 19 = 4 := by
    by_cases he : s 51 = 4
    · exact Or.inr ((row4 (s 19)).mp (he ▸ hs 51 19 (by decide +kernel)))
    · exact Or.inl he
  have c2992 : s 51 ≠ 1 ∨ s 24 = 0 ∨ s 24 = 2 := by
    by_cases he : s 51 = 1
    · exact Or.inr ((row1 (s 24)).mp (he ▸ hs 51 24 (by decide +kernel)))
    · exact Or.inl he
  have c3001 : s 52 ≠ 0 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 43 = 3 := by
    by_cases he : s 52 = 0
    · exact Or.inr ((row0 (s 43)).mp (he ▸ hs 52 43 (by decide +kernel)))
    · exact Or.inl he
  have c3002 : s 52 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2 := by
    by_cases he : s 52 = 1
    · exact Or.inr ((row1 (s 43)).mp (he ▸ hs 52 43 (by decide +kernel)))
    · exact Or.inl he
  have c3003 : s 52 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1 := by
    by_cases he : s 52 = 2
    · exact Or.inr ((row2 (s 43)).mp (he ▸ hs 52 43 (by decide +kernel)))
    · exact Or.inl he
  have c3004 : s 52 ≠ 3 ∨ s 43 = 0 ∨ s 43 = 4 := by
    by_cases he : s 52 = 3
    · exact Or.inr ((row3 (s 43)).mp (he ▸ hs 52 43 (by decide +kernel)))
    · exact Or.inl he
  have c3006 : s 52 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3 := by
    by_cases he : s 52 = 0
    · exact Or.inr ((row0 (s 13)).mp (he ▸ hs 52 13 (by decide +kernel)))
    · exact Or.inl he
  have c3007 : s 52 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2 := by
    by_cases he : s 52 = 1
    · exact Or.inr ((row1 (s 13)).mp (he ▸ hs 52 13 (by decide +kernel)))
    · exact Or.inl he
  have c3008 : s 52 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1 := by
    by_cases he : s 52 = 2
    · exact Or.inr ((row2 (s 13)).mp (he ▸ hs 52 13 (by decide +kernel)))
    · exact Or.inl he
  have c3010 : s 52 ≠ 4 ∨ s 13 = 3 ∨ s 13 = 4 := by
    by_cases he : s 52 = 4
    · exact Or.inr ((row4 (s 13)).mp (he ▸ hs 52 13 (by decide +kernel)))
    · exact Or.inl he
  have c3011 : s 52 ≠ 0 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 19 = 3 := by
    by_cases he : s 52 = 0
    · exact Or.inr ((row0 (s 19)).mp (he ▸ hs 52 19 (by decide +kernel)))
    · exact Or.inl he
  have c3012 : s 52 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2 := by
    by_cases he : s 52 = 1
    · exact Or.inr ((row1 (s 19)).mp (he ▸ hs 52 19 (by decide +kernel)))
    · exact Or.inl he
  have c3013 : s 52 ≠ 2 ∨ s 19 = 0 ∨ s 19 = 1 := by
    by_cases he : s 52 = 2
    · exact Or.inr ((row2 (s 19)).mp (he ▸ hs 52 19 (by decide +kernel)))
    · exact Or.inl he
  have c3015 : s 52 ≠ 4 ∨ s 19 = 3 ∨ s 19 = 4 := by
    by_cases he : s 52 = 4
    · exact Or.inr ((row4 (s 19)).mp (he ▸ hs 52 19 (by decide +kernel)))
    · exact Or.inl he
  have c3021 : s 52 ≠ 0 ∨ s 21 = 1 ∨ s 21 = 2 ∨ s 21 = 3 := by
    by_cases he : s 52 = 0
    · exact Or.inr ((row0 (s 21)).mp (he ▸ hs 52 21 (by decide +kernel)))
    · exact Or.inl he
  have c3022 : s 52 ≠ 1 ∨ s 21 = 0 ∨ s 21 = 2 := by
    by_cases he : s 52 = 1
    · exact Or.inr ((row1 (s 21)).mp (he ▸ hs 52 21 (by decide +kernel)))
    · exact Or.inl he
  have c3023 : s 52 ≠ 2 ∨ s 21 = 0 ∨ s 21 = 1 := by
    by_cases he : s 52 = 2
    · exact Or.inr ((row2 (s 21)).mp (he ▸ hs 52 21 (by decide +kernel)))
    · exact Or.inl he
  have c3024 : s 52 ≠ 3 ∨ s 21 = 0 ∨ s 21 = 4 := by
    by_cases he : s 52 = 3
    · exact Or.inr ((row3 (s 21)).mp (he ▸ hs 52 21 (by decide +kernel)))
    · exact Or.inl he
  have c3027 : s 52 ≠ 1 ∨ s 22 = 0 ∨ s 22 = 2 := by
    by_cases he : s 52 = 1
    · exact Or.inr ((row1 (s 22)).mp (he ▸ hs 52 22 (by decide +kernel)))
    · exact Or.inl he
  have c3032 : s 52 ≠ 1 ∨ s 23 = 0 ∨ s 23 = 2 := by
    by_cases he : s 52 = 1
    · exact Or.inr ((row1 (s 23)).mp (he ▸ hs 52 23 (by decide +kernel)))
    · exact Or.inl he
  have c3047 : s 53 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2 := by
    by_cases he : s 53 = 1
    · exact Or.inr ((row1 (s 43)).mp (he ▸ hs 53 43 (by decide +kernel)))
    · exact Or.inl he
  have c3048 : s 53 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1 := by
    by_cases he : s 53 = 2
    · exact Or.inr ((row2 (s 43)).mp (he ▸ hs 53 43 (by decide +kernel)))
    · exact Or.inl he
  have c3051 : s 53 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3 := by
    by_cases he : s 53 = 0
    · exact Or.inr ((row0 (s 13)).mp (he ▸ hs 53 13 (by decide +kernel)))
    · exact Or.inl he
  have c3057 : s 53 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2 := by
    by_cases he : s 53 = 1
    · exact Or.inr ((row1 (s 19)).mp (he ▸ hs 53 19 (by decide +kernel)))
    · exact Or.inl he
  have c3062 : s 53 ≠ 1 ∨ s 24 = 0 ∨ s 24 = 2 := by
    by_cases he : s 53 = 1
    · exact Or.inr ((row1 (s 24)).mp (he ▸ hs 53 24 (by decide +kernel)))
    · exact Or.inl he
  have c3063 : s 53 ≠ 2 ∨ s 24 = 0 ∨ s 24 = 1 := by
    by_cases he : s 53 = 2
    · exact Or.inr ((row2 (s 24)).mp (he ▸ hs 53 24 (by decide +kernel)))
    · exact Or.inl he
  have c3087 : s 53 ≠ 1 ∨ s 29 = 0 ∨ s 29 = 2 := by
    by_cases he : s 53 = 1
    · exact Or.inr ((row1 (s 29)).mp (he ▸ hs 53 29 (by decide +kernel)))
    · exact Or.inl he
  have c3088 : s 53 ≠ 2 ∨ s 29 = 0 ∨ s 29 = 1 := by
    by_cases he : s 53 = 2
    · exact Or.inr ((row2 (s 29)).mp (he ▸ hs 53 29 (by decide +kernel)))
    · exact Or.inl he
  have c3093 : s 54 ≠ 2 ∨ s 40 = 0 ∨ s 40 = 1 := by
    by_cases he : s 54 = 2
    · exact Or.inr ((row2 (s 40)).mp (he ▸ hs 54 40 (by decide +kernel)))
    · exact Or.inl he
  have c3107 : s 54 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2 := by
    by_cases he : s 54 = 1
    · exact Or.inr ((row1 (s 43)).mp (he ▸ hs 54 43 (by decide +kernel)))
    · exact Or.inl he
  have c3109 : s 54 ≠ 3 ∨ s 43 = 0 ∨ s 43 = 4 := by
    by_cases he : s 54 = 3
    · exact Or.inr ((row3 (s 43)).mp (he ▸ hs 54 43 (by decide +kernel)))
    · exact Or.inl he
  have c3112 : s 54 ≠ 1 ∨ s 44 = 0 ∨ s 44 = 2 := by
    by_cases he : s 54 = 1
    · exact Or.inr ((row1 (s 44)).mp (he ▸ hs 54 44 (by decide +kernel)))
    · exact Or.inl he
  have c3113 : s 54 ≠ 2 ∨ s 44 = 0 ∨ s 44 = 1 := by
    by_cases he : s 54 = 2
    · exact Or.inr ((row2 (s 44)).mp (he ▸ hs 54 44 (by decide +kernel)))
    · exact Or.inl he
  have c3116 : s 54 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3 := by
    by_cases he : s 54 = 0
    · exact Or.inr ((row0 (s 13)).mp (he ▸ hs 54 13 (by decide +kernel)))
    · exact Or.inl he
  have c3117 : s 54 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2 := by
    by_cases he : s 54 = 1
    · exact Or.inr ((row1 (s 13)).mp (he ▸ hs 54 13 (by decide +kernel)))
    · exact Or.inl he
  have c3122 : s 54 ≠ 1 ∨ s 19 = 0 ∨ s 19 = 2 := by
    by_cases he : s 54 = 1
    · exact Or.inr ((row1 (s 19)).mp (he ▸ hs 54 19 (by decide +kernel)))
    · exact Or.inl he
  have c3123 : s 54 ≠ 2 ∨ s 19 = 0 ∨ s 19 = 1 := by
    by_cases he : s 54 = 2
    · exact Or.inr ((row2 (s 19)).mp (he ▸ hs 54 19 (by decide +kernel)))
    · exact Or.inl he
  have c3127 : s 54 ≠ 1 ∨ s 24 = 0 ∨ s 24 = 2 := by
    by_cases he : s 54 = 1
    · exact Or.inr ((row1 (s 24)).mp (he ▸ hs 54 24 (by decide +kernel)))
    · exact Or.inl he
  have c3128 : s 54 ≠ 2 ∨ s 24 = 0 ∨ s 24 = 1 := by
    by_cases he : s 54 = 2
    · exact Or.inr ((row2 (s 24)).mp (he ▸ hs 54 24 (by decide +kernel)))
    · exact Or.inl he
  have c3136 : s 55 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3 := by
    by_cases he : s 55 = 0
    · exact Or.inr ((row0 (s 34)).mp (he ▸ hs 55 34 (by decide +kernel)))
    · exact Or.inl he
  have c3137 : s 55 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2 := by
    by_cases he : s 55 = 1
    · exact Or.inr ((row1 (s 34)).mp (he ▸ hs 55 34 (by decide +kernel)))
    · exact Or.inl he
  have c3141 : s 55 ≠ 0 ∨ s 39 = 1 ∨ s 39 = 2 ∨ s 39 = 3 := by
    by_cases he : s 55 = 0
    · exact Or.inr ((row0 (s 39)).mp (he ▸ hs 55 39 (by decide +kernel)))
    · exact Or.inl he
  have c3143 : s 55 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1 := by
    by_cases he : s 55 = 2
    · exact Or.inr ((row2 (s 39)).mp (he ▸ hs 55 39 (by decide +kernel)))
    · exact Or.inl he
  have c3146 : s 55 ≠ 0 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 10 = 3 := by
    by_cases he : s 55 = 0
    · exact Or.inr ((row0 (s 10)).mp (he ▸ hs 55 10 (by decide +kernel)))
    · exact Or.inl he
  have c3147 : s 55 ≠ 1 ∨ s 10 = 0 ∨ s 10 = 2 := by
    by_cases he : s 55 = 1
    · exact Or.inr ((row1 (s 10)).mp (he ▸ hs 55 10 (by decide +kernel)))
    · exact Or.inl he
  have c3152 : s 55 ≠ 1 ∨ s 11 = 0 ∨ s 11 = 2 := by
    by_cases he : s 55 = 1
    · exact Or.inr ((row1 (s 11)).mp (he ▸ hs 55 11 (by decide +kernel)))
    · exact Or.inl he
  have c3153 : s 55 ≠ 2 ∨ s 11 = 0 ∨ s 11 = 1 := by
    by_cases he : s 55 = 2
    · exact Or.inr ((row2 (s 11)).mp (he ▸ hs 55 11 (by decide +kernel)))
    · exact Or.inl he
  have c3161 : s 55 ≠ 0 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 13 = 3 := by
    by_cases he : s 55 = 0
    · exact Or.inr ((row0 (s 13)).mp (he ▸ hs 55 13 (by decide +kernel)))
    · exact Or.inl he
  have c3162 : s 55 ≠ 1 ∨ s 13 = 0 ∨ s 13 = 2 := by
    by_cases he : s 55 = 1
    · exact Or.inr ((row1 (s 13)).mp (he ▸ hs 55 13 (by decide +kernel)))
    · exact Or.inl he
  have c3163 : s 55 ≠ 2 ∨ s 13 = 0 ∨ s 13 = 1 := by
    by_cases he : s 55 = 2
    · exact Or.inr ((row2 (s 13)).mp (he ▸ hs 55 13 (by decide +kernel)))
    · exact Or.inl he
  have c3164 : s 55 ≠ 3 ∨ s 13 = 0 ∨ s 13 = 4 := by
    by_cases he : s 55 = 3
    · exact Or.inr ((row3 (s 13)).mp (he ▸ hs 55 13 (by decide +kernel)))
    · exact Or.inl he
  have c3166 : s 55 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3 := by
    by_cases he : s 55 = 0
    · exact Or.inr ((row0 (s 14)).mp (he ▸ hs 55 14 (by decide +kernel)))
    · exact Or.inl he
  have c3167 : s 55 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2 := by
    by_cases he : s 55 = 1
    · exact Or.inr ((row1 (s 14)).mp (he ▸ hs 55 14 (by decide +kernel)))
    · exact Or.inl he
  have c3168 : s 55 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1 := by
    by_cases he : s 55 = 2
    · exact Or.inr ((row2 (s 14)).mp (he ▸ hs 55 14 (by decide +kernel)))
    · exact Or.inl he
  have c3169 : s 55 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4 := by
    by_cases he : s 55 = 3
    · exact Or.inr ((row3 (s 14)).mp (he ▸ hs 55 14 (by decide +kernel)))
    · exact Or.inl he
  have c3180 : s 55 ≠ 4 ∨ s 29 = 3 ∨ s 29 = 4 := by
    by_cases he : s 55 = 4
    · exact Or.inr ((row4 (s 29)).mp (he ▸ hs 55 29 (by decide +kernel)))
    · exact Or.inl he
  have c3188 : s 56 ≠ 2 ∨ s 39 = 0 ∨ s 39 = 1 := by
    by_cases he : s 56 = 2
    · exact Or.inr ((row2 (s 39)).mp (he ▸ hs 56 39 (by decide +kernel)))
    · exact Or.inl he
  have c3196 : s 56 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3 := by
    by_cases he : s 56 = 0
    · exact Or.inr ((row0 (s 14)).mp (he ▸ hs 56 14 (by decide +kernel)))
    · exact Or.inl he
  have c3197 : s 56 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2 := by
    by_cases he : s 56 = 1
    · exact Or.inr ((row1 (s 14)).mp (he ▸ hs 56 14 (by decide +kernel)))
    · exact Or.inl he
  have c3198 : s 56 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1 := by
    by_cases he : s 56 = 2
    · exact Or.inr ((row2 (s 14)).mp (he ▸ hs 56 14 (by decide +kernel)))
    · exact Or.inl he
  have c3202 : s 56 ≠ 1 ∨ s 25 = 0 ∨ s 25 = 2 := by
    by_cases he : s 56 = 1
    · exact Or.inr ((row1 (s 25)).mp (he ▸ hs 56 25 (by decide +kernel)))
    · exact Or.inl he
  have c3207 : s 56 ≠ 1 ∨ s 26 = 0 ∨ s 26 = 2 := by
    by_cases he : s 56 = 1
    · exact Or.inr ((row1 (s 26)).mp (he ▸ hs 56 26 (by decide +kernel)))
    · exact Or.inl he
  have c3208 : s 56 ≠ 2 ∨ s 26 = 0 ∨ s 26 = 1 := by
    by_cases he : s 56 = 2
    · exact Or.inr ((row2 (s 26)).mp (he ▸ hs 56 26 (by decide +kernel)))
    · exact Or.inl he
  have c3225 : s 56 ≠ 4 ∨ s 29 = 3 ∨ s 29 = 4 := by
    by_cases he : s 56 = 4
    · exact Or.inr ((row4 (s 29)).mp (he ▸ hs 56 29 (by decide +kernel)))
    · exact Or.inl he
  have c3226 : s 57 ≠ 0 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 32 = 3 := by
    by_cases he : s 57 = 0
    · exact Or.inr ((row0 (s 32)).mp (he ▸ hs 57 32 (by decide +kernel)))
    · exact Or.inl he
  have c3237 : s 57 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2 := by
    by_cases he : s 57 = 1
    · exact Or.inr ((row1 (s 34)).mp (he ▸ hs 57 34 (by decide +kernel)))
    · exact Or.inl he
  have c3251 : s 57 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3 := by
    by_cases he : s 57 = 0
    · exact Or.inr ((row0 (s 14)).mp (he ▸ hs 57 14 (by decide +kernel)))
    · exact Or.inl he
  have c3252 : s 57 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2 := by
    by_cases he : s 57 = 1
    · exact Or.inr ((row1 (s 14)).mp (he ▸ hs 57 14 (by decide +kernel)))
    · exact Or.inl he
  have c3253 : s 57 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1 := by
    by_cases he : s 57 = 2
    · exact Or.inr ((row2 (s 14)).mp (he ▸ hs 57 14 (by decide +kernel)))
    · exact Or.inl he
  have c3254 : s 57 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4 := by
    by_cases he : s 57 = 3
    · exact Or.inr ((row3 (s 14)).mp (he ▸ hs 57 14 (by decide +kernel)))
    · exact Or.inl he
  have c3255 : s 57 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4 := by
    by_cases he : s 57 = 4
    · exact Or.inr ((row4 (s 14)).mp (he ▸ hs 57 14 (by decide +kernel)))
    · exact Or.inl he
  have c3271 : s 58 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3 := by
    by_cases he : s 58 = 0
    · exact Or.inr ((row0 (s 34)).mp (he ▸ hs 58 34 (by decide +kernel)))
    · exact Or.inl he
  have c3273 : s 58 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1 := by
    by_cases he : s 58 = 2
    · exact Or.inr ((row2 (s 34)).mp (he ▸ hs 58 34 (by decide +kernel)))
    · exact Or.inl he
  have c3281 : s 58 ≠ 0 ∨ s 36 = 1 ∨ s 36 = 2 ∨ s 36 = 3 := by
    by_cases he : s 58 = 0
    · exact Or.inr ((row0 (s 36)).mp (he ▸ hs 58 36 (by decide +kernel)))
    · exact Or.inl he
  have c3282 : s 58 ≠ 1 ∨ s 36 = 0 ∨ s 36 = 2 := by
    by_cases he : s 58 = 1
    · exact Or.inr ((row1 (s 36)).mp (he ▸ hs 58 36 (by decide +kernel)))
    · exact Or.inl he
  have c3283 : s 58 ≠ 2 ∨ s 36 = 0 ∨ s 36 = 1 := by
    by_cases he : s 58 = 2
    · exact Or.inr ((row2 (s 36)).mp (he ▸ hs 58 36 (by decide +kernel)))
    · exact Or.inl he
  have c3288 : s 58 ≠ 2 ∨ s 37 = 0 ∨ s 37 = 1 := by
    by_cases he : s 58 = 2
    · exact Or.inr ((row2 (s 37)).mp (he ▸ hs 58 37 (by decide +kernel)))
    · exact Or.inl he
  have c3292 : s 58 ≠ 1 ∨ s 38 = 0 ∨ s 38 = 2 := by
    by_cases he : s 58 = 1
    · exact Or.inr ((row1 (s 38)).mp (he ▸ hs 58 38 (by decide +kernel)))
    · exact Or.inl he
  have c3293 : s 58 ≠ 2 ∨ s 38 = 0 ∨ s 38 = 1 := by
    by_cases he : s 58 = 2
    · exact Or.inr ((row2 (s 38)).mp (he ▸ hs 58 38 (by decide +kernel)))
    · exact Or.inl he
  have c3306 : s 58 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3 := by
    by_cases he : s 58 = 0
    · exact Or.inr ((row0 (s 14)).mp (he ▸ hs 58 14 (by decide +kernel)))
    · exact Or.inl he
  have c3307 : s 58 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2 := by
    by_cases he : s 58 = 1
    · exact Or.inr ((row1 (s 14)).mp (he ▸ hs 58 14 (by decide +kernel)))
    · exact Or.inl he
  have c3308 : s 58 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1 := by
    by_cases he : s 58 = 2
    · exact Or.inr ((row2 (s 14)).mp (he ▸ hs 58 14 (by decide +kernel)))
    · exact Or.inl he
  have c3309 : s 58 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4 := by
    by_cases he : s 58 = 3
    · exact Or.inr ((row3 (s 14)).mp (he ▸ hs 58 14 (by decide +kernel)))
    · exact Or.inl he
  have c3310 : s 58 ≠ 4 ∨ s 14 = 3 ∨ s 14 = 4 := by
    by_cases he : s 58 = 4
    · exact Or.inr ((row4 (s 14)).mp (he ▸ hs 58 14 (by decide +kernel)))
    · exact Or.inl he
  have c3311 : s 58 ≠ 0 ∨ s 29 = 1 ∨ s 29 = 2 ∨ s 29 = 3 := by
    by_cases he : s 58 = 0
    · exact Or.inr ((row0 (s 29)).mp (he ▸ hs 58 29 (by decide +kernel)))
    · exact Or.inl he
  have c3315 : s 58 ≠ 4 ∨ s 29 = 3 ∨ s 29 = 4 := by
    by_cases he : s 58 = 4
    · exact Or.inr ((row4 (s 29)).mp (he ▸ hs 58 29 (by decide +kernel)))
    · exact Or.inl he
  have c3316 : s 59 ≠ 0 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 34 = 3 := by
    by_cases he : s 59 = 0
    · exact Or.inr ((row0 (s 34)).mp (he ▸ hs 59 34 (by decide +kernel)))
    · exact Or.inl he
  have c3317 : s 59 ≠ 1 ∨ s 34 = 0 ∨ s 34 = 2 := by
    by_cases he : s 59 = 1
    · exact Or.inr ((row1 (s 34)).mp (he ▸ hs 59 34 (by decide +kernel)))
    · exact Or.inl he
  have c3318 : s 59 ≠ 2 ∨ s 34 = 0 ∨ s 34 = 1 := by
    by_cases he : s 59 = 2
    · exact Or.inr ((row2 (s 34)).mp (he ▸ hs 59 34 (by decide +kernel)))
    · exact Or.inl he
  have c3341 : s 59 ≠ 0 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 43 = 3 := by
    by_cases he : s 59 = 0
    · exact Or.inr ((row0 (s 43)).mp (he ▸ hs 59 43 (by decide +kernel)))
    · exact Or.inl he
  have c3342 : s 59 ≠ 1 ∨ s 43 = 0 ∨ s 43 = 2 := by
    by_cases he : s 59 = 1
    · exact Or.inr ((row1 (s 43)).mp (he ▸ hs 59 43 (by decide +kernel)))
    · exact Or.inl he
  have c3343 : s 59 ≠ 2 ∨ s 43 = 0 ∨ s 43 = 1 := by
    by_cases he : s 59 = 2
    · exact Or.inr ((row2 (s 43)).mp (he ▸ hs 59 43 (by decide +kernel)))
    · exact Or.inl he
  have c3347 : s 59 ≠ 1 ∨ s 44 = 0 ∨ s 44 = 2 := by
    by_cases he : s 59 = 1
    · exact Or.inr ((row1 (s 44)).mp (he ▸ hs 59 44 (by decide +kernel)))
    · exact Or.inl he
  have c3351 : s 59 ≠ 0 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 14 = 3 := by
    by_cases he : s 59 = 0
    · exact Or.inr ((row0 (s 14)).mp (he ▸ hs 59 14 (by decide +kernel)))
    · exact Or.inl he
  have c3352 : s 59 ≠ 1 ∨ s 14 = 0 ∨ s 14 = 2 := by
    by_cases he : s 59 = 1
    · exact Or.inr ((row1 (s 14)).mp (he ▸ hs 59 14 (by decide +kernel)))
    · exact Or.inl he
  have c3353 : s 59 ≠ 2 ∨ s 14 = 0 ∨ s 14 = 1 := by
    by_cases he : s 59 = 2
    · exact Or.inr ((row2 (s 14)).mp (he ▸ hs 59 14 (by decide +kernel)))
    · exact Or.inl he
  have c3354 : s 59 ≠ 3 ∨ s 14 = 0 ∨ s 14 = 4 := by
    by_cases he : s 59 = 3
    · exact Or.inr ((row3 (s 14)).mp (he ▸ hs 59 14 (by decide +kernel)))
    · exact Or.inl he
  have c3361 : s 0 = 1 ∨ s 0 = 2 ∨ s 1 = 1 ∨ s 1 = 2 ∨ s 2 = 1 ∨ s 2 = 2 ∨ s 3 = 1 ∨ s 3 = 2 ∨ s 4 = 1 ∨ s 4 = 2 ∨ s 5 = 1 ∨ s 5 = 2 ∨ s 6 = 1 ∨ s 6 = 2 ∨ s 7 = 1 ∨ s 7 = 2 ∨ s 8 = 1 ∨ s 8 = 2 ∨ s 9 = 1 ∨ s 9 = 2 ∨ s 10 = 1 ∨ s 10 = 2 ∨ s 11 = 1 ∨ s 11 = 2 ∨ s 12 = 1 ∨ s 12 = 2 ∨ s 13 = 1 ∨ s 13 = 2 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 15 = 1 ∨ s 15 = 2 ∨ s 16 = 1 ∨ s 16 = 2 ∨ s 17 = 1 ∨ s 17 = 2 ∨ s 18 = 1 ∨ s 18 = 2 ∨ s 19 = 1 ∨ s 19 = 2 ∨ s 20 = 1 ∨ s 20 = 2 ∨ s 21 = 1 ∨ s 21 = 2 ∨ s 22 = 1 ∨ s 22 = 2 ∨ s 23 = 1 ∨ s 23 = 2 ∨ s 24 = 1 ∨ s 24 = 2 ∨ s 25 = 1 ∨ s 25 = 2 ∨ s 26 = 1 ∨ s 26 = 2 ∨ s 27 = 1 ∨ s 27 = 2 ∨ s 28 = 1 ∨ s 28 = 2 ∨ s 29 = 1 ∨ s 29 = 2 ∨ s 30 = 1 ∨ s 30 = 2 ∨ s 31 = 1 ∨ s 31 = 2 ∨ s 32 = 1 ∨ s 32 = 2 ∨ s 33 = 1 ∨ s 33 = 2 ∨ s 34 = 1 ∨ s 34 = 2 ∨ s 35 = 1 ∨ s 35 = 2 ∨ s 36 = 1 ∨ s 36 = 2 ∨ s 37 = 1 ∨ s 37 = 2 ∨ s 38 = 1 ∨ s 38 = 2 ∨ s 39 = 1 ∨ s 39 = 2 ∨ s 40 = 1 ∨ s 40 = 2 ∨ s 41 = 1 ∨ s 41 = 2 ∨ s 42 = 1 ∨ s 42 = 2 ∨ s 43 = 1 ∨ s 43 = 2 ∨ s 44 = 1 ∨ s 44 = 2 ∨ s 45 = 1 ∨ s 45 = 2 ∨ s 46 = 1 ∨ s 46 = 2 ∨ s 47 = 1 ∨ s 47 = 2 ∨ s 48 = 1 ∨ s 48 = 2 ∨ s 49 = 1 ∨ s 49 = 2 ∨ s 50 = 1 ∨ s 50 = 2 ∨ s 51 = 1 ∨ s 51 = 2 ∨ s 52 = 1 ∨ s 52 = 2 ∨ s 53 = 1 ∨ s 53 = 2 ∨ s 54 = 1 ∨ s 54 = 2 ∨ s 55 = 1 ∨ s 55 = 2 ∨ s 56 = 1 ∨ s 56 = 2 ∨ s 57 = 1 ∨ s 57 = 2 ∨ s 58 = 1 ∨ s 58 = 2 ∨ s 59 = 1 ∨ s 59 = 2 := by
    obtain ⟨i,hi⟩ := hbad
    fin_cases i
    · exact hi.elim (fun h => (Or.inl h)) (fun h => (Or.inr (Or.inl h)))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inl h)))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    · exact hi.elim (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (fun h => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  have c3362 : s 57 ≠ 4 ∨ s 58 ≠ 4 ∨ s 59 ≠ 4 := step3362 s c660 c659 c657 c2006 c654 c2008 c2412 c1331 c1333 c3307 c1332 c3308 c649 c2371 c1928 c1883 c2007 c2413 c1927 c1882 c1813 c1812 c2281 c643 c2283 c1522 c1387 c1367 c2282 c1523 c1388 c1368 c2328 c2238 c2327 c2237 c2636 c2638 c3002 c2591 c2593 c2762 c2717 c2546 c2548 c1757 c1597 c2501 c2503 c892 c1072 c2456 c2458 c1857 c1682 c997 c1502 c2231 c2233 c807 c1622 c1167 c942 c787 c2862 c2897 c1042 c3107 c3047 c2957 c1727 c2637 c3003 c2502 c893 c1073 c788 c2133 c1463 c3252 c3048 c2958 c2938 c2592 c2813 c2763 c2833 c2718 c2547 c1758 c1598 c2873 c3093 c1713 c1028 c2457 c3143 c1858 c1683 c998 c3188 c1503 c2232 c808 c1623 c1168 c943 c3197 c3167 c2932 c2807 c2132 c1462 c3253 c2683 c2682 c632 c638 c2097 c2052 c2187 c2053 c2098 c2188 c2051 c2141 c703 c747 c882 c702 c748 c883 c1112 c1202 c1247 c1113 c1203 c1248 c3361
  have c3363 : s 57 = 3 ∨ s 57 = 4 ∨ s 59 ≠ 4 := step3363 s c657 c654 c1333 c660 c659 c1331 c3252 c1332 c3253 c2141 c628 c2145 c3251 c1294
  have c3364 : s 58 ≠ 4 ∨ s 59 ≠ 4 := step3364 s c660 c659 c657 c2636 c654 c2638 c3002 c2591 c2593 c2762 c2717 c2546 c2548 c1757 c1597 c2501 c2503 c892 c1072 c2456 c2458 c1857 c1682 c997 c1502 c2231 c2233 c807 c1622 c1167 c942 c2006 c2008 c787 c2862 c2412 c2897 c1042 c3107 c3047 c2957 c1727 c2637 c3003 c2502 c893 c1073 c2007 c788 c2413 c1332 c1331 c2133 c1463 c1333 c3252 c3048 c2958 c2938 c2592 c2813 c2763 c2833 c2718 c2547 c1758 c1598 c2873 c3093 c1713 c1028 c2457 c3143 c1858 c1683 c998 c3188 c1503 c2232 c808 c1623 c1168 c943 c3307 c3197 c3167 c2932 c2807 c2132 c1462 c3308 c3253 c2683 c2682 c643 c649 c2237 c2282 c2327 c2238 c2283 c2328 c2281 c2371 c1368 c1388 c1523 c1367 c1387 c1522 c1812 c1813 c1882 c1927 c1883 c1928 c3362 c3363 c631 c1324 c2054 c2097 c2052 c2187 c2053 c2098 c2188 c3166 c2806 c1461 c1641 c1152 c1153 c1242 c1287 c1243 c1288 c857 c858 c677 c678 c722 c723 c3361
  have c3365 : s 57 = 4 ∨ s 59 ≠ 4 := step3365 s c660 c659 c657 c2636 c654 c2638 c3002 c2591 c2593 c2762 c2717 c2546 c2548 c1757 c1597 c2501 c2503 c892 c1072 c2456 c2458 c1857 c1682 c997 c1502 c2231 c2233 c807 c1622 c1167 c942 c2006 c2008 c787 c2862 c2412 c2897 c1042 c3107 c3047 c2957 c1727 c2637 c3003 c2502 c893 c1073 c2007 c788 c2413 c1332 c1331 c2133 c1463 c1333 c3252 c3048 c2958 c2938 c2592 c2813 c2763 c2833 c2718 c2547 c1758 c1598 c2873 c3093 c1713 c1028 c2457 c3143 c1858 c1683 c998 c3188 c1503 c2232 c808 c1623 c1168 c943 c3307 c3197 c3167 c2932 c2807 c2132 c1462 c3308 c3253 c2683 c2682 c3363 c631 c1324 c1999 c2054 c2097 c2052 c2187 c2053 c2098 c2188 c3196 c3306 c3166 c2931 c2806 c1461 c786 c966 c1641 c1827 c1828 c1963 c1918 c1962 c1917 c2237 c2282 c2327 c2238 c2283 c2328 c1152 c1153 c1242 c1287 c1243 c1288 c1537 c1538 c857 c858 c677 c678 c1347 c1348 c1397 c1398 c722 c723 c3361
  have c3366 : s 14 = 3 ∨ s 59 ≠ 4 := step3366 s c660 c659 c657 c1331 c654 c1333 c2132 c3252 c1332 c3253 c3365 c638 c2141 c1248 c1203 c1113 c2133 c1247 c1202 c1112 c632 c2053 c2051 c702 c882 c747 c2052 c883 c748 c703 c2188 c2098 c2187 c2097 c3364 c2636 c2638 c3002 c2591 c2593 c2762 c2717 c2546 c2548 c1757 c1597 c2501 c2503 c892 c1072 c2456 c2458 c1857 c1682 c997 c1502 c2231 c2233 c807 c1622 c1167 c942 c2006 c2008 c787 c2862 c2412 c2897 c1042 c3107 c3047 c2957 c1727 c2637 c3003 c2502 c893 c1073 c2007 c788 c2413 c1463 c3048 c2958 c2938 c2592 c2813 c2763 c2833 c2718 c2547 c1758 c1598 c2873 c3093 c1713 c1028 c2457 c3143 c1858 c1683 c998 c3188 c1503 c2232 c808 c1623 c1168 c943 c3307 c3197 c3167 c2932 c2807 c1462 c3308 c2683 c2682 c3196 c3306 c2931 c1827 c1828 c1963 c1918 c1962 c1917 c2004 c2229 c2237 c2282 c2327 c2238 c2283 c2328 c1537 c1538 c786 c941 c1347 c1348 c1397 c1398 c3361
  have c3367 : s 59 ≠ 4 := step3367 s c654 c657 c659 c660 c1332 c1333 c2007 c1331 c2008 c3308 c3307 c3364 c3366 c165 c1329 c3309 c3311 c2371 c2375 c1974
  have c3368 : s 14 ≠ 3 ∨ s 14 = 1 ∨ s 14 = 2 ∨ s 57 = 1 ∨ s 57 = 2 := step3368 s c3367 c158 c165 c3352 c3353 c3354 c1463 c2133 c2808 c2933 c3168 c3198 c1462 c2132 c2807 c2932 c3167 c3197 c3307 c3308 c1464 c2134 c2809 c3254 c2006 c2231 c2456 c2681 c2235 c676 c1256 c1606 c796 c931 c3226 c856 c2051 c2096 c2141 c2186 c1624 c809 c1169 c2097 c2222 c2052 c2187 c2053 c2098 c2188 c1997 c2672 c2447 c1998 c2223 c2673 c2448 c793 c833 c968 c1193 c1643 c703 c748 c883 c747 c882 c702 c928 c1063 c1108 c1112 c1202 c1247 c1113 c1203 c1248 c1607 c797 c932 c1157 c3021 c1351 c2701 c1446 c2916 c1018 c1588 c1658 c1703 c1748 c792 c927 c1017 c1062 c1107 c1587 c1657 c1702 c1747 c2413 c2863 c3088 c3113 c2903 c1503 c1858 c2412 c2862 c3087 c3112 c2902 c1502 c1857 c2702 c1352 c1802 c2467 c2742 c1397 c2247 c2347 c2522 c3022 c1517 c2708 c2733 c1358 c1808 c1383 c1518 c2963 c3008 c2962 c2523 c2348 c2468 c2248 c1947 c1948 c2293 c1887 c2557 c1888 c2558 c2302 c2608 c2607 c3361
  have c3369 : s 59 ≠ 1 ∨ s 3 = 2 ∨ s 3 = 1 ∨ s 34 = 2 ∨ s 32 = 0 ∨ s 14 = 3 := step3369 s c3367 c656 c3317 c1335 c2191 c2135 c799
  have c3370 : s 14 = 1 ∨ s 14 = 2 ∨ s 57 = 2 ∨ s 57 = 1 := step3370 s c3367 c3368 c3251 c2931 c2806 c2131 c1461 c3351 c2097 c2142 c2222 c2052 c2187 c2053 c2098 c2188 c1997 c2672 c2447 c1998 c2143 c2223 c2673 c2448 c1112 c1202 c1247 c1113 c1203 c1248 c1607 c797 c932 c1157 c933 c1158 c1608 c798 c2009 c2234 c2459 c2504 c2549 c2594 c2639 c2411 c786 c2861 c1166 c1621 c806 c941 c1501 c1856 c1448 c2793 c2918 c3153 c1447 c2792 c2917 c3152 c2523 c3023 c2348 c723 c2347 c722 c2522 c3022 c1578 c2703 c1353 c1803 c1577 c2702 c1352 c1802 c2468 c2743 c1398 c2248 c2467 c2742 c1397 c2247 c2977 c677 c2302 c912 c857 c1087 c1897 c2567 c1762 c1937 c2607 c1537 c2978 c678 c2303 c913 c858 c1898 c2568 c1088 c1763 c1938 c2608 c1538 c1756 c1596 c762 c891 c1071 c1488 c2828 c2878 c3063 c3128 c1487 c2761 c2827 c2877 c3062 c3127 c3001 c763 c1833 c2382 c1862 c2383 c1007 c1052 c1008 c1053 c1693 c1738 c1692 c1737 c3207 c3293 c3208 c3292 c3369 c3361 c658 c3318 c1335 c2191 c2135 c799
  have c3371 : s 59 ≠ 2 ∨ s 3 = 2 ∨ s 21 = 2 ∨ s 11 = 2 ∨ s 6 = 2 ∨ s 5 = 3 ∨ s 11 = 3 ∨ s 6 = 3 ∨ s 3 = 3 ∨ s 21 = 3 ∨ s 34 = 0 ∨ s 50 = 1 ∨ s 17 = 1 ∨ s 59 = 1 := step3371 s c3367 c652 c3318 c2549 c2233 c2503 c2548 c2207 c942 c1167 c1622 c807 c1631 c2466 c1446 c2916 c3021 c1576 c2517 c892 c913 c1538 c1603 c1526 c3012
  have c3372 : s 52 ≠ 1 ∨ s 43 = 0 ∨ s 13 = 2 ∨ s 50 = 3 ∨ s 50 = 1 := step3372 s c574 c578 c3007 c2617 c1261 c2938
  have c3374 : s 17 ≠ 2 ∨ s 37 = 0 ∨ s 51 = 1 ∨ s 19 = 3 ∨ s 19 = 2 ∨ s 24 = 2 ∨ s 51 = 3 ∨ s 58 = 3 ∨ s 58 = 1 ∨ s 17 = 1 := step3374 s c190 c1468 c2978 c2303 c2986 c1766 c1522 c2362 c2281 c3288
  have c3375 : s 52 = 0 ∨ s 52 = 1 ∨ s 43 = 0 ∨ s 52 = 4 ∨ s 11 = 2 ∨ s 10 = 2 ∨ s 23 = 3 ∨ s 11 = 3 ∨ s 31 = 0 ∨ s 58 = 1 ∨ s 17 = 1 ∨ s 14 ≠ 1 := step3375 s c3367 c162 c156 c3354 c2640 c2959 c1464 c161 c1465 c680 c3309 c1773 c1548 c1549 c2618 c1738 c1727 c1042 c2957 c2356 c3374 c1302 c676 c1126 c2976 c1446 c1384 c1417 c1423 c1197 c1056 c2078
  have c3376 : s 14 = 2 ∨ s 57 = 1 ∨ s 57 = 2 := step3376 s c3367 c3370 c156 c161 c162 c3352 c3354 c1462 c2132 c2932 c3167 c3307 c1464 c3255 c2934 c3254 c3309 c1465 c2135 c2640 c2685 c2100 c2221 c2671 c2096 c2141 c2186 c1260 c1609 c799 c934 c1114 c1159 c1249 c1734 c929 c1113 c1248 c933 c1158 c1608 c798 c3010 c3371 c2636 c3004 c3372 c3375 c575 c3021 c1691 c1546 c1636 c1617 c1622 c2173 c2207 c2213 c248 c3273 c3146 c2317 c2281 c1137 c1523
  have c3377 : s 17 = 1 ∨ s 43 = 0 ∨ s 11 = 1 ∨ s 13 = 1 ∨ s 10 = 1 ∨ s 13 = 3 ∨ s 31 = 0 ∨ s 14 ≠ 2 := step3377 s c157 c164 c1464 c163 c1465 c680 c160 c1463 c1303 c676 c1126 c1176 c1256 c2976 c1456 c1384 c1418 c2088 c2963 c1422 c1268 c1056 c1062 c2957 c2598
  have c3379 : s 36 = 0 ∨ s 7 = 1 ∨ s 37 = 3 ∨ s 19 = 0 ∨ s 18 = 0 ∨ s 52 = 2 ∨ s 36 = 1 ∨ s 17 ≠ 1 ∨ s 52 = 3 ∨ s 21 = 1 := step3379 s c1432 c1523 c1483 c2288 c3012 c2337 c986 c1636 c2348
  have c3380 : s 7 = 1 ∨ s 37 = 3 ∨ s 19 = 0 ∨ s 18 = 0 ∨ s 52 = 2 ∨ s 36 = 1 ∨ s 36 = 3 ∨ s 17 ≠ 1 ∨ s 52 = 3 ∨ s 21 = 1 ∨ s 7 = 3 ∨ s 39 = 0 ∨ s 58 = 2 := step3380 s c3379 c399 c2286 c3281 c998 c2417
  have c3381 : s 13 = 0 ∨ s 36 = 1 ∨ s 51 = 1 ∨ s 36 = 3 ∨ s 17 ≠ 1 ∨ s 52 = 3 ∨ s 51 = 3 ∨ s 18 = 4 ∨ s 21 = 1 ∨ s 13 = 1 ∨ s 7 = 3 ∨ s 31 = 0 ∨ s 39 = 0 ∨ s 58 = 2 := step3381 s c2963 c3008 c1511 c1421 c1541 c2339 c3380 c79 c83 c1017 c2422 c1402 c2093 c1683 c2298 c1636 c3027 c1666
  have c3382 : s 43 = 0 ∨ s 18 = 4 ∨ s 11 = 1 ∨ s 21 = 1 ∨ s 13 = 1 ∨ s 10 = 1 ∨ s 13 = 3 ∨ s 31 = 0 ∨ s 39 = 0 ∨ s 14 ≠ 2 := step3382 s c3367 c164 c157 c3354 c2460 c999 c2640 c163 c1465 c2934 c160 c3308 c2933 c1463 c2959 c3004 c3377 c189 c2304 c2977 c2302 c3381 c146 c1261 c2961 c2937 c2613
  have c3383 : s 57 = 1 ∨ s 57 = 2 := step3383 s c3367 c3376 c157 c160 c163 c164 c3353 c3354 c1463 c2133 c1464 c3254 c3309 c3310 c2135 c2010 c1996 c2221 c2446 c2671 c2096 c2141 c2375 c934 c1249 c2414 c1112 c1247 c1607 c932 c1157 c1500 c3382 c475 c476 c477 c2636 c1041 c3341 c2956 c3317 c3347 c2643 c2232 c2203 c94 c943 c1176 c1407 c1396 c1467 c2973
  have c3384 : s 43 ≠ 0 ∨ s 14 = 0 ∨ s 57 = 2 := step3384 s c3383 c629 c635 c2224 c634 c2225 c810 c2142 c2144 c1322 c2133 c796 c1354 c1246 c1156 c1111 c1325 c3309 c2934 c3308 c2933 c2189 c2187 c2222 c475 c476 c477 c2606 c2936 c3001 c2956 c2917 c1262 c1147 c1182 c1168 c2963 c3008 c1373 c2158 c2226 c1377 c1692 c2291 c1656 c3282 c2318
  have c3385 : s 11 = 1 ∨ s 10 = 1 ∨ s 14 = 0 ∨ s 57 = 2 := step3385 s c3383 c629 c2142 c635 c2144 c1322 c2133 c1111 c1533 c1418 c3384 c634 c2145 c1250 c1246 c2964 c2224 c2225 c1625 c1606 c3024 c1156 c1325 c3354 c3353 c2189 c2099 c2187 c2222 c2097 c2158 c2203 c2088 c1701 c3237 c3316 c1061 c2231 c2637 c3342 c2958 c3003 c1728 c2598 c3032 c1057 c1546 c1421 c2987
  have c3386 : s 10 = 1 ∨ s 14 = 0 ∨ s 57 = 2 := step3386 s c3383 c629 c635 c2144 c634 c2145 c1115 c2142 c1322 c2133 c1111 c1534 c1324 c1325 c2935 c2934 c1940 c1156 c3169 c1464 c3168 c2933 c1463 c1997 c2052 c1533 c3385 c127 c1182 c1447 c2917 c3152 c2941 c676 c2976 c1936 c1536 c1986 c1517 c784 c2987 c788 c703 c1943 c2021 c782
  have c3387 : s 14 = 0 ∨ s 57 = 2 := step3387 s c3383 c629 c635 c2144 c634 c2145 c1115 c2449 c1325 c2447 c1322 c2222 c2142 c1463 c2133 c2933 c3168 c1464 c2934 c3169 c1606 c1111 c1534 c1509 c3386 c116 c1147 c1152 c1442 c1507 c1532 c2912 c3147 c3141 c2976 c2428 c2941 c1761 c2211 c201 c1543 c1623 c2336 c2992 c2347 c1753
  have c3388 : s 10 ≠ 1 ∨ s 57 = 2 := step3388 s c3383 c629 c635 c1324 c634 c1325 c1465 c1322 c3387 c157 c1461 c2979 c2142 c2131 c1608 c1113 c1999 c2000 c3315 c3306 c2329 c2931 c3166 c2449 c2224 c2447 c2222 c112 c1147 c1442 c1507 c1532 c2912 c3147 c2978 c2943 c1763 c2438 c2213 c1541 c1501 c1621 c2992 c2338 c2347 c1751
  have c3389 : s 51 ≠ 1 ∨ s 57 = 2 := step3389 s c3383 c629 c635 c2449 c634 c2450 c1860 c1999 c2000 c3225 c1324 c1322 c3387 c157 c3196 c1874 c2325 c3315 c3306 c2284 c1390 c3180 c3166 c1154 c2142 c2131 c1113 c3388 c1416 c1014 c1506 c1531 c2145 c1609 c1608 c1248 c1289 c2447 c563 c567 c2982 c1512 c1422 c1267 c1542 c1503 c2338 c1013 c3006 c3013 c2421 c987 c1637 c2346
  have c3390 : s 19 = 1 ∨ s 57 = 2 := step3390 s c3389 c3383 c629 c635 c2144 c634 c2145 c1115 c1999 c2000 c3180 c1324 c1322 c3387 c157 c3166 c1154 c1535 c2142 c2131 c1113 c3388 c1531 c2944 c1325 c1465 c1461 c2979 c1248 c2943 c2988 c1306 c1266 c2927
  have c3391 : s 51 = 2 ∨ s 57 = 2 := step3391 s c3367 c3383 c629 c635 c1324 c1322 c3387 c157 c2931 c2142 c2131 c1113 c1999 c634 c2000 c3180 c3166 c1154 c3388 c1531 c3390 c215 c2942 c2608 c922 c3389 c3351 c2504 c1325 c1465 c1461 c2979 c933 c1248 c1289 c2224 c2222 c1542 c2611 c2961 c3342 c1257 c2233 c2503 c1438 c941 c891 c2467
  have c3392 : s 57 = 2 := step3392 s c3383 c629 c634 c635 c2142 c2222 c1322 c2000 c1324 c2145 c1999 c2224 c3180 c3387 c157 c3196 c3166 c2131 c1461 c1154 c1289 c1113 c1248 c1158 c798 c799 c3388 c1371 c1531 c3389 c3390 c215 c3057 c3391 c564 c2978 c1468 c1378 c1447 c1257 c817 c1166 c3051 c1801 c2218 c1823 c3202
  have c3393 : s 57 ≠ 0 := step3393 s c3392 c630
  have c3394 : s 57 ≠ 1 := step3394 s c3392 c633
  have c3395 : s 57 ≠ 3 := step3395 s c3392 c636
  have c3396 : s 57 ≠ 4 := step3396 s c3392 c637
  have c3398 : s 31 ≠ 2 := step3398 s c3393 c3394 c2098
  have c3400 : s 14 ≠ 2 := step3400 s c3393 c3394 c1323
  have c3401 : s 29 ≠ 2 := step3401 s c3393 c3394 c1998
  have c3402 : s 32 ≠ 2 := step3402 s c3393 c3394 c2143
  have c3403 : s 34 ≠ 2 := step3403 s c3393 c3394 c2223
  have c3404 : s 44 ≠ 2 := step3404 s c3393 c3394 c2673
  have c3405 : s 39 ≠ 2 := step3405 s c3393 c3394 c2448
  have c3407 : s 34 ≠ 4 := step3407 s c3395 c3396 c2225
  have c3409 : s 14 ≠ 4 := step3409 s c3395 c3396 c1325
  have c3411 : s 14 ≠ 3 := step3411 s c3396 c3393 c1324
  have c3413 : s 32 ≠ 4 := step3413 s c3396 c3395 c2145
  have c3419 : s 32 ≠ 3 := step3419 s c3396 c3393 c2144
  have c3421 : s 34 ≠ 3 := step3421 s c3396 c3393 c2224
  have c3423 : s 44 ≠ 3 := step3423 s c3396 c3393 c2674
  have c3431 : s 21 ≠ 4 := step3431 s c3407 c3421 c1625
  have c3432 : s 17 ≠ 4 := step3432 s c3409 c3411 c1465
  have c3433 : s 47 ≠ 4 := step3433 s c3409 c3411 c2810
  have c3438 : s 10 ≠ 4 := step3438 s c3413 c3419 c1115
  have c3440 : s 13 ≠ 4 := step3440 s c3413 c3419 c1250
  have c3456 : s 13 = 1 ∨ s 13 = 2 ∨ s 18 = 2 ∨ s 17 = 2 ∨ s 51 ≠ 2 ∨ s 19 ≠ 1 := step3456 s c3402 c3413 c3405 c217 c216 c2990 c564 c1514 c1469 c1269 c3015 c211 c215 c3012 c3122 c2942 c2126 c2963 c2926 c3006 c3116 c1607 c1609 c1256 c1148 c1694 c1693 c1638 c2543 c2521 c1442 c1687 c1131 c2431 c1502
  have c3457 : s 51 ≠ 2 ∨ s 19 ≠ 1 ∨ s 51 = 1 := step3457 s c3402 c3419 c3400 c3409 c3421 c3403 c217 c216 c2990 c211 c215 c2942 c2312 c1137 c2944 c1139 c564 c1468 c1469 c1513 c1768 c1268 c3456 c145 c1247 c2127 c1457 c3162 c2111 c1606 c1111 c1291 c2301 c1153 c2913 c3307 c3309 c3283 c3136 c1761 c2326 c2207 c2362 c1628
  have c3458 : s 13 = 2 ∨ s 13 = 0 ∨ s 51 ≠ 0 ∨ s 17 = 0 ∨ s 10 = 1 ∨ s 10 = 3 := step3458 s c3432 c3402 c1259 c2961 c1457 c1247 c1128 c2111
  have c3459 : s 19 ≠ 1 ∨ s 51 = 1 := step3459 s c3411 c3400 c211 c215 c217 c2989 c1139 c1137 c2942 c3457 c1466 c1542 c1266 c3458 c149 c1263 c1458 c2931 c1302
  have c3460 : s 13 ≠ 2 ∨ s 51 = 2 ∨ s 51 = 1 := step3460 s c3440 c3432 c3411 c3400 c3398 c3423 c3404 c3459 c146 c149 c1268 c2964 c1459 c2929 c1458 c2928 c3163 c1466 c2611 c1541 c912 c2976 c1302 c914 c923 c1462 c3166 c2061 c1306 c2662 c1062 c2937 c1046 c2598
  have c3461 : s 51 ≠ 0 ∨ s 51 = 2 ∨ s 51 = 1 := step3461 s c3432 c3402 c3419 c3404 c3460 c3459 c565 c566 c2615 c1466 c2611 c1266 c1421 c1541 c1129 c3109 c3004 c3117 c3007 c3458 c2127 c1122 c3013 c3123 c2491 c2656 c1736 c931 c1732 c2498 c1398 c952
  have c3462 : s 13 = 0 ∨ s 51 = 2 ∨ s 51 = 1 := step3462 s c3440 c3432 c3461 c2964 c1459 c562 c2980
  have c3463 : s 51 = 2 ∨ s 51 = 1 := step3463 s c3440 c3461 c1468 c1467 c3462 c147 c1256 c2965 c1469
  have c3464 : s 13 ≠ 0 ∨ s 51 = 1 := step3464 s c3402 c3411 c3400 c3403 c3463 c570 c571 c1545 c564 c1544 c3015 c3459 c1543 c3011 c1639 c2311 c2941 c1136 c1469 c1769 c1269 c1268 c1768 c1468 c145 c1256 c2126 c1456 c3161 c1442 c1112 c1607 c1292 c2302 c1153 c2913 c3306 c3283 c3137 c1762 c2327 c2206 c2361 c1628
  have c3465 : s 51 = 1 := step3465 s c3438 c3402 c3419 c3431 c3400 c3421 c3403 c3459 c3463 c564 c571 c2988 c1513 c1543 c1268 c1544 c1136 c2941 c3011 c2914 c3464 c2927 c3007 c2127 c1536 c1183 c1638 c1606 c1156 c1291 c2913 c2202 c2347 c2349 c3307 c1132 c3271 c1491 c2328
  have c3466 : s 51 ≠ 0 := step3466 s c3465 c563
  have c3467 : s 51 ≠ 2 := step3467 s c3465 c567
  have c3468 : s 51 ≠ 3 := step3468 s c3465 c568
  have c3469 : s 51 ≠ 4 := step3469 s c3465 c569
  have c3470 : s 17 ≠ 1 := step3470 s c3466 c3467 c1467
  have c3473 : s 16 ≠ 1 := step3473 s c3466 c3467 c1422
  have c3474 : s 43 ≠ 1 := step3474 s c3466 c3467 c2612
  have c3475 : s 13 ≠ 1 := step3475 s c3466 c3467 c1267
  have c3476 : s 28 ≠ 1 := step3476 s c3466 c3467 c1942
  have c3478 : s 19 ≠ 1 := step3478 s c3467 c3466 c1542
  have c3480 : s 16 ≠ 4 := step3480 s c3469 c3468 c1425
  have c3485 : s 19 ≠ 3 := step3485 s c3469 c3466 c1544
  have c3488 : s 13 ≠ 3 := step3488 s c3469 c3466 c1269
  have c3490 : s 17 ≠ 3 := step3490 s c3469 c3466 c1469
  have c3498 : s 13 = 0 := step3498 s c3440 c3465 c3475 c3433 c3490 c3470 c3411 c3400 c3402 c3419 c3478 c3485 c3476 c3403 c3401 c2804 c2929 c3164 c2962 c2928 c2803 c3163 c1458 c1900 c1258 c1301 c1126 c1461 c2132 c2807 c2932 c3167 c1307 c796 c1896 c1936 c2211 c1986 c2941 c779 c783 c807 c787 c1533 c1353 c1346 c1117
  have c3499 : s 13 ≠ 2 := step3499 s c3498 c146
  have c3500 : s 17 = 2 := step3500 s c3498 c3490 c3470 c1256
  have c3502 : s 32 ≠ 0 := step3502 s c3499 c3488 c3475 c2126
  have c3503 : s 17 ≠ 0 := step3503 s c3499 c3475 c3488 c1456
  have c3511 : s 10 ≠ 1 := step3511 s c3502 c3402 c1112
  have c3516 : s 11 ≠ 1 := step3516 s c3502 c3402 c1157
  have c3517 : s 14 ≠ 1 := step3517 s c3502 c3402 c1292
  have c3521 : s 10 ≠ 3 := step3521 s c3502 c3413 c1114
  have c3522 : s 11 ≠ 3 := step3522 s c3502 c3413 c1159
  have c3527 : s 10 ≠ 2 := step3527 s c3503 c3470 c1128
  have c3528 : s 11 ≠ 2 := step3528 s c3503 c3470 c1178
  have c3546 : s 11 = 0 := step3546 s c3516 c3500 c1448
  have c3549 : s 59 ≠ 0 := step3549 s c3517 c3400 c3411 c3351
  have c3554 : s 16 ≠ 0 := step3554 s c3527 c3511 c3521 c1416
  have c3560 : s 31 ≠ 0 := step3560 s c3528 c3516 c3522 c2086
  have c3574 : s 34 = 1 := step3574 s c3546 c3421 c3403 c1166
  have c3579 : s 59 = 2 := step3579 s c3549 c3574 c2232
  have c3581 : s 8 ≠ 3 := step3581 s c3554 c3480 c1059
  have c3583 : s 8 ≠ 2 := step3583 s c3554 c3473 c1058
  have c3617 : s 8 ≠ 1 := step3617 s c3560 c3398 c1062
  have c3634 : s 43 = 0 := step3634 s c3579 c3474 c3343
  have c3643 : False := step3643 s c3583 c3617 c3634 c3581 c2596
  exact c3643

/-- Every map of the actual second arc four-clique into the template avoids
both private states, at every source vertex. -/
theorem no_private_arc (f : Arc A1 → Fin 5)
    (hf : ∀ p q, A2.Adj p q → Allowed (f p) (f q)) (p : Arc A1) :
    f p ≠ 1 ∧ f p ≠ 2 := by
  obtain ⟨i,rfl⟩ := point_surjective p
  constructor <;> intro he
  · exact no_private (fun i => f (point i)) (fun i j h => hf _ _ h) ⟨i,Or.inl he⟩
  · exact no_private (fun i => f (point i)) (fun i j h => hf _ _ h) ⟨i,Or.inr he⟩

#print axioms no_private
#print axioms no_private_arc
end Erdos595PrivateTriangleCertificate
